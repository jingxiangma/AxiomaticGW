"""Exact-request, corruption and optional kernel-binding tests for fiber-H replay.

Run FiberHReplay alone for pure Python checks. FiberHKernelReplay additionally
requires the separately accepted BlowupF1FiberHValue fixture and invokes Lean.
"""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from gkm_f1_fiber_h import emit, read_report

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/gkm-f1-fiber-h.json"
REPLAY = ROOT / "AxiomaticGW/GKM/Fixtures/BlowupF1FiberHReplay.lean"


def encoded(report):
    return (json.dumps(report, sort_keys=True, indent=2) + "\n").encode()


def coherent_value(raw, numerator=7, denominator=19):
    report = json.loads(raw)
    case = report["cases"][0]
    case["ordinary"] = [numerator, denominator]
    case["equivariant"] = {
        "numerator": [[[0, 0], [numerator, denominator]]],
        "denominator": [[[0, 0], [1, 1]]],
    }
    return encoded(report)


def kernel_cases(raw):
    """Three fresh negative proof obligations plus the unchanged positive control."""
    source = emit(raw)
    return [("positive", True, source),
            ("coherent_nonzero", False, emit(coherent_value(raw))),
            ("wrong_full_class", False, source.replace("⟨2, ![0, 1],", "⟨2, ![1, 0],")),
            ("wrong_power_state_pair", False, source.replace(
                "[⟨.hyperplane, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩]",
                "[⟨.hyperplane, 0⟩, ⟨.point, 1⟩, ⟨.point, 0⟩]"))]


class FiberHReplay(unittest.TestCase):
    def test_saved_report_and_deterministic_export(self):
        raw = REPORT.read_bytes()
        _, grouped = read_report(raw)
        self.assertFalse(grouped["X0"] or grouped["X2"])
        self.assertEqual(len(grouped["X1"]), 1)
        self.assertEqual(emit(raw), REPLAY.read_text())

    def test_exact_request_rejections(self):
        mutations = [
            lambda c: c.update(target="X0"),
            lambda c: c.update(genus=1),
            lambda c: c.update(**{"class": [1, 0]}),
            lambda c: c.update(**{"class": [0, 2]}),
            lambda c: c.update(powers=[0, 1, 0]),
            lambda c: c.update(labels=["pt", "H", "pt"]),
            lambda c: c.update(labels=["E1", "pt", "pt"]),
            lambda c: c.update(powers=[1, 0], labels=["H", "pt"]),
            lambda c: c.update(genus=True),
            lambda c: c.update(powers=[1.0, 0, 0]),
        ]
        for i, mutate in enumerate(mutations):
            with self.subTest(mutation=i):
                report = json.loads(REPORT.read_bytes()); mutate(report["cases"][0])
                with self.assertRaises(ValueError):
                    read_report(encoded(report))

    def test_complete_unique_request_coverage(self):
        for duplicate in [False, True]:
            with self.subTest(duplicate=duplicate):
                report = json.loads(REPORT.read_bytes())
                if duplicate:
                    report["cases"].append(copy.deepcopy(report["cases"][0]))
                else:
                    report["cases"].clear()
                with self.assertRaises(ValueError):
                    read_report(encoded(report))

    def test_source_and_runtime_rejections(self):
        mutations = [
            lambda r: r.update(input_sha256="0" * 64),
            lambda r: r["source"].update(revision="0" * 40),
            lambda r: r["environment"].update(sage="0.0"),
            lambda r: r.update(online_lookup=True),
            lambda r: r.update(cache_ephemeral=False),
            lambda r: r.update(kind="gkm_localization.plane_genus_two_line"),
            lambda r: r.update(schema_version=True),
        ]
        for i, mutate in enumerate(mutations):
            with self.subTest(mutation=i):
                report = json.loads(REPORT.read_bytes()); mutate(report)
                with self.assertRaises(ValueError):
                    read_report(encoded(report))

    def test_duplicate_json_key_rejected(self):
        raw = REPORT.read_text().replace('"genus": 2,', '"genus": 2, "genus": 2,', 1)
        with self.assertRaises(ValueError):
            read_report(raw)

    def test_invalid_exact_coefficients_rejected(self):
        mutations = [
            lambda c: c.update(ordinary=[0, 0]),
            lambda c: c.update(ordinary=[True, 1]),
            lambda c: c.update(ordinary=[1, 1]),
            lambda c: c["equivariant"].update(denominator=[]),
            lambda c: c["equivariant"].update(numerator=[[[0, 0], [1.0, 1]]]),
            lambda c: c["equivariant"].update(
                numerator=[[[0, 0], [1, 1]], [[0, 0], [1, 1]]]),
            lambda c: c["equivariant"].update(
                numerator=[[[0, 0], [1, 1]]], denominator=[[[1, 0], [1, 1]]]),
        ]
        for i, mutate in enumerate(mutations):
            with self.subTest(mutation=i):
                report = json.loads(REPORT.read_bytes()); mutate(report["cases"][0])
                with self.assertRaises(ValueError):
                    read_report(encoded(report))

    def test_incoming_answer_not_hardcoded(self):
        raw = coherent_value(REPORT.read_bytes())
        read_report(raw)  # Coherent arithmetic is deliberately insufficient for acceptance.
        source = emit(raw)
        self.assertIn("def value : ℚ := (7 / 19)", source)
        self.assertIn("(.inr request) = value", source)
        self.assertIn("BlowupF1FiberHValue.reconstructed_query", source)
        self.assertNotEqual(source, REPLAY.read_text())

    def test_negative_kernel_sources_are_distinct(self):
        cases = kernel_cases(REPORT.read_bytes())
        self.assertEqual([flag for _, flag, _ in cases], [True, False, False, False])
        self.assertEqual(len({source for _, _, source in cases}), 4)
        for _, _, source in cases:
            self.assertIn("theorem request_eq : request = BlowupF1FiberHValue.query", source)
            self.assertIn("(.inr request) = value", source)


class FiberHKernelReplay(unittest.TestCase):
    def test_actual_kernel_binding(self):
        for label, accepted, source in kernel_cases(REPORT.read_bytes()):
            with self.subTest(case=label), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "FiberHClaim.lean"
                path.write_text(source)
                result = subprocess.run(["lake", "env", "lean", "--memory=2048", str(path)],
                                        cwd=ROOT, text=True, capture_output=True, timeout=120)
                output = result.stdout + result.stderr
                if accepted:
                    self.assertEqual(result.returncode, 0, output)
                else:
                    self.assertNotEqual(result.returncode, 0, output)
                    self.assertTrue("false" in output or "unsolved goals" in output, output)


if __name__ == "__main__":
    unittest.main()

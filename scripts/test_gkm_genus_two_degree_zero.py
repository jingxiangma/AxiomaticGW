"""Exact query binding and kernel replay of degree-zero genus-two descendants."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from gkm_genus_two_degree_zero import check_report, emit, read_report

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/gkm-genus-two-degree-zero.json"
REPLAY = ROOT / "AxiomaticGW/GKM/Fixtures/GenusTwoDegreeZeroReplay.lean"


class GenusTwoDegreeZeroComparison(unittest.TestCase):
    def test_saved_report(self):
        self.assertEqual(len(check_report(REPORT.read_bytes())["cases"]), 3)
        self.assertEqual(emit(REPORT.read_bytes()), REPLAY.read_text())

    def test_duplicate_json_key(self):
        raw = REPORT.read_bytes().replace(
            b'"schema_version": 1', b'"schema_version": 1, "schema_version": 1')
        with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
            read_report(raw)

    def test_request_and_provenance_changes(self):
        original = json.loads(REPORT.read_bytes())
        mutations = [
            lambda r: r["cases"][0].update(genus=1),
            lambda r: r["cases"][0].update(powers=[1]),
            lambda r: r["cases"][1].update(**{"class": [1, 0]}),
            lambda r: r["cases"][2].update(labels=["E1"]),
            lambda r: r["cases"].pop(),
            lambda r: r["cases"].append(copy.deepcopy(r["cases"][0])),
            lambda r: r.update(input_sha256="0" * 64),
            lambda r: r.update(online_lookup=True),
        ]
        for i, mutate in enumerate(mutations):
            with self.subTest(mutation=i):
                report = copy.deepcopy(original)
                mutate(report)
                with self.assertRaises(ValueError):
                    check_report(json.dumps(report))

    def test_coherent_false_zero(self):
        report = json.loads(REPORT.read_bytes())
        report["cases"][0]["ordinary"] = [0, 1]
        report["cases"][0]["equivariant"] = {
            "numerator": [], "denominator": [[[0, 0], [1, 1]]]}
        # Both coefficient representations agree, but not with the held constant.
        with self.assertRaisesRegex(ValueError, "differs from the held ancestor constant"):
            check_report(json.dumps(report))

    def test_actual_kernel_binding(self):
        raw = REPORT.read_bytes()
        original = json.loads(raw)
        with tempfile.TemporaryDirectory(prefix="gw-g2-zero-binding-") as directory:
            def lean(name, source):
                path = Path(directory) / (name + ".lean")
                path.write_text(source)
                return subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                      text=True, capture_output=True)

            control = lean("accepted", emit(raw, cached=True))
            self.assertEqual(control.returncode, 0, control.stdout + control.stderr)
            for index, target in enumerate(("X0", "X1", "X2")):
                report = copy.deepcopy(original)
                case = next(c for c in report["cases"] if c["target"] == target)
                case["ordinary"] = [0, 1]
                case["equivariant"] = {
                    "numerator": [], "denominator": [[[0, 0], [1, 1]]]}
                corrupted = json.dumps(report).encode()
                # Exact specialization and provenance alone permit the forged zero.
                read_report(corrupted)
                rejected = lean("forged_value_" + str(index), emit(corrupted, cached=True))
                output = rejected.stdout + rejected.stderr
                with self.subTest(target=target):
                    self.assertNotEqual(rejected.returncode, 0, output)
                    self.assertIn("decide", output)
                    for failure in ("unknown module", "maximum recursion depth",
                                    "maximum number of heartbeats"):
                        self.assertNotIn(failure, output)

            # Bypass Python preflight to exercise Lean's full-request equality.
            source = emit(raw, cached=True)
            original_query = "⟨2, ![0], [⟨.unit, 2⟩]⟩"
            mutations = {
                "genus": "⟨1, ![0], [⟨.unit, 2⟩]⟩",
                "class": "⟨2, ![1], [⟨.unit, 2⟩]⟩",
                "power": "⟨2, ![0], [⟨.unit, 3⟩]⟩",
                "state": "⟨2, ![0], [⟨.hyperplane, 2⟩]⟩",
                "arity": "⟨2, ![0], []⟩",
            }
            self.assertEqual(source.count(original_query), 1)
            for field, replacement in mutations.items():
                rejected = lean("forged_" + field, source.replace(original_query, replacement))
                output = rejected.stdout + rejected.stderr
                with self.subTest(field=field):
                    self.assertNotEqual(rejected.returncode, 0, output)
                    self.assertIn("decide", output)
                    for failure in ("unknown module", "maximum recursion depth",
                                    "maximum number of heartbeats"):
                        self.assertNotIn(failure, output)


if __name__ == "__main__":
    unittest.main()

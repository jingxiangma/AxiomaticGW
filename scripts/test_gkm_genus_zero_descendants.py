#!/usr/bin/env python3
"""Offline coverage and kernel rejection of all-arity descendant claims."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from gkm_genus_zero_descendants import emit, query_text, read_report

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/gkm-genus-zero-descendants.json"
REPLAY = ROOT / "AxiomaticGW/GKM/Fixtures/GenusZeroDescendantReplay.lean"


class GenusZeroDescendantTests(unittest.TestCase):
    def setUp(self):
        self.raw = REPORT.read_bytes()
        self.report = json.loads(self.raw)

    def test_saved_replay_and_arities(self):
        self.assertEqual(emit(self.raw), REPLAY.read_text())
        self.assertEqual(len(self.report["cases"]), 34)
        self.assertEqual({len(c["powers"]) for c in self.report["cases"]}, {0, 1, 2, 4, 5, 6})

    def test_missing_duplicate_or_changed_request(self):
        for action in ("missing", "duplicate", "arity", "genus", "power", "label", "class"):
            report = copy.deepcopy(self.report)
            if action == "missing":
                report["cases"].pop()
            elif action == "duplicate":
                report["cases"].append(report["cases"][0])
            else:
                case = report["cases"][0]
                if action == "arity":
                    case["powers"].pop()
                    case["labels"].pop()
                elif action == "genus":
                    case["genus"] = 1
                elif action == "power":
                    case["powers"][0] = True
                elif action == "label":
                    case["labels"][0] = "H"
                else:
                    case["class"][0] = True
            with self.subTest(action=action), self.assertRaises(ValueError):
                read_report(json.dumps(report))

    def test_specialization_and_provenance(self):
        for action in ("value", "source", "schema", "cache"):
            report = copy.deepcopy(self.report)
            if action == "value":
                report["cases"][0]["ordinary"] = [0, 1]
            elif action == "source":
                report["input_sha256"] = "0" * 64
            elif action == "schema":
                report["kind"] = "gkm_localization.three_point_descendants"
            else:
                report["cache_ephemeral"] = False
            with self.subTest(action=action), self.assertRaises(ValueError):
                read_report(json.dumps(report))

    def test_duplicate_json_key(self):
        raw = self.raw.replace(b'"schema_version": 1', b'"schema_version": 1, "schema_version": 1')
        with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
            read_report(raw)

    def test_kernel_rejects_coherent_false_claims(self):
        reports = {}
        wrong = copy.deepcopy(self.report)
        wrong["cases"][0]["ordinary"] = [0, 1]
        wrong["cases"][0]["equivariant"] = {
            "numerator": [], "denominator": [[[0, 0], [1, 1]]]}
        reports["coherent_zero"] = (wrong, 0, "0", ".plane")
        for name, i, j, value, surface in [
                ("psi_monomial_swap", 0, 1, "2", ".plane"),
                ("unstable_request_swap", 9, 8, "1", ".plane"),
                ("equal_energy_curve_swap", 25, 24, "1", ".blowupTwo")]:
            report = copy.deepcopy(self.report)
            for field in ("ordinary", "equivariant"):
                report["cases"][i][field], report["cases"][j][field] = (
                    report["cases"][j][field], report["cases"][i][field])
            reports[name] = (report, i, value, surface)
        with tempfile.TemporaryDirectory(prefix="gw-genus-zero-negative-") as directory:
            def lean(name, source):
                path = Path(directory) / (name + ".lean")
                path.write_text(source)
                return subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                      text=True, capture_output=True, timeout=180)
            control = lean("positive", emit(self.raw))
            self.assertEqual(control.returncode, 0, control.stdout + control.stderr)
            for name, (report, i, value, surface) in reports.items():
                with self.subTest(case=name):
                    query = query_text(report["cases"][i])
                    witness = lean(name + "_counterexample",
                        "module\nimport AxiomaticGW.Surfaces.GenusZeroFullDescendants\n"
                        "open AxiomaticGW\nexample : SurfaceGenusZero.queryValue? "
                        f"(X := {surface}) {query} ≠ some ({value} : ℚ) := by decide +kernel\n")
                    self.assertEqual(witness.returncode, 0, witness.stdout + witness.stderr)
                    # Exact equivariant/ordinary coherence is preflight, not acceptance.
                    rejected = lean(name, emit(json.dumps(report).encode()))
                    output = rejected.stdout + rejected.stderr
                    self.assertNotEqual(rejected.returncode, 0)
                    self.assertIn("decide", output)
                    # Lean's fallback diagnostic can say "did not reduce" even
                    # after kernel reduction refutes the claim. The positive
                    # control and separate kernel counterexample establish the
                    # mathematical rejection, independently of that wording.
                    for failure in ("unknown module", "maximum recursion depth",
                                    "maximum number of heartbeats"):
                        self.assertNotIn(failure, output)


if __name__ == "__main__":
    unittest.main()

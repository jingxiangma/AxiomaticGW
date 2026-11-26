#!/usr/bin/env python3
"""Offline replay and rejection tests for actual three-point descendant claims."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from gkm_three_point_descendants import emit, read_report

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/gkm-three-point-descendants.json"
REPLAY = ROOT / "AxiomaticGW/GKM/Fixtures/ThreePointDescendantReplay.lean"


class ThreePointDescendantTests(unittest.TestCase):
    def setUp(self):
        self.raw = REPORT.read_bytes()
        self.report = json.loads(self.raw)

    def test_saved_replay_and_coverage(self):
        self.assertEqual(emit(self.raw), REPLAY.read_text())
        self.assertEqual(len(self.report["cases"]), 27)

    def test_duplicate_key(self):
        raw = self.raw.replace(b'"schema_version": 1', b'"schema_version": 1, "schema_version": 1')
        with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
            read_report(raw)

    def test_missing_or_duplicate_request(self):
        for duplicate in (False, True):
            report = copy.deepcopy(self.report)
            if duplicate:
                report["cases"].append(report["cases"][0])
            else:
                report["cases"].pop()
            with self.assertRaisesRegex(ValueError, "request coverage"):
                read_report(json.dumps(report))

    def test_wrong_genus_power_class_label(self):
        for field, value in [("genus", 1), ("powers", [True, 0, 0]),
                             ("class", [True]), ("labels", ["pt", "H", "unit"])]:
            report = copy.deepcopy(self.report)
            report["cases"][0][field] = value
            with self.assertRaises(ValueError):
                read_report(json.dumps(report))

    def test_source_and_environment(self):
        for field, value in [("input_sha256", "0" * 64), ("online_lookup", True),
                             ("cache_ephemeral", False)]:
            report = copy.deepcopy(self.report)
            report[field] = value
            with self.assertRaises(ValueError):
                read_report(json.dumps(report))

    def test_incorrect_specialization(self):
        self.report["cases"][2]["ordinary"] = [0, 1]
        with self.assertRaisesRegex(ValueError, "specialization"):
            read_report(json.dumps(self.report))

    def test_kernel_rejects_coherent_false_claims(self):
        reports = {}
        zeroed = copy.deepcopy(self.report)
        zeroed["cases"][2]["ordinary"] = [0, 1]
        zeroed["cases"][2]["equivariant"] = {
            "numerator": [], "denominator": [[[0, 0], [1, 1]]]}
        reports["coherent_zero"] = (zeroed,
            "(0 : ℚ) ≠ SurfaceDescendant.threePointValue .plane ![1] ![1,0,0] "
            "![.point,.hyperplane,.hyperplane]")
        swapped = copy.deepcopy(self.report)
        for field in ("ordinary", "equivariant"):
            swapped["cases"][2][field], swapped["cases"][5][field] = (
                swapped["cases"][5][field], swapped["cases"][2][field])
        reports["insertion_request_swap"] = (swapped,
            "(-2 : ℚ) ≠ SurfaceDescendant.threePointValue .plane ![1] ![1,0,0] "
            "![.point,.hyperplane,.hyperplane]")
        curves = copy.deepcopy(self.report)
        for field in ("ordinary", "equivariant"):
            curves["cases"][18][field], curves["cases"][19][field] = (
                curves["cases"][19][field], curves["cases"][18][field])
        reports["equal_energy_curve_swap"] = (curves,
            "(1 : ℚ) ≠ SurfaceDescendant.threePointValue .blowupTwo ![0,1,0] ![1,0,0] "
            "![.exceptional 0,.exceptional 0,.unit]")
        with tempfile.TemporaryDirectory(prefix="gw-threepoint-negative-") as directory:
            control = Path(directory) / "positive.lean"
            control.write_text(emit(self.raw))
            result = subprocess.run(["lake", "env", "lean", str(control)], cwd=ROOT,
                                    text=True, capture_output=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            for name, (report, counterexample) in reports.items():
                with self.subTest(case=name):
                    witness = Path(directory) / (name + "_counterexample.lean")
                    witness.write_text("module\nimport AxiomaticGW.Surfaces.ThreePointDescendants\n"
                                       "open AxiomaticGW\nexample : " + counterexample +
                                       " := by decide +kernel\n")
                    result = subprocess.run(["lake", "env", "lean", str(witness)], cwd=ROOT,
                                            text=True, capture_output=True, timeout=60)
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    # Exact fraction coherence passes preflight; it is not an acceptance proof.
                    path = Path(directory) / (name + ".lean")
                    path.write_text(emit(json.dumps(report).encode()))
                    result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                            text=True, capture_output=True, timeout=120)
                    output = result.stdout + result.stderr
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("decide", output)
                    for unexpected in ("unknown module", "maximum recursion depth",
                                       "maximum number of heartbeats"):
                        self.assertNotIn(unexpected, output)


if __name__ == "__main__":
    unittest.main()

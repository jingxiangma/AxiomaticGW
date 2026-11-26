#!/usr/bin/env python3
"""Offline schema/arithmetic tests and rejection of coherent false higher coefficients."""

import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from gkm_calibration_recursion import emit, read_report

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/gkm-higher-calibration-comparison.json"
REPLAY = ROOT / "AxiomaticGW/GKM/Fixtures/HigherCalibrationReplay.lean"


class HigherCalibrationTests(unittest.TestCase):
    def setUp(self):
        self.raw = REPORT.read_bytes()
        self.report = json.loads(self.raw)

    def test_frozen_replay_and_exact_arithmetic(self):
        self.assertEqual(emit(self.raw), REPLAY.read_text())
        self.assertEqual(len(self.report["cases"]), 30)
        self.assertEqual(sum(len(c["basis"])**2 for c in self.report["cases"]), 582)

    def test_duplicate_json_key(self):
        raw = self.raw.replace(b'"schema_version": 1', b'"schema_version": 1, "schema_version": 1')
        with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
            read_report(raw)

    def test_missing_and_repeated_request(self):
        for duplicate in (False, True):
            report = copy.deepcopy(self.report)
            if duplicate:
                report["cases"].append(report["cases"][0])
            else:
                report["cases"].pop()
            with self.assertRaisesRegex(ValueError, "request coverage"):
                read_report(json.dumps(report))

    def test_wrong_indices_and_boolean_class(self):
        for field, value in [("inverse_loop_power", 1), ("tail_psi_power", 0), ("class", [True])]:
            report = copy.deepcopy(self.report)
            report["cases"][0][field] = value
            with self.assertRaises(ValueError):
                read_report(json.dumps(report))

    def test_changed_basis_or_source(self):
        report = copy.deepcopy(self.report)
        report["cases"][0]["basis"].reverse()
        with self.assertRaisesRegex(ValueError, "basis order"):
            read_report(json.dumps(report))
        self.report["input_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "provenance"):
            read_report(json.dumps(self.report))

    def test_incorrect_specialization(self):
        self.report["cases"][0]["operator_ordinary"][0][1] = [123, 1]
        with self.assertRaisesRegex(ValueError, "specialization"):
            read_report(json.dumps(self.report))

    def test_kernel_rejects_coherent_false_values_and_indices(self):
        reports = {}
        zeroed = copy.deepcopy(self.report)
        case = zeroed["cases"][0]
        zero = {"numerator": [], "denominator": [[[0, 0], [1, 1]]]}
        for key in ("paired_equivariant", "operator_equivariant"):
            case[key] = [[copy.deepcopy(zero) for _ in case["basis"]] for _ in case["basis"]]
        case["operator_ordinary"] = [[[0, 1] for _ in case["basis"]] for _ in case["basis"]]
        reports["joint_zero_matrix"] = (zeroed, "(0 : ℚ) ≠ SurfaceDescendant.reconstructedCalibrationMatrix .plane 2 ![1] .unit .hyperplane")
        swapped = copy.deepcopy(self.report)
        for key in ("paired_equivariant", "operator_equivariant", "operator_ordinary"):
            swapped["cases"][0][key], swapped["cases"][1][key] = (
                swapped["cases"][1][key], swapped["cases"][0][key])
        reports["loop_power_swap"] = (swapped, "(1 : ℚ) ≠ SurfaceDescendant.reconstructedCalibrationMatrix .plane 2 ![1] .unit .unit")
        swapped_curves = copy.deepcopy(self.report)
        e1 = next(c for c in swapped_curves["cases"] if c["target"] == "X2" and
                  c["class"] == [1, 0, 0] and c["inverse_loop_power"] == 2)
        e2 = next(c for c in swapped_curves["cases"] if c["target"] == "X2" and
                  c["class"] == [0, 1, 0] and c["inverse_loop_power"] == 2)
        e1["class"], e2["class"] = e2["class"], e1["class"]
        reports["equal_energy_curve_swap"] = (swapped_curves, "(-1 : ℚ) ≠ SurfaceDescendant.reconstructedCalibrationMatrix .blowupTwo 2 ![0,1,0] (.exceptional 0) .unit")
        with tempfile.TemporaryDirectory(prefix="gw-higher-calibration-negative-") as directory:
            control = Path(directory) / "positive_control.lean"
            control.write_text(emit(self.raw))
            result = subprocess.run(["lake", "env", "lean", str(control)], cwd=ROOT,
                                    text=True, capture_output=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            for name, (report, counterexample) in reports.items():
                with self.subTest(case=name):
                    witness = Path(directory) / (name + "_counterexample.lean")
                    witness.write_text("module\nimport AxiomaticGW.Surfaces.CalibrationRecursion\n"
                                       "open AxiomaticGW\nexample : " + counterexample +
                                       " := by decide +kernel\n")
                    proof = subprocess.run(["lake", "env", "lean", str(witness)], cwd=ROOT,
                                           text=True, capture_output=True, timeout=60)
                    self.assertEqual(proof.returncode, 0, proof.stdout + proof.stderr)
                    path = Path(directory) / (name + ".lean")
                    # Coherent arithmetic is deliberately insufficient for acceptance.
                    path.write_text(emit(json.dumps(report).encode()))
                    result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                            text=True, capture_output=True, timeout=120)
                    output = result.stdout + result.stderr
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("decide", output)
                    self.assertNotIn("unknown module", output)
                    self.assertNotIn("maximum recursion depth", output)
                    self.assertNotIn("maximum number of heartbeats", output)


if __name__ == "__main__":
    unittest.main()

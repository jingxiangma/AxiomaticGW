#!/usr/bin/env python3
"""Offline arithmetic/schema tests and kernel rejection of coherent false matrices."""

import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from export_gkm_first_calibration import emit, read_report

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/gkm-first-calibration-comparison.json"
REPLAY = ROOT / "AxiomaticGW/GKM/Fixtures/FirstCalibrationReplay.lean"


class FirstCalibrationTests(unittest.TestCase):
    def setUp(self):
        self.raw = REPORT.read_bytes()
        self.report = json.loads(self.raw)

    def test_frozen_replay_and_exact_arithmetic(self):
        self.assertEqual(emit(self.raw), REPLAY.read_text())
        self.assertEqual(len(self.report["cases"]), 25)
        self.assertEqual(sum(len(c["basis"])**2 for c in self.report["cases"]), 564)

    def test_duplicate_json_key(self):
        raw = self.raw.replace(b'"schema_version": 1', b'"schema_version": 1, "schema_version": 1')
        with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
            read_report(raw)

    def test_missing_and_repeated_class(self):
        for duplicate in [False, True]:
            report = copy.deepcopy(self.report)
            if duplicate:
                report["cases"].append(report["cases"][0])
            else:
                report["cases"].pop()
            with self.assertRaisesRegex(ValueError, "curve coverage"):
                read_report(json.dumps(report))

    def test_indices_and_boolean_class(self):
        for field, value in [("inverse_loop_power", 2), ("tail_psi_power", 1),
                             ("class", [True])]:
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

    def test_specialization_and_denominator(self):
        self.report["cases"][0]["operator_ordinary"][0][-1] = [2, 1]
        with self.assertRaisesRegex(ValueError, "specialization"):
            read_report(json.dumps(self.report))
        self.report["cases"][0]["operator_ordinary"][0][-1] = [1, 0]
        with self.assertRaisesRegex(ValueError, "denominator"):
            read_report(json.dumps(self.report))

    def test_kernel_rejects_coherent_false_claims(self):
        reports = {}
        zeroed = copy.deepcopy(self.report)
        case = zeroed["cases"][0]
        zero = {"numerator": [], "denominator": [[[0, 0], [1, 1]]]}
        for key in ("paired_equivariant", "operator_equivariant"):
            case[key] = [[copy.deepcopy(zero) for _ in case["basis"]] for _ in case["basis"]]
        case["operator_ordinary"] = [[[0, 1] for _ in case["basis"]] for _ in case["basis"]]
        case["expected_ordinary"] = [[0 for _ in case["basis"]] for _ in case["basis"]]
        reports["joint_zero_matrix"] = zeroed
        swapped = copy.deepcopy(self.report)
        e1 = next(c for c in swapped["cases"] if c["target"] == "X2" and c["class"] == [1, 0, 0])
        e2 = next(c for c in swapped["cases"] if c["target"] == "X2" and c["class"] == [0, 1, 0])
        e1["class"], e2["class"] = e2["class"], e1["class"]
        reports["same_energy_curve_swap"] = swapped
        with tempfile.TemporaryDirectory(prefix="gw-calibration-negative-") as directory:
            for name, report in reports.items():
                with self.subTest(case=name):
                    path = Path(directory) / (name + ".lean")
                    path.write_text(emit(json.dumps(report).encode()))
                    result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                            text=True, capture_output=True, timeout=60)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("error", result.stdout + result.stderr)
                    self.assertNotIn("unknown module", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()

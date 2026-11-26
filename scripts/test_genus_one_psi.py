#!/usr/bin/env python3
"""Schema regressions and kernel rejection of corrupted held psi claims."""

import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from export_genus_one_psi import read_report, replay_source

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/genus-one-psi-exploration.json"
REPLAY = ROOT / "AxiomaticGW/Tautological/Fixtures/GenusOnePsiReplay.lean"


class PsiExchangeTests(unittest.TestCase):
    def setUp(self):
        self.raw = REPORT.read_bytes()
        self.report = json.loads(self.raw)

    def encoded(self):
        return json.dumps(self.report).encode()

    def test_frozen_export_reproduces(self):
        self.assertEqual(replay_source(self.raw), REPLAY.read_text())

    def test_duplicate_key_rejected(self):
        raw = self.raw.replace(b'"schema_version": 1', b'"schema_version": 1, "schema_version": 1')
        with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
            read_report(raw)

    def test_wrong_locus_or_normalization_rejected(self):
        for field, value in [("locus", "compact_type"), ("normalization", "divide_by_automorphisms")]:
            with self.subTest(field=field):
                report = copy.deepcopy(self.report)
                report[field] = value
                with self.assertRaises(ValueError):
                    read_report(json.dumps(report))

    def test_generator_provenance_rejected(self):
        self.report["generator_parameters"][0]["sigma"] = [True]
        with self.assertRaisesRegex(ValueError, "Wrong generator parameters"):
            read_report(self.encoded())

    def test_label_map_rejected(self):
        self.report["source_label_map"] = [[0, 0]]
        with self.assertRaisesRegex(ValueError, "Wrong label map"):
            read_report(self.encoded())

    def test_boolean_graph_integer_rejected(self):
        self.report["graphs"][0]["genus"] = [True]
        with self.assertRaises(ValueError):
            read_report(self.encoded())

    def test_zero_denominator_rejected(self):
        self.report["witness"][0][1] = 0
        with self.assertRaisesRegex(ValueError, "denominator"):
            read_report(self.encoded())

    def test_omitted_original_row_rejected(self):
        self.report["rows"].pop()
        with self.assertRaisesRegex(ValueError, "row count"):
            read_report(self.encoded())

    def test_kernel_rejects_corrupt_claims(self):
        mutations = {
            "wrong_raw_factor": lambda d: d["requested"].__setitem__(2, [-1, 12]),
            "psi_moved_to_kappa": lambda d: d["graphs"][1].update(kappa=[[1]], leg_psi=[0]),
            "changed_generator_row": lambda d: d["rows"][0].__setitem__(0, [103, 1]),
            "changed_witness": lambda d: d["witness"].__setitem__(0, [0, 1]),
            "hidden_column_rescaling": lambda d: d["column_factors"].__setitem__(2, [1, 2]),
            "lost_loop_automorphism": lambda d: d["automorphism_counts"].__setitem__(2, 1),
            "joint_zero_claim": lambda d: d.update(rows=[[[0, 1]] * 3] * 2,
                                                   requested=[[0, 1]] * 3, witness=[[0, 1]] * 2),
        }
        with tempfile.TemporaryDirectory(prefix="gw-psi-negative-") as directory:
            for name, mutate in mutations.items():
                with self.subTest(case=name):
                    report = copy.deepcopy(self.report)
                    mutate(report)
                    path = Path(directory) / (name + ".lean")
                    path.write_text(replay_source(json.dumps(report).encode()))
                    result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                            capture_output=True, text=True, timeout=60)
                    self.assertNotEqual(result.returncode, 0, name)
                    self.assertIn("error", result.stdout + result.stderr, name)
                    self.assertNotIn("unknown module", result.stdout + result.stderr, name)


if __name__ == "__main__":
    unittest.main()

#!/usr/bin/env python3
"""Offline parsing and kernel rejection tests for the complete L24 correction replay."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from export_l24_corrections import (FRAME_IDS, balanced_coordinates, dense, high_record_hints,
                                    read_report, replay_source, replay_sources)

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/l24-normalization-exploration.json"
REPLAY = ROOT / "AxiomaticGW/Tautological/Fixtures/L24CorrectionsReplay.lean"


class L24CorrectionTests(unittest.TestCase):
    def setUp(self):
        self.raw = REPORT.read_bytes()
        self.report = json.loads(self.raw)

    def test_reproducible_replay(self):
        self.assertEqual(replay_source(self.raw), REPLAY.read_text())
        for name, text in replay_sources(self.raw).items():
            self.assertEqual(text, REPLAY.with_name(name).read_text())
        self.assertEqual(len(self.report["steps"]), 66)
        self.assertEqual(len(self.report["wdvv"]), 5)

    def test_schema_and_context_binding(self):
        duplicate = self.raw.replace(b'"schema_version": 1',
                                     b'"schema_version": 1, "schema_version": 1')
        with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
            read_report(duplicate)
        mutations = [lambda d: d.update(extra=0),
                     lambda d: d.update(schema_version=True),
                     lambda d: d.update(normalization_scale=[True, 1]),
                     lambda d: d.update(normalization="stack_fundamental"),
                     lambda d: d.update(source="different formula"),
                     lambda d: d["permutations"][0].__setitem__(1, True),
                     lambda d: d["pictures"][0][1]["half_psi"][0].reverse(),
                     lambda d: d["graphs"][47]["half_psi"][0].__setitem__(0, 1),
                     lambda d: d["steps"][0]["order"].reverse(),
                     lambda d: d["steps"][29].update(anchors=[0, 0]),
                     lambda d: d["wdvv"][0].update(channel=1),
                     lambda d: d["steps"][0]["row"][0][1].__setitem__(1, 0),
                     lambda d: d["steps"][0]["row"].append(d["steps"][0]["row"][0]),
                     lambda d: d["wdvv"].pop(),
                     lambda d: d["source_sha256"].update(**{
                         "belorousski-pandharipande.json": "0" * 64})]
        for mutate in mutations:
            d = copy.deepcopy(self.report)
            mutate(d)
            with self.assertRaises(ValueError):
                read_report(json.dumps(d))

    def test_kernel_rejects_wrong_correction_coefficients(self):
        cases = (("L24HighPsi", "steps", 0, 0, "double_leading"),
                 ("L24HighPsi", "steps", 2, 2, "reverse_boundary"),
                 ("L24RationalPsi", "steps", 29, 0, "omit_boundary"),
                 ("L24WDVV", "wdvv", 0, 0, "hidden_division"))
        with tempfile.TemporaryDirectory(prefix="gw-l24-negative-") as tmp:
            for namespace, field, index, local_index, kind in cases:
                d = copy.deepcopy(self.report)
                row = d[field][index]["row"]
                if kind == "double_leading":
                    row[0][1][0] *= 2
                elif kind == "reverse_boundary":
                    row[1][1][0] *= -1
                elif kind == "omit_boundary":
                    row.pop()
                else:
                    row[0][1][1] *= 2
                # The parser is not the arithmetic proof boundary.
                read_report(json.dumps(d))
                family = {"L24HighPsi": "high", "L24RationalPsi": "rational",
                          "L24WDVV": "wdvv"}[namespace]
                module = {"high": "High", "rational": "Rational", "wdvv": "WDVV"}[family]
                path = Path(tmp) / (kind + ".lean")
                path.write_text(
                    f"import AxiomaticGW.Tautological.Fixtures.L24{module}CorrectionsReplay\n"
                    "open AxiomaticGW\nset_option maxRecDepth 20000\n"
                    "def altered : RelationCertificate.Coordinates 815 :=\n  " +
                    balanced_coordinates(dense(row)) + "\n"
                    f"example : {namespace}.correctionCoordinates {local_index} ≠ altered := by\n"
                    f"  rw [L24CorrectionsReplay.{family}{local_index}_checked]\n"
                    "  decide +kernel\n")
                result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                        text=True, capture_output=True, timeout=240)
                # Prove the altered claim false; a tactic/reduction error cannot pass.
                self.assertEqual(result.returncode, 0,
                                 kind + "\n" + result.stdout + result.stderr)

    def test_kernel_rejects_corrupted_record_hints(self):
        destination, source, records = high_record_hints(self.report)[2]
        leading = FRAME_IDS.index(self.report["steps"][2]["base"])
        needle = f"({leading}, 1)"
        self.assertIn(needle, records)
        with tempfile.TemporaryDirectory(prefix="gw-l24-record-negative-") as tmp:
            for kind, replacement in (("coefficient", f"({leading}, 2)"),
                                      ("destination", f"({leading + 1}, 1)")):
                path = Path(tmp) / (kind + ".lean")
                path.write_text(
                    "import AxiomaticGW.Tautological.L24HighPsi\n"
                    "import AxiomaticGW.Tautological.StrataCoordinateRecords\n"
                    "open AxiomaticGW AxiomaticGW.StrataOperation\n"
                    "set_option maxRecDepth 20000\n"
                    "def altered : List (Fin 815 × ℚ) := " +
                    records.replace(needle, replacement, 1) + "\n"
                    f"example : imageRecords {destination} {source} ≠ altered := by\n"
                    "  decide +kernel\n")
                result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                        text=True, capture_output=True, timeout=240)
                # Prove the altered claim false; a tactic/reduction error cannot pass.
                self.assertEqual(result.returncode, 0,
                                 kind + "\n" + result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main(verbosity=2)

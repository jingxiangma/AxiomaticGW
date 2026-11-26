#!/usr/bin/env python3
"""Offline provenance validation and kernel rejection of altered pullbacks."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from export_genus_two_psi_pullbacks import read_report, replay_source

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/genus-two-psi-pullbacks-exploration.json"
REPLAY = ROOT / "AxiomaticGW/Tautological/Fixtures/GenusTwoPsiPullbacksReplay.lean"


class PsiPullbackTests(unittest.TestCase):
    def setUp(self):
        self.raw = REPORT.read_bytes()
        self.report = json.loads(self.raw)

    def test_reproducible_replay(self):
        self.assertEqual(replay_source(self.raw), REPLAY.read_text())
        self.assertEqual([c["support_size"] for c in self.report["cases"]], [23, 53, 62])
        self.assertEqual(self.report["cases"][0]["coordinates"][8], [-1, 1])
        self.assertEqual(self.report["cases"][2]["coordinates"][29], [3, 1])

    def test_schema_and_provenance(self):
        duplicate = self.raw.replace(b'"schema_version": 1',
                                     b'"schema_version": 1, "schema_version": 1')
        with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
            read_report(duplicate)
        mutations = [lambda d: d.update(extra=0),
                     lambda d: d.update(schema_version=True),
                     lambda d: d["source_sha256"].update(**{"belorousski-pandharipande.json": "0"*64}),
                     lambda d: d["producer_sha256"].update(**{"admcycles.py": "0"*64}),
                     lambda d: d["cases"][0].update(new_arity=3),
                     lambda d: d["cases"][0].update(normalization="divide_by_automorphisms"),
                     lambda d: d["cases"][0]["coordinates"][8].__setitem__(1, 0),
                     lambda d: d["cases"][0]["coordinates"][8].__setitem__(0, True),
                     lambda d: d["cases"].pop()]
        for mutate in mutations:
            d = copy.deepcopy(self.report)
            mutate(d)
            with self.assertRaises(ValueError):
                read_report(json.dumps(d))

    def test_kernel_rejects_changed_mathematics(self):
        def reverse_tail(d):
            d["cases"][0]["coordinates"][8] = [1, 1]

        def omit_same_genus(d):
            d["cases"][2]["coordinates"][19] = [0, 1]

        def product_as_square(d):
            d["cases"][2]["coordinates"] = copy.deepcopy(d["cases"][1]["coordinates"])

        def hidden_division(d):
            d["cases"][2]["coordinates"][29] = [3, 2]

        def zero_claim(d):
            for c in d["cases"]:
                c["coordinates"] = [[0, 1] for _ in c["coordinates"]]

        with tempfile.TemporaryDirectory(prefix="gw-psi-pullback-negative-") as tmp:
            for mutate in (reverse_tail, omit_same_genus, product_as_square, hidden_division, zero_claim):
                d = copy.deepcopy(self.report)
                mutate(d)
                for c in d["cases"]:
                    c["support_size"] = sum(q[0] != 0 for q in c["coordinates"])
                path = Path(tmp) / (mutate.__name__ + ".lean")
                path.write_text(replay_source(json.dumps(d).encode()))
                result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                        text=True, capture_output=True, timeout=180)
                self.assertNotEqual(result.returncode, 0, mutate.__name__)
                self.assertIn("Tactic `decide`", result.stdout + result.stderr,
                              result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main(verbosity=2)

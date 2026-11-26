#!/usr/bin/env python3
"""Offline schema checks and kernel rejection of altered mathematical claims."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from export_genus_two_psi_product import read_report, replay_source

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/genus-two-psi-product-exploration.json"
REPLAY = ROOT / "AxiomaticGW/Tautological/Fixtures/GenusTwoPsiProductReplay.lean"


class GenusTwoPsiProductTests(unittest.TestCase):
    def setUp(self):
        self.raw = REPORT.read_bytes()
        self.report = json.loads(self.raw)

    def test_reproducible_replay_and_complete_remainder(self):
        self.assertEqual(replay_source(self.raw), REPLAY.read_text())
        self.assertEqual(sum(c[0] != 0 for c in self.report["boundary"]), 25)
        high = [i for i, c in enumerate(self.report["boundary"])
                if c[0] and 2 in self.report["graphs"][i]["genus"]]
        self.assertEqual(high, [8])
        self.assertEqual(self.report["boundary"][8], [3, 1])

    def test_rejects_malformed_and_changed_provenance(self):
        duplicate = self.raw.replace(b'"schema_version": 1',
                                     b'"schema_version": 1, "schema_version": 1')
        with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
            read_report(duplicate)
        mutations = [lambda d: d.update(extra=0),
                     lambda d: d.update(locus="compact_type"),
                     lambda d: d["graphs"][0].update(extra=0),
                     lambda d: d["graphs"][0].update(leg_psi=[True, 1]),
                     lambda d: d["graphs"][0].update(leg_vertices=[0, 1]),
                     lambda d: d["generator_provenance"][10].update(destinations=[7, 9, 19, 29]),
                     lambda d: d["generator_provenance"][0]["parameter"].update(sigma=[True]),
                     lambda d: d["producer_source_sha256"].update(**{"relations.py": "0"*64}),
                     lambda d: d["exploration"].update(online_lookup=True),
                     lambda d: d["witness"][0].__setitem__(1, 0),
                     lambda d: d["original_rows"][0].pop(),
                     lambda d: d["monomial_to_pushforward"].pop()]
        for mutate in mutations:
            d = copy.deepcopy(self.report)
            mutate(d)
            with self.assertRaises(ValueError):
                read_report(json.dumps(d))

    @staticmethod
    def lean(directory, name, report):
        path = Path(directory) / (name + ".lean")
        path.write_text(replay_source(json.dumps(report).encode()))
        return subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                              capture_output=True, text=True, timeout=180)

    def test_kernel_accepts_loop_isomorphism(self):
        d = copy.deepcopy(self.report)
        d["graphs"][26]["half_psi"] = [[0, 1]]
        with tempfile.TemporaryDirectory(prefix="gw-product-isomorphism-") as tmp:
            result = self.lean(tmp, "loop_branch_swap", d)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_kernel_rejects_altered_claims(self):
        def omitted_tail(d):
            d["boundary"][8] = [0, 1]
            d["requested"][8] = [0, 1]

        def erased_conversion(d):
            identity = [[[int(i == j), 1] for j in range(38)] for i in range(38)]
            d.update(original_rows=d["rows"], pushforward_to_monomial=identity,
                     monomial_to_pushforward=identity)

        def zero_claim(d):
            d.update(rows=[[[0, 1]]*38 for _ in range(13)],
                     original_rows=[[[0, 1]]*38 for _ in range(13)],
                     requested=[[0, 1]]*38, witness=[[0, 1]]*13,
                     boundary=[[int(i == 5), 1] for i in range(38)])

        mutations = {
            "wrong_node_branch": lambda d: d["graphs"][8].update(half_psi=[[1, 0]]),
            "product_replaced_by_square": lambda d: d["graphs"][5].update(leg_psi=[2, 0]),
            "omitted_genus_two_tail": omitted_tail,
            "changed_source_row": lambda d: d["original_rows"][10][7].__setitem__(0, -29),
            "automorphism_division": lambda d: d["column_factors"].__setitem__(37, [1, 8]),
            "wrong_decorated_order": lambda d: d["automorphism_counts"].__setitem__(26, 2),
            "erased_kappa_conversion": erased_conversion,
            "coherent_zero_claim": zero_claim,
        }
        with tempfile.TemporaryDirectory(prefix="gw-product-negative-") as tmp:
            for name, mutate in mutations.items():
                with self.subTest(case=name):
                    d = copy.deepcopy(self.report)
                    mutate(d)
                    result = self.lean(tmp, name, d)
                    output = result.stdout + result.stderr
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("decide", output)
                    for invalid_failure in ("unknown module", "maximum recursion depth",
                                            "maximum number of heartbeats", "unexpected token"):
                        self.assertNotIn(invalid_failure, output)


if __name__ == "__main__":
    unittest.main()

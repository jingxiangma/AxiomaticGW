#!/usr/bin/env python3
"""Schema, provenance, and independent kernel counterexamples for the marked frame."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from export_admcycles_certificate import rational_vector
from export_genus_two_psi_square import graph_source, read_report, replay_source

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/genus-two-psi-square-exploration.json"
REPLAY = ROOT / "AxiomaticGW/Tautological/Fixtures/GenusTwoPsiSquareReplay.lean"
PREFIX = ("module\nimport AxiomaticGW.Tautological.GenusTwoPsiSquare\n"
          "open AxiomaticGW RelationCertificate GenusTwoPsiSquare\n")


class GenusTwoPsiSquareTests(unittest.TestCase):
    def setUp(self):
        self.raw = REPORT.read_bytes()
        self.report = json.loads(self.raw)

    def test_saved_replay(self):
        self.assertEqual(replay_source(self.raw), REPLAY.read_text())
        self.assertEqual(len(self.report["graphs"]), 17)
        self.assertEqual(sum(q[0] != 0 for q in self.report["boundary"]), 10)

    def test_duplicate_and_unknown_fields(self):
        raw = self.raw.replace(b'"schema_version": 1', b'"schema_version": 1, "schema_version": 1')
        with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
            read_report(raw)
        for graph_field in (False, True):
            report = copy.deepcopy(self.report)
            (report["graphs"][0] if graph_field else report)["unexpected"] = 0
            with self.assertRaisesRegex(ValueError, "Unknown or missing"):
                read_report(json.dumps(report))

    def test_provenance_and_offline_scope(self):
        mutations = [lambda d: d.update(locus="compact_type"),
                     lambda d: d.update(normalization="divide_by_automorphisms"),
                     lambda d: d.update(source_label_map=[[0, 0]]),
                     lambda d: d["generator_parameters"][0].update(sigma=[True]),
                     lambda d: d["gluing_provenance"].update(target_columns=[4, 6, 15]),
                     lambda d: d["producer_source_sha256"].update(**{"relations.py": "0" * 64}),
                     lambda d: d["exploration"].update(online_lookup=True),
                     lambda d: d["environment"].update(admcycles="unreviewed")]
        for i, mutate in enumerate(mutations):
            with self.subTest(i=i):
                report = copy.deepcopy(self.report)
                mutate(report)
                with self.assertRaises(ValueError):
                    read_report(json.dumps(report))

    def test_boolean_and_out_of_range_graph_fields(self):
        for key, value in [("genus", [True]), ("leg_vertices", [1]),
                           ("leg_psi", [3]), ("kappa", [[0, True]])]:
            with self.subTest(key=key):
                report = copy.deepcopy(self.report)
                report["graphs"][0][key] = value
                with self.assertRaises(ValueError):
                    read_report(json.dumps(report))

    def test_bad_rationals_and_matrix_dimensions(self):
        mutations = [lambda d: d["witness"][0].__setitem__(1, 0),
                     lambda d: d["boundary"][0].__setitem__(0, True),
                     lambda d: d["rows"].pop(),
                     lambda d: d["original_rows"][0].pop(),
                     lambda d: d["pushforward_to_monomial"].pop(),
                     lambda d: d["monomial_to_pushforward"][0].pop()]
        for i, mutate in enumerate(mutations):
            with self.subTest(i=i):
                report = copy.deepcopy(self.report)
                mutate(report)
                with self.assertRaises(ValueError):
                    read_report(json.dumps(report))

    @staticmethod
    def lean(directory, name, source):
        path = Path(directory) / (name + ".lean")
        path.write_text(source)
        return subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                              capture_output=True, text=True, timeout=90)

    def test_equivalent_loop_branch_presentation(self):
        # A branch exchange of a loop is an isomorphism; moving across distinct
        # separating vertices below is not. Exact byte equality would conflate them.
        report = copy.deepcopy(self.report)
        report["graphs"][11]["half_psi"] = [[0, 1]]
        with tempfile.TemporaryDirectory(prefix="gw-g2-psi-isomorphic-") as directory:
            result = self.lean(directory, "branch_swap", replay_source(json.dumps(report).encode()))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_kernel_rejects_corrupt_claims_with_counterexamples(self):
        cases = []
        def case(name, mutate, counterexample):
            report = copy.deepcopy(self.report)
            mutate(report)
            cases.append((name, report, counterexample(report)))

        def graph_counterexample(report, index):
            return graph_source(index, report["graphs"][index]).split(
                "/-- Incoming decorations and incidence agree")[0] + (
                f"example : incomingGraph{index} ≠ columns {index} := by\n"
                "  simp only [columns, graph, decorate, DecoratedStableGraph.toDecoration_eq_mk,\n"
                f"    incomingGraph{index}]\n  decide +kernel\n")
        case("node_to_external", lambda d: d["graphs"][6].update(half_psi=[[0, 0]], leg_psi=[1]),
             lambda d: graph_counterexample(d, 6))
        case("wrong_separating_branch", lambda d: d["graphs"][6].update(half_psi=[[1, 0]]),
             lambda d: graph_counterexample(d, 6))
        case("kappa_square_swap", lambda d: d["graphs"][0].update(kappa=[[2, 0]]),
             lambda d: graph_counterexample(d, 0))
        case("hidden_automorphism_division", lambda d: d["column_factors"].__setitem__(16, [1, 8]),
             lambda d: "example : (1/8 : ℚ) ≠ 1 := by decide +kernel\n")
        case("pure_instead_of_decorated_order", lambda d: d["automorphism_counts"].__setitem__(11, 2),
             lambda d: "example : (graph 11).automorphismCount ≠ 2 := by\n"
                       "  simp only [graph, decorate, DecoratedStableGraph.toDecoration_eq_mk]\n"
                       "  decide +kernel\n")
        case("changed_boundary_row", lambda d: d["rows"][6].__setitem__(8, [103, 1]),
             lambda d: f"example : ({rational_vector(d['rows'][6])} : Coordinates 17) ≠ rows 6 := "
                       "by decide +kernel\n")
        case("wrong_source_row", lambda d: d["original_rows"][0].__setitem__(0, [0, 1]),
             lambda d: f"example : ({rational_vector(d['original_rows'][0])} : Coordinates 17) ≠ "
                       "pushforwardRows 0 := by decide +kernel\n")
        def erase_conversion(d):
            identity = [[[int(i == j), 1] for j in range(17)] for i in range(17)]
            d.update(original_rows=d["rows"], pushforward_to_monomial=identity,
                     monomial_to_pushforward=identity)
        case("coherent_erased_kappa_conversion", erase_conversion,
             lambda d: "example : (Pi.single (1 : Fin 17) (1 : ℚ)) ≠ pushforwardToMonomial 1 := "
                       "by decide +kernel\n")
        case("changed_witness", lambda d: d["witness"].__setitem__(6, [0, 1]),
             lambda d: f"example : check rows requested ⟨{rational_vector(d['witness'])}⟩ = false := "
                       "by decide +kernel\n")
        case("boundary_sign", lambda d: d["boundary"].__setitem__(9, [328, 1989]),
             lambda d: f"example : ({rational_vector(d['boundary'])} : Coordinates 17) ≠ boundary := "
                       "by decide +kernel\n")
        def zero_claim(d):
            d.update(rows=[[[0, 1]] * 17 for _ in range(7)],
                     original_rows=[[[0, 1]] * 17 for _ in range(7)],
                     requested=[[0, 1]] * 17, witness=[[0, 1]] * 7,
                     boundary=[[int(i == 3), 1] for i in range(17)])
        case("coherent_zero_claim", zero_claim,
             lambda d: "example : (0 : Coordinates 17) ≠ requested := by decide +kernel\n")
        with tempfile.TemporaryDirectory(prefix="gw-g2-psi-negative-") as directory:
            control = self.lean(directory, "positive", replay_source(self.raw))
            self.assertEqual(control.returncode, 0, control.stdout + control.stderr)
            for name, report, counterexample in cases:
                with self.subTest(case=name):
                    # Independently prove the specific held assertion is false.
                    witness = self.lean(directory, name + "_counterexample", PREFIX + counterexample)
                    self.assertEqual(witness.returncode, 0, witness.stdout + witness.stderr)
                    rejected = self.lean(directory, name, replay_source(json.dumps(report).encode()))
                    output = rejected.stdout + rejected.stderr
                    self.assertNotEqual(rejected.returncode, 0)
                    self.assertIn("decide", output)
                    for failure in ("unknown module", "maximum recursion depth",
                                    "maximum number of heartbeats", "unexpected token"):
                        self.assertNotIn(failure, output)


if __name__ == "__main__":
    unittest.main()

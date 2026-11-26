#!/usr/bin/env python3
"""Offline BP exchange tests, including kernel rejection and semantic counterexamples."""
import copy
import json
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import time
import unittest

from export_admcycles_certificate import rational_vector
from export_belorousski_pandharipande import graph_expression, read_report, replay_source

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/belorousski-pandharipande.json"
REPLAY = ROOT / "AxiomaticGW/Tautological/Fixtures/BelorousskiPandharipandeReplay.lean"
PREFIX = ("module\nimport AxiomaticGW.Tautological.BelorousskiPandharipande\n"
          "open AxiomaticGW RelationCertificate BelorousskiPandharipande\n")


class BPTests(unittest.TestCase):
    def setUp(self):
        self.raw = REPORT.read_bytes()
        self.report = json.loads(self.raw)

    def test_saved_replay(self):
        self.assertEqual(replay_source(self.raw), REPLAY.read_text())
        self.assertEqual(sum(q[0] != 0 for q in self.report["requested"]), 46)
        self.assertEqual(len(self.report["published_terms"]), 20)

    def test_schema_and_provenance(self):
        duplicate = self.raw.replace(b'"schema_version": 1', b'"schema_version": 1, "schema_version": 1')
        with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
            read_report(duplicate)
        mutations = [lambda d: d.update(unexpected=True),
            lambda d: d.update(locus="compact_type"),
            lambda d: d.update(normalization="average_orbit"),
            lambda d: d.update(source_label_map=[[0, 1], [1, 2], [2, 3]]),
            lambda d: d["generator_provenance"][0]["parameter"].update(sigma=[]),
            lambda d: d["generator_provenance"][4].update(vertex_one_based=1),
            lambda d: d["generator_provenance"][5].update(base_index=4),
            lambda d: d["generator_provenance"][0].update(upstream_index=0),
            lambda d: d["producer_source_sha256"].update(**{"relations.py": "0" * 64}),
            lambda d: d["exploration"].update(online_lookup=True),
            lambda d: d["environment"].update(admcycles="unreviewed"),
            lambda d: d["source_families"][0].update(genus=True),
            lambda d: d["graphs"][0].update(unexpected=0),
            lambda d: d["graphs"][0].update(genus=[True]),
            lambda d: d["graphs"][0].update(leg_vertices=[1, 0, 0]),
            lambda d: d["source_families"][0]["graphs"][0].update(leg_psi=[0]),
            lambda d: d["published_terms"][0].update(destinations=[27, 28, 29]),
            lambda d: d["witness"][0].__setitem__(1, 0),
            lambda d: d["rows"].pop(),
            lambda d: d["generator_provenance"][4]["coefficients"].pop(),
            lambda d: d["monomial_to_pushforward_off_diagonal"][0].__setitem__(0, 0)]
        for i, mutate in enumerate(mutations):
            with self.subTest(i=i):
                d = copy.deepcopy(self.report)
                mutate(d)
                with self.assertRaises(ValueError):
                    read_report(json.dumps(d))

    @staticmethod
    def lean(directory, name, source):
        path = Path(directory) / (name + ".lean")
        path.write_text(source)
        started = time.monotonic()
        process = subprocess.Popen(["lake", "env", "lean", str(path)], cwd=ROOT,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
        try:
            stdout, stderr = process.communicate(timeout=180)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.communicate()
            raise
        print(f"kernel {name}: exit={process.returncode}, seconds={time.monotonic() - started:.3f}",
              flush=True)
        return process.returncode, stdout + stderr

    def test_equivalent_graph_presentations(self):
        d = copy.deepcopy(self.report)
        d["graphs"][76]["half_psi"] = [[0, 1]]
        for g in (d["graphs"][13], d["source_families"][0]["graphs"][5]):
            g["genus"].reverse()
            g["kappa"].reverse()
            g["leg_vertices"] = [1 - v for v in g["leg_vertices"]]
            g["endpoints"] = [[1 - v for v in e] for e in g["endpoints"]]
        with tempfile.TemporaryDirectory(prefix="gw-bp-equivalent-") as directory:
            code, output = self.lean(directory, "equivalent", replay_source(json.dumps(d).encode()))
            self.assertEqual(code, 0, output)

    def test_kernel_rejection(self):
        cases = []
        def case(name, mutate, counterexample):
            d = copy.deepcopy(self.report)
            mutate(d)
            cases.append((name, d, counterexample(d)))

        def graph_neq(g, genus, n, target):
            definitions = ("sourceColumns, sourceGraph" if target.startswith("sourceColumns")
                           else "paperStratum, paperGraph" if target.startswith("paperStratum")
                           else "columns, graph")
            return (f"def changedGraph : DecoratedStableGraph (Fin {n}) := {graph_expression(g, genus, n)}\n"
                f"def changedColumn : TautologicalStratum {genus} (Fin {n}) :=\n"
                f"  .mk changedGraph (by decide +kernel)\n"
                f"example : changedColumn ≠ {target} := by\n"
                f"  simp only [changedColumn, changedGraph, {definitions}, tableGraph,\n"
                "    DecoratedStableGraph.toDecoration_eq_mk]\n  decide +kernel\n")

        case("wrong_node_branch", lambda d: d["graphs"][13].update(half_psi=[[1, 0]]),
             lambda d: graph_neq(d["graphs"][13], 2, 3, "columns 13"))
        case("wrong_external_label", lambda d: d["graphs"][12].update(leg_vertices=[0, 1, 0]),
             lambda d: graph_neq(d["graphs"][12], 2, 3, "columns 12"))
        case("wrong_component_decoration", lambda d: d["source_families"][0]["graphs"][0].update(
             kappa=[[0, 0]], leg_psi=[1, 0]),
             lambda d: graph_neq(d["source_families"][0]["graphs"][0], 2, 2,
                                 "sourceColumns 0 ⟨0, by decide +kernel⟩"))
        case("wrong_published_branch", lambda d: d["published_terms"][3]["graph"].update(half_psi=[[0, 1]]),
             lambda d: graph_neq(d["published_terms"][3]["graph"], 2, 3, "paperStratum 3"))
        case("changed_original_row", lambda d: d["original_rows"][0][0].__setitem__(0, 0),
             lambda d: f"example : ({rational_vector(d['original_rows'][0])} : Coordinates 100) ≠ originalRows 0 := by decide +kernel\n")
        case("changed_glued_source_row", lambda d: d["generator_provenance"][4]["coefficients"][0].__setitem__(0, -16),
             lambda d: f"example : ({rational_vector(d['generator_provenance'][4]['coefficients'])} : Coordinates 7) ≠ sourceRow 0 := by decide +kernel\n")
        case("changed_witness", lambda d: d["witness"].__setitem__(0, [0, 1]),
             lambda d: f"example : check rows requested ⟨{rational_vector(d['witness'])}⟩ = false := by decide +kernel\n")
        case("hidden_automorphism_division", lambda d: d["column_factors"].__setitem__(90, [1, 2]),
             lambda d: "example : (1/2 : ℚ) ≠ 1 := by decide +kernel\n")
        case("lost_tail_exchange", lambda d: d["published_terms"][4].update(automorphism=1),
             lambda d: "example : automorphismOrders (representative 4) ≠ 1 := by decide +kernel\n")
        case("erased_kappa_correction", lambda d: d["pushforward_to_monomial_off_diagonal"][0].__setitem__(2, [0, 1]),
             lambda d: "example : toMonomial (Pi.single 1 1) ≠ Pi.single 1 1 := by decide +kernel\n")
        case("wrong_permutation", lambda d: d["permutation_destinations"][0].__setitem__(12, 15),
             lambda d: "example : columnPermutation 0 12 ≠ 15 := by decide +kernel\n")
        case("lost_repeated_assignment", lambda d: d["published_terms"][1]["destinations"].__setitem__(5, 13),
             lambda d: "example : columnPermutation 5 (representative 1) ≠ 13 := by decide +kernel\n")
        def change_destinations(d):
            for p in d["generator_provenance"][4:]:
                if p["source_family"] == 1:
                    p["destinations"][0] = 21
        case("wrong_gluing_destination", change_destinations,
             lambda d: "example : sourceDestinations 1 ⟨0, by decide +kernel⟩ ≠ 21 := by decide +kernel\n")
        def average_rows(d):
            for row in d["rows"]:
                for q in row:
                    q[1] *= 6
            for q in d["witness"]:
                q[0] *= 6
        case("coherent_orbit_averaging", average_rows,
             lambda d: f"example : ({rational_vector(d['rows'][0])} : Coordinates 100) ≠ rows 0 := by decide +kernel\n")
        def erase_claim(d):
            for field in ("rows", "original_rows", "unsymmetrized_rows"):
                d[field] = [[[0, 1]] * 100 for _ in range(20)]
            d["requested"] = [[0, 1]] * 100
            d["witness"] = [[0, 1]] * 20
        case("coherent_zero_claim", erase_claim,
             lambda d: "example : (0 : Coordinates 100) ≠ requested := by decide +kernel\n")
        with tempfile.TemporaryDirectory(prefix="gw-bp-negative-") as directory:
            for name, report, counterexample in cases:
                with self.subTest(case=name):
                    code, output = self.lean(directory, name, replay_source(json.dumps(report).encode()))
                    self.assertNotEqual(code, 0, "Corrupted complete exchange was accepted")
                    self.assertIn("BP incoming", output)
                    self.assertIn("check did not close", output)
                    self.assertNotIn("maximum recursion depth", output)
                    self.assertNotIn("timeout", output)
                    code, output = self.lean(directory, name + "_counterexample", PREFIX + counterexample)
                    self.assertEqual(code, 0, output)


if __name__ == "__main__":
    unittest.main()

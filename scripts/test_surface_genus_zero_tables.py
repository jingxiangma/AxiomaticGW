#!/usr/bin/env python3
"""Candidate provenance/coverage regressions; Lean separately proves acceptance."""

import json
from fractions import Fraction
import sys
import unittest

sys.dont_write_bytecode = True
import export_surface_genus_zero_tables as exchange


class GenusZeroTableExchange(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report = exchange.payload()
        cls.tables = {target: exchange.table(target) for target in exchange.TARGETS}

    def test_frozen_output_is_reproducible(self):
        for path, content in exchange.outputs().items():
            with self.subTest(path=path.name):
                self.assertEqual(path.read_text(), content)

    def test_complete_bound_includes_all_zeros(self):
        self.assertEqual([len(c["rows"]) for c in self.report["cases"]], [5, 49, 455])
        geometric = 0
        for case in self.report["cases"]:
            curves = [tuple(row["curve"]) for row in case["rows"]]
            self.assertEqual(len(curves), len(set(curves)))
            self.assertEqual(curves, exchange.bounded(case["target"]))
            for row in case["rows"]:
                if row["energy"]:
                    geometric += 1
                    self.assertEqual(row["domain"], "geometric")
                    self.assertEqual(row["point_count"], row["energy"] - 1)
                else:
                    self.assertEqual(row["domain"], "auxiliary_zero_class_empty_query")
                    self.assertEqual(row["value"], [0, 1])
        self.assertEqual(geometric, 506)

    def test_independent_published_plane_values(self):
        self.assertEqual([self.tables["P2"][(d,)] for d in range(1, 5)], [1, 1, 12, 620])
        plane_manifest = json.loads((exchange.ROOT /
            "environments/plane-primary-genus-zero-benchmarks.json").read_text())
        self.assertEqual([str(self.tables["P2"][tuple(q["curve_coordinates"])])
                          for q in plane_manifest["queries"]],
                         [q["expected_rational"] for q in plane_manifest["queries"]])

    def test_exceptional_and_ruling_intersections(self):
        self.assertEqual(exchange.intersection("F1", (1, 0), (1, 0)), -1)
        self.assertEqual(exchange.intersection("F1", (0, 1), (0, 1)), 0)
        self.assertEqual(exchange.intersection("F1", (1, 1), (1, 0)), 0)
        self.assertEqual(exchange.intersection("Bl2P2", (1, 0, 0), (0, 1, 0)), 0)
        self.assertEqual(exchange.intersection("Bl2P2", (1, 0, 0), (0, 0, 1)), 1)

    def test_exceptional_coordinates_are_not_energy(self):
        self.assertEqual(exchange.energy("Bl2P2", (3, 3, 3)),
                         exchange.energy("Bl2P2", (9, 0, 0)))
        self.assertEqual(self.tables["Bl2P2"][(3, 3, 3)], 12)
        self.assertEqual(self.tables["Bl2P2"][(9, 0, 0)], 0)

    def test_two_exceptional_labels_are_symmetric(self):
        values = self.tables["Bl2P2"]
        for (a, b, c), value in values.items():
            self.assertEqual(value, values[(b, a, c)])

    def test_existing_gkm_primary_point_regressions(self):
        # Numerical compatibility only: this does not certify imported CohFT classes.
        gkm = json.loads((exchange.ROOT / "environments/gkm-inputs-osx-arm64.json").read_text())
        targets = {"X0": "P2", "X1": "F1", "X2": "Bl2P2"}
        checked = 0
        for target in gkm["targets"]:
            name = targets[target["target"]]
            for query in target["queries"]:
                if query["genus"] != 0:
                    continue
                curve = tuple(query["class"])
                self.assertEqual(len(query["insertions"]), exchange.energy(name, curve) - 1)
                for insertion in query["insertions"]:
                    self.assertEqual(target["basis"][insertion["basis"]], "pt")
                    self.assertEqual(insertion["psi"], 0)
                value = query["claimed_value"]
                self.assertEqual(value["denominator"], [[[0, 0], [1, 1]]])
                self.assertEqual(len(value["numerator"]), 1)
                self.assertEqual(value["numerator"][0][0], [0, 0])
                self.assertEqual(self.tables[name][curve], Fraction(*value["numerator"][0][1]))
                checked += 1
        self.assertEqual(checked, 3)

    def test_low_energy_domain_is_explicit(self):
        self.assertEqual(exchange.low_energy("F1", (2, 0)), 0)
        self.assertEqual(exchange.low_energy("Bl2P2", (0, 0, 2)), 0)
        self.assertEqual(exchange.low_energy("Bl2P2", (1, 1, 1)), 1)
        with self.assertRaises(ValueError):
            exchange.low_energy("Bl2P2", (2, 2, 2))

    def test_invalid_coordinates_are_rejected(self):
        for curve in [(1,), (1, -1), (True, 0), (1.0, 0)]:
            with self.subTest(curve=curve), self.assertRaises(ValueError):
                exchange.energy("F1", curve)

    def test_binomial_boundary_is_signed(self):
        self.assertEqual(exchange.choose(3, -1), 0)
        self.assertEqual(exchange.choose(3, 4), 0)
        self.assertEqual(exchange.choose(3, 0), 1)
        with self.assertRaises(ValueError):
            exchange.choose(-1, 0)


if __name__ == "__main__":
    unittest.main()

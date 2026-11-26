#!/usr/bin/env python3
"""Published-value and full-class checks; Lean separately proves acceptance."""

from fractions import Fraction
import sys
import unittest

sys.dont_write_bytecode = True
import export_surface_genus_one_tables as exchange


class GenusOneTableExchange(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report = exchange.payload()
        cls.tables = {name: exchange.table(name) for name in exchange.TARGETS}

    def test_frozen_output_is_reproducible(self):
        for path, content in exchange.outputs().items():
            with self.subTest(path=path.name):
                self.assertEqual(path.read_text(), content)

    def test_complete_bound_and_point_counts(self):
        self.assertEqual([len(c["rows"]) for c in self.report["cases"]], [5, 49, 455])
        geometric = 0
        for case in self.report["cases"]:
            curves = [tuple(row["curve"]) for row in case["rows"]]
            self.assertEqual(len(curves), len(set(curves)))
            for row in case["rows"]:
                self.assertEqual(row["point_count"], row["energy"])
                if row["energy"]:
                    geometric += 1
                    self.assertEqual(row["domain"], "geometric")
                else:
                    self.assertEqual(row["domain"], "auxiliary_zero_class_empty_query")
                    self.assertEqual(row["value"], [0, 1])
        self.assertEqual(geometric, 506)

    def test_published_getzler_and_chaudhuri_das_values(self):
        self.assertEqual([self.tables["P2"][(d,)] for d in range(1, 5)], [0, 0, 1, 225])
        self.assertEqual(self.tables["F1"][(2, 5)], 240)
        self.assertEqual(self.tables["Bl2P2"][(2, 3, 5)], 20)
        for anchor in self.report["published_anchors"]:
            self.assertEqual(self.tables[anchor["target"]][tuple(anchor["curve"])],
                             Fraction(*anchor["value"]))

    def test_published_blowup_comparison_for_zero_or_minus_one(self):
        # Chaudhuri--Das section 8: forgetting a coefficient 0 or -1 preserves the value.
        for degree in range(1, 5):
            expected = self.tables["P2"][(degree,)]
            for e1 in [0, -1]:
                self.assertEqual(self.tables["F1"][(degree + e1, degree)], expected)
                for e2 in [0, -1]:
                    self.assertEqual(
                        self.tables["Bl2P2"][(degree + e1, degree + e2, degree)], expected)

    def test_exceptional_labels_are_symmetric_but_not_collapsed_to_energy(self):
        values = self.tables["Bl2P2"]
        for (a, b, c), value in values.items():
            self.assertEqual(value, values[(b, a, c)])
        self.assertEqual(values[(3, 4, 5)], 13775)
        self.assertEqual(values[(12, 0, 0)], 0)

    def test_signed_binomial_boundaries(self):
        self.assertEqual(exchange.choose(3, -1), 0)
        self.assertEqual(exchange.choose(3, 4), 0)
        self.assertEqual(exchange.choose(3, 0), 1)
        with self.assertRaises(ValueError):
            exchange.choose(-1, 0)


if __name__ == "__main__":
    unittest.main()

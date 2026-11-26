#!/usr/bin/env python3
"""Check frozen surface exchange data; mathematical acceptance is Lean's job."""

from collections import defaultdict
from fractions import Fraction
import json
import sys
import unittest

sys.dont_write_bytecode = True
import export_surface_equations as exchange


def freeze(value):
    return tuple(map(freeze, value)) if isinstance(value, (list, tuple)) else value


class SurfaceEquationExchange(unittest.TestCase):
    def test_reproducible_frozen_module(self):
        destination = exchange.ROOT / "AxiomaticGW/Surfaces/Fixtures/GetzlerReplay.lean"
        self.assertEqual(exchange.export(), destination.read_text())

    def test_uncollected_contributions_agree_with_sage(self):
        report = json.loads(exchange.SOURCE.read_bytes())
        frame = json.loads(exchange.FRAME.read_bytes())
        counts = []
        for case, (target, curve, extra, _, _) in zip(report["cases"], exchange.REQUESTS):
            expanded = exchange.expanded_terms(frame, target, curve, extra)
            counts.append(len(expanded))
            collected = defaultdict(Fraction)
            for monomial, coefficient in expanded:
                collected[freeze(monomial)] += Fraction(*coefficient)
            expected = {freeze(m): Fraction(*c) for m, c in case["terms"]}
            self.assertEqual({m: c for m, c in collected.items() if c}, expected)
        self.assertEqual(counts, [16, 34, 72, 3])

    def test_full_curve_coordinates_are_preserved(self):
        first = exchange.point_variable("blowupTwo", ["query", 1, [1, 0, 0], [[2, 0]]])
        second = exchange.point_variable("blowupTwo", ["query", 1, [0, 1, 0], [[2, 0]]])
        self.assertNotEqual(first, second)
        with self.assertRaises(ValueError):
            exchange.point_variable("blowupTwo", ["query", 1, [1], [[2, 0]]])

    def test_powers_and_nonpoint_states_are_not_erased(self):
        for insertion in [[2, 1], [1, 0], [0, 0], [2, False], [2.0, 0]]:
            with self.subTest(insertion=insertion), self.assertRaises(ValueError):
                exchange.point_variable("plane", ["query", 1, [1], [insertion]])

    def test_residual_ancestors_are_not_relabelled_as_queries(self):
        with self.assertRaises(ValueError):
            exchange.point_variable("plane", ["ancestor", 1, [1], [[2, 0]]])

    def test_nonintegral_and_negative_data_are_rejected(self):
        for curve in [[-1], [True], [1.5]]:
            with self.subTest(curve=curve), self.assertRaises(ValueError):
                exchange.point_variable("plane", ["query", 1, curve, []])
        for genus in [-1, True, 1.5]:
            with self.subTest(genus=genus), self.assertRaises(ValueError):
                exchange.point_variable("plane", ["query", genus, [1], []])

    def test_exact_rational_coefficients_are_required(self):
        for coefficient in [[1, 0], [1, -2], [True, 1], [1.5, 2]]:
            with self.subTest(coefficient=coefficient), self.assertRaises(ValueError):
                exchange.lean_terms("plane", [[[], coefficient]])

    def test_complete_original_column_count_is_required(self):
        frame = json.loads(exchange.FRAME.read_bytes())
        frame["graphs"] = frame["graphs"][:-1]
        with self.assertRaises(ValueError):
            exchange.expanded_terms(frame, "P2", (1,), 1)

    def test_original_labels_are_checked(self):
        frame = json.loads(exchange.FRAME.read_bytes())
        for labels in [(1, 1, 1), (1, 1, 1, 1, 1), (1, 1, 1, True),
                       (1, 1, 1, 1.0), (1, 1, 1, -1), (1, 1, 1, 4)]:
            with self.subTest(labels=labels), self.assertRaises(ValueError):
                exchange.expanded_terms(frame, "F1", (2, 0), 0, labels)

    def test_exceptional_requests_agree_with_sage(self):
        report = json.loads((exchange.ROOT / "environments/surface-exceptional-exploration.json").read_bytes())
        frame = json.loads(exchange.FRAME.read_bytes())
        self.assertEqual(len(report["cases"]), 9)
        for case in report["cases"]:
            columns = exchange.expanded_columns(frame, case["target"], tuple(case["curve"]),
                                                0, case["original_labels"])
            self.assertEqual(list(map(len, columns)), case["column_contributions"])
            collected = defaultdict(Fraction)
            for column in columns:
                for monomial, coefficient in column:
                    collected[freeze(monomial)] += Fraction(*coefficient)
            self.assertEqual({m: c for m, c in collected.items() if c},
                             {freeze(m): Fraction(*c) for m, c in case["terms"]})

    def test_exceptional_labels_do_not_collapse_to_equal_energy(self):
        frame = json.loads(exchange.FRAME.read_bytes())
        first = exchange.expanded_terms(frame, "Bl2P2", (2, 0, 0), 0, (1, 3, 3, 3))
        second = exchange.expanded_terms(frame, "Bl2P2", (2, 0, 0), 0, (1, 4, 4, 4))
        self.assertNotEqual(first, second)

    def test_wdvv_requires_its_complete_three_column_frame(self):
        frame = json.loads((exchange.ROOT / "environments/wdvv-candidate-osx-arm64.json").read_bytes())
        with self.assertRaises(ValueError):
            exchange.expanded_columns(frame, "P2", (2,), 2)
        for count in [True, 3.0, 0, -3]:
            with self.subTest(count=count), self.assertRaises(ValueError):
                exchange.expanded_columns(frame, "P2", (2,), 2, expected_columns=count)
        frame["graphs"].pop(1)  # Even the zero-weight column belongs to the held frame.
        with self.assertRaises(ValueError):
            exchange.expanded_columns(frame, "P2", (2,), 2, expected_columns=3)

    def test_wdvv_base_case_requests_agree_with_sage(self):
        report = json.loads((exchange.ROOT / "environments/surface-wdvv-base-cases.json").read_bytes())
        frames = {"WDVV": json.loads((exchange.ROOT / "environments/wdvv-candidate-osx-arm64.json").read_bytes()),
                  "Getzler": json.loads(exchange.FRAME.read_bytes())}
        self.assertEqual(len(report["cases"]), 9)
        for case in report["cases"]:
            columns = exchange.expanded_columns(frames[case["relation"]], case["target"],
                tuple(case["curve"]), case["extra_markings"], case["original_labels"],
                expected_columns=3 if case["relation"] == "WDVV" else 33)
            self.assertEqual(list(map(len, columns)), case["column_contributions"])
            collected = defaultdict(Fraction)
            for column in columns:
                for monomial, coefficient in column:
                    collected[freeze(monomial)] += Fraction(*coefficient)
            self.assertEqual({m: c for m, c in collected.items() if c},
                             {freeze(m): Fraction(*c) for m, c in case["terms"]})

    def test_conic_marking_count_cannot_be_changed(self):
        frame = json.loads((exchange.ROOT / "environments/wdvv-candidate-osx-arm64.json").read_bytes())
        correct = exchange.expanded_columns(frame, "P2", (2,), 2, (1, 1, 2, 2), expected_columns=3)
        changed = exchange.expanded_columns(frame, "P2", (2,), 1, (1, 1, 2, 2), expected_columns=3)
        self.assertNotEqual(correct, changed)


if __name__ == "__main__":
    unittest.main()

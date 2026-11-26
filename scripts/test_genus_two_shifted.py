#!/usr/bin/env python3
"""Reject altered requests and compare finite shifted rows with their held report.

These exchange regressions do not replay the native numerical rows in Lean.
The general evaluator theorem and the small graph regression proofs are separate.
"""
import copy
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest

from explore_genus_two_shifted import compare, validate_payload

ROOT = Path(__file__).resolve().parents[1]
PAYLOAD = ROOT / "environments/genus-two-shifted-native.json"
REPORT = ROOT / "environments/genus-two-shifted-exploration.json"


class ShiftedExchangeTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(PAYLOAD.read_bytes())
        cls.report = json.loads(REPORT.read_bytes())

    def test_exact_rows_and_proof_boundary(self):
        rows = validate_payload(self.data)
        self.assertEqual(len(rows), 10)
        held = {r["name"]: [Fraction(*c) for c in r["coefficients"]] for r in self.report["rows"]}
        self.assertEqual(rows, held)
        self.assertEqual(self.report["determinant_coefficients"], [[0, 1], [7776, 1]])
        self.assertTrue(self.report["proof_boundary"]["uniform_symbolic_compression_proved_in_lean"])
        self.assertFalse(self.report["proof_boundary"]["complete_reconstruction_or_new_invariant"])
        self.assertTrue(self.report["proof_boundary"]["uniform_ppp_row_proved_in_lean"])
        self.assertTrue(self.report["proof_boundary"]["ppp_one_degree_remainder_support_proved_in_lean"])
        self.assertTrue(self.report["proof_boundary"]["mixed_rational_complement_formulas_proved_in_lean"])
        self.assertTrue(self.report["proof_boundary"]["mixed_rows_source_degree_cancellation_proved_in_lean"])
        self.assertTrue(self.report["proof_boundary"]["mixed_rows_strict_source_degree_support_proved_in_lean"])
        self.assertTrue(self.report["proof_boundary"]["uniform_hpp_row_proved_in_lean"])
        self.assertTrue(self.report["proof_boundary"]["hpp_canonical_support_proved_in_lean"])
        self.assertTrue(self.report["proof_boundary"]["hpp_lower_degree_after_canonical_block_proved_in_lean"])
        self.assertTrue(self.report["proof_boundary"]["uniform_hhp_row_proved_in_lean"])
        self.assertTrue(self.report["proof_boundary"]["hhp_canonical_support_proved_in_lean"])
        self.assertTrue(self.report["proof_boundary"]["mixed_rows_lower_degree_after_canonical_block_proved_in_lean"])
        self.assertTrue(self.report["proof_boundary"]["uniform_shifted_determinant_proved_in_lean"])
        self.assertTrue(self.report["proof_boundary"]["exact_shifted_block_solver_proved_in_lean"])
        self.assertTrue(self.report["proof_boundary"]["collected_remainder_strict_decrease_proved_in_lean"])
        self.assertTrue(self.report["proof_boundary"]["solved_step_from_original_geometry_proved_in_lean"])
        self.assertTrue(self.report["proof_boundary"]["canonical_step_uniqueness_from_lower_degrees_proved_in_lean"])
        self.assertFalse(self.report["proof_boundary"]["lower_degree_recursive_evaluation_proved_in_lean"])
        self.assertEqual(self.report["proof_boundary"]["uniform_symbolic_compression_scope"],
                         "Positive-degree HHP/HPP/PPP canonical block only")
        self.assertEqual(self.report["input_sha256"], hashlib.sha256(PAYLOAD.read_bytes()).hexdigest())
        for path, pin in self.report["source_sha256"].items():
            self.assertEqual(hashlib.sha256((ROOT / path).read_bytes()).hexdigest(), pin, path)

    def test_request_corruptions(self):
        def source(c): c["source_curve"][0] -= 1
        def target(c): c["variable_curve"][0] += 1
        def markings(c): c["additional_markings"] += 1
        def labels(c): c["labels"][0] = 2
        def column(c): c["columns"][0]["curve"][0] += 1
        def power(c): c["columns"][0]["insertions"][0][1] = 1
        def denominator(c): c["coefficients"][0][1] = 0
        def missing(c): c["coefficients"].pop()
        for mutation in (source, target, markings, labels, column, power, denominator, missing):
            data = copy.deepcopy(self.data)
            mutation(data["cases"][0])
            with self.subTest(mutation=mutation.__name__), self.assertRaises(ValueError):
                validate_payload(data)
        data = copy.deepcopy(self.data)
        data["cases"][-1] = data["cases"][0]
        with self.assertRaises(ValueError):
            validate_payload(data)

    def test_value_change_is_not_an_accepted_claim(self):
        data = copy.deepcopy(self.data)
        data["cases"][0]["coefficients"][0][0] += 1
        # Syntactic validity is deliberately weaker than the actual comparison.
        validate_payload(data)
        with self.assertRaisesRegex(ValueError, "Native/symbolic coefficient mismatch"):
            compare(json.dumps(data).encode())


if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="gw-shift-tests-") as cache:
        os.environ.update(DOT_SAGE=cache, XDG_CACHE_HOME=cache, MPLCONFIGDIR=cache)
        unittest.main()

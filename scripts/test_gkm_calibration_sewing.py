#!/usr/bin/env python3
"""Independent field-valued checks on the nonlinear two-point sewing packet."""
import itertools
import json
import unittest

from check_gkm_inputs import RationalFunction, polynomial
from export_gkm_first_calibration import read_report as read_first
from gkm_calibration_recursion import read_report as read_higher
from gkm_calibration_sewing import CASES, OUTPUT, REPORT, ROOT, emit


def function(value):
    return RationalFunction(polynomial(value["numerator"]), polynomial(value["denominator"]))


def replay(higher):
    _, first = read_first((ROOT / "environments/gkm-first-calibration-comparison.json").read_bytes())
    _, rest = read_higher(higher)
    checked = nonlinear = 0
    for target, rows in CASES.items():
        entries = {(tuple(r["class"]), r["inverse_loop_power"]): r for r in first[target] + rest[target]}
        for beta, power in rows:
            endpoints = entries[beta, power]["paired_equivariant"]
            rank = len(endpoints)
            tails = []
            for left in itertools.product(*(range(b + 1) for b in beta)):
                right = tuple(b - l for b, l in zip(beta, left))
                if any(left) and any(right):
                    for k in range(1, power):
                        tails.append(((-1)**k, entries[left, k]["paired_equivariant"],
                                     entries[right, power - k]["operator_equivariant"]))
            for i, j in itertools.product(range(rank), repeat=2):
                value = function(endpoints[i][j]) + (-1)**power * function(endpoints[j][i])
                nonlinear += value != 0
                for sign, paired, raised in tails:
                    value += sign * sum(function(paired[h][i]) * function(raised[h][j])
                                        for h in range(rank))
                if value != 0:
                    raise ValueError(f"Sewing failed on {target}, {beta}, power {power}, states {(i,j)}")
                checked += 1
    return checked, nonlinear


class CalibrationSewingTest(unittest.TestCase):
    def test_packet(self):
        raw = REPORT.read_bytes()
        self.assertEqual(emit(raw), OUTPUT.read_text())
        self.assertEqual(replay(raw), (273, 48))

    def test_ordinary_preserving_covariant_change(self):
        packet = json.loads(REPORT.read_bytes())
        row = next(r for r in packet["cases"] if r["target"] == "X0" and r["class"] == [2])
        # Add x at (pt,pt), and also update its correctly raised partner at (unit,pt).
        for key, i in (("paired_equivariant", 2), ("operator_equivariant", 0)):
            row[key][i][2]["numerator"].append([[1, 0], [1, 1]])
        with self.assertRaisesRegex(ValueError, r"Sewing failed on X0, \(2,\), power 4, states \(2, 2\)"):
            replay(json.dumps(packet).encode())


if __name__ == "__main__":
    unittest.main()

"""Published comparisons retain the whole request and are separate from kernel proof."""

import copy
from fractions import Fraction
import json
from pathlib import Path
import unittest

from check_plane_genus_two_benchmarks import check
from export_plane_genus_two_scalar import emit, emit_scalars, read_report

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/genus-two-plane-scalar-native.json"


class PlaneBenchmarks(unittest.TestCase):
    def test_complete_published_comparison(self):
        raw = REPORT.read_bytes()
        self.assertEqual(check(raw), 12)
        _, values = read_report(raw, 4)
        self.assertEqual(values[4], [27, 42, Fraction(25, 4)])

    def test_coherent_alternative_system_is_not_the_published_table(self):
        candidate = copy.deepcopy(json.loads(REPORT.read_bytes()))
        row = candidate["rows"][3]
        # Change N_4 by one, then compensate all three original matrix equations.
        row["values"][0] = [28, 1]
        for equation, correction in zip(row["equations"], [432, 36, 0]):
            for key in ["constant", "remainder"]:
                value = Fraction(*equation[key]) + correction
                equation[key] = [value.numerator, value.denominator]
        raw = json.dumps(candidate).encode()
        read_report(raw, 4)
        with self.assertRaisesRegex(ValueError, "Published value mismatch for N_4"):
            check(raw)

    def test_split_export_preserves_full_scalar_obligations(self):
        raw = REPORT.read_bytes()
        source = emit(raw, 4, split_scalars=True)
        for degree in range(2, 5):
            scalar = emit_scalars(raw, 4, degree)
            self.assertEqual(scalar, emit_scalars(raw, 4, degree))
            self.assertIn(f"GenusTwoPlaneDegree{degree}Scalars.constants", source)
            self.assertIn(f"planeShiftedConstantFast {degree}", scalar)
        quartic = emit_scalars(raw, 4, 4)
        for degree, family in [(0, 1), (3, 1), (3, 2)]:
            self.assertIn(f"theorem coefficients_{degree}_{family}", quartic)
            self.assertIn(f"GenusTwoPlaneDegree4Scalars.coefficients_{degree}_{family}", source)
        self.assertIn("theorem accepted : planeCheckCanonicalTable 4 values", source)
        self.assertIn("theorem coverage", source)
        self.assertIn("theorem claims", source)


if __name__ == "__main__":
    unittest.main()

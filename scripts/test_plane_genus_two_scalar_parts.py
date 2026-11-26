"""Complete component coverage, original claims, and real kernel rejection."""

import copy
from fractions import Fraction
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from export_plane_genus_two_scalar_parts import (
    assignment_representatives, component_claim, emit_component, emit_scalars,
    header, marking_lemma, read_report, scalar_report,
)

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/genus-two-plane-scalar-parts-candidates.json"


class PlaneScalarParts(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw = REPORT.read_bytes()
        cls.report = json.loads(cls.raw)

    def test_every_aggregate_and_original_query_is_preserved(self):
        report, values = read_report(self.raw, 4)
        original = json.loads((ROOT / "environments/genus-two-plane-scalar-native.json").read_bytes())
        self.assertEqual(scalar_report(report), original)
        self.assertEqual(values, [[0, Fraction(-1, 960), 0], [0, 0, 0], [0, 0, 0],
                                  [0, Fraction(-1, 4), Fraction(-1, 12)],
                                  [27, 42, Fraction(25, 4)]])
        reference = ROOT / "environments/plane-genus-two-benchmarks.json"
        published = json.loads(reference.read_bytes())
        queries = [{"target": "P2", "family": family, **query, "expected": value}
                   for row in report["rows"]
                   for family, query, value in zip(["N", "H", "P"], row["requests"], row["values"])]
        self.assertEqual(queries, published["queries"])
        for degree, count in [(2, 360), (3, 360), (4, 504)]:
            source = emit_scalars(self.raw, 4, degree)
            self.assertEqual(source, emit_scalars(self.raw, 4, degree))
            # Each original component, including zero entries, gets its own proof.
            self.assertEqual(source.count(" := by decide +kernel"), count)
            self.assertEqual(source.count("  rw [planeShiftedConstantFast_eq_sum_parts]"), 3)
            expected_dependencies = len(report["rows"][degree-1]["equations"][0][
                "earlier_coefficients"])
            self.assertEqual(source.count("  rw [planeEarlierCoefficient_eq_sum_parts]"),
                             3 * expected_dependencies)
            self.assertIn("theorem constants (i : Fin 3)", source)
            self.assertIn("theorem coefficients_0_1 (i : Fin 3)", source)

    def test_marking_reuse_preserves_every_component_and_public_claim(self):
        self.assertEqual([assignment_representatives(i) for i in range(3)],
                         [[0, 1, 0, 3, 1, 3], [0, 0, 2, 2, 4, 4], [0, 0, 0, 0, 0, 0]])
        for degree, complete, reduced in [(2, 360, 140), (3, 360, 140), (4, 504, 196)]:
            source = emit_scalars(self.raw, 4, degree, reuse_markings=True, proof_method="hybrid")
            original = emit_scalars(self.raw, 4, degree)
            self.assertEqual(source.count(" := by cbv"), 112)
            self.assertEqual(source.count(" := by decide +kernel"), reduced - 112)
            self.assertEqual(source.count("(by decide +kernel)).trans"), complete - reduced)
            self.assertEqual(source.count("  rw [planeShiftedConstantFast_eq_sum_parts]"), 3)
            # Every literal original component statement still occurs unchanged.
            import re
            pattern = r"private theorem (\w+_part_\d+_\d+) : ([\s\S]*?) := by"
            self.assertEqual(re.findall(pattern, source), re.findall(pattern, original))
            # The existing public scalar API is unchanged, including all dependencies.
            public = "/-- All complete constants in HHP/HPP/PPP order. -/"
            self.assertEqual(source.split(public)[1], original.split(public)[1])
            self.assertNotIn("native_decide", source)
            self.assertTrue(all(len(line) <= 100 for line in source.splitlines()))
            fast = emit_scalars(self.raw, 4, degree, reuse_markings=True, proof_method="fast")
            self.assertEqual(re.findall(pattern, fast), re.findall(pattern, original))
            self.assertEqual(fast.split(public)[1], original.split(public)[1])
            self.assertEqual(fast.count(" := by cbv"), 112)
            self.assertEqual(fast.count("  rw [← planeEarlierCoefficientPartFast_eq]"),
                             reduced - 112)
            self.assertEqual(fast.count("(by decide +kernel)).trans"), complete - reduced)
            self.assertTrue(all(len(line) <= 100 for line in fast.splitlines()))

    def test_incomplete_or_malformed_components_are_rejected(self):
        def equation(r):
            return r["rows"][1]["equations"][0]

        mutations = [
            lambda r: r.update(kind="axiomatic_gw.plane_genus_two_scalar"),
            lambda r: r.update(bound=3),
            lambda r: r.update(bound=True),
            lambda r: r.update(schema_version=True),
            lambda r: r.update(extra="unidentified operation"),
            lambda r: r["rows"].pop(),
            lambda r: r["rows"][1]["requests"][0].update(curve=[3]),
            lambda r: equation(r).pop("constant_parts"),
            lambda r: equation(r)["constant_parts"].pop(),
            lambda r: equation(r)["constant_parts"].append([[0, 1]] * 6),
            lambda r: equation(r)["constant_parts"][0].pop(),
            lambda r: equation(r)["constant_parts"][0].append([0, 1]),
            lambda r: equation(r)["constant_parts"][0].__setitem__(0, [0, 1]),
            lambda r: equation(r)["constant_parts"][0].__setitem__(0, [486, 160]),
            lambda r: equation(r)["constant_parts"][0].__setitem__(0, [True, 1]),
            lambda r: equation(r)["constant_parts"][0].__setitem__(0, [1, 0]),
            lambda r: equation(r)["earlier_coefficients"].clear(),
            lambda r: equation(r)["earlier_coefficients"][0]["parts"].pop(),
            lambda r: equation(r)["earlier_coefficients"][0]["parts"][0].pop(),
            lambda r: equation(r)["earlier_coefficients"][0]["parts"][0].__setitem__(0, [1, 1]),
            lambda r: equation(r)["earlier_coefficients"][0].update(degree=1),
        ]
        for index, mutate in enumerate(mutations):
            with self.subTest(index=index):
                report = copy.deepcopy(self.report)
                mutate(report)
                with self.assertRaises(ValueError):
                    read_report(json.dumps(report), 4)
        duplicate = self.raw.decode().replace('"schema_version": 1',
                                             '"schema_version": 1, "schema_version": 1', 1)
        self.assertNotEqual(duplicate, self.raw.decode())
        with self.assertRaises(ValueError):
            read_report(duplicate, 4)

    def test_kernel_rejects_a_forgery_with_unchanged_complete_scalars(self):
        bad = copy.deepcopy(self.report)
        parts = bad["rows"][1]["equations"][0]["earlier_coefficients"][0]["parts"]
        self.assertEqual(parts[0][:2], [[0, 1], [0, 1]])
        parts[0][0], parts[0][1] = [1, 1], [-1, 1]
        # All totals, reconstructed values and original queries are unchanged.
        changed, _ = read_report(json.dumps(bad), 4)
        self.assertEqual(scalar_report(changed), scalar_report(self.report))
        # Exercise the production paths separately: lazy coefficient replay and
        # CBV constant replay. Both mutations preserve the complete scalar sums.
        bad_constant = copy.deepcopy(self.report)
        parts = bad_constant["rows"][1]["equations"][0]["constant_parts"]
        for assignment, change in [(0, 1), (1, -1)]:
            value = Fraction(*parts[0][assignment]) + change
            parts[0][assignment] = [value.numerator, value.denominator]
        changed, _ = read_report(json.dumps(bad_constant), 4)
        self.assertEqual(scalar_report(changed), scalar_report(self.report))
        for method, corruption, earlier, rejected in [
                ("decide", bad, (0, 1), "planeEarlierCoefficientPart 2 0 0 1 0 0 = 1"),
                ("fast", bad, (0, 1), "planeEarlierCoefficientPartFast 2 0 0 1 0 0 = 1"),
                ("hybrid", bad_constant, None, "error: unsolved goals")]:
            for expected, report in [(True, self.report), (False, corruption)]:
                with self.subTest(method=method, accepted=expected), \
                        tempfile.TemporaryDirectory() as directory:
                    path = Path(directory) / "ComponentClaim.lean"
                    path.write_text(emit_component(json.dumps(report).encode(), 4,
                                                   2, 0, 0, 0, earlier=earlier,
                                                   proof_method=method))
                    result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                            text=True, capture_output=True)
                    output = result.stdout + result.stderr
                    if expected:
                        self.assertEqual(result.returncode, 0, output)
                        self.assertNotIn("sorryAx", output)
                    else:
                        self.assertNotEqual(result.returncode, 0)
                        self.assertIn(rejected, output)
                        self.assertNotIn("timeout", output)
                        if method == "hybrid":
                            self.assertIn("Int.ofNat 243", output)
                            self.assertIn("Int.ofNat 323", output)

    def test_kernel_checks_the_actual_marking_reuse_hint(self):
        expression = "planeEarlierCoefficientPart 2 0 0 1"
        # Both proposed representatives happen to have the same numerical value.
        # Only assignment 0 preserves the transported labels of assignment 2.
        for representative, accepted in [(0, True), (1, False)]:
            with self.subTest(representative=representative), \
                    tempfile.TemporaryDirectory() as directory:
                source = header(self.raw, 2, reuse_markings=True)
                source += marking_lemma("coefficient", expression, 4, 2, 0, (0, 1))
                source += component_claim("representative_value",
                                          f"{expression} 0 {representative}", [0, 1])
                source += [
                    f"private theorem reused : {expression} 0 2 = 0 := by",
                    f"  exact (coefficient_marking 0 2 {representative} (by decide +kernel)).trans",
                    "    representative_value", "#print axioms reused",
                    "end AxiomaticGW.GenusTwoPlaneDegree2Scalars", ""]
                path = Path(directory) / "MarkingReuse.lean"
                path.write_text("\n".join(source))
                result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                        text=True, capture_output=True)
                output = result.stdout + result.stderr
                if accepted:
                    self.assertEqual(result.returncode, 0, output)
                    self.assertNotIn("sorryAx", output)
                else:
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("is false", output)
                    self.assertIn("labelPermutation", output)
                    self.assertNotIn("timeout", output)


if __name__ == "__main__":
    unittest.main()

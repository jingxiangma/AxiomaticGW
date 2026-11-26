/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.PlaneGenusTwoCoefficients

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.PlaneNormalization
open AxiomaticGW SurfacePolynomialReduction SurfaceFirstDescendant

-- Equality is of the complete expression, including at classes below the input.
example (q : SurfaceAncestorKey .plane) :
    normalizedTerms q = directNormalizedTerms q := normalizedTerms_plane_eq_direct q

example (p : RationalTerms (SurfaceAncestorKey .plane)) :
    RationalTerms.affineSubstitute normalizedTerms p =
      RationalTerms.affineSubstitute directNormalizedTerms p :=
  affineSubstitute_normalizedTerms_plane_eq p

example (q : SurfaceAncestorKey .plane) (hg : 2 ≤ q.genus)
    {t : ℚ × Multiset (Variable .plane)} (ht : t ∈ normalizedTerms q) :
    ∃ v, t.2 = {v} ∧ SurfaceLowGenus.variableGenus v = q.genus ∧
      SurfaceGenusZero.variableCurve v = q.beta ∧ variableDimensionCompatible v :=
  normalizedTerms_plane_support q hg ht

-- The actual calibration is nonzero in its unit row.
example : SurfaceDescendant.firstCalibrationMatrix .plane ![1] .unit .point = 1 := by
  rw [← SurfaceFirstCalibration.values_eq]
  decide +kernel

example (beta : SurfaceTarget.plane.Curve) (b : SurfaceBasisLabel .plane) :
    SurfaceDescendant.firstCalibrationMatrix .plane beta .point b = 0 :=
  SurfaceFirstCalibration.plane_row_zero beta _ b (by decide)

-- Divisor multiplicities remain exact, including the zero-degree empty product.
example : primaryCoefficient (X := .plane) ![0] 0 = 1 := by decide +kernel

example : primaryCoefficient (X := .plane) ![0] {.hyperplane} = 0 := by decide +kernel

example : primaryCoefficient (X := .plane) ![3]
    {.hyperplane, .point, .hyperplane} = 9 := by decide +kernel

example : primaryCoefficient (X := .plane) ![3]
    {.hyperplane, .unit, .point} = 0 := by decide +kernel

-- Two divisor occurrences give two contributions to the primary correction.
example : terms (X := .plane) 2 ![1] .hyperplane
      {.hyperplane, .hyperplane, .point, .point, .point} =
    RationalTerms.term 1 {query 2 ![1] .hyperplane 3} +
      RationalTerms.term 2 {SurfaceQuery.points .plane 2 ![1] 4} := by decide +kernel

-- At degree zero the correction survives without division by that degree.
example : terms (X := .plane) 2 ![0] .hyperplane {.hyperplane} =
    RationalTerms.term 1 {SurfaceQuery.points .plane 2 ![0] 1} := by decide +kernel

-- Two primary units still vanish after the string step removes one.
example : terms (X := .plane) 2 ![1] .point
    {.unit, .unit, .point, .point, .point} = 0 := by decide +kernel

-- These are dimension criteria, not values of the represented invariants.
example : (SurfaceQuery.points .plane 1 ![0] 0).DimensionCompatible ∧
    ¬(SurfaceQuery.points .plane 1 ![0] 0).GeometricDomain := by decide +kernel

example (d n : ℕ) :
    (SurfaceQuery.points .plane 2 ![d] n).DimensionCompatible ↔ n = 3 * d + 1 := by
  rw [SurfaceQuery.dimensionCompatible_points_plane]
  omega

example (d n : ℕ) :
    (query (X := .plane) 2 ![d] .hyperplane n).DimensionCompatible ↔ n = 3 * d := by
  rw [SurfaceQuery.dimensionCompatible_first_plane]
  change n + 1 + 1 = 3 * d + 2 ↔ _
  omega

example (d n : ℕ) :
    (query (X := .plane) 2 ![d] .point n).DimensionCompatible ↔ n + 1 = 3 * d := by
  rw [SurfaceQuery.dimensionCompatible_first_plane]
  change n + 2 + 1 = 3 * d + 2 ↔ _
  omega

-- The shortcut compares full component classes before expanding any marking data.
example (v : Variable .plane) (beta : SurfaceTarget.plane.Curve)
    (hv : SurfaceGenusZero.variableCurve v ≠ beta)
    (S : Type) [Fintype S] (h : StableArity 2 S) (k : S → ℕ)
    (a : S → SurfaceBasisLabel .plane) :
    SurfaceGenusTwo.planeCoefficientVertex v 2 S h beta k a = 0 := by
  simp only [SurfaceGenusTwo.planeCoefficientVertex, ite_true, if_neg hv]

example (v : Variable .plane) {S : Type} [Fintype S]
    (z : GluingExpression.CotangentTerm 2 S) (beta : SurfaceTarget.plane.Curve)
    (n : ℕ) (a : S → SurfaceBasisLabel .plane) :
    SurfaceGenusTwo.planePointCoefficient v z beta n a =
      SurfaceGenusTwo.pointCoefficient .plane v z beta n a :=
  SurfaceGenusTwo.planePointCoefficient_eq v z beta n a

end AxiomaticGWTest.Surfaces.PlaneNormalization

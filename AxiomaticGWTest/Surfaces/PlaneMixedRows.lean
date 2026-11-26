/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.PlaneMixedRows

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.PlaneMixedRows
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwo BelorousskiPandharipande

private def primary (d : ℕ) : Variable .plane :=
  .inr (SurfaceQuery.points .plane 2 ![d] (3 * d + 1))

private def hyperplane (d : ℕ) : Variable .plane :=
  .inr (SurfaceFirstDescendant.query 2 ![d] .hyperplane (3 * d))

-- Colliding renamed variables collect their coefficients; injectivity is unnecessary.
example : RationalTerms.coefficient
    (RationalTerms.rename (fun _ : Bool ↦ ())
      (RationalTerms.term 2 {false} + RationalTerms.term 3 {true})) {()} = 5 := by
  rw [RationalTerms.coefficient_rename_add, RationalTerms.coefficient_rename_term,
    RationalTerms.coefficient_rename_term]
  decide +kernel

-- Zero scaling keeps no coefficient, including under a noninjective renaming.
example (p : RationalTerms Bool) : RationalTerms.coefficient
    (RationalTerms.rename (fun _ : Bool ↦ ()) (RationalTerms.scale 0 p)) {()} = 0 := by
  rw [RationalTerms.coefficient_rename_scale, zero_mul]

-- The signed unit correction leaves two copies even in the degree-zero sector.
example : remainderVertex .plane (primary 0) (planeCoefficientVertex (primary 0)) 1
    2 (Fin 1) (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0 ![.unit] = 2 := by
  rw [remainderVertex_plane_single_unit_onePsi]
  decide +kernel

-- At n=0, the dilaton correction is multiplied by zero before truncated subtraction.
example : remainderVertex .plane (primary 0) (planeCoefficientVertex (primary 0)) 0
    2 (Fin 2) (by norm_num [StableArity]) (Pi.single 1 1) inferInstance 0 ![.point, .unit] = 3 := by
  rw [remainderVertex_plane_pair_unit_onePsi _ _ _ (by decide)]
  decide +kernel

-- Moving psi to the non-unit state changes three copies to one by string.
example : remainderVertex .plane (primary 0) (planeCoefficientVertex (primary 0)) 0
    2 (Fin 2) (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0 ![.point, .unit] = 1 := by
  rw [remainderVertex_plane_pair_primary_unit _ _ _ (by decide)]
  decide +kernel

-- The repeated-hyperplane primary correction survives at degree zero (0^0=1).
example (s : Fin 2) : remainderVertex .plane (primary 0) (planeCoefficientVertex (primary 0)) 0
    2 (Fin 2) (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0
      ![.hyperplane, .hyperplane] = 1 := by
  rw [remainderVertex_plane_two_hyperplanes_onePsi]
  decide +kernel

-- Both psi placements have the expected nonzero divisor factor in degree three.
example (s : Fin 2) : remainderVertex .plane (hyperplane 3)
    (planeCoefficientVertex (hyperplane 3)) 9 2 (Fin 2) (by norm_num [StableArity])
      (Pi.single s 1) inferInstance 0 ![.hyperplane, .hyperplane] = 3 := by
  rw [remainderVertex_plane_two_hyperplanes_onePsi]
  decide +kernel

-- The quartic row is a coefficient identity in the complete degree-five equation.
example :
    let p := normalizedGenusTwoTerms .plane 12 ![5] 0
      (SurfaceGenusZero.pointLabels ![.hyperplane, .point, .point] 12)
    let f := fun q : SurfaceQuery .plane ↦ RationalTerms.coefficient p {Sum.inr q}
    (f (SurfaceQuery.points .plane 2 ![4] 13),
      f (SurfaceFirstDescendant.query 2 ![4] .hyperplane 12),
      f (SurfaceFirstDescendant.query 2 ![4] .point 11)) = (-36, -132, 576) := by
  have h := normalized_plane_hyperplane_two_points_row 4
  norm_num only at h
  exact h

-- HPP also retains the zero-degree columns; it does not assert their invariant values.
example : planeRemainderPointCoefficient 0 ![1] ![.hyperplane, .point, .point]
    (primary 0) = -36 := by
  rw [planeRemainderPointCoefficient_hyperplane_two_points_canonical]
  decide +kernel

-- Matching the degree alone is insufficient: the requested point multiplicity matters.
example : RationalTerms.coefficient (normalizedGenusTwoTerms .plane 6 ![3] 0
    (SurfaceGenusZero.pointLabels ![.hyperplane, .point, .point] 6))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![2] .hyperplane 7)} = 0 := by
  rw [normalized_plane_hyperplane_two_points_canonical 2 _ rfl]
  decide +kernel

-- This higher-psi line query satisfies the surface dimension equation.
example : (SurfaceAncestorKey.ofLabels (X := .plane) 2 (Fin 1)
    (by norm_num [StableArity]) ![1] ![4] ![.hyperplane]).DimensionCompatible := by
  decide +kernel

-- Dimension-compatible ancestor tags at degree d are excluded by the full formula.
example (d : ℕ) :
    let v : Variable .plane := .inl (SurfaceAncestorKey.ofLabels 2 (Fin 1)
      (by norm_num [StableArity]) ![d] ![3 * d + 1] ![.hyperplane])
    RationalTerms.coefficient (normalizedGenusTwoTerms .plane (3 * d) ![d + 1] 0
      (SurfaceGenusZero.pointLabels ![.hyperplane, .point, .point] (3 * d))) {v} = 0 := by
  dsimp only
  rw [normalized_plane_hyperplane_two_points_canonical d _ rfl]
  simp only [reduceCtorEq, ite_false, mul_zero, add_zero]

-- Any surviving ancestor tag must have strictly smaller degree after the canonical block.
example (d : ℕ) (q : SurfaceAncestorKey .plane)
    (hc : RationalTerms.coefficient (normalizedGenusTwoTerms .plane (3 * d) ![d + 1] 0
      (SurfaceGenusZero.pointLabels ![.hyperplane, .point, .point] (3 * d)))
        {Sum.inl q} ≠ 0) : q.beta 0 < d := by
  exact normalized_plane_hyperplane_two_points_lower d (.inl q)
    (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
    (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
    (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hc

end AxiomaticGWTest.Surfaces.PlaneMixedRows

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.PlaneShiftedStep

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.PlaneShiftedRemainder
open AxiomaticGW SurfacePolynomialReduction BelorousskiPandharipande

-- Cancellation removes the entire dependency, but preserves constants and nonlinear terms.
example : RationalTerms.collect
    ({(2, {0}), (3, {0}), (-5, {0}), (7, 0), (4, {1, 1})} : RationalTerms ℕ) =
      {(7, 0), (4, {1, 1})} := by decide +kernel

-- A nonzero repeated coefficient is summed, not deduplicated.
example : RationalTerms.collect
    ({(2, {0}), (3, {0}), (7, 0)} : RationalTerms ℕ) = {(5, {0}), (7, 0)} := by
  decide +kernel

-- Raw zero terms do not become recursive dependencies.
example : RationalTerms.collect ({(0, {5})} : RationalTerms ℕ) = 0 := by decide +kernel

-- The all-zero polynomial has an empty collected representation even with raw support.
example : RationalTerms.collect ({(2, {5}), (-2, {5})} : RationalTerms ℕ) = 0 := by
  decide +kernel

-- Removing a finite block retains its constant and all other powers.
example : (RationalTerms.collect
    ({(2, {0}), (3, {0}), (7, 0), (4, {1, 1})} : RationalTerms ℕ)).filter
      (fun t ↦ ∀ x ∈ ({0, 2} : Finset ℕ), t.2 ≠ {x}) = {(7, 0), (4, {1, 1})} := by
  decide +kernel

-- Collection preserves evaluation for arbitrary rational values of the remaining variables.
example (v : ℕ → ℚ) :
    RationalTerms.eval v ({(7, 0), (4, {1, 1})} : RationalTerms ℕ) =
      RationalTerms.eval v (RationalTerms.collect {(7, 0), (4, {1, 1})}) :=
  (RationalTerms.eval_collect v _).symm

-- The canonical queries remain distinct at the initial degree.
example : Function.Injective (planeCanonicalQueries 0) := planeCanonicalQueries_injective 0

-- Every degree-one recursive dependency is at degree zero, including ancestor tags.
example (i : Fin 3) (t : ℚ × Multiset (Variable .plane))
    (ht : t ∈ planeShiftedRemainder 1 i) (v : Variable .plane) (hv : v ∈ t.2) :
    SurfaceGenusZero.variableCurve v 0 = 0 := by
  have h := (planeShiftedRemainder_dependencies 1 (by decide) i ht v hv).2.2
  omega

-- Arbitrary changes at the current or higher degree cannot alter a recursive right-hand side.
example (d : ℕ) (hd : 0 < d) (v : Variable .plane → ℚ) :
    planeShiftedRightHandSide
      (fun q ↦ if SurfaceGenusZero.variableCurve q 0 < d then v q else 123) d =
        planeShiftedRightHandSide v d := by
  apply planeShiftedRightHandSide_congr d hd
  intro q _ _ hlt
  exact if_pos hlt

-- The sign of the retained remainder is the sign used by the solver.
example (v : Variable .plane → ℚ) (d : ℕ) (i : Fin 3) :
    RationalTerms.eval v (planeShiftedTerms d i) =
      (planeShiftedMatrix d).mulVec (fun j ↦ v (Sum.inr (planeCanonicalQueries d j))) i -
        planeShiftedRightHandSide v d i := by
  rw [planeShiftedRightHandSide, sub_neg_eq_add]
  exact eval_planeShiftedTerms v d i

-- Agreement below the degree propagates through the actual three equations.
example (d : ℕ) (hd : 0 < d) (v w : Variable .plane → ℚ)
    (hv : ∀ i, RationalTerms.eval v (planeShiftedTerms d i) = 0)
    (hw : ∀ i, RationalTerms.eval w (planeShiftedTerms d i) = 0)
    (h : ∀ q, SurfaceLowGenus.variableGenus q = 2 → variableDimensionCompatible q →
      SurfaceGenusZero.variableCurve q 0 < d → v q = w q) (j : Fin 3) :
    v (Sum.inr (planeCanonicalQueries d j)) = w (Sum.inr (planeCanonicalQueries d j)) :=
  congrFun (planeShiftedValues_unique_of_lower d hd v w hv hw h) j

end AxiomaticGWTest.Surfaces.PlaneShiftedRemainder

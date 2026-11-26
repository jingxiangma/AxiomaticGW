/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.PlaneGenusTwoReconstruction

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.PlaneGenusTwoRecursion
open AxiomaticGW SurfacePolynomialReduction BelorousskiPandharipande

-- A unit first descendant at degree zero reduces to the primary family with
-- the signed dilaton factor three, rather than creating a fourth family.
example : RationalTerms.Equivalent
    (normalizedTerms (⟨2, ![0], {⟨.unit, 1⟩, ⟨.point, 0⟩}, by decide +kernel⟩ :
      SurfaceAncestorKey .plane))
    (RationalTerms.term 3 {Sum.inr (planeCanonicalQueries 0 0)}) := by decide +kernel

-- The nominal P entry at degree zero is dimension-incompatible, so its
-- normalization contributes no variable despite natural subtraction at 3d-1.
example : ¬(planeCanonicalQueries 0 2).DimensionCompatible := by decide +kernel

example : normalizedTerms (⟨2, ![0], {⟨.point, 1⟩}, by decide +kernel⟩ :
    SurfaceAncestorKey .plane) = 0 := by decide +kernel

-- The first positive degree uses only the initial canonical triple.
example (i : Fin 3) (t : ℚ × Multiset (Variable .plane))
    (ht : t ∈ planeShiftedRemainder 1 i) (v : Variable .plane) (hv : v ∈ t.2) :
    ∃ j, v = Sum.inr (planeCanonicalQueries 0 j) := by
  obtain ⟨b, hb, j, hj⟩ := planeShiftedRemainder_canonical_dependencies 1 (by decide) i ht v hv
  have hz : b = 0 := by omega
  exact ⟨j, hz ▸ hj⟩

-- Ancestor tags are completely absent from the collected remainder.
example (d : ℕ) (hd : 0 < d) (i : Fin 3) (t : ℚ × Multiset (Variable .plane))
    (ht : t ∈ planeShiftedRemainder d i) (q : SurfaceAncestorKey .plane) :
    Sum.inl q ∉ t.2 := by
  intro hq
  obtain ⟨_, _, _, h⟩ := planeShiftedRemainder_canonical_dependencies d hd i ht _ hq
  cases h

-- The psi bound retains both exceptional coordinates on the two-point blowup.
example (n : ℕ) (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel .blowupTwo)
    (t : ℚ × Multiset (SurfaceAncestorKey .blowupTwo))
    (ht : t ∈ genusTwoTerms .blowupTwo n ![1, 1, 0] 0 a)
    (q : SurfaceAncestorKey .blowupTwo) (hq : 2 ≤ q.totalPsi) : q ∉ t.2 := by
  intro h
  have he := genusTwoTerms_primary_psi_le_one .blowupTwo n ![1, 1, 0] a ht q h
  omega

-- Extending a canonical table does not merge the three families at degree zero.
example : (fun j ↦ planeCanonicalValuation (fun _ ↦ ![7, -3, 11])
    (Sum.inr (planeCanonicalQueries 0 j))) = ![7, -3, 11] := by
  funext j
  exact planeCanonicalValuation_apply _ _ _

-- Recursion evaluates its initial sector without unfolding any graph search.
example : planeCanonicalValues 0 1 = -1 / 960 := by
  rw [planeCanonicalValues_zero]
  rfl

-- The initial primary value is derived from the complete HPP equation. The
-- lower-genus constant remains an exact computation, not another input seed.
example (v : Variable .plane → ℚ)
    (heq : RationalTerms.eval v (planeShiftedTerms 0 1) = 0)
    (hH : v (Sum.inr (planeCanonicalQueries 0 1)) = -1 / 960)
    (hP : v (Sum.inr (planeCanonicalQueries 0 2)) = 0) :
    (fun j ↦ v (Sum.inr (planeCanonicalQueries 0 j))) = planeCanonicalValues 0 := by
  rw [planeCanonicalValues_zero]
  exact planeCanonicalInitial_eq_of_equation v heq hH hP

-- Changing any genus-two assignment cannot change the initial remainder.
example (v w : Variable .plane → ℚ) :
    RationalTerms.eval v (planeShiftedRemainder 0 1) =
      RationalTerms.eval w (planeShiftedRemainder 0 1) := by
  rw [eval_planeShiftedRemainder_initial, eval_planeShiftedRemainder_initial]

-- The executable solution satisfies the full HHP equation at every positive
-- degree; this consumer uses the original polynomial, not a symbolic matrix.
example (d : ℕ) : RationalTerms.eval (planeCanonicalValuation planeCanonicalValues)
    (normalizedGenusTwoTerms .plane (3 * (d + 1) + 1) ![d + 2] 0
      (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .point]
        (3 * (d + 1) + 1))) = 0 :=
  planeCanonicalValues_equations (d + 1) (by omega) 0

-- Original equations and only the fixed initial triple identify every result.
example (v : Variable .plane → ℚ)
    (hzero : ∀ j, v (Sum.inr (planeCanonicalQueries 0 j)) = planeCanonicalInitial j)
    (heq : ∀ d, 0 < d → ∀ i, RationalTerms.eval v (planeShiftedTerms d i) = 0)
    (d : ℕ) (j : Fin 3) : v (Sum.inr (planeCanonicalQueries d j)) =
      planeCanonicalValues d j :=
  congrFun (eq_planeCanonicalValues_of_equations v hzero heq d) j

end AxiomaticGWTest.Surfaces.PlaneGenusTwoRecursion

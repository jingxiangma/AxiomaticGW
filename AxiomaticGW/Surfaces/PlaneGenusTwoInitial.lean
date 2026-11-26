/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneShiftedClosure

/-!
# Deriving the plane initial sector from the original BP equation

The HPP equation at source degree one has only the degree-zero N and H
variables. Its constant is computed by the already reconstructed lower
genera. The equation therefore determines N from the existing H seed;
there is no independent genus-two primary seed or value oracle.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open SurfacePolynomialReduction SurfaceGenusTwo

private theorem hpp_lower (d : ℕ) (v : Variable .plane)
    (hex : ∀ j, Sum.inr (planeCanonicalQueries d j) ≠ v)
    (hc : RationalTerms.coefficient (planeShiftedTerms d 1) {v} ≠ 0) :
    SurfaceGenusZero.variableCurve v 0 < d :=
  normalized_plane_hyperplane_two_points_lower d v (hex 0) (hex 1) (hex 2) hc

private theorem hpp_row (d : ℕ) :
    ((planeShiftedMatrix d) 1 0, (planeShiftedMatrix d) 1 1,
      (planeShiftedMatrix d) 1 2) = (-36, 12 - 36 * (d : ℚ), 36 * (d : ℚ) ^ 2) :=
  normalized_plane_hyperplane_two_points_row d

/-- Evaluate a complete shifted equation with every genus-two variable zero.
The parameters keep this potentially expensive computation out of module
initialization. Its initial HPP specialization is `planeShiftedConstant 0 1`. -/
def planeShiftedConstant (d : ℕ) (i : Fin 3) : ℚ :=
  RationalTerms.eval (fun _ ↦ 0) (planeShiftedTerms d i)

/-- At the initial HPP request the collected remainder contains no variables. -/
theorem planeShiftedRemainder_initial_no_dependencies
    {t : ℚ × Multiset (Variable .plane)} (ht : t ∈ planeShiftedRemainder 0 1)
    (v : Variable .plane) : v ∉ t.2 := by
  intro hv
  obtain ⟨ht, hex⟩ := Multiset.mem_filter.mp ht
  obtain ⟨hm, hc, hn⟩ := RationalTerms.mem_collect.mp ht
  obtain ⟨u, hu, he⟩ := Multiset.mem_map.mp (Multiset.mem_toFinset.mp hm)
  rcases planeShiftedTerms_bound 0 1 u hu with hz | ⟨w, hw, _⟩
  · exact (Multiset.notMem_zero v ((he.symm.trans hz) ▸ hv)).elim
  · have htw : t.2 = {w} := he.symm.trans hw
    rw [htw, Multiset.mem_singleton] at hv
    subst w
    have hex' (j : Fin 3) : Sum.inr (planeCanonicalQueries 0 j) ≠ v := by
      intro hj
      exact hex _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
        (htw.trans (congrArg (fun w : Variable .plane ↦ ({w} : Multiset _)) hj).symm)
    have hn' : RationalTerms.coefficient (planeShiftedTerms 0 1) {v} ≠ 0 := by
      rw [← htw, ← hc]
      exact hn
    have hlt := hpp_lower 0 v hex' hn'
    exact Nat.not_lt_zero _ hlt

/-- The initial remainder evaluates to the retained lower-genus constant,
independently of every supplied genus-two value. -/
theorem eval_planeShiftedRemainder_initial (v : Variable .plane → ℚ) :
    RationalTerms.eval v (planeShiftedRemainder 0 1) = planeShiftedConstant 0 1 := by
  have he : RationalTerms.eval v (planeShiftedRemainder 0 1) =
      RationalTerms.eval (fun _ ↦ 0) (planeShiftedRemainder 0 1) := by
    apply RationalTerms.eval_congr
    intro t ht q hq
    exact (planeShiftedRemainder_initial_no_dependencies ht q hq).elim
  rw [he, planeShiftedConstant, eval_planeShiftedTerms]
  simp only [Matrix.mulVec, dotProduct, mul_zero, Finset.sum_const_zero, zero_add]

/-- The entire original HPP equation at source degree one has this exact
constant and two coefficients. No final invariant or recurrence is assumed. -/
theorem eval_planeInitialEquation (v : Variable .plane → ℚ) :
    RationalTerms.eval v (planeShiftedTerms 0 1) =
      -36 * v (Sum.inr (planeCanonicalQueries 0 0)) +
      12 * v (Sum.inr (planeCanonicalQueries 0 1)) + planeShiftedConstant 0 1 := by
  rw [eval_planeShiftedTerms, eval_planeShiftedRemainder_initial]
  have hm := hpp_row 0
  have h0 : planeShiftedMatrix 0 1 0 = -36 := congrArg Prod.fst hm
  have h1 : planeShiftedMatrix 0 1 1 = 12 := by
    have hr : planeShiftedMatrix 0 1 1 = 12 - 36 * (0 : ℚ) :=
      congrArg (fun p ↦ p.2.1) hm
    simpa only [mul_zero, sub_zero] using hr
  have h2 : planeShiftedMatrix 0 1 2 = 0 := by
    have hr : planeShiftedMatrix 0 1 2 = 36 * (0 : ℚ) ^ 2 :=
      congrArg (fun p ↦ p.2.2) hm
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using hr
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0, h1, h2,
    zero_mul, add_zero]

/-- The original initial equation derives the primary value from the H seed
and a computable lower-genus constant; it is not an added seed. -/
theorem planeInitialPrimary_of_equation (v : Variable .plane → ℚ)
    (heq : RationalTerms.eval v (planeShiftedTerms 0 1) = 0)
    (hH : v (Sum.inr (planeCanonicalQueries 0 1)) = -1 / 960) :
    v (Sum.inr (planeCanonicalQueries 0 0)) = (planeShiftedConstant 0 1 - 1 / 80) / 36 := by
  rw [eval_planeInitialEquation, hH] at heq
  generalize planeShiftedConstant 0 1 = c at heq ⊢
  linarith

end AxiomaticGW.BelorousskiPandharipande

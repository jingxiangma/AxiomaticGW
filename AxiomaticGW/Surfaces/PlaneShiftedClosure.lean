/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneCanonicalSupport
public import AxiomaticGW.Surfaces.BPCotangentSupport
public import AxiomaticGW.Surfaces.PlaneShiftedRemainder

/-!
# Closure of the three canonical plane families

The full primary BP equation has only first-power or primary genus-two
components. Plane normalization puts each in one of the three canonical
families at its exact degree. After collection, the shifted remainder uses
only these families at strictly smaller degrees. Thus the original equations
determine all canonical values from their degree-zero triple; identifying
that triple with the finite geometric seed package is a separate step.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open SurfacePolynomialReduction SurfaceGenusTwo

/-- All three canonical queries keep their displayed curve degree. -/
theorem planeCanonicalQueries_beta (d : ℕ) (j : Fin 3) :
    (planeCanonicalQueries d j).beta = ![d] := by
  fin_cases j <;> rfl

/-- Every nonconstant term of a full primary plane BP equation is canonical.
This includes all added markings, node powers and signed cotangent tails. -/
theorem normalized_plane_primary_canonical_support (n : ℕ) (beta : SurfaceTarget.plane.Curve)
    (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel .plane)
    {t : ℚ × Multiset (Variable .plane)}
    (ht : t ∈ normalizedGenusTwoTerms .plane n beta 0 a) :
    t.2 = 0 ∨ ∃ d j, t.2 = {Sum.inr (planeCanonicalQueries d j)} := by
  obtain ⟨s, hs, ht⟩ := Multiset.mem_bind.mp ht
  rcases ((genusTwoTerms_bound .plane n beta 0 a) s hs).affine with
    hz | ⟨q, hq, hg, _⟩
  · simp only [hz, Multiset.card_zero, ite_true] at ht
    exact Or.inl (congrArg Prod.snd (RationalTerms.mem_term.mp ht).2)
  · have hk := genusTwoTerms_primary_psi_le_one .plane n beta a hs q
      (by rw [hq]; exact Multiset.mem_singleton_self q)
    simp only [hq, Multiset.card_singleton, one_ne_zero, if_false,
      Multiset.singleton_bind] at ht
    obtain ⟨_, u, hu, rfl⟩ := RationalTerms.mem_scale.mp ht
    obtain ⟨j, hj⟩ := normalizedTerms_plane_canonical_support q hg hk hu
    exact Or.inr ⟨q.beta 0, j, hj⟩

/-- The three selected original equations contain only canonical variables. -/
theorem planeShiftedTerms_canonical_support (d : ℕ) (i : Fin 3)
    {t : ℚ × Multiset (Variable .plane)} (ht : t ∈ planeShiftedTerms d i) :
    t.2 = 0 ∨ ∃ b j, t.2 = {Sum.inr (planeCanonicalQueries b j)} := by
  fin_cases i <;> exact normalized_plane_primary_canonical_support _ _ _ ht

/-- Every retained dependency is one of the three families at a smaller degree.
There are no remaining ancestor variables or other insertion patterns. -/
theorem planeShiftedRemainder_canonical_dependencies (d : ℕ) (hd : 0 < d) (i : Fin 3)
    {t : ℚ × Multiset (Variable .plane)} (ht : t ∈ planeShiftedRemainder d i)
    (v : Variable .plane) (hv : v ∈ t.2) :
    ∃ b, b < d ∧ ∃ j, v = Sum.inr (planeCanonicalQueries b j) := by
  have hlt := (planeShiftedRemainder_dependencies d hd i ht v hv).2.2
  obtain ⟨ht, _⟩ := Multiset.mem_filter.mp ht
  obtain ⟨hm, _, _⟩ := RationalTerms.mem_collect.mp ht
  obtain ⟨u, hu, he⟩ := Multiset.mem_map.mp (Multiset.mem_toFinset.mp hm)
  rcases planeShiftedTerms_canonical_support d i hu with hz | ⟨b, j, hj⟩
  · exact (Multiset.notMem_zero v ((he.symm.trans hz) ▸ hv)).elim
  · rw [he.symm.trans hj, Multiset.mem_singleton] at hv
    refine ⟨b, ?_, j, hv⟩
    simpa only [hv, SurfaceGenusZero.variableCurve, planeCanonicalQueries_beta,
      Matrix.cons_val_zero] using hlt

/-- Only the earlier canonical triples are needed to evaluate the right-hand side. -/
theorem planeShiftedRightHandSide_congr_canonical (d : ℕ) (hd : 0 < d)
    (v w : Variable .plane → ℚ)
    (h : ∀ b, b < d → ∀ j,
      v (Sum.inr (planeCanonicalQueries b j)) = w (Sum.inr (planeCanonicalQueries b j))) :
    planeShiftedRightHandSide v d = planeShiftedRightHandSide w d := by
  funext i
  apply congrArg Neg.neg
  apply RationalTerms.eval_congr
  intro t ht q hq
  obtain ⟨b, hb, j, rfl⟩ := planeShiftedRemainder_canonical_dependencies d hd i ht q hq
  exact h b hb j

/-- A degree-zero canonical triple and all original positive-degree equations
determine every canonical value uniquely. No noncanonical value is prescribed. -/
theorem planeShiftedValues_unique (v w : Variable .plane → ℚ)
    (hzero : ∀ j, v (Sum.inr (planeCanonicalQueries 0 j)) =
      w (Sum.inr (planeCanonicalQueries 0 j)))
    (hv : ∀ d, 0 < d → ∀ i, RationalTerms.eval v (planeShiftedTerms d i) = 0)
    (hw : ∀ d, 0 < d → ∀ i, RationalTerms.eval w (planeShiftedTerms d i) = 0)
    (d : ℕ) : (fun j ↦ v (Sum.inr (planeCanonicalQueries d j))) =
      fun j ↦ w (Sum.inr (planeCanonicalQueries d j)) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hz : d = 0
    · subst d
      exact funext hzero
    · have hd := Nat.pos_of_ne_zero hz
      rw [planeShiftedValues_eq_solve v d hd (hv d hd),
        planeShiftedValues_eq_solve w d hd (hw d hd),
        planeShiftedRightHandSide_congr_canonical d hd v w
          (fun b hb j ↦ congrFun (ih b hb) j)]

end AxiomaticGW.BelorousskiPandharipande

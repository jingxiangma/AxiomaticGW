/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoCanonicalRelations
public import AxiomaticGW.Surfaces.GenusTwoBlowupOrder

/-!
# A four-relation primary genus-two equation on the blowups

At source `beta + E_i` with `energy beta` added points, combine the complete
normalized BP rows as `(3d/2) EHH - EEH + (d/2) EEE - (1/3) HHH`, where `d`
is the plane degree of beta. This is a directly chosen linear combination,
not a transcription of a printed reconstruction recurrence. Every original
constant, signed normalization tail and full curve class is retained.

The combined equation follows from the four original equations. Every
surviving variable is a canonical descendant at an effective subclass of the
shifted source. This module proves neither the primary pivot nor strict order
decrease; those require the actual coefficient and cancellation calculations.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupNRelation
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder

/-- The complete primary BP equation, including its lower-genus constant. -/
def bpRow (X : SurfaceTarget) (n : ℕ) (sigma : X.Curve)
    (a : Fin 3 → SurfaceBasisLabel X) : RationalTerms (Variable X) :=
  BelorousskiPandharipande.normalizedGenusTwoTerms X n sigma 0
    (SurfaceGenusZero.pointLabels a n)

/-- The original four equations at one shifted full class, with exact rational weights. -/
def row (X : SurfaceTarget) (i : Fin X.blowups) (beta : X.Curve) :
    RationalTerms (Variable X) :=
  (bpRow X (X.effective.energy beta) (beta + X.exceptionalCurve i)
    ![.exceptional i, .hyperplane, .hyperplane]).scale
      (3 * (X.planeDegree beta : ℚ) / 2) +
  (bpRow X (X.effective.energy beta) (beta + X.exceptionalCurve i)
    ![.exceptional i, .exceptional i, .hyperplane]).scale (-1) +
  (bpRow X (X.effective.energy beta) (beta + X.exceptionalCurve i)
    ![.exceptional i, .exceptional i, .exceptional i]).scale
      ((X.planeDegree beta : ℚ) / 2) +
  (bpRow X (X.effective.energy beta) (beta + X.exceptionalCurve i)
    ![.hyperplane, .hyperplane, .hyperplane]).scale (-1 / 3)

variable {X : SurfaceTarget}

/-- Each original term is constant or a canonical query at a full effective subclass. -/
theorem row_canonical_support (i : Fin X.blowups) (beta : X.Curve)
    {t : ℚ × Multiset (Variable X)} (ht : t ∈ row X i beta) :
    t.2 = 0 ∨ ∃ gamma : X.Curve, ∃ c ∈ SurfaceGenusTwo.canonicalQueries X gamma,
      t.2 = {Sum.inr c} ∧ ∃ delta : X.Curve, gamma + delta = beta + X.exceptionalCurve i := by
  simp only [row, Multiset.mem_add] at ht
  rcases ht with ((ht | ht) | ht) | ht <;>
    obtain ⟨_, u, hu, rfl⟩ := RationalTerms.mem_scale.mp ht <;>
    exact BelorousskiPandharipande.normalized_primary_canonical_support
      (X.effective.energy beta) (beta + X.exceptionalCurve i) _ (t := u) hu

/-- Collecting cancellations introduces no new canonical variable or curve class. -/
theorem collected_row_canonical_support (i : Fin X.blowups) (beta : X.Curve)
    {t : ℚ × Multiset (Variable X)} (ht : t ∈ RationalTerms.collect (row X i beta)) :
    t.2 = 0 ∨ ∃ gamma : X.Curve, ∃ c ∈ SurfaceGenusTwo.canonicalQueries X gamma,
      t.2 = {Sum.inr c} ∧ ∃ delta : X.Curve, gamma + delta = beta + X.exceptionalCurve i := by
  obtain ⟨hm, _, _⟩ := RationalTerms.mem_collect.mp ht
  obtain ⟨u, hu, he⟩ := Multiset.mem_map.mp (Multiset.mem_toFinset.mp hm)
  simpa only [← he] using row_canonical_support i beta hu

/-- A nonzero coefficient retains a canonical query and its full additive complement. -/
theorem row_coefficient_canonical (i : Fin X.blowups) (beta : X.Curve) (v : Variable X)
    (hc : RationalTerms.coefficient (row X i beta) {v} ≠ 0) :
    ∃ gamma : X.Curve, ∃ c ∈ SurfaceGenusTwo.canonicalQueries X gamma,
      v = Sum.inr c ∧ ∃ delta : X.Curve, gamma + delta = beta + X.exceptionalCurve i := by
  have hm : ({v} : Multiset (Variable X)) ∈ RationalTerms.support (row X i beta) := by
    by_contra hn
    exact hc (RationalTerms.coefficient_eq_zero_of_not_mem_support _ _ hn)
  obtain ⟨t, ht, he⟩ := Multiset.mem_map.mp (Multiset.mem_toFinset.mp hm)
  rcases row_canonical_support i beta ht with hz | ⟨gamma, c, hq, hv, delta, hd⟩
  · have hcard := congrArg Multiset.card (he.symm.trans hz)
    simp only [Multiset.card_singleton, Multiset.card_zero] at hcard
    exact (Nat.one_ne_zero hcard).elim
  · exact ⟨gamma, c, hq, Multiset.singleton_inj.mp (he.symm.trans hv), delta, hd⟩

/-- A nonzero canonical coefficient keeps its own full class in the source splitting. -/
theorem canonical_coefficient_subclass (i : Fin X.blowups) (beta gamma : X.Curve)
    (f : Family X)
    (hc : RationalTerms.coefficient (row X i beta) {Sum.inr (f.query gamma)} ≠ 0) :
    ∃ delta : X.Curve, gamma + delta = beta + X.exceptionalCurve i := by
  obtain ⟨eta, c, hq, hv, delta, hd⟩ := row_coefficient_canonical i beta _ hc
  obtain ⟨g, hg⟩ := family_of_mem_canonicalQueries hq
  have hb (family : Family X) (b : X.Curve) : (family.query b).beta = b := by
    cases family <;> rfl
  have he := congrArg SurfaceQuery.beta ((Sum.inr.inj hv).trans hg.symm)
  rw [hb, hb] at he
  exact ⟨delta, he ▸ hd⟩

/-- The shifted relation never increases plane degree; equal-degree cancellation
is a separate coefficient calculation. -/
theorem canonical_coefficient_planeDegree_le (i : Fin X.blowups) (beta gamma : X.Curve)
    (f : Family X)
    (hc : RationalTerms.coefficient (row X i beta) {Sum.inr (f.query gamma)} ≠ 0) :
    X.planeDegree gamma ≤ X.planeDegree beta := by
  obtain ⟨delta, hd⟩ := canonical_coefficient_subclass i beta gamma f hc
  exact X.planeDegree_le_of_shifted_add_eq i hd

/-- No unresolved ancestor coefficient survives the combined primary equation. -/
theorem row_ancestor_coefficient_eq_zero (i : Fin X.blowups) (beta : X.Curve)
    (q : SurfaceAncestorKey X) :
    RationalTerms.coefficient (row X i beta) {Sum.inl q} = 0 := by
  by_contra hc
  obtain ⟨_, _, _, he, _⟩ := row_coefficient_canonical i beta (.inl q) hc
  cases he

/-- Evaluation depends only on canonical descendants at effective source subclasses. -/
theorem eval_row_congr_canonical (i : Fin X.blowups) (beta : X.Curve)
    (v w : Variable X → ℚ)
    (h : ∀ gamma : X.Curve, (∃ delta : X.Curve, gamma + delta = beta + X.exceptionalCurve i) →
      ∀ c ∈ SurfaceGenusTwo.canonicalQueries X gamma, v (Sum.inr c) = w (Sum.inr c)) :
    RationalTerms.eval v (row X i beta) = RationalTerms.eval w (row X i beta) := by
  apply RationalTerms.eval_congr
  intro t ht x hx
  rcases row_canonical_support i beta ht with hz | ⟨gamma, c, hc, hm, delta, hd⟩
  · exact (Multiset.notMem_zero x (hz ▸ hx)).elim
  · rw [hm, Multiset.mem_singleton] at hx
    subst x
    exact h gamma ⟨delta, hd⟩ c hc

/-- The combined equation is derived from the four complete BP equations. -/
theorem eval_row_eq_zero (i : Fin X.blowups) (beta : X.Curve) (v : Variable X → ℚ)
    (hEHH : RationalTerms.eval v (bpRow X (X.effective.energy beta)
      (beta + X.exceptionalCurve i) ![.exceptional i, .hyperplane, .hyperplane]) = 0)
    (hEEH : RationalTerms.eval v (bpRow X (X.effective.energy beta)
      (beta + X.exceptionalCurve i) ![.exceptional i, .exceptional i, .hyperplane]) = 0)
    (hEEE : RationalTerms.eval v (bpRow X (X.effective.energy beta)
      (beta + X.exceptionalCurve i) ![.exceptional i, .exceptional i, .exceptional i]) = 0)
    (hHHH : RationalTerms.eval v (bpRow X (X.effective.energy beta)
      (beta + X.exceptionalCurve i) ![.hyperplane, .hyperplane, .hyperplane]) = 0) :
    RationalTerms.eval v (row X i beta) = 0 := by
  simp only [row, RationalTerms.eval_add, RationalTerms.eval_scale,
    hEHH, hEEH, hEEE, hHHH, mul_zero, add_zero]

end AxiomaticGW.SurfaceGenusTwoBlowupNRelation

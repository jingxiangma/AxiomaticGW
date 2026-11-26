/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoCanonicalQueries
public import AxiomaticGW.Surfaces.BPCotangentSupport
public import AxiomaticGW.Surfaces.GenusTwoNormalizedBP
public import AxiomaticGW.Surfaces.L24CotangentSupport
public import AxiomaticGW.Surfaces.GenusTwoNormalizedL24
public import AxiomaticGW.Coefficients.CollectedTerms

/-!
# Canonical variables in the complete primary BP and L24 equations

The existing low-cotangent bound and full-class affine bound apply before
normalization. Lifting the canonical terminal theorem through the complete
substitution leaves only constants and the canonical genus-two queries at
effective subclasses. All signed marking and calibration tails are retained.

The L24 low-cotangent bound uses its actual nonzero source diagrams, their
component genera and their preserved boundary edges. These results classify
actual variables and collected coefficients. They do not assert a pivot,
an order decrease, or a reconstruction recurrence. They
apply to primary external powers; higher external powers are not covered.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open SurfacePolynomialReduction SurfaceGenusTwo
variable {X : SurfaceTarget}

/-- Every nonconstant term of the complete normalized primary BP equation is
one canonical query at a full effective subclass of its source. -/
theorem normalized_primary_canonical_support (n : ℕ) (beta : X.Curve)
    (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X)
    {t : ℚ × Multiset (Variable X)}
    (ht : t ∈ normalizedGenusTwoTerms X n beta 0 a) :
    t.2 = 0 ∨ ∃ gamma : X.Curve, ∃ c ∈ canonicalQueries X gamma,
      t.2 = {Sum.inr c} ∧ ∃ delta : X.Curve, gamma + delta = beta := by
  obtain ⟨s, hs, ht⟩ := Multiset.mem_bind.mp ht
  rcases ((genusTwoTerms_bound X n beta 0 a) s hs).affine with
    hz | ⟨q, hq, hg, _, delta, hdelta⟩
  · simp only [hz, Multiset.card_zero, ite_true] at ht
    exact Or.inl (congrArg Prod.snd (RationalTerms.mem_term.mp ht).2)
  · have hk := genusTwoTerms_primary_psi_le_one X n beta a hs q
      (by rw [hq]; exact Multiset.mem_singleton_self q)
    simp only [hq, Multiset.card_singleton, one_ne_zero, if_false,
      Multiset.singleton_bind] at ht
    obtain ⟨_, u, hu, rfl⟩ := RationalTerms.mem_scale.mp ht
    obtain ⟨gamma, c, hc, hm, epsilon, he⟩ :=
      normalizedTerms_canonical_support q hg hk hu
    exact Or.inr ⟨gamma, c, hc, hm, epsilon + delta,
      by rw [← add_assoc, he, hdelta]⟩

/-- Collection changes coefficients but introduces no new variable or full
curve class. Its constants remain allowed. -/
theorem collected_normalized_primary_canonical_support (n : ℕ) (beta : X.Curve)
    (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X)
    {t : ℚ × Multiset (Variable X)}
    (ht : t ∈ RationalTerms.collect (normalizedGenusTwoTerms X n beta 0 a)) :
    t.2 = 0 ∨ ∃ gamma : X.Curve, ∃ c ∈ canonicalQueries X gamma,
      t.2 = {Sum.inr c} ∧ ∃ delta : X.Curve, gamma + delta = beta := by
  obtain ⟨hm, _, _⟩ := RationalTerms.mem_collect.mp ht
  obtain ⟨u, hu, he⟩ := Multiset.mem_map.mp (Multiset.mem_toFinset.mp hm)
  simpa only [← he] using normalized_primary_canonical_support n beta a hu

/-- A nonzero collected singleton coefficient belongs to a canonical query
at an effective subclass. This conclusion does not use syntactic occurrence
as evidence that a coefficient is nonzero. -/
theorem normalized_primary_coefficient_canonical (n : ℕ) (beta : X.Curve)
    (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X) (v : Variable X)
    (hc : RationalTerms.coefficient (normalizedGenusTwoTerms X n beta 0 a) {v} ≠ 0) :
    ∃ gamma : X.Curve, ∃ c ∈ canonicalQueries X gamma,
      v = Sum.inr c ∧ ∃ delta : X.Curve, gamma + delta = beta := by
  have hm : ({v} : Multiset (Variable X)) ∈
      RationalTerms.support (normalizedGenusTwoTerms X n beta 0 a) := by
    by_contra hn
    exact hc (RationalTerms.coefficient_eq_zero_of_not_mem_support _ _ hn)
  obtain ⟨t, ht, he⟩ := Multiset.mem_map.mp (Multiset.mem_toFinset.mp hm)
  rcases normalized_primary_canonical_support n beta a ht with
    hz | ⟨gamma, c, hq, hv, delta, hd⟩
  · have hcard := congrArg Multiset.card (he.symm.trans hz)
    simp only [Multiset.card_singleton, Multiset.card_zero] at hcard
    exact (Nat.one_ne_zero hcard).elim
  · exact ⟨gamma, c, hq, Multiset.singleton_inj.mp (he.symm.trans hv), delta, hd⟩

/-- No ancestor variable survives the full primary BP normalization, at any
requested full class, including the source and incomparable classes. -/
theorem normalized_primary_ancestor_coefficient_eq_zero (n : ℕ) (beta : X.Curve)
    (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X) (q : SurfaceAncestorKey X) :
    RationalTerms.coefficient (normalizedGenusTwoTerms X n beta 0 a) {Sum.inl q} = 0 := by
  by_contra hc
  obtain ⟨_, _, _, he, _⟩ := normalized_primary_coefficient_canonical n beta a (.inl q) hc
  cases he

/-- The complete primary BP equation needs values only on canonical queries
at effective subclasses. Constants and every normalization correction stay
in the equation. -/
theorem eval_normalized_primary_congr_canonical {A : Type*} [CommRing A] [Algebra ℚ A]
    (n : ℕ) (beta : X.Curve) (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X)
    (v w : Variable X → A)
    (h : ∀ gamma : X.Curve, (∃ delta : X.Curve, gamma + delta = beta) →
      ∀ c ∈ canonicalQueries X gamma, v (Sum.inr c) = w (Sum.inr c)) :
    RationalTerms.eval v (normalizedGenusTwoTerms X n beta 0 a) =
      RationalTerms.eval w (normalizedGenusTwoTerms X n beta 0 a) := by
  apply RationalTerms.eval_congr
  intro t ht x hx
  rcases normalized_primary_canonical_support n beta a ht with
    hz | ⟨gamma, c, hc, hm, delta, hd⟩
  · exact (Multiset.notMem_zero x (hz ▸ hx)).elim
  · rw [hm, Multiset.mem_singleton] at hx
    subst x
    exact h gamma ⟨delta, hd⟩ c hc

end AxiomaticGW.BelorousskiPandharipande

namespace AxiomaticGW.L24Relation
open SurfacePolynomialReduction SurfaceGenusTwo
variable {X : SurfaceTarget}

-- Elaboration traverses the same 815-column dispatch as the complete L24 source.
set_option maxRecDepth 20000

/-- Every nonconstant term of the complete normalized primary L24 equation is
one canonical query at a full effective subclass of its source. -/
theorem normalized_primary_canonical_support (n : ℕ) (beta : X.Curve)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    {t : ℚ × Multiset (Variable X)}
    (ht : t ∈ normalizedGenusTwoTerms X n beta 0 a) :
    t.2 = 0 ∨ ∃ gamma : X.Curve, ∃ c ∈ canonicalQueries X gamma,
      t.2 = {Sum.inr c} ∧ ∃ delta : X.Curve, gamma + delta = beta := by
  obtain ⟨s, hs, ht⟩ := Multiset.mem_bind.mp ht
  rcases ((genusTwoTerms_bound X n beta 0 a) s hs).affine with
    hz | ⟨q, hq, hg, _, delta, hdelta⟩
  · simp only [hz, Multiset.card_zero, ite_true] at ht
    exact Or.inl (congrArg Prod.snd (RationalTerms.mem_term.mp ht).2)
  · have hk := genusTwoTerms_primary_psi_le_one X n beta a hs q
      (by rw [hq]; exact Multiset.mem_singleton_self q)
    simp only [hq, Multiset.card_singleton, one_ne_zero, if_false,
      Multiset.singleton_bind] at ht
    obtain ⟨_, u, hu, rfl⟩ := RationalTerms.mem_scale.mp ht
    obtain ⟨gamma, c, hc, hm, epsilon, he⟩ :=
      normalizedTerms_canonical_support q hg hk hu
    exact Or.inr ⟨gamma, c, hc, hm, epsilon + delta,
      by rw [← add_assoc, he, hdelta]⟩

/-- Collection changes coefficients but introduces no new variable or full
curve class. Its constants remain allowed. -/
theorem collected_normalized_primary_canonical_support (n : ℕ) (beta : X.Curve)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    {t : ℚ × Multiset (Variable X)}
    (ht : t ∈ RationalTerms.collect (normalizedGenusTwoTerms X n beta 0 a)) :
    t.2 = 0 ∨ ∃ gamma : X.Curve, ∃ c ∈ canonicalQueries X gamma,
      t.2 = {Sum.inr c} ∧ ∃ delta : X.Curve, gamma + delta = beta := by
  obtain ⟨hm, _, _⟩ := RationalTerms.mem_collect.mp ht
  obtain ⟨u, hu, he⟩ := Multiset.mem_map.mp (Multiset.mem_toFinset.mp hm)
  simpa only [← he] using normalized_primary_canonical_support n beta a hu

/-- A nonzero collected singleton coefficient belongs to a canonical query
at an effective subclass. This conclusion does not use syntactic occurrence
as evidence that a coefficient is nonzero. -/
theorem normalized_primary_coefficient_canonical (n : ℕ) (beta : X.Curve)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) (v : Variable X)
    (hc : RationalTerms.coefficient (normalizedGenusTwoTerms X n beta 0 a) {v} ≠ 0) :
    ∃ gamma : X.Curve, ∃ c ∈ canonicalQueries X gamma,
      v = Sum.inr c ∧ ∃ delta : X.Curve, gamma + delta = beta := by
  have hm : ({v} : Multiset (Variable X)) ∈
      RationalTerms.support (normalizedGenusTwoTerms X n beta 0 a) := by
    by_contra hn
    exact hc (RationalTerms.coefficient_eq_zero_of_not_mem_support _ _ hn)
  obtain ⟨t, ht, he⟩ := Multiset.mem_map.mp (Multiset.mem_toFinset.mp hm)
  rcases normalized_primary_canonical_support n beta a ht with
    hz | ⟨gamma, c, hq, hv, delta, hd⟩
  · have hcard := congrArg Multiset.card (he.symm.trans hz)
    simp only [Multiset.card_singleton, Multiset.card_zero] at hcard
    exact (Nat.one_ne_zero hcard).elim
  · exact ⟨gamma, c, hq, Multiset.singleton_inj.mp (he.symm.trans hv), delta, hd⟩

/-- No ancestor variable survives the full primary L24 normalization, at any
requested full class, including the source and incomparable classes. -/
theorem normalized_primary_ancestor_coefficient_eq_zero (n : ℕ) (beta : X.Curve)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) (q : SurfaceAncestorKey X) :
    RationalTerms.coefficient (normalizedGenusTwoTerms X n beta 0 a) {Sum.inl q} = 0 := by
  by_contra hc
  obtain ⟨_, _, _, he, _⟩ := normalized_primary_coefficient_canonical n beta a (.inl q) hc
  cases he

/-- The complete primary L24 equation needs values only on canonical queries
at effective subclasses. Constants and every normalization correction stay
in the equation. -/
theorem eval_normalized_primary_congr_canonical {A : Type*} [CommRing A] [Algebra ℚ A]
    (n : ℕ) (beta : X.Curve) (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (v w : Variable X → A)
    (h : ∀ gamma : X.Curve, (∃ delta : X.Curve, gamma + delta = beta) →
      ∀ c ∈ canonicalQueries X gamma, v (Sum.inr c) = w (Sum.inr c)) :
    RationalTerms.eval v (normalizedGenusTwoTerms X n beta 0 a) =
      RationalTerms.eval w (normalizedGenusTwoTerms X n beta 0 a) := by
  apply RationalTerms.eval_congr
  intro t ht x hx
  rcases normalized_primary_canonical_support n beta a ht with
    hz | ⟨gamma, c, hc, hm, delta, hd⟩
  · exact (Multiset.notMem_zero x (hz ▸ hx)).elim
  · rw [hm, Multiset.mem_singleton] at hx
    subst x
    exact h gamma ⟨delta, hd⟩ c hc

end AxiomaticGW.L24Relation

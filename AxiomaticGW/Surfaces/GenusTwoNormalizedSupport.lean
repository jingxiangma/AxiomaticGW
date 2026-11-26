/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.OnePsiSupport
public import AxiomaticGW.Surfaces.GenusTwoNormalizedBP
public import AxiomaticGW.Surfaces.GenusTwoNormalizedL24

/-!
# Genus-two dependencies after ancestor normalization

Primary/first-descendant normalization preserves affine genus-two support and
effective full-class remainders. All remaining variables outside the input
class have strictly smaller anticanonical energy, including rational-tail
corrections. At the input class their exact coefficients can be calculated
using direct normalization without calibration. These facts do not assert
that the combined BP/L24 system is invertible.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction
open SurfaceGenusZero (variableCurve)
open SurfaceLowGenus (variableGenus)
variable {X : SurfaceTarget}

/-- Affine genus-two support with dimension compatibility and a full effective remainder. -/
def NormalizedTermsBound (beta : X.Curve) (p : RationalTerms (Variable X)) : Prop :=
  ∀ t ∈ p, t.2 = 0 ∨ ∃ v, t.2 = {v} ∧ variableGenus v = 2 ∧
    variableDimensionCompatible v ∧ ∃ delta : X.Curve, variableCurve v + delta = beta

/-- The complete normalization preserves the support needed for recursive reconstruction. -/
theorem normalizedTerms_bound {beta : X.Curve} {p : RationalTerms (SurfaceAncestorKey X)}
    (hp : TermsBound 2 beta p) :
    NormalizedTermsBound beta (RationalTerms.affineSubstitute normalizedTerms p) := by
  intro t ht
  obtain ⟨s, hs, ht⟩ := Multiset.mem_bind.mp ht
  rcases (hp s hs).affine with hz | ⟨q, hq, hg, _, delta, hdelta⟩
  · simp only [hz, Multiset.card_zero, ite_true] at ht
    unfold RationalTerms.term at ht
    split_ifs at ht
    · exact (Multiset.notMem_zero _ ht).elim
    · exact Or.inl (congrArg Prod.snd (Multiset.mem_singleton.mp ht))
  · simp only [hq, Multiset.card_singleton, one_ne_zero, if_false,
      Multiset.singleton_bind] at ht
    unfold RationalTerms.scale at ht
    split_ifs at ht
    · exact (Multiset.notMem_zero _ ht).elim
    · obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp ht
      obtain ⟨v, hm, hv, hd, epsilon, he⟩ := normalizedTerms_support q (by omega) hr
      exact Or.inr ⟨v, hm, hv.trans hg, hd, epsilon + delta,
        by rw [← add_assoc, he, hdelta]⟩

/-- Any normalized dependency either has the exact input class or smaller energy. -/
theorem NormalizedTermsBound.dependency {beta : X.Curve} {p : RationalTerms (Variable X)}
    (hp : NormalizedTermsBound beta p) {t : ℚ × Multiset (Variable X)} (ht : t ∈ p)
    (v : Variable X) (hv : v ∈ t.2) :
    variableGenus v = 2 ∧ variableDimensionCompatible v ∧
      (variableCurve v = beta ∨
        X.effective.energy (variableCurve v) < X.effective.energy beta) := by
  rcases hp t ht with hm | ⟨w, hm, hg, hd, delta, hdelta⟩
  · exact (Multiset.notMem_zero v (hm ▸ hv)).elim
  · rw [hm, Multiset.mem_singleton] at hv
    subst w
    refine ⟨hg, hd, ?_⟩
    by_cases hz : delta = 0
    · exact Or.inl (by simpa only [hz, add_zero] using hdelta)
    · have hpos : 0 < X.effective.energy delta :=
        Nat.pos_of_ne_zero (fun he ↦ hz ((X.effective.energy_eq_zero_iff delta).mp he))
      have he := congrArg X.effective.energy hdelta
      rw [map_add] at he
      exact Or.inr (by omega)

/-- Keep every term containing an unknown at the original full class. -/
def normalizedSameClassTerms (beta : X.Curve) (p : RationalTerms (Variable X)) :
    RationalTerms (Variable X) := p.filter (fun t ↦ ¬∀ v ∈ t.2, variableCurve v ≠ beta)

/-- Constants and strictly smaller-class variables remain in the recursive remainder. -/
def normalizedSmallerClassTerms (beta : X.Curve) (p : RationalTerms (Variable X)) :
    RationalTerms (Variable X) := p.filter (fun t ↦ ∀ v ∈ t.2, variableCurve v ≠ beta)

/-- The complete normalized equation splits without discarding a constant or correction. -/
theorem eval_normalized_split_by_class {A : Type*} [CommRing A] [Algebra ℚ A]
    (v : Variable X → A) (beta : X.Curve) (p : RationalTerms (Variable X)) :
    RationalTerms.eval v p = RationalTerms.eval v (normalizedSameClassTerms beta p) +
      RationalTerms.eval v (normalizedSmallerClassTerms beta p) := by
  rw [← RationalTerms.eval_add, normalizedSameClassTerms, normalizedSmallerClassTerms,
    add_comm, Multiset.filter_add_not]

/-- Removing all original-class unknowns gives a strictly decreasing remainder. -/
theorem normalizedSmallerClassTerms_dependencies {beta : X.Curve}
    {p : RationalTerms (Variable X)} (hp : NormalizedTermsBound beta p)
    {t : ℚ × Multiset (Variable X)} (ht : t ∈ normalizedSmallerClassTerms beta p)
    (v : Variable X) (hv : v ∈ t.2) :
    variableGenus v = 2 ∧ variableDimensionCompatible v ∧
      X.effective.energy (variableCurve v) < X.effective.energy beta := by
  obtain ⟨ht, hne⟩ := Multiset.mem_filter.mp ht
  obtain ⟨hg, hd, he⟩ := hp.dependency ht v hv
  exact ⟨hg, hd, he.resolve_left (hne v hv)⟩

/-- The retained system consists precisely of singleton unknowns at the input class. -/
theorem normalizedSameClassTerms_dependencies {beta : X.Curve}
    {p : RationalTerms (Variable X)} (hp : NormalizedTermsBound beta p)
    {t : ℚ × Multiset (Variable X)} (ht : t ∈ normalizedSameClassTerms beta p) :
    ∃ v, t.2 = {v} ∧ variableGenus v = 2 ∧ variableDimensionCompatible v ∧
      variableCurve v = beta := by
  obtain ⟨ht, hsame⟩ := Multiset.mem_filter.mp ht
  rcases hp t ht with hz | ⟨v, hv, hg, hd, _⟩
  · exact (hsame (by simp only [hz, Multiset.notMem_zero, false_implies, implies_true])).elim
  · refine ⟨v, hv, hg, hd, ?_⟩
    by_contra hne
    apply hsame
    intro w hw
    rw [hv, Multiset.mem_singleton] at hw
    exact hw ▸ hne

/-- Calibration tails do not change the same-class coefficient matrix of an
entire genus-two equation. This is uniform in classes, powers and marking counts. -/
theorem coefficient_normalized_eq_direct {beta : X.Curve}
    {p : RationalTerms (SurfaceAncestorKey X)} (hp : TermsBound 2 beta p)
    (v : Variable X) (hv : variableCurve v = beta) :
    RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms p) {v} =
      RationalTerms.coefficient (RationalTerms.affineSubstitute directNormalizedTerms p) {v} := by
  unfold RationalTerms.affineSubstitute
  simp only [RationalTerms.coefficient, Multiset.map_bind, Multiset.sum_bind]
  congr 1
  apply Multiset.map_congr rfl
  intro t ht
  by_cases hz : t.2.card = 0
  · simp only [hz, ite_true]
  · simp only [if_neg hz]
    change RationalTerms.coefficient (RationalTerms.scale t.1 (t.2.bind normalizedTerms)) {v} =
      RationalTerms.coefficient (RationalTerms.scale t.1 (t.2.bind directNormalizedTerms)) {v}
    rw [RationalTerms.coefficient_scale, RationalTerms.coefficient_scale]
    congr 1
    simp only [RationalTerms.coefficient, Multiset.map_bind, Multiset.sum_bind]
    congr 1
    apply Multiset.map_congr rfl
    intro q hq
    apply coefficient_normalizedTerms_eq_direct_of_energy_le
    rw [hv]
    rcases ((hp t ht).dependency q hq).2.2 with he | he
    · exact le_of_eq (congrArg X.effective.energy he)
    · exact le_of_lt he

/-- The recursive remainder makes no contribution to an input-class coefficient. -/
theorem coefficient_direct_smallerClassTerms_eq_zero {beta : X.Curve}
    {p : RationalTerms (SurfaceAncestorKey X)} (hp : TermsBound 2 beta p)
    (v : Variable X) (hv : variableCurve v = beta) :
    RationalTerms.coefficient
      (RationalTerms.affineSubstitute directNormalizedTerms
        (smallerClassTerms beta p)) {v} = 0 := by
  unfold RationalTerms.affineSubstitute RationalTerms.coefficient
  rw [Multiset.map_bind, Multiset.sum_bind]
  apply Multiset.sum_eq_zero
  intro c hc
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hc
  obtain ⟨ht, hne⟩ := Multiset.mem_filter.mp ht
  by_cases hz : t.2.card = 0
  · simp only [hz, ite_true]
    change RationalTerms.coefficient (RationalTerms.term t.1 0) {v} = 0
    rw [RationalTerms.coefficient_term, if_neg (by
      intro he
      have hc := congrArg Multiset.card he
      simp only [Multiset.card_zero, Multiset.card_singleton] at hc
      omega)]
  · simp only [if_neg hz]
    change RationalTerms.coefficient
      (RationalTerms.scale t.1 (t.2.bind directNormalizedTerms)) {v} = 0
    rw [RationalTerms.coefficient_scale]
    apply mul_eq_zero_of_right
    simp only [RationalTerms.coefficient, Multiset.map_bind, Multiset.sum_bind]
    apply Multiset.sum_eq_zero
    intro d hd
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hd
    apply coefficient_directNormalizedTerms_eq_zero q ((hp t ht).1 q hq).1 v
    intro he
    exact hne q hq (he.symm.trans hv)

/-- Exact leading coefficients need only original-class ancestors and direct
normalization. All omitted terms stay in the proved decreasing remainder. -/
theorem coefficient_normalized_eq_sameClass_direct {beta : X.Curve}
    {p : RationalTerms (SurfaceAncestorKey X)} (hp : TermsBound 2 beta p)
    (v : Variable X) (hv : variableCurve v = beta) :
    RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms p) {v} =
      RationalTerms.coefficient
        (RationalTerms.affineSubstitute directNormalizedTerms (sameClassTerms beta p)) {v} := by
  rw [coefficient_normalized_eq_direct hp v hv]
  have he : p = sameClassTerms beta p + smallerClassTerms beta p := by
    rw [sameClassTerms, smallerClassTerms, add_comm, Multiset.filter_add_not]
  conv_lhs => rw [he]
  rw [RationalTerms.affineSubstitute, Multiset.add_bind, RationalTerms.coefficient_add]
  change RationalTerms.coefficient
      (RationalTerms.affineSubstitute directNormalizedTerms (sameClassTerms beta p)) {v} +
    RationalTerms.coefficient
      (RationalTerms.affineSubstitute directNormalizedTerms (smallerClassTerms beta p)) {v} = _
  rw [coefficient_direct_smallerClassTerms_eq_zero hp v hv, add_zero]

end AxiomaticGW.SurfaceGenusTwo

namespace AxiomaticGW.BelorousskiPandharipande
open RelationCertificate PsiBoundaryExpansion

/-- The complete normalized BP family retains affine full-class support. -/
theorem normalizedGenusTwoTerms_bound (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 3) → ℕ) (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X) :
    SurfaceGenusTwo.NormalizedTermsBound beta (normalizedGenusTwoTerms X n beta k a) :=
  SurfaceGenusTwo.normalizedTerms_bound (genusTwoTerms_bound X n beta k a)

end AxiomaticGW.BelorousskiPandharipande

namespace AxiomaticGW.L24Relation
open RelationCertificate PsiBoundaryExpansion

/-- The complete normalized L24 family retains affine full-class support. -/
theorem normalizedGenusTwoTerms_bound (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    SurfaceGenusTwo.NormalizedTermsBound beta (normalizedGenusTwoTerms X n beta k a) :=
  SurfaceGenusTwo.normalizedTerms_bound (genusTwoTerms_bound X n beta k a)

end AxiomaticGW.L24Relation

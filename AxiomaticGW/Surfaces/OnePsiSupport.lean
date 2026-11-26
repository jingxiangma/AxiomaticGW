/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.OnePsiReduction
public import AxiomaticGW.Surfaces.GenusOneSupport

/-!
# Full-class support of primary and first-descendant normalization

The direct string, dilaton and divisor substitution preserves genus and full
curve class. The ancestor correction has a positive rational tail, hence a
strictly smaller main energy. These are support statements about the actual
uncollected expressions, independent of geometric inputs or numerical seeds.
-/

@[expose] public section

namespace AxiomaticGW

private theorem mem_term_monomial {σ : Type*} (c : ℚ) (m : Multiset σ)
    {t : ℚ × Multiset σ} (ht : t ∈ RationalTerms.term c m) : t.2 = m := by
  unfold RationalTerms.term at ht
  split_ifs at ht
  · exact (Multiset.notMem_zero _ ht).elim
  · exact congrArg Prod.snd (Multiset.mem_singleton.mp ht)

private theorem mem_scale_monomial {σ : Type*} (c : ℚ) (p : RationalTerms σ)
    {t : ℚ × Multiset σ} (ht : t ∈ RationalTerms.scale c p) :
    ∃ s ∈ p, t.2 = s.2 := by
  unfold RationalTerms.scale at ht
  split_ifs at ht
  · exact (Multiset.notMem_zero _ ht).elim
  · obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp ht
    exact ⟨s, hs, rfl⟩

namespace SurfaceFirstDescendant
variable {X : SurfaceTarget}

private theorem dimensionTerms_support (q : SurfaceQuery X)
    {t : ℚ × Multiset (SurfaceQuery X)} (ht : t ∈ dimensionTerms q) :
    t.2 = {q} ∧ q.DimensionCompatible := by
  unfold dimensionTerms at ht
  split_ifs at ht with hd
  · exact ⟨mem_term_monomial _ _ ht, hd⟩
  · exact (Multiset.notMem_zero _ ht).elim

/-- Every surviving primary term retains the exact genus and curve class. -/
theorem primaryTerms_support (g : ℕ) (beta : X.Curve) (m : Multiset (SurfaceBasisLabel X))
    {t : ℚ × Multiset (SurfaceQuery X)} (ht : t ∈ primaryTerms g beta m) :
    ∃ q, t.2 = {q} ∧ q.genus = g ∧ q.beta = beta ∧ q.DimensionCompatible := by
  obtain ⟨s, hs, hm⟩ := mem_scale_monomial _ _ ht
  obtain ⟨hs, hd⟩ := dimensionTerms_support _ hs
  exact ⟨_, hm.trans hs, rfl, rfl, hd⟩

/-- String, dilaton and cup-product corrections preserve the entire curve class. -/
theorem terms_support (g : ℕ) (beta : X.Curve) (b : SurfaceBasisLabel X)
    (m : Multiset (SurfaceBasisLabel X)) {t : ℚ × Multiset (SurfaceQuery X)}
    (ht : t ∈ terms g beta b m) :
    ∃ q, t.2 = {q} ∧ q.genus = g ∧ q.beta = beta ∧ q.DimensionCompatible := by
  unfold terms at ht
  split_ifs at ht
  · exact primaryTerms_support _ _ _ ht
  · obtain ⟨s, hs, hm⟩ := mem_scale_monomial _ _ ht
    obtain ⟨q, hq, hg, hb, hd⟩ := primaryTerms_support _ _ _ hs
    exact ⟨q, hm.trans hq, hg, hb, hd⟩
  · rcases Multiset.mem_add.mp ht with ht | ht
    · obtain ⟨s, hs, hm⟩ := mem_scale_monomial _ _ ht
      obtain ⟨hs, hd⟩ := dimensionTerms_support _ hs
      exact ⟨_, hm.trans hs, rfl, rfl, hd⟩
    · obtain ⟨s, hs, hm⟩ := mem_scale_monomial _ _ ht
      obtain ⟨hs, hd⟩ := dimensionTerms_support _ hs
      exact ⟨_, hm.trans hs, rfl, rfl, hd⟩

end SurfaceFirstDescendant

namespace SurfacePolynomialReduction
open SurfaceGenusZero (variableCurve)
open SurfaceLowGenus (variableGenus)
variable {X : SurfaceTarget}

/-- The existing dimension condition interpreted according to the variable's tag. -/
def variableDimensionCompatible : Variable X → Prop
  | .inl q => q.DimensionCompatible
  | .inr q => q.DimensionCompatible

private theorem rename_query_support (g : ℕ) (beta : X.Curve)
    (p : RationalTerms (SurfaceQuery X))
    (hp : ∀ s ∈ p, ∃ q, s.2 = {q} ∧ q.genus = g ∧ q.beta = beta ∧ q.DimensionCompatible)
    {t : ℚ × Multiset (Variable X)} (ht : t ∈ RationalTerms.rename Sum.inr p) :
    ∃ v, t.2 = {v} ∧ variableGenus v = g ∧ variableCurve v = beta ∧
      variableDimensionCompatible v := by
  obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp ht
  obtain ⟨q, hq, hg, hb, hd⟩ := hp s hs
  exact ⟨.inr q, by rw [hq, Multiset.map_singleton], hg, hb, hd⟩

/-- Canonical primary reduction has no constant term or change of curve class. -/
theorem canonicalPrimaryTerms_support (q : SurfaceAncestorKey X) (hg : 2 ≤ q.genus)
    {t : ℚ × Multiset (Variable X)} (ht : t ∈ canonicalPrimaryTerms q) :
    ∃ v, t.2 = {v} ∧ variableGenus v = q.genus ∧ variableCurve v = q.beta ∧
      variableDimensionCompatible v := by
  unfold canonicalPrimaryTerms at ht
  by_cases hp : q.IsPrimary
  · rw [if_pos ⟨hg, hp⟩] at ht
    exact rename_query_support _ _ _ (fun s hs ↦
      SurfaceFirstDescendant.primaryTerms_support _ _ _ hs) ht
  · rw [if_neg (fun h ↦ hp h.2)] at ht
    simp only [basicTerms, reduceVariable, hp, false_and, ite_false] at ht
    split_ifs at ht with hd
    · exact ⟨.inl q, mem_term_monomial _ _ ht, rfl, rfl, hd⟩
    · exact (Multiset.notMem_zero _ ht).elim

/-- A coefficient at a different full class is absent even before collection. -/
theorem coefficient_canonicalPrimaryTerms_eq_zero (q : SurfaceAncestorKey X)
    (hg : 2 ≤ q.genus) (v : Variable X) (hv : variableCurve v ≠ q.beta) :
    RationalTerms.coefficient (canonicalPrimaryTerms q) {v} = 0 := by
  unfold RationalTerms.coefficient
  apply Multiset.sum_eq_zero
  intro c hc
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hc
  have hne : t.2 ≠ {v} := by
    obtain ⟨w, hw, _, hb, _⟩ := canonicalPrimaryTerms_support q hg ht
    intro he
    have h : w = v := Multiset.singleton_inj.mp (hw.symm.trans he)
    exact hv (h ▸ hb)
  exact if_neg hne

/-- Direct normalization omits only the smaller-class rational-tail corrections.
It is used to extract leading coefficients, not as a replacement GW equation. -/
def directNormalizedTerms (q : SurfaceAncestorKey X) : RationalTerms (Variable X) :=
  if h : 2 ≤ q.genus ∧ q.totalPsi = 1 then
    RationalTerms.rename Sum.inr (SurfaceFirstDescendant.terms q.genus q.beta
      (q.onePsiInsertion h.2).label (q.onePsiPrimaries h.2))
  else canonicalPrimaryTerms q

/-- Every direct-normalization variable is a dimension-compatible request at
the original genus and full class; constants are not introduced. -/
theorem directNormalizedTerms_support (q : SurfaceAncestorKey X) (hg : 2 ≤ q.genus)
    {t : ℚ × Multiset (Variable X)} (ht : t ∈ directNormalizedTerms q) :
    ∃ v, t.2 = {v} ∧ variableGenus v = q.genus ∧ variableCurve v = q.beta ∧
      variableDimensionCompatible v := by
  unfold directNormalizedTerms at ht
  split_ifs at ht
  · exact rename_query_support _ _ _ (fun s hs ↦
      SurfaceFirstDescendant.terms_support _ _ _ _ hs) ht
  · exact canonicalPrimaryTerms_support q hg ht

/-- Direct normalization never transfers a coefficient to another full class. -/
theorem coefficient_directNormalizedTerms_eq_zero (q : SurfaceAncestorKey X)
    (hg : 2 ≤ q.genus) (v : Variable X) (hv : variableCurve v ≠ q.beta) :
    RationalTerms.coefficient (directNormalizedTerms q) {v} = 0 := by
  unfold RationalTerms.coefficient
  apply Multiset.sum_eq_zero
  intro c hc
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hc
  apply if_neg
  intro he
  obtain ⟨w, hw, _, hb, _⟩ := directNormalizedTerms_support q hg ht
  have h : w = v := Multiset.singleton_inj.mp (hw.symm.trans he)
  exact hv (h ▸ hb)

/-- Normalization preserves affine support and genus, and can only remove an
effective curve class. The assertion applies to every uncollected term. -/
theorem normalizedTerms_support (q : SurfaceAncestorKey X) (hg : 2 ≤ q.genus)
    {t : ℚ × Multiset (Variable X)} (ht : t ∈ normalizedTerms q) :
    ∃ v, t.2 = {v} ∧ variableGenus v = q.genus ∧ variableDimensionCompatible v ∧
      ∃ delta : X.Curve, variableCurve v + delta = q.beta := by
  unfold normalizedTerms at ht
  split_ifs at ht with h
  · rcases Multiset.mem_add.mp ht with ht | ht
    · obtain ⟨v, hm, hv, hb, hd⟩ := rename_query_support _ _ _ (fun s hs ↦
        SurfaceFirstDescendant.terms_support _ _ _ _ hs) ht
      exact ⟨v, hm, hv, hd, 0, by rw [add_zero, hb]⟩
    · obtain ⟨split, hs, ht⟩ := Multiset.mem_sum.mp ht
      obtain ⟨b, _, ht⟩ := Multiset.mem_sum.mp ht
      obtain ⟨s, ht, hm⟩ := mem_scale_monomial _ _ ht
      obtain ⟨v, hmon, hv, hb, hd⟩ := canonicalPrimaryTerms_support
        (SurfaceAncestorKey.ofLabels q.genus (Fin q.orderedInsertions.length) q.ordered_stable
          split.1 0 (Function.update q.orderedLabels (q.onePsiMark h.2) b)) hg ht
      have hsplit : split.1 + split.2 = q.beta := by
        have hs := (Finset.mem_filter.mp hs).1
        rw [X.splittings_eq] at hs
        exact (X.effective.mem_splittings _ _ _).mp hs
      exact ⟨v, hm.trans hmon, hv, hd, split.2, by rw [hb]; exact hsplit⟩
  · obtain ⟨v, hm, hv, hb, hd⟩ := canonicalPrimaryTerms_support q hg ht
    exact ⟨v, hm, hv, hd, 0, by rw [add_zero, hb]⟩

/-- Normalization of genus at least two creates no constant term. Every retained
term is a singleton, including the signed calibration tails and unchanged higher ancestors. -/
theorem eval_zero_normalizedTerms (q : SurfaceAncestorKey X) (hg : 2 ≤ q.genus) :
    RationalTerms.eval (fun _ ↦ (0 : ℚ)) (normalizedTerms q) = 0 := by
  unfold RationalTerms.eval
  apply Multiset.sum_eq_zero
  intro c hc
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hc
  obtain ⟨v, hv, _⟩ := normalizedTerms_support q hg ht
  simp only [hv, Multiset.map_singleton, Multiset.prod_singleton, mul_zero]

/-- Rational tails cannot alter a coefficient at the same or higher energy.
The statement still compares individual full-class variables, not energy classes. -/
theorem coefficient_normalizedTerms_eq_direct_of_energy_le (q : SurfaceAncestorKey X)
    (v : Variable X)
    (hv : X.effective.energy q.beta ≤ X.effective.energy (variableCurve v)) :
    RationalTerms.coefficient (normalizedTerms q) {v} =
      RationalTerms.coefficient (directNormalizedTerms q) {v} := by
  unfold normalizedTerms directNormalizedTerms
  split_ifs with h
  · rw [RationalTerms.coefficient_add]
    suffices hc : RationalTerms.coefficient
        (∑ split ∈ X.positiveTailSplittings q.beta, ∑ b : SurfaceBasisLabel X,
          RationalTerms.scale
            (-SurfaceDescendant.firstCalibrationMatrix X split.2 b
              (q.orderedLabels (q.onePsiMark h.2)))
            (canonicalPrimaryTerms (SurfaceAncestorKey.ofLabels q.genus
              (Fin q.orderedInsertions.length) q.ordered_stable split.1 0
              (Function.update q.orderedLabels (q.onePsiMark h.2) b)))) {v} = 0 by
      rw [hc, add_zero]
    rw [RationalTerms.coefficient_sum]
    apply Finset.sum_eq_zero
    intro split hs
    rw [RationalTerms.coefficient_sum]
    apply Finset.sum_eq_zero
    intro b _
    rw [RationalTerms.coefficient_scale]
    have hne : variableCurve v ≠ split.1 := by
      intro he
      have hlt := normalizedTail_energy_lt X q.beta split hs
      rw [he] at hv
      omega
    rw [coefficient_canonicalPrimaryTerms_eq_zero
      (SurfaceAncestorKey.ofLabels q.genus (Fin q.orderedInsertions.length) q.ordered_stable
        split.1 0 (Function.update q.orderedLabels (q.onePsiMark h.2) b)) h.1 v hne, mul_zero]
  · rfl

/-- In particular, direct normalization gives the exact coefficient at the input class. -/
theorem coefficient_normalizedTerms_eq_direct (q : SurfaceAncestorKey X)
    (v : Variable X) (hv : variableCurve v = q.beta) :
    RationalTerms.coefficient (normalizedTerms q) {v} =
      RationalTerms.coefficient (directNormalizedTerms q) {v} :=
  coefficient_normalizedTerms_eq_direct_of_energy_le q v (by rw [hv])

end SurfacePolynomialReduction
end AxiomaticGW

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.OnePsiSupport
public import AxiomaticGW.Coefficients.TermSupport

/-!
# Canonical genus-two queries on the fixed surfaces

Primary and first-power normalization leaves only the primary point family,
one first descendant for each basis divisor, and the point first descendant
at positive energy. Full ancestor normalization retains its signed rational
tail terms at effective subclasses. These support results assert no values,
pivots or reconstruction recurrence.
-/

@[expose] public section

namespace AxiomaticGW

namespace SurfaceQuery

/-- The primary point count follows from the integer surface dimension equation. -/
theorem dimensionCompatible_points {X : SurfaceTarget} (g : ℕ) (beta : X.Curve)
    (n : ℕ) : (points X g beta n).DimensionCompatible ↔
      n + 1 = X.effective.energy beta + g := by
  unfold DimensionCompatible totalCodimension
  simp only [points, List.length_replicate, List.get_eq_getElem, List.getElem_replicate,
    SurfaceBasisLabel.codimension, add_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  change ((n * 2 : ℕ) : ℤ) =
    (X.effective.energy beta : ℤ) + (g : ℤ) - 1 + (n : ℤ) ↔ _
  omega

/-- A first descendant retains the actual codimension of its basis label. -/
theorem dimensionCompatible_first {X : SurfaceTarget} (g : ℕ) (beta : X.Curve)
    (b : SurfaceBasisLabel X) (n : ℕ) :
    (SurfaceFirstDescendant.query g beta b n).DimensionCompatible ↔
      n + b.codimension + 1 = X.effective.energy beta + g := by
  have hsum : (SurfaceFirstDescendant.query g beta b n).totalCodimension =
      b.codimension + 1 + n * 2 := by
    rw [totalCodimension, ← List.sum_ofFn]
    change (List.ofFn ((fun s : SurfaceInsertion X ↦ s.label.codimension + s.psi) ∘
      (SurfaceFirstDescendant.query g beta b n).insertions.get)).sum = _
    rw [← List.map_ofFn, List.ofFn_get]
    simp only [SurfaceFirstDescendant.query, List.map_cons, List.sum_cons,
      List.map_replicate, List.sum_replicate, SurfaceBasisLabel.codimension,
      add_zero, nsmul_eq_mul, Nat.cast_id]
  rw [DimensionCompatible, hsum]
  simp only [SurfaceFirstDescendant.query, List.length_cons, List.length_replicate]
  change (((b.codimension + 1) + n * 2 : ℕ) : ℤ) =
    (X.effective.energy beta : ℤ) + (g : ℤ) - 1 + ((n + 1 : ℕ) : ℤ) ↔ _
  omega

end SurfaceQuery

namespace SurfaceGenusTwo

/-- Complete primary/first-descendant requests at one full curve class.
The dimension-incompatible point descendant at class zero is excluded. -/
def canonicalQueries (X : SurfaceTarget) (beta : X.Curve) : List (SurfaceQuery X) :=
  let e := X.effective.energy beta
  SurfaceQuery.points X 2 beta (e + 1) ::
    SurfaceFirstDescendant.query 2 beta .hyperplane e ::
    (List.finRange X.blowups).map (fun i ↦
      SurfaceFirstDescendant.query 2 beta (.exceptional i) e) ++
    if e = 0 then [] else [SurfaceFirstDescendant.query 2 beta .point (e - 1)]

/-- Membership distinguishes every divisor and retains the positive-energy point condition. -/
theorem mem_canonicalQueries {X : SurfaceTarget} (beta : X.Curve) (q : SurfaceQuery X) :
    q ∈ canonicalQueries X beta ↔
      q = SurfaceQuery.points X 2 beta (X.effective.energy beta + 1) ∨
      q = SurfaceFirstDescendant.query 2 beta .hyperplane (X.effective.energy beta) ∨
      (∃ i, q = SurfaceFirstDescendant.query 2 beta (.exceptional i)
        (X.effective.energy beta)) ∨
      (0 < X.effective.energy beta ∧
        q = SurfaceFirstDescendant.query 2 beta .point (X.effective.energy beta - 1)) := by
  simp only [canonicalQueries, List.mem_cons, List.mem_append, List.mem_map,
    List.mem_finRange, true_and]
  by_cases he : X.effective.energy beta = 0
  · simp only [he, ite_true, List.not_mem_nil, or_false, Nat.lt_irrefl, false_and, eq_comm]
  · simp only [if_neg he, List.mem_singleton]
    have hp : 0 < X.effective.energy beta := Nat.pos_of_ne_zero he
    simp only [hp, true_and, eq_comm, or_assoc]

/-- Every canonical request belongs to the geometric query domain, including class zero. -/
theorem canonicalQueries_geometricDomain {X : SurfaceTarget} (beta : X.Curve)
    {q : SurfaceQuery X} (hq : q ∈ canonicalQueries X beta) : q.GeometricDomain := by
  rcases (mem_canonicalQueries beta q).mp hq with h | h | ⟨i, h⟩ | ⟨_, h⟩ <;>
    subst q <;>
    exact Or.inr (by
      unfold StableArity
      simp only [SurfaceQuery.points, SurfaceFirstDescendant.query]
      omega)

/-- Every listed request satisfies the exact dimension equation. -/
theorem canonicalQueries_dimensionCompatible {X : SurfaceTarget} (beta : X.Curve)
    {q : SurfaceQuery X} (hq : q ∈ canonicalQueries X beta) : q.DimensionCompatible := by
  rcases (mem_canonicalQueries beta q).mp hq with h | h | ⟨i, h⟩ | ⟨he, h⟩ <;> subst q
  · exact (SurfaceQuery.dimensionCompatible_points 2 beta _).mpr (by omega)
  · rw [SurfaceQuery.dimensionCompatible_first]
    rfl
  · rw [SurfaceQuery.dimensionCompatible_first]
    rfl
  · rw [SurfaceQuery.dimensionCompatible_first]
    simp only [SurfaceBasisLabel.codimension]
    omega

/-- Natural subtraction does not turn the nominal class-zero point descendant into a query. -/
theorem point_first_dimensionCompatible_iff {X : SurfaceTarget} (beta : X.Curve) :
    (SurfaceFirstDescendant.query 2 beta .point
      (X.effective.energy beta - 1)).DimensionCompatible ↔ beta ≠ 0 := by
  rw [SurfaceQuery.dimensionCompatible_first]
  simp only [SurfaceBasisLabel.codimension]
  constructor
  · intro hd hb
    rw [hb, map_zero] at hd
    omega
  · intro hb
    have he : 0 < X.effective.energy beta := Nat.pos_of_ne_zero
      (fun hz ↦ hb ((X.effective.energy_eq_zero_iff beta).mp hz))
    omega

end SurfaceGenusTwo

namespace SurfaceFirstDescendant
variable {X : SurfaceTarget}

private theorem mem_dimensionTerms {q : SurfaceQuery X}
    {t : ℚ × Multiset (SurfaceQuery X)} (ht : t ∈ dimensionTerms q) :
    t.2 = {q} ∧ q.DimensionCompatible := by
  unfold dimensionTerms at ht
  split_ifs at ht with hd
  · exact ⟨congrArg Prod.snd (RationalTerms.mem_term.mp ht).2, hd⟩
  · exact (Multiset.notMem_zero _ ht).elim

/-- A surviving primary term has exactly the canonical point count at its full class. -/
theorem primaryTerms_canonical_support (beta : X.Curve)
    (m : Multiset (SurfaceBasisLabel X)) {t : ℚ × Multiset (SurfaceQuery X)}
    (ht : t ∈ primaryTerms 2 beta m) :
    t.2 = {SurfaceQuery.points X 2 beta (X.effective.energy beta + 1)} := by
  obtain ⟨_, s, hs, rfl⟩ := RationalTerms.mem_scale.mp ht
  obtain ⟨hm, hd⟩ := mem_dimensionTerms hs
  rw [SurfaceQuery.dimensionCompatible_points] at hd
  have hn : m.count .point = X.effective.energy beta + 1 := by omega
  rw [hm, hn]

private theorem primary_dimension_canonical (beta : X.Curve) (n : ℕ)
    {t : ℚ × Multiset (SurfaceQuery X)}
    (ht : t ∈ dimensionTerms (SurfaceQuery.points X 2 beta n)) :
    t.2 = {SurfaceQuery.points X 2 beta (X.effective.energy beta + 1)} := by
  obtain ⟨hm, hd⟩ := mem_dimensionTerms ht
  rw [SurfaceQuery.dimensionCompatible_points] at hd
  have hn : n = X.effective.energy beta + 1 := by omega
  rw [hm, hn]

/-- String, dilaton and divisor corrections leave only the complete canonical list. -/
theorem terms_canonical_support (beta : X.Curve) (b : SurfaceBasisLabel X)
    (m : Multiset (SurfaceBasisLabel X)) {t : ℚ × Multiset (SurfaceQuery X)}
    (ht : t ∈ terms 2 beta b m) :
    ∃ q ∈ SurfaceGenusTwo.canonicalQueries X beta, t.2 = {q} := by
  unfold terms at ht
  split_ifs at ht with hu hb
  · exact ⟨_, (SurfaceGenusTwo.mem_canonicalQueries beta _).mpr (Or.inl rfl),
      primaryTerms_canonical_support beta _ ht⟩
  · obtain ⟨_, s, hs, rfl⟩ := RationalTerms.mem_scale.mp ht
    exact ⟨_, (SurfaceGenusTwo.mem_canonicalQueries beta _).mpr (Or.inl rfl),
      primaryTerms_canonical_support beta _ (t := s) hs⟩
  · rcases Multiset.mem_add.mp ht with ht | ht
    · obtain ⟨_, s, hs, rfl⟩ := RationalTerms.mem_scale.mp ht
      obtain ⟨hm, hd⟩ := mem_dimensionTerms hs
      rw [SurfaceQuery.dimensionCompatible_first] at hd
      cases b with
      | unit => exact (hb rfl).elim
      | hyperplane =>
        have hn : m.count .point = X.effective.energy beta := by
          simp only [SurfaceBasisLabel.codimension] at hd
          omega
        refine ⟨_, (SurfaceGenusTwo.mem_canonicalQueries beta _).mpr (Or.inr (Or.inl rfl)), ?_⟩
        rw [hm, hn]
      | exceptional i =>
        have hn : m.count .point = X.effective.energy beta := by
          simp only [SurfaceBasisLabel.codimension] at hd
          omega
        refine ⟨_, (SurfaceGenusTwo.mem_canonicalQueries beta _).mpr
          (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))), ?_⟩
        rw [hm, hn]
      | point =>
        have hn : m.count .point = X.effective.energy beta - 1 := by
          simp only [SurfaceBasisLabel.codimension] at hd
          omega
        have he : 0 < X.effective.energy beta := by
          simp only [SurfaceBasisLabel.codimension] at hd
          omega
        refine ⟨_, (SurfaceGenusTwo.mem_canonicalQueries beta _).mpr
          (Or.inr (Or.inr (Or.inr ⟨he, rfl⟩))), ?_⟩
        rw [hm, hn]
    · obtain ⟨_, s, hs, rfl⟩ := RationalTerms.mem_scale.mp ht
      exact ⟨_, (SurfaceGenusTwo.mem_canonicalQueries beta _).mpr (Or.inl rfl),
        primary_dimension_canonical beta _ (t := s) hs⟩

end SurfaceFirstDescendant

namespace SurfacePolynomialReduction
variable {X : SurfaceTarget}

private theorem canonicalPrimaryTerms_primary_support (q : SurfaceAncestorKey X)
    (hg : q.genus = 2) (hp : q.IsPrimary)
    {t : ℚ × Multiset (Variable X)} (ht : t ∈ canonicalPrimaryTerms q) :
    t.2 = {Sum.inr (SurfaceQuery.points X 2 q.beta (X.effective.energy q.beta + 1))} := by
  rw [canonicalPrimaryTerms, if_pos ⟨by omega, hp⟩] at ht
  obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp ht
  rw [hg] at hs
  rw [SurfaceFirstDescendant.primaryTerms_canonical_support _ _ hs,
    Multiset.map_singleton]

/-- Direct low-psi normalization leaves only canonical descendants at the exact input class. -/
theorem directNormalizedTerms_canonical_support (q : SurfaceAncestorKey X)
    (hg : q.genus = 2) (hk : q.totalPsi ≤ 1)
    {t : ℚ × Multiset (Variable X)} (ht : t ∈ directNormalizedTerms q) :
    ∃ c ∈ SurfaceGenusTwo.canonicalQueries X q.beta, t.2 = {Sum.inr c} := by
  unfold directNormalizedTerms at ht
  split_ifs at ht with h
  · obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp ht
    rw [hg] at hs
    obtain ⟨c, hc, hm⟩ := SurfaceFirstDescendant.terms_canonical_support _ _ _ hs
    exact ⟨c, hc, by rw [hm, Multiset.map_singleton]⟩
  · have hz : q.totalPsi = 0 := by
      have hne : q.totalPsi ≠ 1 := fun he ↦ h ⟨by omega, he⟩
      omega
    exact ⟨_, (SurfaceGenusTwo.mem_canonicalQueries q.beta _).mpr (Or.inl rfl),
      canonicalPrimaryTerms_primary_support q hg (q.totalPsi_eq_zero_iff.mp hz) ht⟩

/-- Full low-psi normalization retains canonical descendants at effective subclasses,
including every signed rational-tail correction. -/
theorem normalizedTerms_canonical_support (q : SurfaceAncestorKey X)
    (hg : q.genus = 2) (hk : q.totalPsi ≤ 1)
    {t : ℚ × Multiset (Variable X)} (ht : t ∈ normalizedTerms q) :
    ∃ beta : X.Curve, ∃ c ∈ SurfaceGenusTwo.canonicalQueries X beta,
      t.2 = {Sum.inr c} ∧ ∃ delta : X.Curve, beta + delta = q.beta := by
  unfold normalizedTerms at ht
  split_ifs at ht with h
  · rcases Multiset.mem_add.mp ht with ht | ht
    · obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp ht
      rw [hg] at hs
      obtain ⟨c, hc, hm⟩ := SurfaceFirstDescendant.terms_canonical_support _ _ _ hs
      exact ⟨q.beta, c, hc, by rw [hm, Multiset.map_singleton], 0, add_zero _⟩
    · obtain ⟨split, hs, ht⟩ := Multiset.mem_sum.mp ht
      obtain ⟨b, _, ht⟩ := Multiset.mem_sum.mp ht
      obtain ⟨_, s, hsTerm, rfl⟩ := RationalTerms.mem_scale.mp ht
      let r := SurfaceAncestorKey.ofLabels q.genus (Fin q.orderedInsertions.length)
        q.ordered_stable split.1 0 (Function.update q.orderedLabels (q.onePsiMark h.2) b)
      have hr : r.genus = 2 := hg
      have hp : r.IsPrimary := by
        intro i hi
        change i ∈ (Finset.univ : Finset (Fin q.orderedInsertions.length)).val.map
          (fun j ↦ ⟨Function.update q.orderedLabels (q.onePsiMark h.2) b j, 0⟩) at hi
        obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hi
        rfl
      have hm := canonicalPrimaryTerms_primary_support r hr hp hsTerm
      have hb : split.1 + split.2 = q.beta := by
        rw [X.positiveTailSplittings_eq, X.effective.mem_positiveTailSplittings] at hs
        exact hs.1
      exact ⟨split.1, _, (SurfaceGenusTwo.mem_canonicalQueries split.1 _).mpr (Or.inl rfl),
        hm, split.2, hb⟩
  · have hz : q.totalPsi = 0 := by
      have hne : q.totalPsi ≠ 1 := fun he ↦ h ⟨by omega, he⟩
      omega
    exact ⟨q.beta, _, (SurfaceGenusTwo.mem_canonicalQueries q.beta _).mpr (Or.inl rfl),
      canonicalPrimaryTerms_primary_support q hg (q.totalPsi_eq_zero_iff.mp hz) ht,
      0, add_zero _⟩

end SurfacePolynomialReduction
end AxiomaticGW

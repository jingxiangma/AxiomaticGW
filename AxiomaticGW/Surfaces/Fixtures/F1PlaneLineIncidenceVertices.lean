/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.F1PlaneLineIncidence
public import AxiomaticGW.Surfaces.GenusTwoL24PointCache
public import AxiomaticGW.Surfaces.PointBenchmarkCache
public import AxiomaticGW.Surfaces.GenusTwoFirstCoefficients

/-! # Incidence of the original lower-genus and class-zero divisor terminals

The primary tables through 2E+F, the diagonal pairing, and the first-descendant
normalizer imply the incidence constraint on every component used by the shifted L24 equation.
-/

@[expose] public section
namespace AxiomaticGW.F1PlaneLineIncidence
open SurfaceLowGenusPointCache SurfacePointBenchmarkCache

private theorem cubic_good : ∀ a b c : Label, SurfacePrimary.classicalValue {a,b,c} ≠ 0 →
    Allowed 0 (data {a,b,c}) := by decide +kernel

private theorem rational_classical (m : Multiset Label) (h : SurfacePrimary.classicalValue m ≠ 0) :
    Allowed 0 (data m) := by
  have hc : m.card = 3 := by
    by_contra hn
    exact h (if_neg hn)
  obtain ⟨a,b,c,rfl⟩ := Multiset.card_eq_three.mp hc
  exact cubic_good a b c h

private theorem singleton_good : ∀ a : Label, Allowed 0 (data {a}) := by decide +kernel

private theorem no_factor (b : X.Curve) (a : Label) (m : Multiset Label)
    (ha : a.primaryFactor b = 0) (hn : (m.map (SurfaceBasisLabel.primaryFactor b)).prod ≠ 0) :
    m.count a = 0 := by
  apply Multiset.count_eq_zero_of_notMem
  intro ham
  obtain ⟨m', hm⟩ := Multiset.exists_cons_of_mem ham
  apply hn
  rw [hm, Multiset.map_cons, Multiset.prod_cons, ha, zero_mul]

private theorem with_cases {P : X.Curve → Prop}
    (h : ∀ (e : Fin 3) (d : Fin 2), P (![e.val, d.val] : X.Curve))
    (b : X.Curve) (hb : b ≤ cap) : P b := by
  have he : b 0 ≤ 2 := hb 0
  have hd : b 1 ≤ 1 := hb 1
  have hx : b = ![b 0,b 1] := by funext i; fin_cases i <;> rfl
  rw [hx]
  exact h ⟨_, by omega⟩ ⟨_, by omega⟩

/-- The certified rational primary table and signed divisor intersections have this support. -/
private theorem rational_allowed (b : X.Curve) (m : Multiset Label) (hb : b ≤ cap)
    (hv : rationalPrimary X (genusZero X) b m ≠ 0) : Allowed b (data m) := by
  by_cases hz : b = 0
  · subst b
    exact rational_classical m (by simpa only [rationalPrimary, ite_true] using hv)
  have hc : m.count .point = X.effective.energy b - 1 := by
    by_contra hn
    exact hv (by simp only [rationalPrimary, if_neg hz, if_neg hn])
  have hp : (m.map (SurfaceBasisLabel.primaryFactor b)).prod ≠ 0 := by
    intro hn
    exact hv (by simp only [rationalPrimary, if_neg hz, if_pos hc, hn, ite_true])
  have hn : genusZero X b ≠ 0 := by
    intro hn
    exact hv (by simp only [rationalPrimary, if_neg hz, if_pos hc, if_neg hp, hn, mul_zero])
  revert hz hc hp hn
  apply with_cases _ b hb
  intro e d
  fin_cases e <;> fin_cases d <;> intro hz hc hp hn
  · exact (hz (by decide +kernel)).elim
  · have h : m.count .point = 1 := hc.trans (by decide +kernel)
    exact Or.inr (Or.inr ⟨by decide +kernel, Or.inl (by change m.count .point ≤ 1; omega)⟩)
  · have h : m.count .point = 0 := hc.trans (by decide +kernel)
    exact Or.inr (Or.inl ⟨by decide +kernel, by decide +kernel, h,
      no_factor _ .hyperplane m (by decide +kernel) hp⟩)
  · have h : m.count .point = 2 := hc.trans (by decide +kernel)
    exact Or.inr (Or.inr ⟨by decide +kernel, Or.inr ⟨by decide +kernel, h,
      no_factor _ (.exceptional 0) m (by decide +kernel) hp⟩⟩)
  · exact (hn (by decide +kernel)).elim
  · exact (hn (by decide +kernel)).elim

private theorem elliptic_allowed (b : X.Curve) (m : Multiset Label) (hb : b ≤ cap)
    (hv : ellipticPrimary X (genusOne X) b m ≠ 0) : Allowed b (data m) := by
  by_cases hz : b = 0
  · subst b
    have hc : m.card = 1 := by
      by_contra hn
      exact hv (by
        simp only [ellipticPrimary, ite_true, SurfacePrimary.genusOneZeroValue, if_neg hn])
    obtain ⟨a,rfl⟩ := Multiset.card_eq_one.mp hc
    exact singleton_good a
  · have he : genusOne X b = 0 := by
      apply with_cases _ b hb
      intro e d
      fin_cases e <;> fin_cases d <;> decide +kernel
    exact (hv (by simp only [ellipticPrimary, if_neg hz, he, mul_zero, ite_self])).elim

private theorem rational_primary_zero (q : SurfaceAncestorKey X) (hb : q.beta ≤ cap)
    (hz : ¬ Allowed q.beta (data q.primaryLabels)) :
    rationalPrimary X (genusZero X) q.beta q.primaryLabels = 0 := by
  by_contra h
  exact hz (rational_allowed _ _ hb h)

private theorem elliptic_primary_zero (q : SurfaceAncestorKey X) (hb : q.beta ≤ cap)
    (hz : ¬ Allowed q.beta (data q.primaryLabels)) :
    ellipticPrimary X (genusOne X) q.beta q.primaryLabels = 0 := by
  by_contra h
  exact hz (elliptic_allowed _ _ hb h)

private theorem rational_zero (n : ℕ) (q : SurfaceAncestorKey X) (hb : q.beta ≤ cap)
    (hz : ¬Allowed q.beta (data q.primaryLabels)) : rationalFuel X (genusZero X) n q = 0 := by
  induction n generalizing q with
  | zero => simp only [rationalFuel, rational_primary_zero q hb hz, ite_self]
  | succ n ih =>
    rw [rationalFuel]
    split_ifs with hg hprim
    · exact rational_primary_zero q hb hz
    · unfold SurfaceGenusZero.ancestorStep
      apply List.sum_eq_zero
      intro z h
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp h
      apply mul_eq_zero_of_right
      apply graph_zero
      · intro g S _ h b k a hbound hbad
        exact ih (SurfaceAncestorKey.ofLabels g S h b k a) hbound (by rwa [profile_ofLabels])
      · exact hb
      · rwa [profile_relabel, profile_ordered]
    · rfl

private theorem elliptic_zero (n : ℕ) (q : SurfaceAncestorKey X) (hb : q.beta ≤ cap)
    (hz : ¬Allowed q.beta (data q.primaryLabels)) :
    ellipticFuel X (genusZero X) (genusOne X) n q = 0 := by
  induction n generalizing q with
  | zero => simp only [ellipticFuel, elliptic_primary_zero q hb hz, ite_self]
  | succ n ih =>
    rw [ellipticFuel]
    split_ifs with hg hprim
    · exact elliptic_primary_zero q hb hz
    · unfold ellipticStep
      apply List.sum_eq_zero
      intro z h
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp h
      apply mul_eq_zero_of_right
      apply graph_zero
      · intro g S _ h b k a hbound hbad
        dsimp only
        split_ifs
        · apply rational_zero _ _ hbound
          rwa [profile_ofLabels]
        · apply ih _ hbound
          rwa [profile_ofLabels]
      · exact hb
      · rwa [profile_relabel, profile_ordered]
    · rfl

/-- The genus-zero and genus-one ancestor recursions preserve the primary support. -/
theorem original_vertex_zero (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (b : X.Curve) (k : S → ℕ) (a : S → Label) (hb : b ≤ cap) (hz : ¬Allowed b (profile a)) :
    SurfaceGenusTwo.constantVertexWithPoints X (genusZero X) (genusOne X) g S h b k a = 0 := by
  unfold SurfaceGenusTwo.constantVertexWithPoints
  dsimp only
  split_ifs
  · unfold componentValue
    split_ifs
    · apply rational_zero _ _ hb
      rwa [profile_ofLabels]
    · apply elliptic_zero _ _ hb
      rwa [profile_ofLabels]
  all_goals rfl

open SurfacePolynomialReduction SurfaceGenusTwo

/-- The class-zero genus-two first descendant with one marking in a specified basis state. -/
def requested (b : Label) : Variable X := .inr (SurfaceFirstDescendant.query 2 0 b 0)

private theorem dimension_off (u : SurfaceQuery X) (b : Label) (hu : Sum.inr u ≠ requested b) :
    RationalTerms.coefficient
      (RationalTerms.rename Sum.inr (SurfaceFirstDescendant.dimensionTerms u))
      {requested b} = 0 := by
  unfold SurfaceFirstDescendant.dimensionTerms
  split_ifs
  · rw [RationalTerms.coefficient_rename_term, Multiset.map_singleton]
    exact if_neg (fun h ↦ hu (Multiset.singleton_inj.mp h))
  · rw [RationalTerms.rename_zero, RationalTerms.coefficient_zero]

private theorem primary_off (m : Multiset Label) (b : Label) :
    RationalTerms.coefficient (RationalTerms.rename Sum.inr (SurfaceFirstDescendant.primaryTerms
      2 (0 : X.Curve) m)) {requested b} = 0 := by
  rw [SurfaceFirstDescendant.primaryTerms, RationalTerms.coefficient_rename_scale,
    dimension_off _ _ (SurfaceFirstDescendant.query_ne_points 0 0 b 0 _), mul_zero]

private theorem one_off (a b : Label) (m : Multiset Label) (hm : m ≠ 0) :
    RationalTerms.coefficient (RationalTerms.rename Sum.inr (SurfaceFirstDescendant.terms
      2 (0 : X.Curve) a m)) {requested b} = 0 := by
  unfold SurfaceFirstDescendant.terms
  split_ifs with hu hd
  · exact primary_off _ _
  · rw [RationalTerms.coefficient_rename_scale, primary_off, mul_zero]
  · rw [RationalTerms.coefficient_rename_add, RationalTerms.coefficient_rename_scale,
      RationalTerms.coefficient_rename_scale,
      dimension_off _ _ (SurfaceFirstDescendant.query_ne_points 0 0 b 0 _),
      mul_zero, add_zero]
    by_cases hc : m.count .point = 0
    · obtain ⟨z,hz⟩ := Multiset.exists_mem_of_ne_zero hm
      have hn : z ≠ .point := fun h ↦ by
        subst z
        have := Multiset.count_pos.mpr hz
        omega
      have hf : z.primaryFactor (0 : X.Curve) = 0 := by
        cases z with
        | unit | hyperplane => rfl
        | exceptional i =>
          have hi : i = 0 := Subsingleton.elim _ _
          subst i
          decide +kernel
        | point => exact (hn rfl).elim
      obtain ⟨m',h⟩ := Multiset.exists_cons_of_mem hz
      rw [h, SurfaceFirstDescendant.primaryCoefficient_cons, hf, zero_mul, zero_mul]
    · rw [dimension_off, mul_zero]
      intro h
      have he := congrArg (fun z : SurfaceQuery X ↦ z.insertions.length) (Sum.inr.inj h)
      simp only [SurfaceFirstDescendant.query, List.length_cons, List.length_replicate,
        Nat.zero_add] at he
      omega

private theorem zero_direct (q : SurfaceAncestorKey X) (hg : q.genus = 2) (hb : q.beta = 0)
    (hd : q.DimensionCompatible) (hbad : ¬Allowed 0 (data q.primaryLabels)) (b : Label) :
    RationalTerms.coefficient (directNormalizedTerms q) {requested b} = 0 := by
  unfold directNormalizedTerms
  split_ifs with hh
  · rw [hg,hb]
    apply one_off
    intro hm
    have hi := congrArg (Multiset.map SurfaceInsertion.label)
      (Multiset.cons_erase (q.onePsiInsertion_mem hh.2)).symm
    change q.primaryLabels = _ at hi
    rw [Multiset.map_cons] at hi
    change q.primaryLabels = (q.onePsiInsertion hh.2).label ::ₘ q.onePsiPrimaries hh.2 at hi
    rw [hi, hm] at hbad
    exact hbad (singleton_good _)
  · by_cases hp : q.IsPrimary
    · exact coefficient_canonicalPrimaryTerms_eq_zero_of_not_points q hg hp _
        (fun beta m ↦ SurfaceFirstDescendant.query_ne_points 0 beta b 0 m)
    · simp only [canonicalPrimaryTerms, hp, and_false, ite_false, basicTerms, reduceVariable,
        hd, ite_true, false_and, RationalTerms.coefficient_term, Multiset.singleton_inj,
        requested, reduceCtorEq]

/-- A genus-two class-zero first-descendant column has compatible incidence at every
terminal. Its same-class first-power contribution requires a single marking. -/
theorem coefficient_vertex_zero (b : Label) (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (c : X.Curve) (k : S → ℕ) (a : S → Label) (hc : c ≤ cap) (hz : ¬Allowed c (profile a)) :
    coefficientVertex X (requested b) g S h c k a = 0 := by
  unfold requested
  rw [← firstCoefficientVertex_eq (X := X) 0 b 0]
  unfold firstCoefficientVertex
  dsimp only
  by_cases hg : g = 2
  · subst g
    rw [if_pos rfl]
    split_ifs with hb hd
    · subst c
      apply zero_direct _ rfl rfl hd
      rwa [profile_ofLabels]
    all_goals rfl
  · rw [if_neg hg]
    have hval := original_vertex_zero g S h c k a hc hz
    rw [constantVertexWithPoints_eq X _ _ (genusZero_eq X) (genusOne_eq X)] at hval
    rw [← hval]
    unfold constantVertex vertexTerms residualTerms
    have hq : (SurfaceAncestorKey.ofLabels g S h c k a).genus = g := rfl
    rw [hq]
    split_ifs <;> simp_all only [RationalTerms.coefficient_zero, RationalTerms.coefficient_term,
      ite_true, Multiset.singleton_ne_zero, ite_false]


end AxiomaticGW.F1PlaneLineIncidence

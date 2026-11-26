/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.Incidence
public import AxiomaticGW.Surfaces.LowGenusPointCache
public import AxiomaticGW.Surfaces.PointBenchmarkCache

/-! # Exceptional incidence for the original lower-genus recursion

The rational and elliptic primary tables, plus the dual node pairing, force vanishing away
from a single exceptional support for every descendant component of class `(e,f,0)`
with `e,f ≤ 2`, including the mixed class and both doubled exceptional axes.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoExceptionalIncidence
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
    (h : ∀ (e f : Fin 2), P (![e.val, f.val, 0] : X.Curve))
    (b : X.Curve) (hb : b ≤ cap) : P b := by
  have he : b 0 ≤ 1 := hb 0
  have hf : b 1 ≤ 1 := hb 1
  have hl : b 2 = 0 := Nat.eq_zero_of_le_zero (hb 2)
  have hx : b = ![b 0,b 1,0] := by funext i; fin_cases i <;> first | rfl | exact hl
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
  · have h : m.count .point = 0 := hc.trans (by decide +kernel)
    exact Or.inr (Or.inr (Or.inl ⟨h, by decide +kernel,
      no_factor _ .hyperplane m (by decide +kernel) hp,
      no_factor _ (.exceptional 0) m (by decide +kernel) hp⟩))
  · have h : m.count .point = 0 := hc.trans (by decide +kernel)
    exact Or.inr (Or.inl ⟨h, by decide +kernel,
      no_factor _ .hyperplane m (by decide +kernel) hp,
      no_factor _ (.exceptional 1) m (by decide +kernel) hp⟩)
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

/-- The square of exceptional coefficients up to two, retaining zero plane degree. -/
def doubleCap : X.Curve := ![2,2,0]

private theorem beyond_primitive (b : X.Curve) (hb : b ≤ doubleCap) (h : ¬ b ≤ cap) :
    genusZero X b = 0 ∧ genusOne X b = 0 := by
  have he : b 0 ≤ 2 := hb 0
  have hf : b 1 ≤ 2 := hb 1
  have hl : b 2 = 0 := Nat.eq_zero_of_le_zero (hb 2)
  have hx : b = ![b 0,b 1,0] := by funext i; fin_cases i <;> first | rfl | exact hl
  have finite : ∀ e f : Fin 3, let c : X.Curve := ![e.val, f.val, 0]
      (¬ ∀ j : Fin 3, c j ≤ cap j) → genusZero X c = 0 ∧ genusOne X c = 0 := by decide +kernel
  rw [hx] at h ⊢
  exact finite ⟨_, by omega⟩ ⟨_, by omega⟩ h

private theorem ne_zero_outside (b : X.Curve) (h : ¬ b ≤ cap) : b ≠ 0 := by
  rintro rfl
  exact h (fun _ ↦ Nat.zero_le _)

private theorem rational_primary_zero (q : SurfaceAncestorKey X) (hb : q.beta ≤ doubleCap)
    (hz : ¬ Allowed q.beta (data q.primaryLabels)) :
    rationalPrimary X (genusZero X) q.beta q.primaryLabels = 0 := by
  by_cases h : q.beta ≤ cap
  · by_contra hn
    exact hz (rational_allowed _ _ h hn)
  · simp [rationalPrimary, ne_zero_outside _ h, (beyond_primitive _ hb h).1]

private theorem elliptic_primary_zero (q : SurfaceAncestorKey X) (hb : q.beta ≤ doubleCap)
    (hz : ¬ Allowed q.beta (data q.primaryLabels)) :
    ellipticPrimary X (genusOne X) q.beta q.primaryLabels = 0 := by
  by_cases h : q.beta ≤ cap
  · by_contra hn
    exact hz (elliptic_allowed _ _ h hn)
  · simp [ellipticPrimary, ne_zero_outside _ h, (beyond_primitive _ hb h).2]

private theorem rational_zero (n : ℕ) (q : SurfaceAncestorKey X) (hb : q.beta ≤ doubleCap)
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
      apply graph_zero_of_le
      · intro g S _ h b k a hbound hbad
        exact ih (SurfaceAncestorKey.ofLabels g S h b k a) hbound (by rwa [profile_ofLabels])
      · exact hb
      · rwa [profile_relabel, profile_ordered]
    · rfl

private theorem elliptic_zero (n : ℕ) (q : SurfaceAncestorKey X) (hb : q.beta ≤ doubleCap)
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
      apply graph_zero_of_le
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

/-- Arbitrary cotangent powers and marking multiplicities on rational and elliptic vertices
obey the same necessary incidence constraint as the primary tables. -/
theorem component_zero_of_le_doubleCap (q : SurfaceAncestorKey X) (hb : q.beta ≤ doubleCap)
    (hz : ¬Allowed q.beta (data q.primaryLabels)) :
    SurfaceLowGenusPointCache.componentValue X (genusZero X) (genusOne X) q = 0 := by
  unfold SurfaceLowGenusPointCache.componentValue
  split_ifs
  · exact rational_zero _ _ hb hz
  · exact elliptic_zero _ _ hb hz

/-- Restriction to the original mixed exceptional box. -/
theorem component_zero (q : SurfaceAncestorKey X) (hb : q.beta ≤ cap)
    (hz : ¬Allowed q.beta (data q.primaryLabels)) :
    SurfaceLowGenusPointCache.componentValue X (genusZero X) (genusOne X) q = 0 :=
  component_zero_of_le_doubleCap q (hb.trans (by intro j; fin_cases j <;> decide +kernel)) hz

/-- The same incidence vanishing in the original lower-genus ancestor evaluator. -/
theorem original_component_zero (q : SurfaceAncestorKey X) (hb : q.beta ≤ cap)
    (hz : ¬Allowed q.beta (data q.primaryLabels)) :
    SurfaceGenusOne.componentValue X (SurfaceGenusOne.ancestorValue X) q = 0 := by
  rw [← componentValue_eq X (genusZero X) (genusOne X) (genusZero_eq X) (genusOne_eq X)]
  exact component_zero q hb hz

/-- Every rational or elliptic ancestor in the full mixed exceptional class vanishes,
for arbitrary marked insertions and cotangent powers. -/
theorem mixed_component_zero (q : SurfaceAncestorKey X) (hq : q.beta = cap) :
    SurfaceGenusOne.componentValue X (SurfaceGenusOne.ancestorValue X) q = 0 := by
  apply original_component_zero q (hq.le)
  rw [hq]
  simp [Allowed, cap]

end AxiomaticGW.BlowupTwoExceptionalIncidence

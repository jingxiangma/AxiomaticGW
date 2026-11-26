/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Coefficients.RationalTerms

/-!
# Collecting terms before recursive evaluation

Collection preserves evaluation and removes every zero coefficient. This is
needed when a recursive dependency bound holds after cancellation rather than
for the original list of graph terms. Constants and repeated monomials retain
their complete coefficients.
-/

@[expose] public section

namespace AxiomaticGW.RationalTerms

variable {σ : Type*} [DecidableEq σ]

/-- Merge repeated monomials and omit their zero total coefficients. -/
def collect (p : RationalTerms σ) : RationalTerms σ :=
  (support p).val.bind (fun m ↦ term (coefficient p m) m)

/-- A retained term has its complete nonzero coefficient and an original monomial. -/
theorem mem_collect {p : RationalTerms σ} {t : ℚ × Multiset σ} :
    t ∈ collect p ↔ t.2 ∈ support p ∧ t.1 = coefficient p t.2 ∧ t.1 ≠ 0 := by
  constructor
  · intro ht
    obtain ⟨m, hm, ht⟩ := Multiset.mem_bind.mp ht
    unfold term at ht
    split_ifs at ht with hc
    · exact (Multiset.notMem_zero _ ht).elim
    · rw [Multiset.mem_singleton] at ht
      subst t
      exact ⟨hm, rfl, hc⟩
  · rintro ⟨hm, hc, hn⟩
    apply Multiset.mem_bind.mpr
    refine ⟨t.2, hm, ?_⟩
    rw [term, ← hc, if_neg hn]
    exact Multiset.mem_singleton.mpr (Prod.eta t).symm

/-- Collection preserves evaluation in every commutative rational algebra. -/
theorem eval_collect {A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (p : RationalTerms σ) : eval v (collect p) = eval v p := by
  have h : eval v (collect p) =
      ∑ m ∈ support p, algebraMap ℚ A (coefficient p m) * (m.map v).prod := by
    change ((support p).val.bind (fun m ↦ term (coefficient p m) m) |>.map
      (fun t ↦ algebraMap ℚ A t.1 * (t.2.map v).prod)).sum = _
    rw [Multiset.map_bind, Multiset.sum_bind]
    change ((support p).val.map (fun m ↦ eval v (term (coefficient p m) m))).sum = _
    simp only [eval_term]
    rfl
  rw [h, eval_eq_sum v p (support p) (fun t ht ↦
    Multiset.mem_toFinset.mpr (Multiset.mem_map.mpr ⟨t, ht, rfl⟩))]

/-- Filtering monomials either retains or removes their complete coefficient. -/
theorem coefficient_filter (p : RationalTerms σ) (f : Multiset σ → Prop)
    [DecidablePred f] (m : Multiset σ) :
    coefficient (p.filter (fun t ↦ f t.2)) m = if f m then coefficient p m else 0 := by
  induction p using Multiset.induction_on with
  | empty => simp only [Multiset.filter_zero, coefficient_zero, ite_self]
  | cons t p ih =>
    have hcons (q : RationalTerms σ) :
        coefficient (t ::ₘ q) m = (if t.2 = m then t.1 else 0) + coefficient q m := by
      simp only [coefficient, Multiset.map_cons, Multiset.sum_cons]
    by_cases ht : f t.2
    · rw [Multiset.filter_cons_of_pos p ht, hcons, hcons, ih]
      by_cases hm : t.2 = m
      · have hf : f m := hm ▸ ht
        simp only [if_pos hm, if_pos hf]
      · simp only [if_neg hm, zero_add]
    · rw [Multiset.filter_cons_of_neg p ht, hcons, ih]
      by_cases hm : t.2 = m
      · have hf : ¬f m := hm ▸ ht
        simp only [if_neg hf]
      · simp only [if_neg hm, zero_add]

/-- A monomial absent from the original support has coefficient zero. -/
theorem coefficient_eq_zero_of_not_mem_support (p : RationalTerms σ) (m : Multiset σ)
    (hm : m ∉ support p) : coefficient p m = 0 := by
  apply Multiset.sum_eq_zero
  intro c hc
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hc
  apply if_neg
  intro he
  exact hm (Multiset.mem_toFinset.mpr (Multiset.mem_map.mpr ⟨t, ht, he⟩))

/-- Collection preserves each coefficient, including a cancelled monomial. -/
theorem coefficient_collect (p : RationalTerms σ) (m : Multiset σ) :
    coefficient (collect p) m = coefficient p m := by
  unfold collect coefficient
  rw [Multiset.map_bind, Multiset.sum_bind]
  change ((support p).val.map (fun n ↦ coefficient (term (coefficient p n) n) m)).sum = _
  simp only [coefficient_term]
  change (∑ n ∈ support p, if n = m then coefficient p n else 0) = coefficient p m
  rw [Finset.sum_eq_single m]
  · exact if_pos rfl
  · intro n _ hne
    exact if_neg hne
  · intro hm
    rw [coefficient_eq_zero_of_not_mem_support p m hm, ite_self]

/-- Isolate a finite family of distinct singleton variables without dropping
the constant or any other monomial. -/
theorem eval_isolate_finset {A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (p : RationalTerms σ) (s : Finset σ) :
    eval v p = (∑ x ∈ s, algebraMap ℚ A (coefficient p {x}) * v x) +
      eval v (p.filter (fun t ↦ ∀ x ∈ s, t.2 ≠ {x})) := by
  induction s using Finset.induction_on generalizing p with
  | empty =>
    simp only [Finset.sum_empty, Finset.notMem_empty, false_implies, implies_true,
      Multiset.filter_true, zero_add]
  | @insert x s hx ih =>
    rw [eval_isolate_singleton v p x, ih, Finset.sum_insert hx]
    have hc (y : σ) (hy : y ∈ s) :
        coefficient (p.filter (fun t ↦ t.2 ≠ {x})) {y} = coefficient p {y} := by
      rw [coefficient_filter p (fun m ↦ m ≠ {x}), if_pos]
      intro he
      have hyx := Multiset.singleton_inj.mp he
      exact hx (hyx ▸ hy)
    have hs : (∑ y ∈ s, algebraMap ℚ A
        (coefficient (p.filter (fun t ↦ t.2 ≠ {x})) {y}) * v y) =
        ∑ y ∈ s, algebraMap ℚ A (coefficient p {y}) * v y :=
      Finset.sum_congr rfl (fun y hy ↦ congrArg
        (fun c : ℚ ↦ algebraMap ℚ A c * v y) (hc y hy))
    rw [hs, add_assoc]
    congr 1
    congr 1
    congr 1
    rw [Multiset.filter_filter]
    apply Multiset.filter_congr
    intro t _
    simp only [Finset.mem_insert, forall_eq_or_imp, and_comm]

end AxiomaticGW.RationalTerms

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.BigOperators.Ring.Multiset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Executable rational polynomial terms

Finite multisets of coefficient/monomial pairs provide an executable expansion
format for graph equations. Repeated variables and repeated terms retain their
multiplicities. This is a computation format, interpreted in the existing
`MvPolynomial` ring, rather than a second polynomial algebra with new instances.

The finite coefficient checker compares the union of the two monomial supports.
Its soundness holds for every valuation in every commutative rational algebra.
-/

@[expose] public section

namespace AxiomaticGW

/-- Uncollected rational terms with permutation-invariant monomials. -/
abbrev RationalTerms (σ : Type*) := Multiset (ℚ × Multiset σ)

namespace RationalTerms

variable {σ : Type*}

/-- A term with zero coefficient is omitted at construction time. -/
def term (c : ℚ) (m : Multiset σ) : RationalTerms σ :=
  if c = 0 then 0 else {(c, m)}

/-- Multiplication by an exact rational coefficient. -/
def scale (c : ℚ) (p : RationalTerms σ) : RationalTerms σ :=
  if c = 0 then 0 else p.map (fun t ↦ (c * t.1, t.2))

/-- Distributive multiplication retains every pair of terms. -/
def mul (p q : RationalTerms σ) : RationalTerms σ :=
  p.bind (fun s ↦ q.map (fun t ↦ (s.1 * t.1, s.2 + t.2)))

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- Evaluate terms in any commutative rational algebra. -/
def eval (v : σ → A) (p : RationalTerms σ) : A :=
  (p.map (fun t ↦ algebraMap ℚ A t.1 * (t.2.map v).prod)).sum

theorem eval_zero (v : σ → A) : eval v (0 : RationalTerms σ) = 0 := rfl

/-- Evaluation only depends on the variables occurring in the supplied terms. -/
theorem eval_congr (v w : σ → A) (p : RationalTerms σ)
    (h : ∀ t ∈ p, ∀ x ∈ t.2, v x = w x) : eval v p = eval w p := by
  unfold eval
  congr 1
  apply Multiset.map_congr rfl
  intro t ht
  congr 1
  congr 1
  exact Multiset.map_congr rfl (h t ht)

theorem eval_add (v : σ → A) (p q : RationalTerms σ) :
    eval v (p + q) = eval v p + eval v q := by
  simp only [eval, Multiset.map_add, Multiset.sum_add]

/-- The additive interpretation also commutes with finite graph sums. -/
def evalAddHom (v : σ → A) : RationalTerms σ →+ A where
  toFun := eval v
  map_zero' := eval_zero v
  map_add' := eval_add v

theorem eval_sum {ι : Type*} (v : σ → A) (s : Finset ι) (p : ι → RationalTerms σ) :
    eval v (∑ i ∈ s, p i) = ∑ i ∈ s, eval v (p i) :=
  map_sum (evalAddHom v) p s

theorem eval_list_sum (v : σ → A) (p : List (RationalTerms σ)) :
    eval v p.sum = (p.map (eval v)).sum := map_list_sum (evalAddHom v) p

theorem eval_term (v : σ → A) (c : ℚ) (m : Multiset σ) :
    eval v (term c m) = algebraMap ℚ A c * (m.map v).prod := by
  unfold term
  split_ifs with hc
  · rw [eval_zero, hc, map_zero, zero_mul]
  · simp only [eval, Multiset.map_singleton, Multiset.sum_singleton]

theorem eval_scale (v : σ → A) (c : ℚ) (p : RationalTerms σ) :
    eval v (scale c p) = algebraMap ℚ A c * eval v p := by
  unfold scale
  split_ifs with hc
  · rw [eval_zero, hc, map_zero, zero_mul]
  · simp only [eval, Multiset.map_map, Function.comp_def, map_mul, mul_assoc,
      Multiset.sum_map_mul_left]

theorem eval_mul (v : σ → A) (p q : RationalTerms σ) :
    eval v (mul p q) = eval v p * eval v q := by
  simp only [eval, mul, Multiset.map_bind, Multiset.sum_bind, Multiset.map_map,
    Function.comp_def, map_mul, Multiset.map_add, Multiset.prod_add]
  have h (s t : ℚ × Multiset σ) :
      algebraMap ℚ A s.1 * algebraMap ℚ A t.1 *
        ((s.2.map v).prod * (t.2.map v).prod) =
      (algebraMap ℚ A s.1 * (s.2.map v).prod) *
        (algebraMap ℚ A t.1 * (t.2.map v).prod) := mul_mul_mul_comm _ _ _ _
  simp only [h, Multiset.sum_map_mul_left, Multiset.sum_map_mul_right]

/-- The ordinary mathlib polynomial represented by the finite terms. -/
noncomputable def polynomial (p : RationalTerms σ) : MvPolynomial σ ℚ :=
  eval MvPolynomial.X p

theorem aeval_polynomial (v : σ → A) (p : RationalTerms σ) :
    MvPolynomial.aeval v (polynomial p) = eval v p := by
  simp only [polynomial, eval, map_multiset_sum, Multiset.map_map, Function.comp_def,
    map_mul, AlgHom.commutes, map_multiset_prod, MvPolynomial.aeval_X]

section Coefficients

variable [DecidableEq σ]

/-- All monomials present in the input, including cancelled coefficients. -/
def support (p : RationalTerms σ) : Finset (Multiset σ) := (p.map Prod.snd).toFinset

/-- Exact collected coefficient of one monomial. -/
def coefficient (p : RationalTerms σ) (m : Multiset σ) : ℚ :=
  (p.map (fun t ↦ if t.2 = m then t.1 else 0)).sum

theorem coefficient_zero (m : Multiset σ) : coefficient (0 : RationalTerms σ) m = 0 := rfl

theorem coefficient_term (c : ℚ) (m n : Multiset σ) :
    coefficient (term c m) n = if m = n then c else 0 := by
  by_cases hc : c = 0
  · simp only [hc, term, ite_true, coefficient_zero, ite_self]
  · rw [term, if_neg hc]
    simp only [coefficient, Multiset.map_singleton, Multiset.sum_singleton]

/-- Collection commutes with concatenation, including cancellation. -/
theorem coefficient_add (p q : RationalTerms σ) (m : Multiset σ) :
    coefficient (p + q) m = coefficient p m + coefficient q m := by
  simp only [coefficient, Multiset.map_add, Multiset.sum_add]

/-- A fixed monomial coefficient is an additive map on uncollected terms. -/
def coefficientAddHom (m : Multiset σ) : RationalTerms σ →+ ℚ where
  toFun p := coefficient p m
  map_zero' := coefficient_zero m
  map_add' p q := coefficient_add p q m

theorem coefficient_sum {ι : Type*} (s : Finset ι) (p : ι → RationalTerms σ)
    (m : Multiset σ) : coefficient (∑ i ∈ s, p i) m = ∑ i ∈ s, coefficient (p i) m :=
  map_sum (coefficientAddHom m) p s

theorem coefficient_list_sum (ps : List (RationalTerms σ)) (m : Multiset σ) :
    coefficient ps.sum m = (ps.map (fun p ↦ coefficient p m)).sum :=
  map_list_sum (coefficientAddHom m) ps

theorem coefficient_scale (c : ℚ) (p : RationalTerms σ) (m : Multiset σ) :
    coefficient (scale c p) m = c * coefficient p m := by
  unfold scale
  split_ifs with hc
  · rw [coefficient_zero, hc, zero_mul]
  · simp only [coefficient, Multiset.map_map, Function.comp_def]
    rw [← Multiset.sum_map_mul_left]
    congr 1
    apply Multiset.map_congr rfl
    intro t _
    split_ifs <;> simp only [mul_zero]

/-- A product has an empty monomial precisely from its two empty factors. -/
theorem coefficient_mul_zero (p q : RationalTerms σ) :
    coefficient (mul p q) 0 = coefficient p 0 * coefficient q 0 := by
  have hpair (s t : ℚ × Multiset σ) :
      (if s.2 + t.2 = 0 then s.1 * t.1 else 0) =
        (if s.2 = 0 then s.1 else 0) * (if t.2 = 0 then t.1 else 0) := by
    by_cases hs : s.2 = 0
    · simp only [hs, zero_add, ite_true]
      split_ifs <;> simp only [mul_zero]
    · have hne : s.2 + t.2 ≠ 0 := by
        intro he
        have hcard := congrArg Multiset.card he
        simp only [Multiset.card_add, Multiset.card_zero] at hcard
        exact hs (Multiset.card_eq_zero.mp (Nat.eq_zero_of_add_eq_zero_right hcard))
      simp only [if_neg hne, if_neg hs, zero_mul]
  simp only [coefficient, mul, Multiset.map_bind, Multiset.sum_bind,
    Multiset.map_map, Function.comp_def, hpair, Multiset.sum_map_mul_left,
    Multiset.sum_map_mul_right]

/-- Only empty/singleton factors can contribute to a singleton in a product. -/
theorem coefficient_mul_singleton (p q : RationalTerms σ) (x : σ) :
    coefficient (mul p q) {x} =
      coefficient p 0 * coefficient q {x} + coefficient p {x} * coefficient q 0 := by
  have hpair (s t : ℚ × Multiset σ) :
      (if s.2 + t.2 = {x} then s.1 * t.1 else 0) =
        (if s.2 = 0 then s.1 else 0) * (if t.2 = {x} then t.1 else 0) +
        (if s.2 = {x} then s.1 else 0) * (if t.2 = 0 then t.1 else 0) := by
    by_cases hs : s.2 = 0
    · simp only [hs, zero_add, if_true]
      have hne : (0 : Multiset σ) ≠ {x} := by
        intro he
        have hcard := congrArg Multiset.card he
        simp only [Multiset.card_zero, Multiset.card_singleton] at hcard
        exact Nat.zero_ne_one hcard
      simp only [if_neg hne, zero_mul, add_zero]
      split_ifs <;> simp only [mul_zero]
    · by_cases ht : t.2 = 0
      · simp only [ht, add_zero, if_neg hs, zero_mul, zero_add, if_true]
        split_ifs <;> simp only [zero_mul]
      · have hne : s.2 + t.2 ≠ {x} := by
          intro he
          have hcard := congrArg Multiset.card he
          have hspos : 0 < s.2.card := Nat.pos_of_ne_zero
            (fun h ↦ hs (Multiset.card_eq_zero.mp h))
          have htpos : 0 < t.2.card := Nat.pos_of_ne_zero
            (fun h ↦ ht (Multiset.card_eq_zero.mp h))
          rw [Multiset.card_add, Multiset.card_singleton] at hcard
          omega
        simp only [if_neg hne, if_neg hs, if_neg ht, zero_mul, mul_zero, add_zero]
  simp only [coefficient, mul, Multiset.map_bind, Multiset.sum_bind,
    Multiset.map_map, Function.comp_def, hpair, Multiset.sum_map_add,
    Multiset.sum_map_mul_left, Multiset.sum_map_mul_right]

/-- Isolate the complete coefficient of a singleton, retaining every other term.
This identity itself does not assert any decrease of the remaining variables. -/
theorem eval_isolate_singleton (v : σ → A) (p : RationalTerms σ) (x : σ) :
    eval v p = algebraMap ℚ A (coefficient p {x}) * v x +
      eval v (p.filter (fun t ↦ t.2 ≠ {x})) := by
  induction p using Multiset.induction_on with
  | empty =>
    simp only [eval_zero, coefficient, Multiset.map_zero, Multiset.sum_zero,
      map_zero, zero_mul, Multiset.filter_zero, add_zero]
  | @cons t p ih =>
    obtain ⟨c, m⟩ := t
    have hev : eval v ((c, m) ::ₘ p) =
        algebraMap ℚ A c * (m.map v).prod + eval v p := by
      simp only [eval, Multiset.map_cons, Multiset.sum_cons]
    have hcoeff : coefficient ((c, m) ::ₘ p) {x} =
        (if m = {x} then c else 0) + coefficient p {x} := by
      simp only [coefficient, Multiset.map_cons, Multiset.sum_cons]
    rw [hev, hcoeff, ih]
    by_cases hm : m = {x}
    · simp only [hm, map_add, Multiset.map_singleton,
        Multiset.prod_singleton, Multiset.filter_cons, ne_eq, not_true_eq_false,
        if_false, if_true, zero_add, add_mul, add_assoc]
    · rw [if_neg hm, zero_add,
        Multiset.filter_cons_of_pos p (show (c, m).2 ≠ {x} from hm)]
      simp only [eval, Multiset.map_cons, Multiset.sum_cons]
      exact add_left_comm _ _ _

/-- Collect over any finite set containing all original monomials. -/
theorem eval_eq_sum (v : σ → A) (p : RationalTerms σ) (s : Finset (Multiset σ))
    (hs : ∀ t ∈ p, t.2 ∈ s) :
    eval v p = ∑ m ∈ s, algebraMap ℚ A (coefficient p m) * (m.map v).prod := by
  simp only [coefficient, map_multiset_sum, Multiset.map_map, Function.comp_def,
    apply_ite, map_zero, ← Multiset.sum_map_mul_right]
  rw [← Multiset.sum_map_sum]
  unfold eval
  congr 1
  apply Multiset.map_congr rfl
  intro t ht
  rw [Finset.sum_eq_single t.2]
  · rw [if_pos rfl]
  · intro m _ hne
    rw [if_neg (Ne.symm hne), zero_mul]
  · exact fun hnot ↦ (hnot (hs t ht)).elim

/-- Finite exact equality check, bound to both complete inputs. -/
def Equivalent (p q : RationalTerms σ) : Prop :=
  ∀ m ∈ support p ∪ support q, coefficient p m = coefficient q m

/-- Boolean comparison avoids dependent membership proofs during kernel replay. -/
def checkEquivalent (p q : RationalTerms σ) : Bool :=
  decide (((support p ∪ support q).filter
    (fun m ↦ coefficient p m ≠ coefficient q m)).card = 0)

theorem checkEquivalent_eq_true (p q : RationalTerms σ) :
    checkEquivalent p q = true ↔ Equivalent p q := by
  simp only [checkEquivalent, decide_eq_true_eq, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff, ne_eq, not_not, Equivalent]

instance (p q : RationalTerms σ) : Decidable (Equivalent p q) :=
  decidable_of_iff (checkEquivalent p q = true) (checkEquivalent_eq_true p q)

/-- Accepted finite coefficient equality preserves every algebraic valuation. -/
theorem eval_eq_of_equivalent (v : σ → A) (p q : RationalTerms σ)
    (h : Equivalent p q) : eval v p = eval v q := by
  have hp : ∀ t ∈ p, t.2 ∈ support p ∪ support q := by
    intro t ht
    exact Finset.mem_union_left _ (Multiset.mem_toFinset.mpr
      (Multiset.mem_map.mpr ⟨t, ht, rfl⟩))
  have hq : ∀ t ∈ q, t.2 ∈ support p ∪ support q := by
    intro t ht
    exact Finset.mem_union_right _ (Multiset.mem_toFinset.mpr
      (Multiset.mem_map.mpr ⟨t, ht, rfl⟩))
  rw [eval_eq_sum v p _ hp, eval_eq_sum v q _ hq]
  exact Finset.sum_congr rfl (fun m hm ↦ by rw [h m hm])

theorem polynomial_eq_of_equivalent (p q : RationalTerms σ) (h : Equivalent p q) :
    polynomial p = polynomial q := eval_eq_of_equivalent MvPolynomial.X p q h

end Coefficients

end RationalTerms

end AxiomaticGW

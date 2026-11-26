/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Coefficients.AffineSubstitution

/-!
# Singleton coefficients after affine substitution

These formulas compute coefficients of the existing `affineSubstitute`
operation. Its interpretation as polynomial substitution still requires
affine support. In particular, the product rule below requires that at least
one monomial in each pair of factors be constant; it does not apply an
affine substitution to a nonlinear product as if it were a ring map.
-/

@[expose] public section

namespace AxiomaticGW.RationalTerms

variable {σ τ : Type*} [DecidableEq τ]

theorem coefficient_bind {ι : Type*} (s : Multiset ι) (f : ι → RationalTerms τ)
    (m : Multiset τ) :
    coefficient (s.bind f) m = (s.map (fun i ↦ coefficient (f i) m)).sum := by
  simp only [coefficient, Multiset.map_bind, Multiset.sum_bind]

/-- Constant input terms do not contribute to a singleton coefficient. -/
theorem coefficient_affineSubstitute_singleton (f : σ → RationalTerms τ)
    (p : RationalTerms σ) (v : τ) :
    coefficient (affineSubstitute f p) {v} =
      (p.map (fun t ↦ t.1 * (t.2.map (fun q ↦ coefficient (f q) {v})).sum)).sum := by
  rw [affineSubstitute, coefficient_bind]
  congr 1
  apply Multiset.map_congr rfl
  intro t _
  by_cases hz : t.2.card = 0
  · have hm := Multiset.card_eq_zero.mp hz
    simp only [hm, Multiset.card_zero, if_true, coefficient_term,
      Multiset.zero_ne_singleton, if_false, Multiset.map_zero, Multiset.sum_zero, mul_zero]
  · simp only [if_neg hz, coefficient_scale, coefficient_bind]

theorem coefficient_affineSubstitute_zero (f : σ → RationalTerms τ) (v : τ) :
    coefficient (affineSubstitute f 0) {v} = 0 := rfl

theorem coefficient_affineSubstitute_bind {ι : Type*} (f : σ → RationalTerms τ)
    (s : Multiset ι) (p : ι → RationalTerms σ) (v : τ) :
    coefficient (affineSubstitute f (s.bind p)) {v} =
      (s.map (fun i ↦ coefficient (affineSubstitute f (p i)) {v})).sum := by
  simp only [coefficient_affineSubstitute_singleton, Multiset.map_bind, Multiset.sum_bind]

theorem coefficient_affineSubstitute_add (f : σ → RationalTerms τ)
    (p q : RationalTerms σ) (v : τ) :
    coefficient (affineSubstitute f (p + q)) {v} =
      coefficient (affineSubstitute f p) {v} +
        coefficient (affineSubstitute f q) {v} := by
  simp only [coefficient_affineSubstitute_singleton, Multiset.map_add, Multiset.sum_add]

/-- Singleton collection after the specified affine substitution is additive. -/
def affineCoefficientAddHom (f : σ → RationalTerms τ) (v : τ) : RationalTerms σ →+ ℚ where
  toFun p := coefficient (affineSubstitute f p) {v}
  map_zero' := coefficient_affineSubstitute_zero f v
  map_add' p q := coefficient_affineSubstitute_add f p q v

theorem coefficient_affineSubstitute_sum {ι : Type*} (f : σ → RationalTerms τ)
    (s : Finset ι) (p : ι → RationalTerms σ) (v : τ) :
    coefficient (affineSubstitute f (∑ i ∈ s, p i)) {v} =
      ∑ i ∈ s, coefficient (affineSubstitute f (p i)) {v} :=
  map_sum (affineCoefficientAddHom f v) p s

theorem coefficient_affineSubstitute_scale (f : σ → RationalTerms τ)
    (c : ℚ) (p : RationalTerms σ) (v : τ) :
    coefficient (affineSubstitute f (scale c p)) {v} =
      c * coefficient (affineSubstitute f p) {v} := by
  unfold scale
  split_ifs with hc
  · rw [coefficient_affineSubstitute_zero, hc, zero_mul]
  · simp only [coefficient_affineSubstitute_singleton, Multiset.map_map,
      Function.comp_def, mul_assoc, Multiset.sum_map_mul_left]

theorem coefficient_affineSubstitute_term (f : σ → RationalTerms τ)
    (c : ℚ) (m : Multiset σ) (v : τ) :
    coefficient (affineSubstitute f (term c m)) {v} =
      c * (m.map (fun q ↦ coefficient (f q) {v})).sum := by
  unfold term
  split_ifs with hc
  · rw [coefficient_affineSubstitute_zero, hc, zero_mul]
  · simp only [coefficient_affineSubstitute_singleton, Multiset.map_singleton,
      Multiset.sum_singleton]

/-- The linear product rule is valid when every pair of terms has a constant
factor. This hypothesis holds for residual genus-two graph expansions. -/
theorem coefficient_affineSubstitute_mul [DecidableEq σ] (f : σ → RationalTerms τ)
    (p q : RationalTerms σ) (v : τ)
    (hpq : ∀ s ∈ p, ∀ t ∈ q, s.2 = 0 ∨ t.2 = 0) :
    coefficient (affineSubstitute f (mul p q)) {v} =
      coefficient p 0 * coefficient (affineSubstitute f q) {v} +
        coefficient (affineSubstitute f p) {v} * coefficient q 0 := by
  rw [coefficient_affineSubstitute_singleton]
  simp only [mul, Multiset.map_bind, Multiset.sum_bind, Multiset.map_map,
    Function.comp_def]
  have hpair (s : ℚ × Multiset σ) (hs : s ∈ p) (t : ℚ × Multiset σ) (ht : t ∈ q) :
      s.1 * t.1 * ((s.2 + t.2).map (fun u ↦ coefficient (f u) {v})).sum =
        (if s.2 = 0 then s.1 else 0) *
            (t.1 * (t.2.map (fun u ↦ coefficient (f u) {v})).sum) +
          (s.1 * (s.2.map (fun u ↦ coefficient (f u) {v})).sum) *
            (if t.2 = 0 then t.1 else 0) := by
    rcases hpq s hs t ht with hz | hz
    · simp only [hz, zero_add, ite_true, Multiset.map_zero, Multiset.sum_zero,
        mul_zero, zero_mul, add_zero, mul_assoc]
    · simp only [hz, add_zero, ite_true, Multiset.map_zero, Multiset.sum_zero,
        mul_zero, zero_add]
      exact mul_right_comm _ _ _
  calc
    _ = (p.map (fun s ↦ (q.map (fun t ↦
        (if s.2 = 0 then s.1 else 0) *
            (t.1 * (t.2.map (fun u ↦ coefficient (f u) {v})).sum) +
          (s.1 * (s.2.map (fun u ↦ coefficient (f u) {v})).sum) *
            (if t.2 = 0 then t.1 else 0))).sum)).sum := by
      congr 1
      apply Multiset.map_congr rfl
      intro s hs
      congr 1
      exact Multiset.map_congr rfl (hpair s hs)
    _ = _ := by
      rw [coefficient_affineSubstitute_singleton, coefficient_affineSubstitute_singleton]
      simp only [coefficient, Multiset.sum_map_add, Multiset.sum_map_mul_left,
        Multiset.sum_map_mul_right]

end AxiomaticGW.RationalTerms

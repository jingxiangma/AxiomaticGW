/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Coefficients.WeightedCurveClass

/-!
# Splitting an effective remainder

If a summand vanishes unless its first curve class contains a fixed effective
class, translate that class out of the ordered splitting. Only the effective
remainder is enumerated. The statement uses every coordinate, not just energy.
-/

@[expose] public section

namespace AxiomaticGW.WeightedCurveClass

/-- Ordered splittings are invariant under exchanging their two components. -/
theorem sum_splittings_swap {n : ℕ} {A : Type*} [AddCommMonoid A]
    (beta : Fin n → ℕ) (f : (Fin n → ℕ) × (Fin n → ℕ) → A) :
    (∑ p ∈ splittings beta, f p) = ∑ p ∈ splittings beta, f p.swap := by
  apply Finset.sum_equiv (Equiv.prodComm _ _)
  · intro p
    rcases p with ⟨a, b⟩
    simp only [mem_splittings, Equiv.prodComm_apply, Prod.swap, add_comm]
  · intro p _
    rfl

/-- Translate a supported first component out of an ordered full-class sum. -/
theorem sum_splittings_add_left {n : ℕ} {A : Type*} [AddCommMonoid A]
    (beta delta : Fin n → ℕ) (f : (Fin n → ℕ) × (Fin n → ℕ) → A)
    (hf : ∀ a b, ¬beta ≤ a → f (a, b) = 0) :
    (∑ p ∈ splittings (beta + delta), f p) =
      ∑ p ∈ splittings delta, f (beta + p.1, p.2) := by
  let shift (p : (Fin n → ℕ) × (Fin n → ℕ)) := (beta + p.1, p.2)
  have hsub : (splittings delta).image shift ⊆ splittings (beta + delta) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    rw [mem_splittings] at hq ⊢
    exact (add_assoc beta q.1 q.2).trans (congrArg (beta + ·) hq)
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_image
    intro p _ q _ he
    change (beta + p.1, p.2) = (beta + q.1, q.2) at he
    apply Prod.ext
    · have he' := congrArg Prod.fst he
      exact add_left_cancel he'
    · have he' := congrArg Prod.snd he
      exact he'
  · intro p hp hnot
    apply hf p.1 p.2
    intro hle
    apply hnot
    refine Finset.mem_image.mpr ⟨(p.1 - beta, p.2), ?_, ?_⟩
    · rw [mem_splittings]
      have he := (mem_splittings (beta + delta) p.1 p.2).mp hp
      funext i
      have hi := congrFun he i
      have hli := hle i
      change beta i ≤ p.1 i at hli
      change p.1 i + p.2 i = beta i + delta i at hi
      change p.1 i - beta i + p.2 i = delta i
      omega
    · change (beta + (p.1 - beta), p.2) = p
      apply Prod.ext
      · funext i
        have hi := hle i
        change beta i ≤ p.1 i at hi
        change beta i + (p.1 i - beta i) = p.1 i
        omega
      · rfl

/-- The same effective-remainder translation for a supported second component. -/
theorem sum_splittings_add_right {n : ℕ} {A : Type*} [AddCommMonoid A]
    (beta delta : Fin n → ℕ) (f : (Fin n → ℕ) × (Fin n → ℕ) → A)
    (hf : ∀ a b, ¬beta ≤ b → f (a, b) = 0) :
    (∑ p ∈ splittings (beta + delta), f p) =
      ∑ p ∈ splittings delta, f (p.1, beta + p.2) := by
  rw [sum_splittings_swap (beta + delta) f,
    sum_splittings_add_left beta delta (fun p ↦ f p.swap)
      (fun a b h ↦ hf b a h)]
  exact (sum_splittings_swap delta (fun p ↦ f (p.1, beta + p.2))).symm

end AxiomaticGW.WeightedCurveClass

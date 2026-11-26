/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.EquivariantCoefficients

/-! # Arithmetic of equivariant functions regular at the ordinary specialization -/

@[expose] public section
namespace AxiomaticGW.GKM.EquivariantCoefficients

/-- Regular summands specialize over their common product denominator. -/
theorem Specializes.add {f g : Coefficient} {a b : ℚ} (hf : Specializes f a)
    (hg : Specializes g b) : Specializes (f + g) (a + b) := by
  obtain ⟨n, d, hd, rfl, rfl⟩ := hf
  obtain ⟨n', d', hd', rfl, rfl⟩ := hg
  refine ⟨n*d' + d*n', d*d', map_mul atZero d d' ▸ mul_ne_zero hd hd', ?_, ?_⟩
  · simp only [map_add, map_mul]
    exact (div_add_div _ _ (embed_ne_zero_of_atZero d hd) (embed_ne_zero_of_atZero d' hd')).symm
  · simp only [map_add, map_mul]
    exact (div_add_div _ _ hd hd').symm

/-- Products of regular values specialize multiplicatively. -/
theorem Specializes.mul {f g : Coefficient} {a b : ℚ} (hf : Specializes f a)
    (hg : Specializes g b) : Specializes (f * g) (a * b) := by
  obtain ⟨n, d, hd, rfl, rfl⟩ := hf
  obtain ⟨n', d', hd', rfl, rfl⟩ := hg
  refine ⟨n*n', d*d', map_mul atZero d d' ▸ mul_ne_zero hd hd', ?_, ?_⟩
  all_goals simp only [map_mul, div_mul_div_comm]

/-- Every nonnegative power of a regular function specializes to the same power of its value. -/
theorem Specializes.pow {f : Coefficient} {a : ℚ} (hf : Specializes f a) (n : ℕ) :
    Specializes (f^n) (a^n) := by
  induction n with
  | zero => simpa only [pow_zero, map_one] using specializes_of_eq_polynomial 1 rfl
  | succ n ih => simpa only [pow_succ] using ih.mul hf

/-- A finite sum specializes when every complete coefficient in the sum is regular. -/
theorem Specializes.sum {ι : Type*} (s : Finset ι) (f : ι → Coefficient) (a : ι → ℚ)
    (h : ∀ i ∈ s, Specializes (f i) (a i)) : Specializes (∑ i ∈ s, f i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, map_zero] using specializes_of_eq_polynomial 0 rfl
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj)))

end AxiomaticGW.GKM.EquivariantCoefficients

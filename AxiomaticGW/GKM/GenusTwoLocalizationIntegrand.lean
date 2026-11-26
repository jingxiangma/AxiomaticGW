/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.GenusTwoLocalizationClass

/-! # Hodge polynomials and inverse flag factors before integration

The cotangent class is nilpotent in the rational stable-curve ring. Thus the
flag denominator has a finite inverse over the character field. Multiplying
these inverses with the two Hodge factors and ordered descendants recovers
the complete vertex expansion.
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoLocalizationClass
open TensorProduct
noncomputable section

variable {C : StableCurveCohomology ℚ} {K : Type*} [Field K] [CharZero K]

/-- The first power beyond the dimension vanishes at each marked point. -/
theorem psi_nilpotent (P : PsiClasses C) (n : ℕ) (s : Fin n) :
    (P.psi 2 (Fin n) (stable n) s) ^ (3+n+1) = 0 := by
  apply C.eq_zero_of_dimension_lt 2 _ (stable n) (3+n+1)
  · simpa only [smul_eq_mul, mul_one] using
      SetLike.pow_mem_graded (3+n+1) (P.psi_degree 2 (Fin n) (stable n) s)
  · simp only [StableArity.dimension, Fintype.card_fin]
    omega

/-- Truncated reciprocal of the character minus a cotangent class. -/
def flagSeries {A : Type*} [CommRing A] [Algebra ℚ A] (w : K) (ψ : A) (d : ℕ) : K ⊗[ℚ] A :=
  ∑ k ∈ Finset.range d, (w⁻¹^(k+1)) ⊗ₜ[ℚ] (ψ^k)

/-- The exact remainder of the truncated geometric series in the tensor product. -/
theorem flagSeries_remainder {A : Type*} [CommRing A] [Algebra ℚ A] (w : K) (hw : w ≠ 0)
    (ψ : A) (d : ℕ) :
    (w ⊗ₜ[ℚ] (1 : A) - (1 : K) ⊗ₜ[ℚ] ψ) * flagSeries w ψ d =
      1 - ((w⁻¹^d) ⊗ₜ[ℚ] (ψ^d)) := by
  induction d with
  | zero => simp only [flagSeries, Finset.range_zero, Finset.sum_empty, mul_zero, pow_zero,
      ← Algebra.TensorProduct.one_def, sub_self]
  | succ d ih =>
    change _ * (∑ k ∈ Finset.range (d+1), (w⁻¹^(k+1)) ⊗ₜ[ℚ] (ψ^k)) = _
    rw [Finset.sum_range_succ, mul_add, ← flagSeries, ih, sub_mul]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [show w * w⁻¹^(d+1) = w⁻¹^d by rw [pow_succ', mul_inv_cancel_left₀ hw], ← pow_succ']
    abel

/-- A flag at a stable genus-two vertex has a genuine inverse at nonzero character. -/
theorem flag_inverse (P : PsiClasses C) (n : ℕ) (s : Fin n) (w : K) (hw : w ≠ 0) :
    let ψ := P.psi 2 (Fin n) (stable n) s
    (w ⊗ₜ[ℚ] (1 : C.H 2 (Fin n)) - (1 : K) ⊗ₜ[ℚ] ψ) * flagSeries w ψ (3+n+1) = 1 := by
  dsimp only
  rw [flagSeries_remainder w hw, psi_nilpotent, TensorProduct.tmul_zero, sub_zero]

/-- The signed Hodge Euler polynomial divided by its tangent weight. -/
def hodgeFactor (D : HodgeClasses C) (n : ℕ) (u : K) : K ⊗[ℚ] (C.H 2 (Fin n)) :=
  ∑ i : Fin 3, ((-1 : K)^i.val * u^((1 : ℤ)-i.val)) ⊗ₜ[ℚ] (D.coefficient n i : C.H 2 (Fin n))

/-- In rank two the normalized Hodge factor is the character minus λ₁ plus λ₂/character. -/
theorem hodgeFactor_eq (D : HodgeClasses C) (n : ℕ) (u : K) :
    hodgeFactor D n u = u ⊗ₜ[ℚ] (1 : C.H 2 (Fin n)) -
      (1 : K) ⊗ₜ[ℚ] (D.first n : C.H 2 (Fin n)) + u⁻¹ ⊗ₜ[ℚ] (D.second n : C.H 2 (Fin n)) := by
  rw [hodgeFactor, Fin.sum_univ_three]
  norm_num [HodgeClasses.coefficient, TensorProduct.neg_tmul, sub_eq_add_neg]

/-- Ordered marked descendants, excluding the flags, in the original source cohomology. -/
def markedDescendants (P : PsiClasses C) (m : List ℕ) (f : ℕ) : C.H 2 (Fin (m.length + f)) :=
  ∏ t : Fin m.length, P.psi 2 _ (stable _) (Fin.castAdd f t) ^ m.get t

private theorem monomial_split (P : PsiClasses C) (m : List ℕ) {f : ℕ} (k : Fin f → ℕ) :
    P.monomial 2 _ (stable _) (markedPowers m k) = markedDescendants P m f *
      ∏ t, P.psi 2 _ (stable _) (Fin.natAdd m.length t) ^ k t := by
  rw [PsiClasses.monomial, Fin.prod_univ_add, markedDescendants]
  congr 1
  · apply Finset.prod_congr rfl
    intro t _
    simp only [markedPowers, Function.comp_apply, List.get_eq_getElem, Fin.val_cast,
      Fin.val_castAdd, List.getElem_append_left t.isLt]
  · apply Finset.prod_congr rfl
    intro t _
    simp only [markedPowers, Function.comp_apply, List.get_eq_getElem, Fin.val_cast,
      Fin.val_natAdd, List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem_ofFn]

private theorem tensor_product {A : Type*} [CommRing A] [Algebra ℚ A] {f : ℕ}
    (a : Fin f → K) (b : Fin f → A) (s : Finset (Fin f)) :
    ∏ t ∈ s, (a t ⊗ₜ[ℚ] b t) = (∏ t ∈ s, a t) ⊗ₜ[ℚ] (∏ t ∈ s, b t) := by
  induction s using Finset.induction with
  | empty => simp only [Finset.prod_empty, Algebra.TensorProduct.one_def]
  | insert t s ht ih => rw [Finset.prod_insert ht, ih, Algebra.TensorProduct.tmul_mul_tmul,
      Finset.prod_insert ht, Finset.prod_insert ht]

/-- The two rank-two Hodge factors, ordered marking classes and all inverse flag factors. -/
def integrand (D : HodgeClasses C) (P : PsiClasses C) {f : ℕ} (m : List ℕ)
    (u v : K) (flag : Fin f → K) : K ⊗[ℚ] (C.H 2 (Fin (m.length + f))) :=
  hodgeFactor D _ v * hodgeFactor D _ u * ((1 : K) ⊗ₜ[ℚ] markedDescendants P m f) *
    ∏ t, flagSeries (flag t) (P.psi 2 _ (stable _) (Fin.natAdd m.length t)) (3+m.length+f+1)

/-- Factorization in source cohomology of the entire finite vertex expansion. -/
theorem expansion_eq_product (D : HodgeClasses C) (P : PsiClasses C) {f : ℕ} (m : List ℕ)
    (u v : K) (flag : Fin f → K) :
    expansion D P m u v flag = integrand D P m u v flag := by
  classical
  simp only [integrand, expansion, flagBox, hodgeFactor, flagSeries, Finset.prod_univ_sum,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    rw [Finset.sum_comm]
    enter [2, i]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [tensor_product]
  simp only [term, monomial, monomial_split, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    pow_add (-1 : K)]
  congr 1
  · have exp (s : Fin f) : (flag s)^(-(k s : ℤ)-1) = (flag s)⁻¹^(k s+1) := by
      rw [show -(k s : ℤ)-1 = -((k s+1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, inv_pow]
    simp_rw [exp]
    ac_rfl
  · ac_rfl

/-- The rational-function vertex is the integral of the factored stable-curve class. -/
theorem integrate_product (D : HodgeClasses C) (P : PsiClasses C) (I : StableCurveIntegration C)
    {f : ℕ} (m : List ℕ) (u v : K) (flag : Fin f → K) :
    integrate I _ (integrand D P m u v flag) =
      GenusTwoLocalizationVertex.source (fun i j _ ↦ moment D P I i j) m u v flag := by
  rw [← expansion_eq_product, integrate_expansion]

end
end AxiomaticGW.GKM.GenusTwoLocalizationClass

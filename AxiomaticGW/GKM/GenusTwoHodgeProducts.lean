/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.GenusTwoHodgeForgetful

/-! # Hodge products at arbitrary genus-two arity

The Hodge classes come from the unmarked genus-two curve, of dimension three.
Naturality transports their high-degree vanishing to all vertices. The one-marked
square identity also descends to zero markings using the unmarked κ₀ normalization.
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoLocalizationClass
variable {C : StableCurveCohomology ℚ} {D : HodgeClasses C}

private theorem forget_first (H : D.Natural) (n : ℕ) :
    C.rename 2 _ _ (stable (n+1)) (stable n).option (finSuccEquiv n) (D.first (n+1)) =
      C.forget 2 (Fin n) (stable n) (D.first n) := H.forget n 0

private theorem forget_second (H : D.Natural) (n : ℕ) :
    C.rename 2 _ _ (stable (n+1)) (stable n).option (finSuccEquiv n) (D.second (n+1)) =
      C.forget 2 (Fin n) (stable n) (D.second n) := H.forget n 1

/-- Hodge monomials above codimension three vanish as classes at every arity. -/
theorem hodge_product_zero (H : D.Natural) (a b : ℕ) (hab : 3 < a + 2 * b) (n : ℕ) :
    (D.first n : C.H 2 (Fin n))^a * (D.second n : C.H 2 (Fin n))^b = 0 := by
  induction n with
  | zero =>
    apply C.eq_zero_of_dimension_lt 2 _ (stable 0) (a+2*b)
    · simpa only [smul_eq_mul, mul_one, Nat.mul_comm b 2] using SetLike.mul_mem_graded
        (SetLike.pow_mem_graded a (D.first 0).property)
        (SetLike.pow_mem_graded b (D.second 0).property)
    · simpa only [StableArity.dimension, Fintype.card_fin] using hab
  | succ n ih =>
    apply (C.rename 2 _ _ (stable (n+1)) (stable n).option (finSuccEquiv n)).injective
    simp only [map_mul, map_pow, map_zero, forget_first H, forget_second H]
    simpa only [map_mul, map_pow, map_zero] using congrArg (C.forget 2 (Fin n) (stable n)) ih

/-- Integration along the last marking with its cotangent class recovers twice any unmarked
genus-two class. Consequently unmarked pullback is injective, including in positive codimension. -/
theorem forget_unmarked_injective {I : StableCurveIntegration C} (U : ForgetfulPushforward C I)
    (P : PsiClasses C) (base : P.kappa U 2 (Fin 0) (stable 0) 0 = 2) :
    Function.Injective (C.forget 2 (Fin 0) (stable 0)) := by
  intro a b hab
  have push (c : C.H 2 (Fin 0)) : U.push 2 (Fin 0) (stable 0)
      (C.forget 2 _ (stable 0) c * P.psi 2 _ (stable 0).option none) = c+c := by
    have h := base
    simp only [PsiClasses.kappa, zero_add, pow_one] at h
    rw [U.projection_formula, h, mul_two]
  have h := (push a).symm.trans ((congrArg
    (fun z ↦ U.push 2 (Fin 0) (stable 0) (z * P.psi 2 _ (stable 0).option none)) hab).trans
      (push b))
  have ha (v : C.H 2 (Fin 0)) : (1/2 : ℚ) • (v+v) = v := by
    rw [← two_smul ℚ v, smul_smul]
    norm_num
  exact (ha a).symm.trans ((congrArg ((1/2 : ℚ) • ·) h).trans (ha b))

/-- One one-marked square identification determines λ₁² = 2λ₂ on all stable genus-two arities. -/
theorem square_at_all_arities (H : D.Natural) {I : StableCurveIntegration C}
    (U : ForgetfulPushforward C I) (P : PsiClasses C)
    (base : P.kappa U 2 (Fin 0) (stable 0) 0 = 2)
    (single : (D.first 1 : C.H 2 (Fin 1)) ^ 2 = 2 * (D.second 1 : C.H 2 (Fin 1))) (n : ℕ) :
    (D.first n : C.H 2 (Fin n))^2 = 2 * (D.second n : C.H 2 (Fin n)) := by
  induction n with
  | zero =>
    apply forget_unmarked_injective U P base
    have h := congrArg (C.rename 2 _ _ (stable 1) (stable 0).option (finSuccEquiv 0)) single
    simpa only [map_pow, map_mul, map_ofNat, forget_first H, forget_second H] using h
  | succ n ih =>
    apply (C.rename 2 _ _ (stable (n+1)) (stable n).option (finSuccEquiv n)).injective
    simp only [map_pow, map_mul, map_ofNat, forget_first H, forget_second H]
    simpa only [map_pow, map_mul, map_ofNat] using congrArg (C.forget 2 _ (stable n)) ih

/-- The λ₂² term vanishes before integration, even when marked points increase the dimension. -/
theorem top_hodge_square_zero (H : D.Natural) (n : ℕ) :
    (D.second n : C.H 2 (Fin n))^2 = 0 := by
  simpa only [pow_zero, one_mul] using hodge_product_zero H 0 2 (by decide) n

/-- Integrated square relation for the actual Hodge monomials, with arbitrary cotangent powers. -/
theorem square_moment (H : D.Natural) {I : StableCurveIntegration C}
    (U : ForgetfulPushforward C I) (P : PsiClasses C)
    (base : P.kappa U 2 (Fin 0) (stable 0) 0 = 2)
    (single : (D.first 1 : C.H 2 (Fin 1)) ^ 2 = 2 * (D.second 1 : C.H 2 (Fin 1))) (p : List ℕ) :
    moment D P I 1 1 p = 2 * moment D P I 0 2 p := by
  have h := square_at_all_arities H U P base single p.length
  simp only [moment, monomial, HodgeClasses.coefficient, one_mul]
  rw [← pow_two, h, two_mul, add_mul, map_add, two_mul]

open TensorProduct in
/-- Opposite nonzero tangent characters cancel all positive Hodge classes in the vertex Euler
factor. This is the rank-two Mumford identity before integration at every marking arity. -/
theorem opposite_hodge_factors (H : D.Natural) {I : StableCurveIntegration C}
    (U : ForgetfulPushforward C I) (P : PsiClasses C)
    (base : P.kappa U 2 (Fin 0) (stable 0) 0 = 2)
    (single : (D.first 1 : C.H 2 (Fin 1)) ^ 2 = 2 * (D.second 1 : C.H 2 (Fin 1)))
    {K : Type*} [Field K] [CharZero K] (n : ℕ) (u : K) (hu : u ≠ 0) :
    hodgeFactor D n (-u) * hodgeFactor D n u = (-(u^2)) ⊗ₜ[ℚ] (1 : C.H 2 (Fin n)) := by
  rw [hodgeFactor_eq, hodgeFactor_eq, inv_neg, neg_tmul, neg_tmul, neg_tmul]
  let x := u ⊗ₜ[ℚ] (1 : C.H 2 (Fin n))
  let y := (1 : K) ⊗ₜ[ℚ] (D.first n : C.H 2 (Fin n))
  let z := u⁻¹ ⊗ₜ[ℚ] (D.second n : C.H 2 (Fin n))
  change (-x - y + -z) * (x - y + z) = _
  have hy : y*y = x*z + x*z := by
    dsimp only [x, y, z]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hu, one_mul]
    rw [← pow_two, square_at_all_arities H U P base single n, two_mul, tmul_add]
  have hz : z*z = 0 := by
    dsimp only [z]
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← pow_two (D.second n : C.H 2 (Fin n)),
      top_hodge_square_zero H n, tmul_zero]
  calc
    _ = y*y - x*x - (x*z + x*z) - z*z := by ring
    _ = -(x*x) := by rw [hy, hz]; ring
    _ = _ := by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, pow_two]

end AxiomaticGW.GKM.GenusTwoLocalizationClass

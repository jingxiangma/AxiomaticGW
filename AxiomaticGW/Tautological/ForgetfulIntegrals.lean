/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.RationalTailPullback

/-! # String and dilaton integrals with a pulled-back source class

The forgetful correction for a cotangent monomial is a sum of rational three-point tails.
The forgotten cotangent class kills every such tail. The remaining integral with a new
cotangent insertion is expressed using κ₀, defined by the forgetful pushforward.
-/

@[expose] public section
namespace AxiomaticGW.PsiBoundaryExpansion
open TensorProduct
variable {R : Type*} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
  {g : ℕ} {S : Type} [Fintype S] [DecidableEq S]

/-- Integrating a decorated rational tail multiplies by the volume of the three-point space. -/
theorem integrate_tailPush (F : SeparatingPushforward C I) (h : StableArity g S) (s : S)
    (a : C.H g S) : I.integrate g (Option S) h.option (tailPush F h s a) =
      I.integrate g S h a * I.integrate 0 (Option Bool) tailStable 1 := by
  simp only [tailPush, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, LinearMap.flip_apply,
    TensorProduct.mk_apply, I.integrate_rename]
  refine (F.integrate_push g 0 _ _ (tailMainStable h s) tailStable _).trans ?_
  rw [I.tensorIntegral_tmul, I.integrate_rename]

/-- The forgotten marking lies on the rational tail, whose cotangent line vanishes. -/
theorem newPsi_mul_tailPush (F : SeparatingPushforward C I) (P : PsiClasses C)
    (h : StableArity g S) (s : S) (a : C.H g S) :
    P.psi g (Option S) h.option none * tailPush F h s a = 0 := by
  have hp := P.rename_psi g ({t : S // t ≠ s} ⊕ Bool) (Option S)
    (StableArity.separating (tailMainStable h s) tailStable) h.option (tailLabels s) (.inr true)
  change _ = P.psi g (Option S) h.option none at hp
  have hz : P.psi 0 (Option Bool) tailStable (some true) = 0 := by
    apply C.eq_zero_of_dimension_lt 0 _ tailStable 1 _ (P.psi_degree _ _ _ _)
    norm_num [StableArity.dimension]
  have hb : tailRestriction C h s (P.psi g (Option S) h.option none) =
      C.rename g S _ h (tailMainStable h s) (Equiv.optionSubtypeNe s).symm 0 ⊗ₜ[R] 1 := by
    simp only [tailRestriction, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, map_zero,
      TensorProduct.zero_tmul]
    rw [← hp, AlgEquiv.symm_apply_apply]
    refine (P.separating_psi_right g 0 _ _ (tailMainStable h s) tailStable true).trans ?_
    rw [hz, TensorProduct.tmul_zero]
  rw [mul_tailPush_of_restriction F h s _ 0 a hb, zero_mul, map_zero]

omit [DecidableEq S] in
private theorem integrate_forget (U : ForgetfulPushforward C I) (h : StableArity g S)
    (a : C.H g S) : I.integrate g (Option S) h.option (C.forget g S h a) = 0 := by
  have hz : U.push g S h 1 = 0 :=
    U.push_eq_zero_of_degree_zero g S h 1 SetLike.GradedOne.one_mem
  rw [← U.integrate_push g S h, ← mul_one (C.forget g S h a), U.projection_formula,
    hz, mul_zero, map_zero]

variable (U : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (hK : TailCompatible K F N) (H : TailForgetCompatible C)

include hK H

private theorem upstairs_monomial (h : StableArity g S) (d : S → ℕ) :
    P.monomial g (Option S) h.option (fun t ↦ t.elim 0 d) =
      C.forget g S h (P.monomial g S h d) +
      ∑ s, if d s = 0 then 0 else tailPush F h s
        (P.monomial g S h (Function.update d s (d s - 1))) :=
  (eq_sub_iff_add_eq.mp (forget_monomial F N P K hK H h d)).symm

include U

/-- Forgetting a string marking lowers each positive cotangent power once, counting repetitions. -/
theorem string_integral (vol : I.integrate 0 (Option Bool) tailStable 1 = 1)
    (h : StableArity g S) (a : C.H g S) (d : S → ℕ) :
    I.integrate g (Option S) h.option (C.forget g S h a *
      P.monomial g (Option S) h.option (fun t ↦ t.elim 0 d)) =
      ∑ s, if d s = 0 then 0 else I.integrate g S h
        (a * P.monomial g S h (Function.update d s (d s - 1))) := by
  rw [upstairs_monomial F N P K hK H h d, mul_add, ← map_mul, map_add, integrate_forget U h,
    zero_add, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs with hd
  · rw [mul_zero, map_zero]
  · rw [forget_mul_tailPush F H, integrate_tailPush, vol, mul_one]

omit [DecidableEq S] in
/-- One new cotangent insertion yields κ₀ multiplying the remaining monomial. -/
theorem dilaton_integral (h : StableArity g S) (a : C.H g S) (d : S → ℕ) :
    I.integrate g (Option S) h.option (C.forget g S h a * P.psi g (Option S) h.option none *
      P.monomial g (Option S) h.option (fun t ↦ t.elim 0 d)) =
      I.integrate g S h ((a * P.monomial g S h d) * P.kappa U g S h 0) := by
  classical
  rw [upstairs_monomial F N P K hK H h d, mul_add, Finset.mul_sum]
  have hz (s : S) : C.forget g S h a * P.psi g (Option S) h.option none *
      (if d s = 0 then 0 else tailPush F h s
        (P.monomial g S h (Function.update d s (d s - 1)))) = 0 := by
    split_ifs <;> first | exact mul_zero _ | rw [mul_assoc, newPsi_mul_tailPush, mul_zero]
  simp only [hz, Finset.sum_const_zero, add_zero]
  rw [mul_right_comm, ← map_mul, ← U.integrate_push g S h, U.projection_formula]
  simp only [PsiClasses.kappa, zero_add, pow_one]

end AxiomaticGW.PsiBoundaryExpansion

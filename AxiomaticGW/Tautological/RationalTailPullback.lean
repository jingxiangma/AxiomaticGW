/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.RationalTail
public import AxiomaticGW.Tautological.LegPsiRealization

/-!
# Cotangent monomials under forgetting a marking

The section carrying the old and new markings is the existing raw rational
three-point tail. Forgetting the new marking contracts this tail and recovers
the original main curve. `TailForgetCompatible` records only that primitive
composition of geometric maps. It contains no decorated pullback equation,
relation or numerical invariant.

Projection, cotangent restriction and the existing one-psi comparison derive
all power and monomial corrections. A positive power loses one at the main
node in its correction, with coefficient minus one, independently of its size.
The geometric source is Bae--Schmitt, arXiv:2012.09887, Proposition 3.10 and the
section interpretation in its proof. Geometric applicability remains explicit.
-/

@[expose] public section

namespace AxiomaticGW.PsiBoundaryExpansion

open TensorProduct
universe u

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

/-- Restrict an upstairs class to the actual rational-tail boundary. -/
def tailRestriction (C : StableCurveCohomology R) {g : ℕ} {S : Type}
    [Fintype S] [DecidableEq S] (h : StableArity g S) (s : S) :
    C.H g (Option S) →ₐ[R]
      C.H g (Option {t : S // t ≠ s}) ⊗[R] C.H 0 (Option Bool) :=
  (C.separating g 0 {t : S // t ≠ s} Bool (tailMainStable h s) tailStable).comp
    (C.rename g ({t : S // t ≠ s} ⊕ Bool) (Option S)
      (StableArity.separating (tailMainStable h s) tailStable) h.option
      (tailLabels s)).symm.toAlgHom

/-- Primitive section identity: forgetting after this attachment is the main projection. -/
def TailForgetCompatible (C : StableCurveCohomology R) : Prop :=
  ∀ (g : ℕ) (S : Type) [Fintype S] [DecidableEq S] (h : StableArity g S) (s : S)
      (a : C.H g S),
    tailRestriction C h s (C.forget g S h a) =
      C.rename g S (Option {t : S // t ≠ s}) h (tailMainStable h s)
        (Equiv.optionSubtypeNe s).symm a ⊗ₜ[R] 1

/-- Raw tail attachment, with arbitrary decoration on the main component. -/
noncomputable def tailPush (F : SeparatingPushforward C I) {g : ℕ} {S : Type}
    [Fintype S] [DecidableEq S] (h : StableArity g S) (s : S) :
    C.H g S →ₗ[R] C.H g (Option S) :=
  (C.rename g ({t : S // t ≠ s} ⊕ Bool) (Option S)
    (StableArity.separating (tailMainStable h s) tailStable) h.option
    (tailLabels s)).toLinearMap.comp
      ((F.push g 0 {t : S // t ≠ s} Bool (tailMainStable h s) tailStable).comp
        (((TensorProduct.mk R (C.H g (Option {t : S // t ≠ s})) (C.H 0 (Option Bool))).flip
          (1 : C.H 0 (Option Bool))).comp
          (C.rename g S (Option {t : S // t ≠ s}) h (tailMainStable h s)
            (Equiv.optionSubtypeNe s).symm).toLinearMap))

/-- The unweighted tail is exactly the already used primitive boundary expression. -/
theorem tailPush_one (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    {g : ℕ} {S : Type} [Fintype S] [DecidableEq S] (h : StableArity g S) (s : S) :
    tailPush F h s 1 = (tailExpression g S h s).classValue F N := by
  simp only [tailPush, LinearMap.comp_apply, LinearMap.flip_apply,
    AlgEquiv.toLinearMap_apply, map_one, TensorProduct.mk_apply, tailExpression,
    GluingExpression.classValue]

/-- Projection formula for a specified main-component restriction. -/
theorem mul_tailPush_of_restriction (F : SeparatingPushforward C I)
    {g : ℕ} {S : Type} [Fintype S] [DecidableEq S] (h : StableArity g S) (s : S)
    (b : C.H g (Option S)) (c a : C.H g S)
    (hb : tailRestriction C h s b =
      C.rename g S (Option {t : S // t ≠ s}) h (tailMainStable h s)
        (Equiv.optionSubtypeNe s).symm c ⊗ₜ[R] 1) :
    b * tailPush F h s a = tailPush F h s (c * a) := by
  let e := C.rename g ({t : S // t ≠ s} ⊕ Bool) (Option S)
    (StableArity.separating (tailMainStable h s) tailStable) h.option (tailLabels s)
  apply e.symm.injective
  change e.symm (b * e _) = e.symm (e _)
  rw [map_mul, AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]
  simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
    AlgEquiv.toLinearMap_apply]
  rw [← F.projection_formula g 0 _ _ (tailMainStable h s) tailStable (e.symm b)]
  change F.push g 0 _ _ _ _ (tailRestriction C h s b * _) = _
  rw [hb, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]

/-- The section identity gives projection against every original class. -/
theorem forget_mul_tailPush (F : SeparatingPushforward C I) (H : TailForgetCompatible C)
    {g : ℕ} {S : Type} [Fintype S] [DecidableEq S] (h : StableArity g S) (s : S)
    (b a : C.H g S) :
    C.forget g S h b * tailPush F h s a = tailPush F h s (b * a) :=
  mul_tailPush_of_restriction F h s _ b a (H g S h s b)

/-- Every retained marking outside the contracted tail stays on the main component. -/
theorem tailRestriction_psi_ne (P : PsiClasses C)
    {g : ℕ} {S : Type} [Fintype S] [DecidableEq S] (h : StableArity g S)
    (s t : S) (ht : t ≠ s) :
    tailRestriction C h s (P.psi g (Option S) h.option (some t)) =
      C.rename g S (Option {t : S // t ≠ s}) h (tailMainStable h s)
        (Equiv.optionSubtypeNe s).symm (P.psi g S h t) ⊗ₜ[R] 1 := by
  have hp := P.rename_psi g ({t : S // t ≠ s} ⊕ Bool) (Option S)
    (StableArity.separating (tailMainStable h s) tailStable) h.option
    (tailLabels s) (.inl ⟨t, ht⟩)
  change _ = P.psi g (Option S) h.option (some t) at hp
  simp only [tailRestriction, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [← hp, AlgEquiv.symm_apply_apply]
  have hs : C.separating g 0 _ _ (tailMainStable h s) tailStable
      (P.psi g ({t : S // t ≠ s} ⊕ Bool)
        (StableArity.separating (tailMainStable h s) tailStable) (.inl ⟨t, ht⟩)) =
      P.psi g (Option {t : S // t ≠ s}) (tailMainStable h s) (some ⟨t, ht⟩) ⊗ₜ[R] 1 :=
    P.separating_psi_left g 0 _ _ (tailMainStable h s) tailStable ⟨t, ht⟩
  rw [hs, P.rename_psi, Equiv.optionSubtypeNe_symm_of_ne ht]

/-- The old marking on the rational three-point tail has zero restricted psi class. -/
theorem tailRestriction_psi_self (P : PsiClasses C)
    {g : ℕ} {S : Type} [Fintype S] [DecidableEq S] (h : StableArity g S) (s : S) :
    tailRestriction C h s (P.psi g (Option S) h.option (some s)) = 0 := by
  have hp := P.rename_psi g ({t : S // t ≠ s} ⊕ Bool) (Option S)
    (StableArity.separating (tailMainStable h s) tailStable) h.option
    (tailLabels s) (.inr false)
  change _ = P.psi g (Option S) h.option (some s) at hp
  have hz : P.psi 0 (Option Bool) tailStable (some false) = 0 := by
    apply C.eq_zero_of_dimension_lt 0 (Option Bool) tailStable 1 _ (P.psi_degree _ _ _ _)
    norm_num [StableArity.dimension]
  simp only [tailRestriction, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [← hp, AlgEquiv.symm_apply_apply]
  have hs : C.separating g 0 _ _ (tailMainStable h s) tailStable
      (P.psi g ({t : S // t ≠ s} ⊕ Bool)
        (StableArity.separating (tailMainStable h s) tailStable) (.inr false)) =
      1 ⊗ₜ[R] P.psi 0 (Option Bool) tailStable (some false) :=
    P.separating_psi_right g 0 _ _ (tailMainStable h s) tailStable false
  rw [hs, hz, TensorProduct.tmul_zero]

/-- The upstairs psi at the tail marking annihilates every tail decoration. -/
theorem psi_self_mul_tailPush (F : SeparatingPushforward C I) (P : PsiClasses C)
    {g : ℕ} {S : Type} [Fintype S] [DecidableEq S] (h : StableArity g S) (s : S)
    (a : C.H g S) :
    P.psi g (Option S) h.option (some s) * tailPush F h s a = 0 := by
  have hb : tailRestriction C h s (P.psi g (Option S) h.option (some s)) =
      C.rename g S (Option {t : S // t ≠ s}) h (tailMainStable h s)
        (Equiv.optionSubtypeNe s).symm 0 ⊗ₜ[R] 1 := by
    rw [tailRestriction_psi_self, map_zero, TensorProduct.zero_tmul]
  rw [mul_tailPush_of_restriction F h s _ 0 a hb, zero_mul, map_zero]

/-- Other upstairs psi powers multiply the main decoration in the usual way. -/
theorem psi_ne_mul_tailPush (F : SeparatingPushforward C I) (P : PsiClasses C)
    {g : ℕ} {S : Type} [Fintype S] [DecidableEq S] (h : StableArity g S)
    (s t : S) (ht : t ≠ s) (a : C.H g S) :
    P.psi g (Option S) h.option (some t) * tailPush F h s a =
      tailPush F h s (P.psi g S h t * a) :=
  mul_tailPush_of_restriction F h s _ _ a (tailRestriction_psi_ne P h s t ht)

/-- Powers at other markings retain their full exponent on the main component. -/
theorem psi_ne_pow_mul_tailPush (F : SeparatingPushforward C I) (P : PsiClasses C)
    {g : ℕ} {S : Type} [Fintype S] [DecidableEq S] (h : StableArity g S)
    (s t : S) (ht : t ≠ s) (k : ℕ) (a : C.H g S) :
    P.psi g (Option S) h.option (some t) ^ k * tailPush F h s a =
      tailPush F h s (P.psi g S h t ^ k * a) := by
  induction k generalizing a with
  | zero => simp only [pow_zero, one_mul]
  | succ k ih =>
    rw [pow_succ, mul_assoc, psi_ne_mul_tailPush F P h s t ht, ih, pow_succ, mul_assoc]

/-- The existing one-psi law identifies the raw section correction. -/
theorem forget_psi_eq (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (P : PsiClasses C) (K : PsiForgetFormula P) (hK : TailCompatible K F N)
    {g : ℕ} {S : Type} [Fintype S] [DecidableEq S] (h : StableArity g S) (s : S) :
    C.forget g S h (P.psi g S h s) =
      P.psi g (Option S) h.option (some s) - tailPush F h s 1 := by
  rw [tailPush_one F N, ← hK g S h s, K.psi_eq_forget_add_boundary, add_sub_cancel_right]

/-- The power correction has coefficient minus one and one less main-node power. -/
theorem forget_psi_pow_succ (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (hK : TailCompatible K F N) (H : TailForgetCompatible C)
    {g : ℕ} {S : Type} [Fintype S] [DecidableEq S] (h : StableArity g S) (s : S) (k : ℕ) :
    C.forget g S h (P.psi g S h s ^ (k + 1)) =
      P.psi g (Option S) h.option (some s) ^ (k + 1) -
        tailPush F h s (P.psi g S h s ^ k) := by
  induction k with
  | zero => simpa only [Nat.zero_add, pow_one, pow_zero] using forget_psi_eq F N P K hK h s
  | succ k ih =>
    calc
      C.forget g S h (P.psi g S h s ^ (k + 1 + 1)) =
          C.forget g S h (P.psi g S h s) *
            C.forget g S h (P.psi g S h s ^ (k + 1)) := by
        rw [pow_succ, map_mul, mul_comm]
      _ = P.psi g (Option S) h.option (some s) *
            C.forget g S h (P.psi g S h s ^ (k + 1)) -
          C.forget g S h (P.psi g S h s ^ (k + 1)) * tailPush F h s 1 := by
        rw [forget_psi_eq F N P K hK h s, sub_mul, mul_comm (tailPush F h s 1)]
      _ = _ := by
        rw [forget_mul_tailPush F H, mul_one, ih, mul_sub, psi_self_mul_tailPush,
          sub_zero, ← pow_succ']

/-- A zero exponent contributes no correction. -/
theorem forget_psi_pow (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (hK : TailCompatible K F N) (H : TailForgetCompatible C)
    {g : ℕ} {S : Type} [Fintype S] [DecidableEq S] (h : StableArity g S) (s : S) (k : ℕ) :
    C.forget g S h (P.psi g S h s ^ k) =
      P.psi g (Option S) h.option (some s) ^ k -
        if k = 0 then 0 else tailPush F h s (P.psi g S h s ^ (k - 1)) := by
  cases k with
  | zero => simp only [pow_zero, map_one, ↓reduceIte, sub_zero]
  | succ k =>
    simpa only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel] using
      forget_psi_pow_succ F N P K hK H h s k

/-- Finite products inherit only the single-tail corrections, with all other powers retained. -/
theorem forget_psi_product (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (hK : TailCompatible K F N) (H : TailForgetCompatible C)
    {g : ℕ} {S : Type} [Fintype S] [DecidableEq S] (h : StableArity g S)
    (d : S → ℕ) (U : Finset S) :
    C.forget g S h (∏ i ∈ U, P.psi g S h i ^ d i) =
      (∏ i ∈ U, P.psi g (Option S) h.option (some i) ^ d i) -
        ∑ s ∈ U, if d s = 0 then 0 else tailPush F h s
          (P.psi g S h s ^ (d s - 1) * ∏ i ∈ U.erase s, P.psi g S h i ^ d i) := by
  induction U using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, map_one, sub_zero]
  | @insert t U ht ih =>
    have hrest : P.psi g (Option S) h.option (some t) ^ d t *
        (∑ s ∈ U, if d s = 0 then 0 else tailPush F h s
          (P.psi g S h s ^ (d s - 1) * ∏ i ∈ U.erase s, P.psi g S h i ^ d i)) =
        ∑ s ∈ U, if d s = 0 then 0 else tailPush F h s
          (P.psi g S h s ^ (d s - 1) *
            ∏ i ∈ (insert t U).erase s, P.psi g S h i ^ d i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      have hts : t ≠ s := fun he ↦ ht (he ▸ hs)
      by_cases hd : d s = 0
      · simp only [hd, ↓reduceIte, mul_zero]
      · rw [if_neg hd, if_neg hd, psi_ne_pow_mul_tailPush F P h s t hts,
          Finset.erase_insert_of_ne hts,
          Finset.prod_insert (fun hm ↦ ht (Finset.mem_of_mem_erase hm))]
        congr 1
        ring
    have hhead : (if d t = 0 then 0 else tailPush F h t (P.psi g S h t ^ (d t - 1))) *
        C.forget g S h (∏ i ∈ U, P.psi g S h i ^ d i) =
        if d t = 0 then 0 else tailPush F h t
          (P.psi g S h t ^ (d t - 1) * ∏ i ∈ U, P.psi g S h i ^ d i) := by
      by_cases hd : d t = 0
      · simp only [hd, ↓reduceIte, zero_mul]
      · rw [if_neg hd, if_neg hd, mul_comm, forget_mul_tailPush F H, mul_comm]
    rw [Finset.prod_insert ht, map_mul, forget_psi_pow F N P K hK H, sub_mul,
      hhead, ih, mul_sub, hrest, Finset.prod_insert ht, Finset.sum_insert ht,
      Finset.erase_insert ht]
    ring

/-- The pullback of any component monomial, including powers on future node branches.
The main component keeps every other power, while the attaching flag loses exactly one. -/
theorem forget_monomial (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (hK : TailCompatible K F N) (H : TailForgetCompatible C)
    {g : ℕ} {S : Type} [Fintype S] [DecidableEq S] (h : StableArity g S) (d : S → ℕ) :
    C.forget g S h (P.monomial g S h d) =
      P.monomial g (Option S) h.option (fun s ↦ s.elim 0 d) -
        ∑ s, if d s = 0 then 0 else
          tailPush F h s (P.monomial g S h (Function.update d s (d s - 1))) := by
  have hupdate (s : S) : P.monomial g S h (Function.update d s (d s - 1)) =
      P.psi g S h s ^ (d s - 1) *
        ∏ i ∈ Finset.univ.erase s, P.psi g S h i ^ d i := by
    rw [PsiClasses.monomial, ← Finset.mul_prod_erase _ _ (Finset.mem_univ s),
      Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro t ht
    rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]
  have hp := forget_psi_product F N P K hK H h d Finset.univ
  simp only [← hupdate] at hp
  simpa only [PsiClasses.monomial, Fintype.prod_option, Option.elim_none, Option.elim_some,
    pow_zero, one_mul] using hp

end AxiomaticGW.PsiBoundaryExpansion

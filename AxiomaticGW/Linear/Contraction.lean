/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Linear.Copairing
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.LinearAlgebra.Multilinear.TensorProduct

/-!
# Contraction of named multilinear slots

This file contracts two distinguished inputs of a multilinear map against the
copairing of a symmetric perfect pairing. Remaining inputs are indexed by an
arbitrary type `S`, while the two contracted inputs are indexed by `Fin 2`.

Separating contraction is derived by combining two maps, relabelling their two
node inputs as `Fin 2`, and applying the same self-contraction operation.
-/

@[expose] public section

namespace AxiomaticGW

open TensorProduct

namespace SymmetricPerfectPairing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V]

/-- A multilinear map with one input is canonically a linear map. This is
implemented through currying and evaluation of the resulting empty
multilinear map. -/
noncomputable def finOneToLinear :
    MultilinearMap R (fun _ : Fin 1 ↦ V) R →ₗ[R] (V →ₗ[R] R) :=
  (LinearMap.compRight R
    (MultilinearMap.constLinearEquivOfIsEmpty R R (fun _ : Fin 0 ↦ V) R).symm.toLinearMap).comp
    (multilinearCurryLeftEquiv R (fun _ : Fin 1 ↦ V) R).toLinearMap

omit [Module.Free R V] [Module.Finite R V] in
/-- Evaluation of the one-input-to-linear-map identification. -/
@[simp]
theorem finOneToLinear_apply
    (f : MultilinearMap R (fun _ : Fin 1 ↦ V) R) (x : V) :
    finOneToLinear f x = f (fun _ ↦ x) := by
  simp only [finOneToLinear, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, multilinearCurryLeftEquiv_apply,
    LinearMap.compRight_apply, MultilinearMap.constLinearEquivOfIsEmpty_symm_apply,
    MultilinearMap.curryLeft_apply]
  congr 1
  funext i
  fin_cases i
  rfl

/-- A two-input multilinear map is canonically a bilinear form. -/
noncomputable def finTwoToBilin :
    MultilinearMap R (fun _ : Fin 2 ↦ V) R →ₗ[R] LinearMap.BilinForm R V :=
  (LinearMap.compRight R (finOneToLinear (R := R) (V := V))).comp
    (multilinearCurryLeftEquiv R (fun _ : Fin 2 ↦ V) R).toLinearMap

omit [Module.Free R V] [Module.Finite R V] in
/-- Evaluation of the two-input-to-bilinear-form identification. -/
@[simp]
theorem finTwoToBilin_apply
    (f : MultilinearMap R (fun _ : Fin 2 ↦ V) R) (x y : V) :
    finTwoToBilin f x y = f (Fin.cons x fun _ ↦ y) := by
  simp [finTwoToBilin]

/-- Contract a two-input multilinear map against the copairing. -/
noncomputable def contractTwo (P : SymmetricPerfectPairing R V) :
    MultilinearMap R (fun _ : Fin 2 ↦ V) R →ₗ[R] R :=
  (LinearMap.applyₗ P.copairing).comp
    ((TensorProduct.uncurry (RingHom.id R) V V R).comp finTwoToBilin)

/-- Contraction is evaluation of the bilinear form on the copairing tensor. -/
theorem contractTwo_apply (P : SymmetricPerfectPairing R V)
    (f : MultilinearMap R (fun _ : Fin 2 ↦ V) R) :
    P.contractTwo f = TensorProduct.lift (finTwoToBilin f) P.copairing := rfl

/-- Contract the two `Fin 2` inputs of a multilinear map, leaving the inputs
labelled by `S`. -/
noncomputable def selfContract (P : SymmetricPerfectPairing R V)
    {S : Type*} (f : MultilinearMap R (fun _ : S ⊕ Fin 2 ↦ V) R) :
    MultilinearMap R (fun _ : S ↦ V) R :=
  P.contractTwo.compMultilinearMap f.currySum

/-- Pointwise evaluation of self-contraction. -/
@[simp]
theorem selfContract_apply (P : SymmetricPerfectPairing R V)
    {S : Type*} (f : MultilinearMap R (fun _ : S ⊕ Fin 2 ↦ V) R)
    (a : S → V) :
    P.selfContract f a = P.contractTwo (f.currySum a) := rfl

/-- Self-contraction is additive in the multilinear map. -/
@[simp]
theorem selfContract_add (P : SymmetricPerfectPairing R V) {S : Type*}
    (f g : MultilinearMap R (fun _ : S ⊕ Fin 2 ↦ V) R) :
    P.selfContract (f + g) = P.selfContract f + P.selfContract g := by
  simp [selfContract]

/-- Self-contraction is compatible with scalar multiplication. -/
@[simp]
theorem selfContract_smul (P : SymmetricPerfectPairing R V) {S : Type*}
    (r : R) (f : MultilinearMap R (fun _ : S ⊕ Fin 2 ↦ V) R) :
    P.selfContract (r • f) = r • P.selfContract f := by
  simp [selfContract]

/-- The transposition of the two distinguished node labels. -/
def swapFinTwo : Equiv.Perm (Fin 2) := Equiv.swap 0 1

omit [Module.Free R V] [Module.Finite R V] in
/-- Relabelling a two-input map by the transposition flips its associated
bilinear form. -/
theorem finTwoToBilin_domDomCongr_swap
    (f : MultilinearMap R (fun _ : Fin 2 ↦ V) R) (x y : V) :
    finTwoToBilin (f.domDomCongr swapFinTwo) x y = finTwoToBilin f y x := by
  simp only [finTwoToBilin_apply, MultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The contraction of two inputs does not depend on their ordering. -/
theorem contractTwo_domDomCongr_swap (P : SymmetricPerfectPairing R V)
    (f : MultilinearMap R (fun _ : Fin 2 ↦ V) R) :
    P.contractTwo (f.domDomCongr swapFinTwo) = P.contractTwo f := by
  rw [contractTwo_apply, contractTwo_apply]
  have flip_tensor (t : V ⊗[R] V) :
      TensorProduct.lift (finTwoToBilin (f.domDomCongr swapFinTwo)) t =
        TensorProduct.lift (finTwoToBilin f) (TensorProduct.comm R V V t) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
        simp only [TensorProduct.lift.tmul, TensorProduct.comm_tmul]
        exact finTwoToBilin_domDomCongr_swap f x y
    | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  rw [flip_tensor, P.copairing_comm]

/-- Relabel the inputs of two maps with distinguished `Option` nodes as one
family of ordinary labels and two ordered node labels. The first node is
`0 : Fin 2` and the second node is `1 : Fin 2`. -/
def separatingLabelsEquiv (S T : Type*) :
    Option S ⊕ Option T ≃ (S ⊕ T) ⊕ Fin 2 where
  toFun
    | .inl none => .inr 0
    | .inl (some s) => .inl (.inl s)
    | .inr none => .inr 1
    | .inr (some t) => .inl (.inr t)
  invFun
    | .inl (.inl s) => .inl (some s)
    | .inl (.inr t) => .inr (some t)
    | .inr i => Fin.cases (.inl none) (fun _ ↦ .inr none) i
  left_inv x := by
    rcases x with x | x
    · rcases x with _ | s <;> rfl
    · rcases x with _ | t <;> rfl
  right_inv x := by
    rcases x with (s | t) | i
    · rfl
    · rfl
    · fin_cases i <;> rfl

/-- Contract the distinguished node of each of two scalar-valued multilinear
maps. The remaining labels are the disjoint union `S ⊕ T`. -/
noncomputable def pairContract (P : SymmetricPerfectPairing R V)
    {S T : Type*} (f : MultilinearMap R (fun _ : Option S ↦ V) R)
    (g : MultilinearMap R (fun _ : Option T ↦ V) R) :
    MultilinearMap R (fun _ : S ⊕ T ↦ V) R :=
  P.selfContract
    (((LinearMap.mul' R R).compMultilinearMap (f.domCoprod g)).domDomCongr
      (separatingLabelsEquiv S T))

/-- Pointwise evaluation of separating contraction through the common
two-slot contraction operation. -/
@[simp]
theorem pairContract_apply (P : SymmetricPerfectPairing R V)
    {S T : Type*} (f : MultilinearMap R (fun _ : Option S ↦ V) R)
    (g : MultilinearMap R (fun _ : Option T ↦ V) R) (a : S ⊕ T → V) :
    P.pairContract f g a =
      P.contractTwo
        ((((LinearMap.mul' R R).compMultilinearMap (f.domCoprod g)).domDomCongr
          (separatingLabelsEquiv S T)).currySum a) := rfl

/-- Contracting two metric functionals against the copairing recovers the
metric. This is the abstract sewing identity used by separating gluing. -/
theorem contract_toDual_mul_toDual (P : SymmetricPerfectPairing R V)
    (x y : V) :
    TensorProduct.lift
        (((LinearMap.mul R R).comp (P.toDual x)).compl₂ (P.toDual y))
        P.copairing =
      P.form x y := by
  have contraction (t : V ⊗[R] V) :
      TensorProduct.lift
          (((LinearMap.mul R R).comp (P.toDual x)).compl₂ (P.toDual y)) t =
        P.form (P.tensorEndEquiv t x) y := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul u v =>
        simp [P.isSymm.eq]
    | add t₁ t₂ h₁ h₂ =>
        simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) h₁ h₂
  rw [contraction, P.tensorEndEquiv_copairing]
  rfl

end SymmetricPerfectPairing

end AxiomaticGW

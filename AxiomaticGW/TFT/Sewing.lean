/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Linear.Contraction
public import AxiomaticGW.TFT.Correlator

/-!
# Sewing identities for Frobenius correlators

This file proves the algebraic identities behind nonseparating and separating
gluing. All proofs are basis-free and use the canonical copairing constructed
from the perfect Frobenius pairing.
-/

@[expose] public section

namespace AxiomaticGW

open TensorProduct TFT

namespace CommFrobeniusAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]

/-- The Frobenius sewing identity: contracting the two metric functionals
associated to `x` and `y` gives the trace pairing of `x` and `y`. -/
theorem sewing_identity (F : CommFrobeniusAlgebra R A) (x y : A) :
    TensorProduct.lift
        (((LinearMap.mul R R).comp (F.pairing.toDual x)).compl₂
          (F.pairing.toDual y))
        F.casimir =
      F.counit (x * y) := by
  simpa only [casimir, pairing_apply] using
    F.pairing.contract_toDual_mul_toDual x y

/-- Contracting multiplication against the Casimir tensor inserts the handle
element. The extra factor `z` is the product of all inputs not being glued. -/
theorem contract_mul_casimir (F : CommFrobeniusAlgebra R A) (z : A) :
    TensorProduct.lift
        ((LinearMap.mul R A).compr₂ (F.counit.comp (LinearMap.mulLeft R z)))
        F.casimir =
      F.counit (z * F.handleElement) := by
  have contraction (t : A ⊗[R] A) :
      TensorProduct.lift
          ((LinearMap.mul R A).compr₂ (F.counit.comp (LinearMap.mulLeft R z))) t =
        F.counit (z * LinearMap.mul' R A t) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rfl
    | add t₁ t₂ h₁ h₂ =>
        simpa only [map_add, mul_add] using congrArg₂ (· + ·) h₁ h₂
  rw [contraction]
  rfl

/-- Contracting the two node inputs of a genus-`g` correlator attaches one
handle and produces the genus-`g+1` correlator. -/
theorem selfContract_correlator (F : CommFrobeniusAlgebra R A) (g : ℕ)
    (S : Type*) [Fintype S] :
    F.pairing.selfContract (F.correlator g (S ⊕ Fin 2)) =
      F.correlator (g + 1) S := by
  ext a
  rw [F.pairing.selfContract_apply, F.pairing.contractTwo_apply]
  have hform :
      SymmetricPerfectPairing.finTwoToBilin
          ((F.correlator g (S ⊕ Fin 2)).currySum a) =
        (LinearMap.mul R A).compr₂
          (F.counit.comp
            (LinearMap.mulLeft R ((∏ s, a s) * F.handleElement ^ g))) := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [SymmetricPerfectPairing.finTwoToBilin_apply,
      MultilinearMap.currySum_apply', correlator_apply,
      Fintype.prod_sum_type, Fin.prod_univ_two, LinearMap.compr₂_apply,
      LinearMap.comp_apply, LinearMap.mulLeft_apply]
    simp only [Sum.elim_inl, Sum.elim_inr, Fin.cons_zero]
    change F.counit
        (((∏ s, a s) * (x * y)) * F.handleElement ^ g) =
      F.counit (((∏ s, a s) * F.handleElement ^ g) * (x * y))
    congr 1
    ac_rfl
  rw [hform]
  change TensorProduct.lift
      ((LinearMap.mul R A).compr₂
        (F.counit.comp
          (LinearMap.mulLeft R ((∏ s, a s) * F.handleElement ^ g))))
      F.casimir = _
  rw [F.contract_mul_casimir]
  simp only [correlator_apply]
  congr 1
  rw [pow_add, pow_one]
  ac_rfl

/-- Contracting one node input from each of two correlators produces the
correlator of the connected separating gluing. -/
theorem pairContract_correlator (F : CommFrobeniusAlgebra R A)
    (g₁ g₂ : ℕ) (S T : Type*) [Fintype S] [Fintype T] :
    F.pairing.pairContract (F.correlator g₁ (Option S))
        (F.correlator g₂ (Option T)) =
      F.correlator (g₁ + g₂) (S ⊕ T) := by
  ext a
  rw [F.pairing.pairContract_apply, F.pairing.contractTwo_apply]
  let x₀ : A := (∏ s, a (.inl s)) * F.handleElement ^ g₁
  let y₀ : A := (∏ t, a (.inr t)) * F.handleElement ^ g₂
  have hform :
      SymmetricPerfectPairing.finTwoToBilin
          (((((LinearMap.mul' R R).compMultilinearMap
              ((F.correlator g₁ (Option S)).domCoprod
                (F.correlator g₂ (Option T)))).domDomCongr
            (SymmetricPerfectPairing.separatingLabelsEquiv S T))).currySum a) =
        (((LinearMap.mul R R).comp (F.pairing.toDual x₀)).compl₂
          (F.pairing.toDual y₀)) := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp [SymmetricPerfectPairing.finTwoToBilin_apply,
      MultilinearMap.currySum_apply', MultilinearMap.domDomCongr_apply,
      SymmetricPerfectPairing.separatingLabelsEquiv, correlator_apply,
      Fintype.prod_option, x₀, y₀]
    congr 1 <;> congr 1 <;> ac_rfl
  rw [hform]
  change TensorProduct.lift
      (((LinearMap.mul R R).comp (F.pairing.toDual x₀)).compl₂
        (F.pairing.toDual y₀)) F.casimir = _
  rw [F.sewing_identity]
  simp only [correlator_apply, Fintype.prod_sum_type]
  congr 1
  simp only [x₀, y₀, pow_add]
  ac_rfl

end CommFrobeniusAlgebra

end AxiomaticGW

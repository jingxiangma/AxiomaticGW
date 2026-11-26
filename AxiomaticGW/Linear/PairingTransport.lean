/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Linear.Contraction

/-!
# State transport for perfect metrics and contractions

A linear equivalence transports a metric and its canonical inverse tensor.
The tensor--endomorphism characterization proves that inverse-metric
contraction is independent of the state-space presentation. These theorems
supply the gluing step in `CohFT.comap` and the GKM basis adapter.
-/

@[expose] public section

namespace AxiomaticGW.SymmetricPerfectPairing
open TensorProduct
variable {R V W U : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup U] [Module R U]

/-- Pull a symmetric perfect metric back along a linear equivalence. -/
def comap (P : SymmetricPerfectPairing R V) (e : W ≃ₗ[R] V) :
    SymmetricPerfectPairing R W where
  form := P.form.compl₁₂ e.toLinearMap e.toLinearMap
  isSymm := ⟨fun x y ↦ P.isSymm.eq (e x) (e y)⟩
  isPerfPair := by
    letI : P.form.IsPerfPair := P.isPerfPair
    exact LinearMap.IsPerfPair.compl₁₂ P.form e e

/-- Both state inputs are transported by the same equivalence. -/
theorem comap_apply (P : SymmetricPerfectPairing R V) (e : W ≃ₗ[R] V) (x y : W) :
    (P.comap e).form x y = P.form (e x) (e y) := rfl

variable [Module.Free R V] [Module.Finite R V]
  [Module.Free R W] [Module.Finite R W]

/-- The metric identification of tensors with endomorphisms commutes with
transport of the tensor factors and the state being tested. -/
theorem tensorEndEquiv_map_comap (P : SymmetricPerfectPairing R V)
    (e : W ≃ₗ[R] V) (t : W ⊗[R] W) (w : W) :
    P.tensorEndEquiv (TensorProduct.map e.toLinearMap e.toLinearMap t) (e w) =
      e ((P.comap e).tensorEndEquiv t w) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul x y =>
      simp only [TensorProduct.map_tmul, tensorEndEquiv_tmul, comap_apply,
        LinearEquiv.map_smul, LinearEquiv.coe_coe]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

/-- Transporting the inverse metric tensor recovers the original copairing. -/
theorem map_copairing_comap (P : SymmetricPerfectPairing R V) (e : W ≃ₗ[R] V) :
    TensorProduct.map e.toLinearMap e.toLinearMap (P.comap e).copairing = P.copairing := by
  apply P.tensorEndEquiv.injective
  ext v
  obtain ⟨w, rfl⟩ := e.surjective v
  rw [tensorEndEquiv_map_comap, copairing_contract, copairing_contract]

/-- Contraction of two transformed states is independent of the chosen basis,
including for cohomology-valued outputs. -/
theorem contractTwoTarget_compLinearEquiv (P : SymmetricPerfectPairing R V)
    (e : W ≃ₗ[R] V) (f : MultilinearMap R (fun _ : Fin 2 ↦ V) U) :
    (P.comap e).contractTwoTarget (f.compLinearMap (fun _ ↦ e.toLinearMap)) =
      P.contractTwoTarget f := by
  rw [contractTwoTarget_apply, contractTwoTarget_apply, ← P.map_copairing_comap e]
  induction (P.comap e).copairing using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
      simp only [TensorProduct.lift.tmul, TensorProduct.map_tmul,
        finTwoToLinearTarget_apply, MultilinearMap.compLinearMap_apply]
      congr 1
      funext i
      fin_cases i <;> rfl
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Nonseparating contraction commutes with transport of every state input. -/
theorem selfContractTarget_compLinearEquiv (P : SymmetricPerfectPairing R V)
    (e : W ≃ₗ[R] V) {S : Type*}
    (f : MultilinearMap R (fun _ : S ⊕ Fin 2 ↦ V) U) :
    (P.comap e).selfContractTarget (f.compLinearMap (fun _ ↦ e.toLinearMap)) =
      (P.selfContractTarget f).compLinearMap (fun _ ↦ e.toLinearMap) := by
  ext a
  simp only [selfContractTarget_apply, MultilinearMap.compLinearMap_apply]
  rw [← P.contractTwoTarget_compLinearEquiv e]
  congr 1
  ext b
  simp only [MultilinearMap.currySum_apply', MultilinearMap.compLinearMap_apply]
  congr 1
  funext i
  cases i <;> rfl

/-- Separating contraction commutes with the same state transport on both
components and on all remaining labels. -/
theorem pairContractTarget_compLinearEquiv (P : SymmetricPerfectPairing R V)
    (e : W ≃ₗ[R] V) {S T U₁ U₂ : Type*}
    [AddCommGroup U₁] [Module R U₁] [AddCommGroup U₂] [Module R U₂]
    (f : MultilinearMap R (fun _ : Option S ↦ V) U₁)
    (g : MultilinearMap R (fun _ : Option T ↦ V) U₂) :
    (P.comap e).pairContractTarget
        (f.compLinearMap (fun _ ↦ e.toLinearMap))
        (g.compLinearMap (fun _ ↦ e.toLinearMap)) =
      (P.pairContractTarget f g).compLinearMap (fun _ ↦ e.toLinearMap) := by
  rw [pairContractTarget, pairContractTarget, ← selfContractTarget_compLinearEquiv]
  congr 1

end AxiomaticGW.SymmetricPerfectPairing

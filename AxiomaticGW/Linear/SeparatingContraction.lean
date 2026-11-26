/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Linear.Contraction

/-!
# Separating contraction with linear scalar functionals

Integration is linear but usually not multiplicative. This module uses the
tensor product of two linear functionals to scalarize a separating
contraction. No algebra homomorphism structure is required on either
functional, and the targets need only be modules.
-/

@[expose] public section

namespace AxiomaticGW.SymmetricPerfectPairing

open TensorProduct

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V]

/-- Scalarizing a separating contraction by two linear functionals equals
contracting the separately scalarized maps. The scalar multiplication map
is applied after the ordinary tensor product of the functionals. -/
theorem pairContractTarget_comp_map
    {W₁ W₂ : Type*} [AddCommGroup W₁] [Module R W₁]
    [AddCommGroup W₂] [Module R W₂]
    (P : SymmetricPerfectPairing R V) {S T : Type*}
    (f : MultilinearMap R (fun _ : Option S ↦ V) W₁)
    (g : MultilinearMap R (fun _ : Option T ↦ V) W₂)
    (φ : W₁ →ₗ[R] R) (ψ : W₂ →ₗ[R] R) :
    ((LinearMap.mul' R R).comp (TensorProduct.map φ ψ)).compMultilinearMap
        (P.pairContractTarget f g) =
      P.pairContract (φ.compMultilinearMap f) (ψ.compMultilinearMap g) := by
  rw [pairContractTarget, selfContractTarget_comp]
  rfl

end AxiomaticGW.SymmetricPerfectPairing

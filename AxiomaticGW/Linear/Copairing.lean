/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
import AxiomaticGW.Linear.PerfectPairing
import Mathlib.LinearAlgebra.Contraction

/-!
# Canonical copairings

The copairing is the inverse image of the identity under the canonical
equivalence `V tensor V ~= End(V)` induced by a symmetric perfect pairing.
-/

namespace AxiomaticGW

open Module TensorProduct

namespace SymmetricPerfectPairing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V]

/-- Contract the first tensor factor using the metric, identifying
`V tensor V` with `End(V)`. -/
noncomputable def tensorEndEquiv (P : SymmetricPerfectPairing R V) :
    V ⊗[R] V ≃ₗ[R] Module.End R V :=
  (TensorProduct.congr P.toDual (LinearEquiv.refl R V)).trans
    (dualTensorHomEquiv R V V)

@[simp]
theorem tensorEndEquiv_tmul (P : SymmetricPerfectPairing R V) (x y z : V) :
    P.tensorEndEquiv (x ⊗ₜ[R] y) z = P.form x z • y := by
  simp [tensorEndEquiv]

/-- The inverse metric tensor, characterized by contraction to the identity
endomorphism. -/
noncomputable def copairing (P : SymmetricPerfectPairing R V) : V ⊗[R] V :=
  P.tensorEndEquiv.symm LinearMap.id

@[simp]
theorem tensorEndEquiv_copairing (P : SymmetricPerfectPairing R V) :
    P.tensorEndEquiv P.copairing = LinearMap.id := by
  simp [copairing]

@[simp]
theorem copairing_contract (P : SymmetricPerfectPairing R V) (x : V) :
    P.tensorEndEquiv P.copairing x = x := by
  simp

end SymmetricPerfectPairing

end AxiomaticGW

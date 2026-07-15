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

## Reading the Lean notation

* `V ⊗[R] V` is the tensor product over `R`.
* `x ⊗ₜ[R] y` is a pure tensor inside that tensor product.
* `Module.End R V` abbreviates the type of `R`-linear endomorphisms of `V`.
* `r • y` is scalar multiplication of `y` by `r`.
* The hypotheses `Module.Free` and `Module.Finite` provide the finite-free
  duality needed for `Vᵛ ⊗ V ≃ End(V)`.
-/

namespace AxiomaticGW

open Module TensorProduct

namespace SymmetricPerfectPairing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V]

/-- Contract the first tensor factor using the metric, identifying
`V tensor V` with `End(V)`.

The displayed definition is a composition of two equivalences.  First
`P.toDual` changes the first copy of `V` into `Vᵛ`.  Then mathlib's
`dualTensorHomEquiv` identifies `Vᵛ ⊗ V` with linear endomorphisms of `V`. -/
noncomputable def tensorEndEquiv (P : SymmetricPerfectPairing R V) :
    V ⊗[R] V ≃ₗ[R] Module.End R V :=
  -- Apply the metric isomorphism to the first tensor factor and do nothing to
  -- the second tensor factor.
  (TensorProduct.congr P.toDual (LinearEquiv.refl R V)).trans
    -- Interpret a dual vector tensored with a vector as a rank-one map.
    (dualTensorHomEquiv R V V)

/-- On a pure tensor, the associated endomorphism sends `z` to
`P.form x z • y`.  This formula fixes our convention for which tensor leg is
contracted. -/
@[simp]
theorem tensorEndEquiv_tmul (P : SymmetricPerfectPairing R V) (x y z : V) :
    P.tensorEndEquiv (x ⊗ₜ[R] y) z = P.form x z • y := by
  simp [tensorEndEquiv]

/-- The inverse metric tensor, characterized by contraction to the identity
endomorphism.

`P.tensorEndEquiv.symm` is the inverse direction of the equivalence.  Applying
it to `LinearMap.id` therefore gives the unique tensor whose contraction is
the identity map. -/
noncomputable def copairing (P : SymmetricPerfectPairing R V) : V ⊗[R] V :=
  P.tensorEndEquiv.symm LinearMap.id

/-- The defining universal property of the copairing: mapping it forward gives
the identity endomorphism. -/
@[simp]
theorem tensorEndEquiv_copairing (P : SymmetricPerfectPairing R V) :
    P.tensorEndEquiv P.copairing = LinearMap.id := by
  simp [copairing]

/-- The preceding endomorphism equality evaluated at a vector `x`.  In basis
notation, if `copairing = ∑ᵢ uᵢ ⊗ vᵢ`, this says
`∑ᵢ P.form uᵢ x • vᵢ = x`. -/
@[simp]
theorem copairing_contract (P : SymmetricPerfectPairing R V) (x : V) :
    P.tensorEndEquiv P.copairing x = x := by
  simp

end SymmetricPerfectPairing

end AxiomaticGW

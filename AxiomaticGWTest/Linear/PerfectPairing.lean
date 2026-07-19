/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Linear.PerfectPairing

-- Regression-test declarations are intentionally not part of the public library API.
set_option linter.privateModule false

/-!
# Regression tests for symmetric perfect pairings

These tests exercise `AxiomaticGW.Linear.PerfectPairing` only through its
public API. In particular, the abstract tests deliberately assume neither
`Module.Free` nor `Module.Finite`.
-/

noncomputable section

namespace AxiomaticGWTest
namespace LinearPerfectPairing

/-! ## Abstract public-API tests -/

section AbstractAPI

open AxiomaticGW

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable (P : SymmetricPerfectPairing R V) (x y : V)

-- The form field is a bilinear form with the advertised source and target.
example : LinearMap.BilinForm R V := P.form

-- Symmetry and perfectness are stored proofs about that same form.
example : P.form.IsSymm := P.isSymm
example : P.form.IsPerfPair := P.isPerfPair

-- `toDual` is an equivalence from `V` to its `R`-linear dual.
example : V ≃ₗ[R] Module.Dual R V := P.toDual

-- One application produces a dual vector; two applications produce a scalar.
example : Module.Dual R V := P.toDual x
example : R := P.toDual x y

-- Dot notation exposes the public evaluation theorem and fixes the first-slot convention.
example : P.toDual x y = P.form x y := P.toDual_apply x y

-- The fully qualified theorem name works from outside the source namespace as well.
example : P.toDual x y = P.form x y :=
  AxiomaticGW.SymmetricPerfectPairing.toDual_apply P x y

-- As linear maps, the forward map of `toDual` is exactly the curried form.
example : P.toDual.toLinearMap = P.form := by
  ext u v
  exact P.toDual_apply u v

-- Perfectness is usable through the public equivalence, without finite/free assumptions.
example {u v : V} (h : ∀ w, P.form u w = P.form v w) : u = v := by
  apply P.toDual.injective
  apply LinearMap.ext
  intro w
  simpa only [P.toDual_apply] using h w

-- Every dual functional has the expected preimage under the public equivalence.
example (f : Module.Dual R V) : P.toDual (P.toDual.symm f) = f :=
  P.toDual.apply_symm_apply f

-- The stored class-valued proof can be installed locally for direct mathlib API use.
example : Function.Bijective P.form := by
  letI : P.form.IsPerfPair := P.isPerfPair
  exact LinearMap.IsPerfPair.bijective_left P.form

-- Symmetry also yields the reversed-looking formula; hence symmetric values alone
-- cannot distinguish the slot convention. The preceding first-slot theorem does.
example : P.toDual x y = P.form y x := by
  rw [P.toDual_apply]
  exact P.isSymm.eq x y

end AbstractAPI

/-! ## Zero-module boundary regression -/

-- On the zero module, the zero form is symmetric and both induced dual maps are bijective.
def zeroModulePairing (R : Type*) [CommRing R] :
    AxiomaticGW.SymmetricPerfectPairing R (Fin 0 → R) where
  form := 0
  isSymm := LinearMap.BilinForm.isSymm_zero
  isPerfPair := by
    constructor
    · constructor
      · intro u v _
        exact Subsingleton.elim u v
      · intro f
        exact ⟨0, Subsingleton.elim _ f⟩
    · constructor
      · intro u v _
        exact Subsingleton.elim u v
      · intro f
        exact ⟨0, Subsingleton.elim _ f⟩

-- The concrete stored form evaluates to zero, as the zero-module mathematics requires.
example (R : Type*) [CommRing R] (x y : Fin 0 → R) :
    (zeroModulePairing R).form x y = 0 := by
  simp only [zeroModulePairing, LinearMap.zero_apply]

-- Public `toDual_apply` transfers the same computation to the derived equivalence.
example (R : Type*) [CommRing R] (x y : Fin 0 → R) :
    (zeroModulePairing R).toDual x y = 0 := by
  rw [AxiomaticGW.SymmetricPerfectPairing.toDual_apply]
  simp only [zeroModulePairing, LinearMap.zero_apply]

-- Even in the degenerate zero-dimensional boundary case, `toDual` is bijective.
example (R : Type*) [CommRing R] :
    Function.Bijective (zeroModulePairing R).toDual :=
  (zeroModulePairing R).toDual.bijective

end LinearPerfectPairing
end AxiomaticGWTest

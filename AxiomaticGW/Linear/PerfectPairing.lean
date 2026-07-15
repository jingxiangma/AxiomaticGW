/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Symmetric perfect pairings

A small bundled interface for the metric on a CohFT state space.  Perfectness
is expressed using mathlib's `LinearMap.IsPerfPair`.
-/

namespace AxiomaticGW

open Module

/-- A symmetric bilinear form whose two induced maps to the dual are
equivalences.  This is explicit data rather than a typeclass because one module
may carry several metrics. -/
structure SymmetricPerfectPairing (R V : Type*) [CommRing R] [AddCommGroup V]
    [Module R V] where
  form : LinearMap.BilinForm R V
  isSymm : form.IsSymm
  isPerfPair : form.IsPerfPair

namespace SymmetricPerfectPairing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The equivalence between a module and its dual induced by a perfect
pairing. -/
noncomputable def toDual (P : SymmetricPerfectPairing R V) :
    V ≃ₗ[R] Dual R V := by
  letI : P.form.IsPerfPair := P.isPerfPair
  exact P.form.toPerfPair

@[simp]
theorem toDual_apply (P : SymmetricPerfectPairing R V) (x y : V) :
    P.toDual x y = P.form x y := by
  simp [toDual]

end SymmetricPerfectPairing

end AxiomaticGW

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
import AxiomaticGW.Frobenius.Basic
import AxiomaticGW.Linear.Copairing

/-!
# Constructions from commutative Frobenius algebras
-/

namespace AxiomaticGW

open TensorProduct

namespace CommFrobeniusAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Construct a Frobenius algebra from an invariant perfect pairing. -/
def ofInvariantPairing (form : LinearMap.BilinForm R A)
    (isPerfPair : form.IsPerfPair)
    (invariant : ∀ a b c : A, form (a * b) c = form a (b * c)) :
    CommFrobeniusAlgebra R A where
  counit := form.flip 1
  isPerfPair := by
    have hform : tracePairing (form.flip 1) = form := by
      ext a b
      simpa using invariant a b 1
    rw [hform]
    exact isPerfPair

@[simp]
theorem ofInvariantPairing_counit (form : LinearMap.BilinForm R A)
    (isPerfPair : form.IsPerfPair)
    (invariant : ∀ a b c : A, form (a * b) c = form a (b * c)) (a : A) :
    (ofInvariantPairing form isPerfPair invariant).counit a = form a 1 := rfl

@[simp]
theorem pairing_ofInvariantPairing (form : LinearMap.BilinForm R A)
    (isPerfPair : form.IsPerfPair)
    (invariant : ∀ a b c : A, form (a * b) c = form a (b * c)) :
    (ofInvariantPairing form isPerfPair invariant).pairing.form = form := by
  ext a b
  simpa using invariant a b 1

section FiniteFree

variable [Module.Free R A] [Module.Finite R A]

/-- The Casimir tensor of a Frobenius algebra. -/
noncomputable def casimir (F : CommFrobeniusAlgebra R A) : A ⊗[R] A :=
  F.pairing.copairing

@[simp]
theorem tensorEndEquiv_casimir (F : CommFrobeniusAlgebra R A) :
    F.pairing.tensorEndEquiv F.casimir = LinearMap.id := by
  simp [casimir]

/-- The handle (Euler) element, obtained by multiplying the two legs of the
Casimir tensor. -/
noncomputable def handleElement (F : CommFrobeniusAlgebra R A) : A :=
  LinearMap.mul' R A F.casimir

end FiniteFree

end CommFrobeniusAlgebra

end AxiomaticGW

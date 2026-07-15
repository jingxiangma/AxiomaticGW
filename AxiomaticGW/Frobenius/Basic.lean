/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
import AxiomaticGW.Linear.PerfectPairing
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Commutative Frobenius algebras

The primitive datum is a Frobenius functional `counit : A -> R`.  Its trace
pairing is required to be perfect; symmetry and Frobenius invariance are
derived theorems.
-/

namespace AxiomaticGW

/-- The bilinear trace pairing associated to a linear functional. -/
def tracePairing {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (counit : A →ₗ[R] R) : LinearMap.BilinForm R A :=
  (LinearMap.mul R A).compr₂ counit

@[simp]
theorem tracePairing_apply {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (counit : A →ₗ[R] R) (a b : A) :
    tracePairing counit a b = counit (a * b) := rfl

/-- A commutative Frobenius algebra, presented by its Frobenius functional. -/
structure CommFrobeniusAlgebra (R A : Type*) [CommRing R] [CommRing A]
    [Algebra R A] where
  counit : A →ₗ[R] R
  isPerfPair : (tracePairing counit).IsPerfPair

namespace CommFrobeniusAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

@[ext]
theorem ext {F G : CommFrobeniusAlgebra R A} (h : F.counit = G.counit) : F = G := by
  cases F
  cases G
  simp_all

/-- The symmetric perfect pairing underlying a commutative Frobenius
algebra. -/
def pairing (F : CommFrobeniusAlgebra R A) : SymmetricPerfectPairing R A where
  form := tracePairing F.counit
  isSymm := ⟨fun a b => by simp [mul_comm]⟩
  isPerfPair := F.isPerfPair

@[simp]
theorem pairing_apply (F : CommFrobeniusAlgebra R A) (a b : A) :
    F.pairing.form a b = F.counit (a * b) := rfl

theorem pairing_isSymm (F : CommFrobeniusAlgebra R A) :
    F.pairing.form.IsSymm := F.pairing.isSymm

/-- Frobenius invariance of the trace pairing. -/
theorem pairing_assoc (F : CommFrobeniusAlgebra R A) (a b c : A) :
    F.pairing.form (a * b) c = F.pairing.form a (b * c) := by
  simp only [pairing_apply, mul_assoc]

end CommFrobeniusAlgebra

end AxiomaticGW

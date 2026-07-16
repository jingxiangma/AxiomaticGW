/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.TFT.Frobenius

/-!
# Recovering Frobenius data from topological correlators

The one-point correlator recovers the Frobenius counit. The three-point
correlator, with its last input converted through the perfect metric, recovers
a bilinear product on the state space.

The existing `CommFrobeniusAlgebra` structure is parameterized by pre-existing
`CommRing` and `Algebra` typeclasses. Consequently, installing a product
recovered on a bare module as a new ring instance is a separate foundational
task. This file also provides the reverse construction when those algebra
typeclasses are already present and the recovered trace pairing is compatible
with them.
-/

@[expose] public section

namespace AxiomaticGW

namespace TopologicalCorrelatorTheory

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V]

/-- The three-point correlator, curried into three successive linear maps. -/
noncomputable def threePointFunctional (T : TopologicalCorrelatorTheory R V) :
    V →ₗ[R] V →ₗ[R] V →ₗ[R] R :=
  (LinearMap.compRight R
    (SymmetricPerfectPairing.finTwoToBilin (R := R) (V := V))).comp
    (multilinearCurryLeftEquiv R (fun _ : Fin 3 ↦ V) R).toLinearMap <|
    T.correlator 0 (Fin 3)

/-- Evaluation of the curried three-point functional. -/
@[simp]
theorem threePointFunctional_apply (T : TopologicalCorrelatorTheory R V)
    (x y z : V) :
    T.threePointFunctional x y z =
      T.correlator 0 (Fin 3) (Fin.cons x (Fin.cons y fun _ ↦ z)) := by
  simp [threePointFunctional]

/-- The product recovered from the three-point correlator by raising its last
index with the inverse metric. -/
noncomputable def product (T : TopologicalCorrelatorTheory R V) :
    V →ₗ[R] V →ₗ[R] V :=
  (LinearMap.compRight R
      (LinearMap.compRight R T.pairing.toDual.symm.toLinearMap)).comp
    ((LinearMap.compRight R
      (SymmetricPerfectPairing.finTwoToBilin (R := R) (V := V))).comp
      (multilinearCurryLeftEquiv R (fun _ : Fin 3 ↦ V) R).toLinearMap) <|
    T.correlator 0 (Fin 3)

/-- The recovered product is characterized by the original three-point
correlator. -/
theorem pairing_product (T : TopologicalCorrelatorTheory R V) (x y z : V) :
    T.pairing.form (T.product x y) z = T.threePointFunctional x y z := by
  rw [← T.pairing.toDual_apply]
  simp [product, threePointFunctional]

end TopologicalCorrelatorTheory

section ExistingAlgebra

namespace TopologicalCorrelatorTheory

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]

/-- Compatibility required to interpret a correlator theory on an already
existing algebra as a `CommFrobeniusAlgebra`. -/
def IsTraceCompatible (T : TopologicalCorrelatorTheory R A) : Prop :=
  ∀ x y : A, T.counit (x * y) = T.pairing.form x y

/-- Recover a Frobenius algebra on an existing commutative algebra when its
multiplication is compatible with the correlator counit and metric. -/
noncomputable def toCommFrobeniusAlgebra
    (T : TopologicalCorrelatorTheory R A) (h : T.IsTraceCompatible) :
    CommFrobeniusAlgebra R A where
  counit := T.counit
  isPerfPair := by
    have hform : tracePairing T.counit = T.pairing.form := by
      ext x y
      exact h x y
    rw [hform]
    exact T.pairing.isPerfPair

end TopologicalCorrelatorTheory

end ExistingAlgebra

namespace CommFrobeniusAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]

/-- The one-point correlator of the theory associated to `F` recovers its
original counit. -/
theorem toTopologicalCorrelatorTheory_counit
    (F : CommFrobeniusAlgebra R A) :
    F.toTopologicalCorrelatorTheory.counit = F.counit := by
  ext x
  simp [TopologicalCorrelatorTheory.counit,
    toTopologicalCorrelatorTheory, correlator_apply]

/-- The three-point product recovered from the correlator theory of `F` is
the original algebra multiplication. -/
theorem toTopologicalCorrelatorTheory_product
    (F : CommFrobeniusAlgebra R A) (x y : A) :
    F.toTopologicalCorrelatorTheory.product x y = x * y := by
  apply F.pairing.toDual.injective
  apply LinearMap.ext
  intro z
  rw [F.pairing.toDual_apply]
  change F.toTopologicalCorrelatorTheory.pairing.form
      (F.toTopologicalCorrelatorTheory.product x y) z =
    F.pairing.form (x * y) z
  rw [F.toTopologicalCorrelatorTheory.pairing_product]
  simp [TopologicalCorrelatorTheory.threePointFunctional,
    toTopologicalCorrelatorTheory, correlator_apply, mul_assoc]

/-- The forward correlator theory satisfies trace compatibility with the
original algebra. -/
theorem toTopologicalCorrelatorTheory_isTraceCompatible
    (F : CommFrobeniusAlgebra R A) :
    F.toTopologicalCorrelatorTheory.IsTraceCompatible := by
  intro x y
  rw [F.toTopologicalCorrelatorTheory_counit]
  exact F.pairing_apply x y

/-- Recovering the Frobenius structure from its associated correlator theory
returns the original structure. -/
theorem toCommFrobeniusAlgebra_toTopologicalCorrelatorTheory
    (F : CommFrobeniusAlgebra R A) :
    F.toTopologicalCorrelatorTheory.toCommFrobeniusAlgebra
        F.toTopologicalCorrelatorTheory_isTraceCompatible = F := by
  apply CommFrobeniusAlgebra.ext
  change F.toTopologicalCorrelatorTheory.counit = F.counit
  exact F.toTopologicalCorrelatorTheory_counit

end CommFrobeniusAlgebra

end AxiomaticGW

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW

/-!
# API regression tests

These examples check that the public import and local-instance interfaces work
as intended. They are deliberately kept outside the production library.
-/

namespace AxiomaticGWTest

open AxiomaticGW TensorProduct

namespace CommFrobeniusAlgebra

/-- The canonical coalgebra can be installed locally without choosing a global
Frobenius structure. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) (a : A) :
    letI : Coalgebra R A := F.toCoalgebra
    Coalgebra.counit (R := R) (A := A) a = F.counit a := by
  rfl

/-- The cocommutativity proof is compatible with the locally installed coalgebra. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) (a : A) :
    TensorProduct.comm R A A (F.comul a) = F.comul a := by
  letI : Coalgebra R A := F.toCoalgebra
  letI : Coalgebra.IsCocomm R A := F.toIsCocomm
  exact Coalgebra.comm_comul R a

/-- The rank-two example remains available through the project entry point. -/
example (R : Type*) [CommRing R] :
    (AxiomaticGW.CommFrobeniusAlgebra.productAlgebra R).handleElement = 1 := by
  simp

/-- The bundled correlator theory exposes the nonseparating gluing law. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) (g : ℕ) :
    F.pairing.selfContract (F.correlator g (Fin 1 ⊕ Fin 2)) =
      F.correlator (g + 1) (Fin 1) := by
  exact (F.toTopologicalCorrelatorTheory.nonseparating g (Fin 1))

/-- The bundled correlator theory exposes the separating gluing law. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) (g₁ g₂ : ℕ) :
    F.pairing.pairContract (F.correlator g₁ (Option (Fin 1)))
        (F.correlator g₂ (Option (Fin 1))) =
      F.correlator (g₁ + g₂) (Fin 1 ⊕ Fin 1) := by
  exact (F.toTopologicalCorrelatorTheory.separating g₁ g₂ (Fin 1) (Fin 1))

/-- The base-ring example computes every genus and finite arity. -/
example (R : Type*) [CommRing R] (g : ℕ) (a : Fin 3 → R) :
    (AxiomaticGW.CommFrobeniusAlgebra.baseRing R).correlator g (Fin 3) a =
      ∏ i, a i := by
  simp

/-- Restriction to stable arities preserves the underlying correlator. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) :
    F.toTopologicalCohFT.omega 0 (Fin 3) AxiomaticGW.StableArity.zero_fin_three =
      F.correlator 0 (Fin 3) := by
  rfl

/-- The three-point product extracted from the forward theory is the original
algebra multiplication. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (F : AxiomaticGW.CommFrobeniusAlgebra R A) (x y : A) :
    F.toTopologicalCorrelatorTheory.product x y = x * y := by
  exact F.toTopologicalCorrelatorTheory_product x y

end CommFrobeniusAlgebra

namespace FullCohFT

/-- The constant stable-curve system is concentrated in codimension zero. -/
example (r : ℚ) : r ∈ AxiomaticGW.constantDegree ℚ 0 := by
  simp [AxiomaticGW.constantDegree]

/-- Scalar topological correlators become the classes of the full CohFT over
the constant target. -/
example {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Free ℚ V] [Module.Finite ℚ V]
    (T : AxiomaticGW.TopologicalCohFT ℚ V) :
    T.toConstantCohFT.omega 0 (Fin 3) AxiomaticGW.StableArity.zero_fin_three =
      T.omega 0 (Fin 3) AxiomaticGW.StableArity.zero_fin_three := by
  rfl

/-- Relabelling is exposed by the converted full CohFT. -/
example {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Free ℚ V] [Module.Finite ℚ V]
    (T : AxiomaticGW.TopologicalCohFT ℚ V) (e : Fin 3 ≃ Fin 3) :
    ((AxiomaticGW.constantStableCurveCohomology ℚ).rename 0
      (Fin 3) (Fin 3) AxiomaticGW.StableArity.zero_fin_three
      AxiomaticGW.StableArity.zero_fin_three e).toLinearMap.compMultilinearMap
        ((T.toConstantCohFT.omega 0 (Fin 3)
          AxiomaticGW.StableArity.zero_fin_three).domDomCongr e) =
      T.toConstantCohFT.omega 0 (Fin 3)
        AxiomaticGW.StableArity.zero_fin_three := by
  exact T.toConstantCohFT.relabel 0 (Fin 3) (Fin 3)
    AxiomaticGW.StableArity.zero_fin_three
    AxiomaticGW.StableArity.zero_fin_three e

/-- The converted full CohFT exposes nonseparating gluing with a
cohomology-valued target. -/
example {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Free ℚ V] [Module.Finite ℚ V]
    (T : AxiomaticGW.TopologicalCohFT ℚ V) (g : ℕ) (S : Type) [Fintype S]
    (h : AxiomaticGW.StableArity (g + 1) S) :
    T.pairing.selfContractTarget
        ((T.toConstantCohFT.omega g (Option (Option S))
          (AxiomaticGW.StableArity.double_option_iff.mpr h)).domDomCongr
            (AxiomaticGW.doubleOptionEquiv S)) =
      LinearMap.compMultilinearMap
        ((AxiomaticGW.constantStableCurveCohomology ℚ).nonseparating g S h).toLinearMap
        (T.toConstantCohFT.omega (g + 1) S h) := by
  exact T.toConstantCohFT.nonseparating g S h

/-- Flat-unit insertion survives conversion to the full CohFT. -/
example {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Free ℚ V] [Module.Finite ℚ V]
    (T : AxiomaticGW.TopologicalCohFT ℚ V) (g : ℕ) (S : Type) [Fintype S]
    (h : AxiomaticGW.StableArity g S) (a : S → V) :
    T.toConstantCohFT.omega g (Option S) (AxiomaticGW.StableArity.option h)
        (fun | none => T.unit | some s => a s) =
      (AxiomaticGW.constantStableCurveCohomology ℚ).forget g S h
        (T.toConstantCohFT.omega g S h a) := by
  exact T.toConstantCohFT.unit_insert g S h a

/-- Separating gluing survives conversion to the tensor-valued full CohFT. -/
example {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Free ℚ V] [Module.Finite ℚ V]
    (T : AxiomaticGW.TopologicalCohFT ℚ V) (g₁ g₂ : ℕ)
    (S U : Type) [Fintype S] [Fintype U]
    (h₁ : AxiomaticGW.StableArity g₁ (Option S))
    (h₂ : AxiomaticGW.StableArity g₂ (Option U)) :
    T.pairing.pairContractTarget
        (T.toConstantCohFT.omega g₁ (Option S) h₁)
        (T.toConstantCohFT.omega g₂ (Option U) h₂) =
      LinearMap.compMultilinearMap
        ((AxiomaticGW.constantStableCurveCohomology ℚ).separating
          g₁ g₂ S U h₁ h₂).toLinearMap
        (T.toConstantCohFT.omega (g₁ + g₂) (S ⊕ U)
          (AxiomaticGW.StableArity.separating h₁ h₂)) := by
  exact T.toConstantCohFT.separating g₁ g₂ S U h₁ h₂

/-- Conversion to the full constant model and back preserves all scalar
correlators. -/
example {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Free ℚ V] [Module.Finite ℚ V]
    (T : AxiomaticGW.TopologicalCohFT ℚ V) (g : ℕ) (S : Type) [Fintype S]
    (h : AxiomaticGW.StableArity g S) :
    T.toConstantCohFT.toTopologicalCohFT.omega g S h = T.omega g S h := by
  simp

/-- The generic degree-zero construction specializes to the original
topological theory on the constant target. -/
example {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Free ℚ V] [Module.Finite ℚ V]
    (T : AxiomaticGW.TopologicalCohFT ℚ V) (g : ℕ) (S : Type) [Fintype S]
    (h : AxiomaticGW.StableArity g S) :
    (T.toConstantCohFT.topologicalPart
      (AxiomaticGW.constantStableCurveCohomology.connectedDegreeZero ℚ)).omega
        g S h = T.omega g S h := by
  simp

/-- The genus-zero product extracted from a topological CohFT is associative. -/
example {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Free ℚ V] [Module.Finite ℚ V]
    (T : AxiomaticGW.TopologicalCohFT ℚ V) (x y z : V) :
    let T₀ := T.toConstantCohFT.toGenusZeroCohFT
    let G := AxiomaticGW.constantStableCurveCohomology.genusZeroGeometry ℚ
    T₀.product G (T₀.product G x y) z = T₀.product G x (T₀.product G y z) := by
  exact T.toConstantCohFT.toGenusZeroCohFT.product_assoc
    (AxiomaticGW.constantStableCurveCohomology.genusZeroGeometry ℚ) x y z

/-- Frobenius reconstruction agrees with every stable correlator, in every
genus and finite label type. -/
example {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Free ℚ V] [Module.Finite ℚ V]
    (T : AxiomaticGW.TopologicalCohFT ℚ V) (g : ℕ) (S : Type) [Fintype S]
    (h : AxiomaticGW.StableArity g S) :
    ((T.toCommFrobeniusAlgebra.toTopologicalCohFT.omega g S h).compLinearMap
      (fun _ ↦ (AxiomaticGW.GenusZeroCohFT.FrobeniusCarrier.toStateSpace
        T.toConstantCohFT.toGenusZeroCohFT
        (AxiomaticGW.constantStableCurveCohomology.genusZeroGeometry ℚ)).symm.toLinearMap)) =
      T.omega g S h := by
  exact T.classification g S h

end FullCohFT

end AxiomaticGWTest

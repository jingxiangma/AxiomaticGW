/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.Relabel
public import AxiomaticGW.Tautological.LegPsiRealization
public import AxiomaticGW.GW.Basic

/-!
# Realization and certificate transport under external relabelling

Primitive naturality of raw graph maps gives the linear transport and
integrated evaluation laws. CohFT/GW naturality then determines the exact
transport of state insertions, with the full curve class unchanged.
-/

@[expose] public section

namespace AxiomaticGW

namespace RelationCertificate

/-- Label transport retains the original exact coordinate weights. -/
theorem relabel_interpret {g n : ℕ} {S T : Type} [Fintype S] [Fintype T]
    (e : S ≃ T) (columns : Fin n → TautologicalStratum g S) (x : Coordinates n) :
    StrataModule.relabel e (interpret columns x) =
      interpret (fun i ↦ (columns i).relabel e) x := by
  simp only [interpret_apply, map_sum, map_smul, StrataModule.relabel_basis]

end RelationCertificate

namespace StrataRealization

universe u

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {g : ℕ} {S T : Type} [Fintype S] [Fintype T]

attribute [local instance] strataRealizationModule

/-- Raw graph maps are natural under the covariant external label transport. -/
def RelabelCompatible (A : StrataRealization C g S) (B : StrataRealization C g T)
    (hS : StableArity g S) (hT : StableArity g T) (e : S ≃ T) : Prop :=
  ∀ x, B.map (StrataModule.basis (x.relabel e)) =
    C.rename g S T hS hT e (A.map (StrataModule.basis x))

/-- Basis-level naturality extends to every rational combination. -/
theorem map_relabel (A : StrataRealization C g S) (B : StrataRealization C g T)
    (hS : StableArity g S) (hT : StableArity g T) (e : S ≃ T)
    (hAB : A.RelabelCompatible B hS hT e) (r : StrataModule g S) :
    B.map (StrataModule.relabel e r) = C.rename g S T hS hT e (A.map r) := by
  have heq : B.map.comp (StrataModule.relabel e) =
      (((C.rename g S T hS hT e).toLinearMap).restrictScalars ℚ).comp A.map := by
    apply Finsupp.lhom_ext
    intro x q
    have hs : Finsupp.single x q = q • StrataModule.basis x := by
      simp only [StrataModule.basis, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs]
    simp only [LinearMap.comp_apply, map_smul, StrataModule.relabel_basis]
    exact congrArg (fun y : C.H g T ↦ q • y) (hAB x)
  exact congrArg (fun f ↦ f r) heq

/-- Relabelling preserves the realization kernel without changing the row. -/
theorem relabel_mem_kernel (A : StrataRealization C g S) (B : StrataRealization C g T)
    (hS : StableArity g S) (hT : StableArity g T) (e : S ≃ T)
    (hAB : A.RelabelCompatible B hS hT e) {r : StrataModule g S}
    (hr : r ∈ A.kernel) : StrataModule.relabel e r ∈ B.kernel := by
  rw [B.mem_kernel_iff, A.map_relabel B hS hT e hAB,
    (A.mem_kernel_iff r).mp hr, map_zero]

/-- Transporting both the graph and held insertion preserves its integral. -/
theorem integrateAgainst_relabel (A : StrataRealization C g S)
    (B : StrataRealization C g T) (I : StableCurveIntegration C)
    (hS : StableArity g S) (hT : StableArity g T) (e : S ≃ T)
    (hAB : A.RelabelCompatible B hS hT e) (w : C.H g S) (r : StrataModule g S) :
    B.integrateAgainst I hT (C.rename g S T hS hT e w) (StrataModule.relabel e r) =
      A.integrateAgainst I hS w r := by
  rw [integrateAgainst_apply, integrateAgainst_apply, A.map_relabel B hS hT e hAB,
    ← map_mul, I.integrate_rename]

/-- State insertions are pulled back by the same label bijection as the graph. -/
theorem integrateAgainst_relabel_cohFT {V : Type u}
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (A : StrataRealization C g S) (B : StrataRealization C g T)
    (I : StableCurveIntegration C) (hS : StableArity g S) (hT : StableArity g T)
    (e : S ≃ T) (hAB : A.RelabelCompatible B hS hT e) (Omega : CohFT R V C)
    (a : T → V) (r : StrataModule g S) :
    B.integrateAgainst I hT (Omega.omega g T hT a) (StrataModule.relabel e r) =
      A.integrateAgainst I hS (Omega.omega g S hS (a ∘ e)) r := by
  have hrel := congrArg (fun f ↦ f a) (Omega.relabel g S T hS hT e)
  simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.domDomCongr_apply] at hrel
  change C.rename g S T hS hT e (Omega.omega g S hS (a ∘ e)) =
    Omega.omega g T hT a at hrel
  rw [← hrel, A.integrateAgainst_relabel B I hS hT e hAB]

/-- GW label transport preserves the full class and reindexes all states. -/
theorem integrateAgainst_relabel_gw {V Bclass : Type u}
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid Bclass] {D : EffectiveCurveMonoid Bclass}
    (A : StrataRealization C g S) (B : StrataRealization C g T)
    (I : StableCurveIntegration C) (hS : StableArity g S) (hT : StableArity g T)
    (e : S ≃ T) (hAB : A.RelabelCompatible B hS hT e)
    (Omega : GromovWittenTheory R V Bclass D C) (beta : Bclass)
    (a : T → V) (r : StrataModule g S) :
    B.integrateAgainst I hT (Omega.omega g T hT beta a) (StrataModule.relabel e r) =
      A.integrateAgainst I hS (Omega.omega g S hS beta (a ∘ e)) r := by
  have hrel := congrArg (fun f ↦ f a) (Omega.relabel g S T hS hT e beta)
  simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.domDomCongr_apply] at hrel
  change C.rename g S T hS hT e (Omega.omega g S hS beta (a ∘ e)) =
    Omega.omega g T hT beta a at hrel
  rw [← hrel, A.integrateAgainst_relabel B I hS hT e hAB]

/-- A checked original row witness gives the expanded relabelled integral. -/
theorem certificate_relabel_eq_zero {m n : ℕ} (A : StrataRealization C g S)
    (B : StrataRealization C g T) (I : StableCurveIntegration C)
    (hS : StableArity g S) (hT : StableArity g T) (e : S ≃ T)
    (hAB : A.RelabelCompatible B hS hT e) (w : C.H g T)
    (columns : Fin n → TautologicalStratum g S)
    (rows : Fin m → RelationCertificate.Coordinates n)
    (requested : RelationCertificate.Coordinates n)
    (certificate : RelationCertificate.Certificate m)
    (hcheck : RelationCertificate.check rows requested certificate = true)
    (hrows : ∀ row, A.map (RelationCertificate.interpret columns (rows row)) = 0) :
    (∑ i, requested i • I.integrate g T hT
      (w * B.map (StrataModule.basis ((columns i).relabel e)))) = 0 := by
  have hz := RelationCertificate.evaluation_eq_zero columns rows requested certificate hcheck
    ((B.integrateAgainst I hT w).comp (StrataModule.relabel e)) (by
      intro row
      rw [LinearMap.comp_apply, integrateAgainst_apply, A.map_relabel B hS hT e hAB,
        hrows row, map_zero, mul_zero, map_zero])
  simpa only [LinearMap.comp_apply, RelationCertificate.relabel_interpret,
    RelationCertificate.interpret_apply, map_sum, map_smul,
    StrataModule.relabel_basis, integrateAgainst_apply] using hz

end StrataRealization

end AxiomaticGW

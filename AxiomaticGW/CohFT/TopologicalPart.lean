/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.CohFT.Frobenius
public import AxiomaticGW.CohFT.Topological

/-!
# The topological part of a CohFT

Coherent connected degree-zero cohomology turns the degree-zero projection of
every CohFT class into a scalar-valued topological CohFT.
-/

@[expose] public section

namespace AxiomaticGW

namespace CohFT

variable {R V : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  {C : StableCurveCohomology R}

/-- Scalarize a CohFT class by projecting to connected degree-zero
cohomology. -/
noncomputable def scalarOmega (Ω : CohFT R V C) (D : ConnectedDegreeZero C)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) :
    MultilinearMap R (fun _ : S ↦ V) R :=
  (D.scalar g S h).toLinearMap.compMultilinearMap (Ω.omega g S h)

/-- Degree-zero scalarization is natural under relabelling. -/
theorem scalarOmega_relabel (Ω : CohFT R V C)
    (D : ConnectedDegreeZero C) (g : ℕ)
    (S T : Type) [Fintype S] [Fintype T]
    (hS : StableArity g S) (hT : StableArity g T) (e : S ≃ T) :
    (Ω.scalarOmega D g S hS).domDomCongr e = Ω.scalarOmega D g T hT := by
  ext a
  have hΩ := congrArg (fun f ↦ f a) (Ω.relabel g S T hS hT e)
  change C.rename g S T hS hT e (Ω.omega g S hS (a ∘ e)) =
    Ω.omega g T hT a at hΩ
  change D.scalar g S hS (Ω.omega g S hS (a ∘ e)) =
    D.scalar g T hT (Ω.omega g T hT a)
  calc
    D.scalar g S hS (Ω.omega g S hS (a ∘ e)) =
        D.scalar g T hT (C.rename g S T hS hT e
          (Ω.omega g S hS (a ∘ e))) :=
      (D.rename_scalar g S T hS hT e _).symm
    _ = D.scalar g T hT (Ω.omega g T hT a) := congrArg (D.scalar g T hT) hΩ

/-- The scalar-valued topological part of a CohFT. -/
noncomputable def topologicalPart (Ω : CohFT R V C)
    (D : ConnectedDegreeZero C) : TopologicalCohFT R V where
  pairing := Ω.pairing
  unit := Ω.unit
  omega := Ω.scalarOmega D
  relabel := scalarOmega_relabel Ω D
  unit_insert := by
    intro g S _ h a
    change D.scalar g (Option S) (StableArity.option h)
        (Ω.omega g (Option S) (StableArity.option h)
          (fun | none => Ω.unit | some s => a s)) =
      D.scalar g S h (Ω.omega g S h a)
    have hΩ := Ω.unit_insert g S h a
    calc
      D.scalar g (Option S) (StableArity.option h)
          (Ω.omega g (Option S) (StableArity.option h)
            (fun | none => Ω.unit | some s => a s)) =
        D.scalar g (Option S) (StableArity.option h)
          (C.forget g S h (Ω.omega g S h a)) := congrArg _ hΩ
      _ = D.scalar g S h (Ω.omega g S h a) := D.forget_scalar g S h _
  nonseparating := by
    intro g S _ h
    rw [← scalarOmega_relabel Ω D g (Option (Option S)) (S ⊕ Fin 2)
      (StableArity.double_option_iff.mpr h)
      (StableArity.sum_fin_two_iff.mpr h) (doubleOptionEquiv S)]
    simp only [scalarOmega]
    rw [LinearMap.compMultilinearMap_domDomCongr]
    rw [← Ω.pairing.selfContractTarget_comp]
    rw [Ω.nonseparating]
    all_goals
      ext a
      simp only [LinearMap.compMultilinearMap_apply]
      exact D.nonseparating_scalar g S h _
  separating := by
    intro g₁ g₂ S T _ _ h₁ h₂
    simp only [scalarOmega]
    rw [← Ω.pairing.pairContractTarget_comp_lift]
    rw [Ω.separating]
    ext a
    simp only [LinearMap.compMultilinearMap_apply]
    exact D.separating_scalar g₁ g₂ S T h₁ h₂ _
  normalization := by
    intro a
    change D.scalar 0 (Option (Fin 2)) StableArity.zero_option_fin_two
        (Ω.omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two
          (fun | none => Ω.unit | some i => a i)) = Ω.pairing.form (a 0) (a 1)
    have hΩ := Ω.normalization a
    calc
      D.scalar 0 (Option (Fin 2)) StableArity.zero_option_fin_two
          (Ω.omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two
            (fun | none => Ω.unit | some i => a i)) =
        D.scalar 0 (Option (Fin 2)) StableArity.zero_option_fin_two
          (algebraMap R (C.H 0 (Option (Fin 2)))
            (Ω.pairing.form (a 0) (a 1))) := congrArg _ hΩ
      _ = Ω.pairing.form (a 0) (a 1) := AlgHom.commutes _ _

end CohFT

end AxiomaticGW

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.CohFT.Basic
public import AxiomaticGW.Linear.PairingTransport

/-!
# Changing the state-space presentation of a full CohFT

The class-valued theory, including its flat unit and both gluing identities,
is transported along a linear equivalence. This supports fixed-point and
geometric basis presentations of the same imported GKM theory. It requires
an actual CohFT as input; numerical localization tables do not supply one.
-/

@[expose] public section

namespace AxiomaticGW.CohFT
variable {R V W : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCommGroup W] [Module R W] [Module.Free R W] [Module.Finite R W]
  {C : StableCurveCohomology R}

/-- Transport a full CohFT to another presentation of its state space.
The metric, copairing, and flat unit are derived from the equivalence; both
gluing laws are proved from the existing theory's laws. No new CohFT classes
or geometric comparisons are assumed by this construction. -/
noncomputable def comap (Ω : CohFT R V C) (e : W ≃ₗ[R] V) : CohFT R W C where
  pairing := Ω.pairing.comap e
  unit := e.symm Ω.unit
  omega := fun g S _ h ↦ (Ω.omega g S h).compLinearMap (fun _ ↦ e.toLinearMap)
  relabel := by
    intro g S T _ _ hS hT q
    ext a
    have h := congrArg (fun f ↦ f (fun t ↦ e (a t))) (Ω.relabel g S T hS hT q)
    simpa only [LinearMap.compMultilinearMap_apply, MultilinearMap.domDomCongr_apply,
      MultilinearMap.compLinearMap_apply, LinearEquiv.coe_coe] using h
  unit_insert := by
    intro g S _ h a
    change Ω.omega g (Option S) (StableArity.option h)
        (fun i ↦ e ((fun | none => e.symm Ω.unit | some s => a s) i)) = _
    have hstates : (fun i ↦ e ((fun | none => e.symm Ω.unit | some s => a s) i)) =
        (fun | none => Ω.unit | some s => e (a s)) := by
      funext i
      cases i <;> simp only [LinearEquiv.apply_symm_apply]
    exact (congrArg (Ω.omega g (Option S) (StableArity.option h)) hstates).trans
      (Ω.unit_insert g S h (fun s ↦ e (a s)))
  nonseparating := by
    intro g S _ h
    have hrename : ((Ω.omega g (Option (Option S))
          (StableArity.double_option_iff.mpr h)).compLinearMap
            (fun _ ↦ e.toLinearMap)).domDomCongr (doubleOptionEquiv S) =
        ((Ω.omega g (Option (Option S))
          (StableArity.double_option_iff.mpr h)).domDomCongr
            (doubleOptionEquiv S)).compLinearMap (fun _ ↦ e.toLinearMap) := by
      ext a
      rfl
    rw [hrename, Ω.pairing.selfContractTarget_compLinearEquiv, Ω.nonseparating]
    rfl
  separating := by
    intro g₁ g₂ S T _ _ h₁ h₂
    rw [Ω.pairing.pairContractTarget_compLinearEquiv, Ω.separating]
    rfl
  normalization := by
    intro a
    change Ω.omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two
        (fun i ↦ e ((fun | none => e.symm Ω.unit | some j => a j) i)) = _
    have hstates : (fun i ↦ e ((fun | none => e.symm Ω.unit | some j => a j) i)) =
        (fun | none => Ω.unit | some j => e (a j)) := by
      funext i
      cases i <;> simp only [LinearEquiv.apply_symm_apply]
    exact (congrArg (Ω.omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two)
      hstates).trans (Ω.normalization (fun j ↦ e (a j)))

/-- Class-valued correlators transform by applying the equivalence to every
insertion, with labels, genus, and the stable-curve target unchanged. -/
theorem comap_omega_apply (Ω : CohFT R V C) (e : W ≃ₗ[R] V)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (a : S → W) :
    (Ω.comap e).omega g S h a = Ω.omega g S h (fun s ↦ e (a s)) := rfl

/-- The metric of the transported theory is the pulled-back metric. -/
theorem comap_pairing_apply (Ω : CohFT R V C) (e : W ≃ₗ[R] V) (a b : W) :
    (Ω.comap e).pairing.form a b = Ω.pairing.form (e a) (e b) := rfl

/-- The transported flat unit restricts to the original flat unit. -/
theorem comap_unit_apply (Ω : CohFT R V C) (e : W ≃ₗ[R] V) :
    e (Ω.comap e).unit = Ω.unit := e.apply_symm_apply _

/-- Returning through the inverse state equivalence preserves every class. -/
theorem comap_omega_roundTrip (Ω : CohFT R V C) (e : W ≃ₗ[R] V)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (a : S → V) :
    ((Ω.comap e).comap e.symm).omega g S h a = Ω.omega g S h a := by
  simp only [comap_omega_apply, LinearEquiv.apply_symm_apply]

end AxiomaticGW.CohFT

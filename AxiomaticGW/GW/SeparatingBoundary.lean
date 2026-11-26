/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.CohFT.SeparatingPushforward
public import AxiomaticGW.GW.Descendants.Basic

/-!
# Curve-class-resolved separating boundary equations

The numerical equation follows from primary GW gluing, primitive proper
push-pull laws, and linear product integration. The sum retains every
effective ordered splitting of the full class. Source cotangent monomials
produce the existing ancestor invariants on the two components.
-/

@[expose] public section

namespace AxiomaticGW

open TensorProduct

universe u

namespace GromovWittenTheory

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

/-- Integrate the actual GW class in `beta` against raw pushforward of a
product decoration. The input is independent of how `beta` later splits. -/
def separatingInvariant (Omega : GromovWittenTheory R V B D C)
    (F : SeparatingPushforward C I) (g₁ g₂ : ℕ) (S T : Type)
    [Fintype S] [Fintype T]
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (beta : B) (x : C.H g₁ (Option S) ⊗[R] C.H g₂ (Option T)) :
    MultilinearMap R (fun _ : S ⊕ T ↦ V) R :=
  ((I.integrate (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂)).comp
    (LinearMap.mulRight R (F.push g₁ g₂ S T h₁ h₂ x))).compMultilinearMap
      (Omega.omega (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂) beta)

/-- The boundary integrand contains the entire class and pushed decoration. -/
theorem separatingInvariant_apply (Omega : GromovWittenTheory R V B D C)
    (F : SeparatingPushforward C I) (g₁ g₂ : ℕ) (S T : Type)
    [Fintype S] [Fintype T]
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (beta : B) (x : C.H g₁ (Option S) ⊗[R] C.H g₂ (Option T)) (a : S ⊕ T → V) :
    Omega.separatingInvariant F g₁ g₂ S T h₁ h₂ beta x a =
      I.integrate (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂)
        (Omega.omega (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂) beta a *
          F.push g₁ g₂ S T h₁ h₂ x) := rfl

/-- Gluing with any product decoration is a finite convolution of the
component class contractions, followed by the same decorated integral. -/
theorem separatingInvariant_eq_contraction (Omega : GromovWittenTheory R V B D C)
    (F : SeparatingPushforward C I) (g₁ g₂ : ℕ) (S T : Type)
    [Fintype S] [Fintype T]
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (beta : B) (x : C.H g₁ (Option S) ⊗[R] C.H g₂ (Option T)) :
    Omega.separatingInvariant F g₁ g₂ S T h₁ h₂ beta x =
      ∑ split ∈ D.splittings beta,
        ((I.tensorIntegral g₁ g₂ (Option S) (Option T) h₁ h₂).comp
          (LinearMap.mulRight R x)).compMultilinearMap
            (Omega.pairing.pairContractTarget
              (Omega.omega g₁ (Option S) h₁ split.1)
              (Omega.omega g₂ (Option T) h₂ split.2)) := by
  ext a
  rw [separatingInvariant_apply, F.integrate_mul_push]
  have hglue := congrArg (fun f ↦ f a) (Omega.separating g₁ g₂ S T h₁ h₂ beta)
  simp only [sum_apply, LinearMap.compMultilinearMap_apply, AlgHom.toLinearMap_apply] at hglue
  rw [← hglue, Finset.sum_mul, map_sum]
  simp only [sum_apply, LinearMap.compMultilinearMap_apply,
    LinearMap.comp_apply, LinearMap.mulRight_apply]

/-- A pure tensor decoration gives inverse-metric contraction of the two
separately integrated component families, for every full-class splitting. -/
theorem separatingInvariant_tmul (Omega : GromovWittenTheory R V B D C)
    (F : SeparatingPushforward C I) (g₁ g₂ : ℕ) (S T : Type)
    [Fintype S] [Fintype T]
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (beta : B) (x : C.H g₁ (Option S)) (y : C.H g₂ (Option T)) :
    Omega.separatingInvariant F g₁ g₂ S T h₁ h₂ beta (x ⊗ₜ[R] y) =
      ∑ split ∈ D.splittings beta,
        Omega.pairing.pairContract
          (((I.integrate g₁ (Option S) h₁).comp (LinearMap.mulRight R x)).compMultilinearMap
            (Omega.omega g₁ (Option S) h₁ split.1))
          (((I.integrate g₂ (Option T) h₂).comp (LinearMap.mulRight R y)).compMultilinearMap
            (Omega.omega g₂ (Option T) h₂ split.2)) := by
  rw [separatingInvariant_eq_contraction]
  apply Finset.sum_congr rfl
  intro split _
  rw [I.tensorIntegral_mul_tmul, Omega.pairing.pairContractTarget_comp_map]

/-- Source monomials retain all external and node powers in the component
ancestor invariants; no stable-map psi comparison is silently substituted. -/
theorem separatingInvariant_monomial (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (F : SeparatingPushforward C I)
    (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (beta : B) (k : Option S → ℕ) (l : Option T → ℕ) :
    Omega.separatingInvariant F g₁ g₂ S T h₁ h₂ beta
        (P.monomial g₁ (Option S) h₁ k ⊗ₜ[R] P.monomial g₂ (Option T) h₂ l) =
      ∑ split ∈ D.splittings beta,
        Omega.pairing.pairContract (Omega.ancestorInvariant P I g₁ (Option S) h₁ split.1 k)
          (Omega.ancestorInvariant P I g₂ (Option T) h₂ split.2 l) := by
  rw [separatingInvariant_tmul]
  rfl

end GromovWittenTheory

end AxiomaticGW

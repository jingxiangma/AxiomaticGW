/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.CohFT.NonseparatingPushforward
public import AxiomaticGW.GW.Descendants.Basic

/-!
# Curve-class-resolved nonseparating boundary equations

These equations follow from the existing primary GW gluing axiom and
primitive proper push-pull laws. They retain the entire effective class and
use the copairing of its perfect metric, without choosing a basis.
Cotangent decorations here are stable-curve ancestors, not stable-map
descendants. No recurrence or numerical surface value is assumed.
-/

@[expose] public section

namespace AxiomaticGW

universe u

namespace GromovWittenTheory

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

/-- Class-resolved boundary evaluation retains the full effective class;
nonseparating gluing does not split or replace it by its energy. -/
def nonseparatingInvariant (Omega : GromovWittenTheory R V B D C)
    (F : NonseparatingPushforward C I) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity (g + 1) S) (beta : B) (x : C.H g (Option (Option S))) :
    MultilinearMap R (fun _ : S ↦ V) R :=
  ((I.integrate (g + 1) S h).comp (LinearMap.mulRight R (F.push g S h x))).compMultilinearMap
    (Omega.omega (g + 1) S h beta)

/-- Evaluation in one curve class uses the actual GW class and pushforward. -/
theorem nonseparatingInvariant_apply (Omega : GromovWittenTheory R V B D C)
    (F : NonseparatingPushforward C I) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity (g + 1) S) (beta : B) (x : C.H g (Option (Option S))) (a : S → V) :
    Omega.nonseparatingInvariant F g S h beta x a =
      I.integrate (g + 1) S h (Omega.omega (g + 1) S h beta a * F.push g S h x) := rfl

/-- The curve-class-resolved nonseparating equation follows from the GW
gluing axiom and primitive proper push-pull laws. -/
theorem nonseparatingInvariant_eq_selfContract (Omega : GromovWittenTheory R V B D C)
    (F : NonseparatingPushforward C I) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity (g + 1) S) (beta : B) (x : C.H g (Option (Option S))) :
    Omega.nonseparatingInvariant F g S h beta x =
      Omega.pairing.selfContract
        (((I.integrate g (Option (Option S)) (StableArity.double_option_iff.mpr h)).comp
          (LinearMap.mulRight R x)).compMultilinearMap
            ((Omega.omega g (Option (Option S))
              (StableArity.double_option_iff.mpr h) beta).domDomCongr
              (doubleOptionEquiv S))) := by
  rw [← Omega.pairing.selfContractTarget_comp]
  ext a
  rw [nonseparatingInvariant_apply, F.integrate_mul_push]
  have hglue := congrArg (fun f ↦ f a) (Omega.nonseparating g S h beta)
  exact congrArg (fun y ↦ I.integrate g (Option (Option S))
    (StableArity.double_option_iff.mpr h) (y * x)) hglue.symm

/-- For a source psi monomial, the contraction uses the existing ancestor
invariant with every node and external power retained in the same class. -/
theorem nonseparatingInvariant_monomial (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (F : NonseparatingPushforward C I)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity (g + 1) S)
    (beta : B) (k : Option (Option S) → ℕ) :
    Omega.nonseparatingInvariant F g S h beta
        (P.monomial g (Option (Option S)) (StableArity.double_option_iff.mpr h) k) =
      Omega.pairing.selfContract
        ((Omega.ancestorInvariant P I g (Option (Option S))
          (StableArity.double_option_iff.mpr h) beta k).domDomCongr (doubleOptionEquiv S)) := by
  rw [nonseparatingInvariant_eq_selfContract]
  rfl

end GromovWittenTheory

end AxiomaticGW

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.CohFT.Ancestors

/-!
# Proper pushforward and nonseparating boundary evaluation

The primitive proper pushforward is independent of CohFT and GW classes.
Its projection and integration laws, together with the existing CohFT gluing
axiom, imply the boundary contraction equations below. The class-resolved GW
extension is in `GW/NonseparatingBoundary.lean`. No final numerical recurrence
is included as a field.

The map uses the ordered two-marking source and the raw pushforward of that
map. It is not normalized by a graph automorphism order. Stable-curve psi
decorations give ancestor boundary equations; a comparison with stable-map
descendants is a separate obligation.
-/

@[expose] public section

namespace AxiomaticGW

universe u

/-- Primitive proper pushforward along nonseparating gluing. These are
explicit geometric inputs, rather than a construction of moduli spaces. -/
structure NonseparatingPushforward {R : Type u} [CommRing R] [Algebra ℚ R]
    (C : StableCurveCohomology R) (I : StableCurveIntegration C) where
  /-- The two node markings are ordered in the source. -/
  push : ∀ (g : ℕ) (S : Type) [Fintype S] (_h : StableArity (g + 1) S),
    C.H g (Option (Option S)) →ₗ[R] C.H (g + 1) S
  /-- Relabelling the retained markings commutes with proper pushforward. -/
  push_rename : ∀ (g : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (hS : StableArity (g + 1) S) (hT : StableArity (g + 1) T) (e : S ≃ T),
    (push g T hT).comp
      (C.rename g (Option (Option S)) (Option (Option T))
        (StableArity.double_option_iff.mpr hS)
        (StableArity.double_option_iff.mpr hT) e.optionCongr.optionCongr).toLinearMap =
      (C.rename (g + 1) S T hS hT e).toLinearMap.comp (push g S hS)
  /-- The gluing map does not distinguish its two node branches. -/
  push_swap : ∀ (g : ℕ) (S : Type) [Fintype S] (h : StableArity (g + 1) S),
    (push g S h).comp
      (C.rename g (Option (Option S)) (Option (Option S))
        (StableArity.double_option_iff.mpr h)
        (StableArity.double_option_iff.mpr h) (swapDoubleOption S)).toLinearMap =
      push g S h
  /-- The source boundary has codimension one in the target. -/
  push_degree : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity (g + 1) S) (d : ℕ) (x : C.H g (Option (Option S))),
    x ∈ (C.H g (Option (Option S))).degree d →
      push g S h x ∈ (C.H (g + 1) S).degree (d + 1)
  /-- Projection formula, with the existing nonseparating pullback. -/
  projection_formula : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity (g + 1) S) (x : C.H (g + 1) S)
      (y : C.H g (Option (Option S))),
    push g S h (C.nonseparating g S h x * y) = x * push g S h y
  /-- The integral of the raw proper pushforward is the source integral. -/
  integrate_push : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity (g + 1) S) (x : C.H g (Option (Option S))),
    I.integrate (g + 1) S h (push g S h x) =
      I.integrate g (Option (Option S)) (StableArity.double_option_iff.mpr h) x

namespace NonseparatingPushforward

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

/-- Evaluation against a pushed class is derived from the two primitive
push-pull laws, with every source insertion retained. -/
theorem integrate_mul_push (F : NonseparatingPushforward C I)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity (g + 1) S)
    (x : C.H (g + 1) S) (y : C.H g (Option (Option S))) :
    I.integrate (g + 1) S h (x * F.push g S h y) =
      I.integrate g (Option (Option S)) (StableArity.double_option_iff.mpr h)
        (C.nonseparating g S h x * y) := by
  rw [← F.projection_formula, F.integrate_push]

end NonseparatingPushforward

namespace CohFT

variable {R V : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

/-- Integrate a CohFT class against the raw nonseparating pushforward of a
specified lower-genus class. This uses actual cohomology operations. -/
def nonseparatingInvariant (Omega : CohFT R V C)
    (F : NonseparatingPushforward C I) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity (g + 1) S) (x : C.H g (Option (Option S))) :
    MultilinearMap R (fun _ : S ↦ V) R :=
  ((I.integrate (g + 1) S h).comp (LinearMap.mulRight R (F.push g S h x))).compMultilinearMap
    (Omega.omega (g + 1) S h)

/-- Evaluation retains the entire pushed decoration in the integrand. -/
theorem nonseparatingInvariant_apply (Omega : CohFT R V C)
    (F : NonseparatingPushforward C I) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity (g + 1) S) (x : C.H g (Option (Option S))) (a : S → V) :
    Omega.nonseparatingInvariant F g S h x a =
      I.integrate (g + 1) S h (Omega.omega (g + 1) S h a * F.push g S h x) := rfl

/-- Nonseparating boundary evaluation is the inverse-metric contraction of
the lower-genus class family, integrated with the same source decoration. -/
theorem nonseparatingInvariant_eq_selfContract (Omega : CohFT R V C)
    (F : NonseparatingPushforward C I) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity (g + 1) S) (x : C.H g (Option (Option S))) :
    Omega.nonseparatingInvariant F g S h x =
      Omega.pairing.selfContract
        (((I.integrate g (Option (Option S)) (StableArity.double_option_iff.mpr h)).comp
          (LinearMap.mulRight R x)).compMultilinearMap
            ((Omega.omega g (Option (Option S)) (StableArity.double_option_iff.mpr h)).domDomCongr
              (doubleOptionEquiv S))) := by
  rw [← Omega.pairing.selfContractTarget_comp]
  ext a
  rw [nonseparatingInvariant_apply, F.integrate_mul_push]
  have hglue := congrArg (fun f ↦ f a) (Omega.nonseparating g S h)
  exact congrArg (fun y ↦ I.integrate g (Option (Option S))
    (StableArity.double_option_iff.mpr h) (y * x)) hglue.symm

/-- A source cotangent monomial gives precisely the existing CohFT ancestor
contraction, retaining both ordered node powers. -/
theorem nonseparatingInvariant_monomial (Omega : CohFT R V C)
    (P : PsiClasses C) (F : NonseparatingPushforward C I)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity (g + 1) S)
    (k : Option (Option S) → ℕ) :
    Omega.nonseparatingInvariant F g S h
        (P.monomial g (Option (Option S)) (StableArity.double_option_iff.mpr h) k) =
      Omega.pairing.selfContract
        ((Omega.ancestor P I g (Option (Option S))
          (StableArity.double_option_iff.mpr h) k).domDomCongr (doubleOptionEquiv S)) := by
  rw [nonseparatingInvariant_eq_selfContract]
  rfl

end CohFT

end AxiomaticGW

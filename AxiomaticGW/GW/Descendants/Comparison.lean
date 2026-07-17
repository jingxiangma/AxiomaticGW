/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GW.Descendants.Basic

/-!
# Descendant--ancestor comparison

Stable-map and stable-curve cotangent classes differ on loci contracted by
stabilization. The comparison therefore includes an explicit boundary term.
-/

@[expose] public section

namespace AxiomaticGW

universe u

/-- Boundary correction comparing stabilized stable-map descendants with
stable-curve ancestors. -/
structure DescendantAncestorComparison
    {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {Omega : CurveClassGW R V B D C}
    (P : PsiClasses C) (M : StableMapDescendants Omega) where
  /-- Contributions supported on stabilization boundary strata. -/
  boundaryCorrection : ∀ (g : ℕ) (S : Type) [Fintype S]
    (_h : StableArity g S), B → (S → ℕ) →
      MultilinearMap R (fun _ : S ↦ V) (C.H g S)
  /-- Stable-map descendants equal ancestors plus contracted-tail terms. -/
  comparison : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (beta : B) (k : S → ℕ),
    M.descendantClass g S h beta k =
      Omega.ancestorClass P g S h beta k +
        boundaryCorrection g S h beta k

namespace DescendantAncestorComparison

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {Omega : CurveClassGW R V B D C}
  {P : PsiClasses C} {M : StableMapDescendants Omega}

/-- No boundary correction remains when every cotangent power is zero. -/
theorem boundaryCorrection_zero (X : DescendantAncestorComparison P M)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (beta : B) :
    X.boundaryCorrection g S h beta (fun _ ↦ 0) = 0 := by
  have hcomparison := X.comparison g S h beta (fun _ ↦ 0)
  rw [M.descendantClass_zero, Omega.ancestorClass_zero] at hcomparison
  have hsubtract := congrArg
    (fun f ↦ f - Omega.omega g S h beta) hcomparison
  simpa [add_sub_cancel_left] using hsubtract.symm

/-- Integrating the class comparison gives the numerical
descendant--ancestor relation. -/
theorem invariant_eq_ancestor_add_boundary
    (X : DescendantAncestorComparison P M) (I : StableCurveIntegration C)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (beta : B) (k : S → ℕ) :
    M.invariant I g S h beta k =
      Omega.ancestorInvariant P I g S h beta k +
        (I.integrate g S h).compMultilinearMap
          (X.boundaryCorrection g S h beta k) := by
  apply MultilinearMap.ext
  intro a
  change I.integrate g S h (M.descendantClass g S h beta k a) =
    I.integrate g S h (Omega.ancestorClass P g S h beta k a) +
      I.integrate g S h (X.boundaryCorrection g S h beta k a)
  have hcomparison := congrArg (fun f ↦ f a) (X.comparison g S h beta k)
  rw [hcomparison]
  change I.integrate g S h
      (Omega.ancestorClass P g S h beta k a +
        X.boundaryCorrection g S h beta k a) = _
  rw [map_add]

end DescendantAncestorComparison

end AxiomaticGW

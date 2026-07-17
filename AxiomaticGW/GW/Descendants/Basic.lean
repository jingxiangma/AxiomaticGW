/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GW.Basic

/-!
# Stable-map descendants and curve ancestors

Ancestor classes use cotangent lines on stable curves. Stable-map descendants
are separate pushed-forward classes and agree with the primary theory only when
all powers vanish.
-/

@[expose] public section

namespace AxiomaticGW

universe u

namespace CurveClassGW

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R}

/-- A curve-class-resolved ancestor class, formed with stable-curve `psi`. -/
noncomputable def ancestorClass (Omega : CurveClassGW R V B D C)
    (P : PsiClasses C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : B) (k : S → ℕ) :
    MultilinearMap R (fun _ : S ↦ V) (C.H g S) :=
  (CohFT.multiplyPsi P g S h k).compMultilinearMap
    (Omega.omega g S h beta)

@[simp]
theorem ancestorClass_apply (Omega : CurveClassGW R V B D C)
    (P : PsiClasses C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : B) (k : S → ℕ) (a : S → V) :
    Omega.ancestorClass P g S h beta k a =
      Omega.omega g S h beta a * P.monomial g S h k := rfl

@[simp]
theorem ancestorClass_zero (Omega : CurveClassGW R V B D C)
    (P : PsiClasses C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : B) :
    Omega.ancestorClass P g S h beta (fun _ ↦ 0) =
      Omega.omega g S h beta := by
  apply MultilinearMap.ext
  intro a
  simp [ancestorClass_apply]

/-- Numerical ancestor invariant in a fixed curve class. -/
noncomputable def ancestorInvariant (Omega : CurveClassGW R V B D C)
    (P : PsiClasses C) (I : StableCurveIntegration C)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (beta : B) (k : S → ℕ) :
    MultilinearMap R (fun _ : S ↦ V) R :=
  (I.integrate g S h).compMultilinearMap
    (Omega.ancestorClass P g S h beta k)

@[simp]
theorem ancestorInvariant_apply (Omega : CurveClassGW R V B D C)
    (P : PsiClasses C) (I : StableCurveIntegration C)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (beta : B) (k : S → ℕ) (a : S → V) :
    Omega.ancestorInvariant P I g S h beta k a =
      I.integrate g S h
        (Omega.omega g S h beta a * P.monomial g S h k) := rfl

end CurveClassGW

/-- Stable-map descendant classes after stabilization to the stable-curve
target. This family is deliberately distinct from `PsiClasses`. -/
structure StableMapDescendants {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} (Omega : CurveClassGW R V B D C) where
  /-- Stabilized descendant class with stable-map cotangent powers `k`. -/
  descendantClass : ∀ (g : ℕ) (S : Type) [Fintype S]
    (_h : StableArity g S), B → (S → ℕ) →
      MultilinearMap R (fun _ : S ↦ V) (C.H g S)
  /-- Zero cotangent powers recover the primary GW class. -/
  descendantClass_zero : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (beta : B),
    descendantClass g S h beta (fun _ ↦ 0) = Omega.omega g S h beta
  /-- Relabelling transports markings, powers, and inputs together. -/
  relabel : ∀ (g : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (hS : StableArity g S) (hT : StableArity g T)
      (e : S ≃ T) (beta : B) (k : S → ℕ),
    (C.rename g S T hS hT e).toLinearMap.compMultilinearMap
        ((descendantClass g S hS beta k).domDomCongr e) =
      descendantClass g T hT beta (fun t ↦ k (e.symm t))
  /-- Descendant powers add their codimension to the primary output degree. -/
  descendant_degree : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (beta : B) (k : S → ℕ)
      (p : S → ℕ) (a : S → V) (q : ℕ),
    (∀ s, a s ∈ Omega.graded.degree (p s)) →
      GWOutputDegree Omega.graded.dimension g (∑ s, p s) q
        (Omega.c1Degree beta) →
      descendantClass g S h beta k a ∈
        (C.H g S).degree (q + ∑ s, k s)

namespace StableMapDescendants

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {Omega : CurveClassGW R V B D C}

/-- Integrate a stabilized descendant class. -/
noncomputable def invariant (M : StableMapDescendants Omega)
    (I : StableCurveIntegration C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : B) (k : S → ℕ) :
    MultilinearMap R (fun _ : S ↦ V) R :=
  (I.integrate g S h).compMultilinearMap
    (M.descendantClass g S h beta k)

@[simp]
theorem invariant_apply (M : StableMapDescendants Omega)
    (I : StableCurveIntegration C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : B) (k : S → ℕ) (a : S → V) :
    M.invariant I g S h beta k a =
      I.integrate g S h (M.descendantClass g S h beta k a) := rfl

@[simp]
theorem invariant_zero (M : StableMapDescendants Omega)
    (I : StableCurveIntegration C) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : B) :
    M.invariant I g S h beta (fun _ ↦ 0) =
      (I.integrate g S h).compMultilinearMap
        (Omega.omega g S h beta) := by
  simp [invariant, M.descendantClass_zero]

end StableMapDescendants

end AxiomaticGW

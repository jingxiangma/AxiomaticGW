/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GW.Descendants.Equations

/-!
# Abstract virtual GW realization

This is the boundary between the axiomatic theory and future geometry. A
geometric construction must supply a primary curve-class theory, stabilized
stable-map descendants, and their boundary-corrected ancestor comparison.
Actual moduli stacks and virtual fundamental classes are not constructed here.
-/

@[expose] public section

namespace AxiomaticGW

universe u

/-- Algebraic output required from an abstract virtual stable-map
construction. Every field is consumed by the axiomatic GW endpoint. -/
structure VirtualGWPackage
    {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] (D : EffectiveCurveMonoid B)
    (C : StableCurveCohomology R) (P : PsiClasses C) where
  /-- Stabilized primary virtual classes and their gluing laws. -/
  primary : CurveClassGW R V B D C
  /-- Stable-map cotangent insertions pushed to stable curves. -/
  descendants : StableMapDescendants primary
  /-- Stabilization-boundary comparison with stable-curve ancestors. -/
  comparison : DescendantAncestorComparison P descendants

namespace VirtualGWPackage

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {P : PsiClasses C}

/-- A virtual package realizes the primary axiomatic GW theory. -/
def toCurveClassGW
    (G : VirtualGWPackage (R := R) (V := V) (B := B) D C P) :
    CurveClassGW R V B D C :=
  G.primary

/-- A virtual package realizes the stable-map descendant extension of its
primary theory. -/
def toStableMapDescendants
    (G : VirtualGWPackage (R := R) (V := V) (B := B) D C P) :
    StableMapDescendants G.toCurveClassGW :=
  G.descendants

/-- The realized descendants satisfy the boundary-corrected ancestor
comparison. -/
def toDescendantAncestorComparison
    (G : VirtualGWPackage (R := R) (V := V) (B := B) D C P) :
    DescendantAncestorComparison P G.toStableMapDescendants :=
  G.comparison

end VirtualGWPackage

end AxiomaticGW

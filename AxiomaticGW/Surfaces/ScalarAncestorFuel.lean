/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.ScalarAncestorStep

/-! # Effective-coordinate contractions at every lower-genus cotangent step

The rational and elliptic recursions retain the original fuel and primary
terminals. Every intermediate boundary uses the same full-coordinate
splittings, including the rational vertices of elliptic boundary graphs.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceLowGenusPointCache

/-- Rational ancestor recursion with the coordinate contraction at every positive step. -/
def coordinateRationalFuel (X : SurfaceTarget) (v₀ : X.Curve → ℚ) :
    ℕ → SurfaceAncestorKey X → ℚ
  | 0, q => rationalFuel X v₀ 0 q
  | fuel + 1, q =>
    if hg : q.genus = 0 then
      if hp : q.IsPrimary then rationalPrimary X v₀ q.beta q.primaryLabels
      else scalarRationalStep (coordinateRationalFuel X v₀ fuel) q hg hp
    else 0

theorem coordinateRationalFuel_eq (X : SurfaceTarget) (v₀ : X.Curve → ℚ) (fuel : ℕ) :
    coordinateRationalFuel X v₀ fuel = rationalFuel X v₀ fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    funext q
    simp only [coordinateRationalFuel, rationalFuel, ih, scalarRationalStep,
      SurfaceGenusZero.ancestorStep, GluingExpression.scalarSurfaceEval_eq]

/-- The elliptic boundary evaluates rational branches with coordinate recursion as well. -/
def coordinateEllipticStep (X : SurfaceTarget) (v₀ : X.Curve → ℚ)
    (next : SurfaceAncestorKey X → ℚ) (q : SurfaceAncestorKey X)
    (hg : q.genus = 1) (hp : ¬q.IsPrimary) : ℚ :=
  ((PsiBoundaryExpansion.genusOneTerms (SurfaceGenusOne.extraCount q)).map fun t ↦
    t.1 * t.2.scalarSurfaceEval X
      (fun g S _ h beta k a ↦
        let r := SurfaceAncestorKey.ofLabels g S h beta k a
        if r.genus = 0 then coordinateRationalFuel X v₀ r.totalPsi r else next r)
      q.beta (SurfaceGenusOne.lowerAncestorPowers q hg hp)
        (q.orderedLabels ∘ SurfaceGenusOne.ancestorFrame q hg hp)).sum

theorem coordinateEllipticStep_eq (X : SurfaceTarget) (v₀ : X.Curve → ℚ)
    (next : SurfaceAncestorKey X → ℚ) (q : SurfaceAncestorKey X)
    (hg : q.genus = 1) (hp : ¬q.IsPrimary) :
    coordinateEllipticStep X v₀ next q hg hp = ellipticStep X v₀ next q hg hp := by
  simp only [coordinateEllipticStep, ellipticStep, GluingExpression.scalarSurfaceEval_eq,
    coordinateRationalFuel_eq, rationalValue]

/-- Elliptic ancestor recursion with effective-coordinate sums at all component genera. -/
def coordinateEllipticFuel (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ) :
    ℕ → SurfaceAncestorKey X → ℚ
  | 0, q => ellipticFuel X v₀ v₁ 0 q
  | fuel + 1, q =>
    if hg : q.genus = 1 then
      if hp : q.IsPrimary then ellipticPrimary X v₁ q.beta q.primaryLabels
      else coordinateEllipticStep X v₀ (coordinateEllipticFuel X v₀ v₁ fuel) q hg hp
    else 0

theorem coordinateEllipticFuel_eq (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ) (fuel : ℕ) :
    coordinateEllipticFuel X v₀ v₁ fuel = ellipticFuel X v₀ v₁ fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    funext q
    simp only [coordinateEllipticFuel, ellipticFuel, ih, coordinateEllipticStep_eq]

/-- Coordinate recursion dispatches at the original total cotangent fuel. -/
def coordinateComponent (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ) (q : SurfaceAncestorKey X) : ℚ :=
  if q.genus = 0 then coordinateRationalFuel X v₀ q.totalPsi q
  else coordinateEllipticFuel X v₀ v₁ q.totalPsi q

theorem coordinateComponent_eq (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    (q : SurfaceAncestorKey X) : coordinateComponent X v₀ v₁ q = componentValue X v₀ v₁ q := by
  simp only [coordinateComponent, componentValue, rationalValue, ellipticValue,
    coordinateRationalFuel_eq, coordinateEllipticFuel_eq]

end AxiomaticGW.SurfaceLowGenusPointCache

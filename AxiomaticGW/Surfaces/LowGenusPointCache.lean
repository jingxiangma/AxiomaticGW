/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusOneAncestors

/-!
# Primary point functions inside the original low-genus ancestor recursion

The supplied functions replace only the already reconstructed primary point
values. The genus-zero and genus-one ancestor fuel, psi-boundary expressions,
marking frames, full class splittings, inverse metric and degree-zero primary
terms remain unchanged. Equality requires that each supplied point function
equal the existing evaluator; no new invariant or recurrence is assumed.

This upward evaluator can reuse a proved finite primary table with the original
algorithm as fallback outside its certified range. It does not import a fixture
or add a dimension-vanishing rule to intermediate numerical queries.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceLowGenusPointCache

private theorem mul_skip_zero (c v : ℚ) : (if c = 0 then 0 else c * v) = c * v := by
  by_cases hc : c = 0
  · rw [if_pos hc, hc, zero_mul]
  · exact if_neg hc

/-- The existing rational primary formula, with an exact zero-product guard. -/
def rationalPrimary (X : SurfaceTarget) (v₀ : X.Curve → ℚ) (beta : X.Curve)
    (m : Multiset (SurfaceBasisLabel X)) : ℚ :=
  if beta = 0 then SurfacePrimary.classicalValue m else
    if m.count .point = X.effective.energy beta - 1 then
      let c := (m.map (SurfaceBasisLabel.primaryFactor beta)).prod
      if c = 0 then 0 else c * v₀ beta
    else 0

/-- The existing elliptic primary formula preserves its own class-zero constants. -/
def ellipticPrimary (X : SurfaceTarget) (v₁ : X.Curve → ℚ) (beta : X.Curve)
    (m : Multiset (SurfaceBasisLabel X)) : ℚ :=
  if beta = 0 then SurfacePrimary.genusOneZeroValue m else
    if m.count .point = X.effective.energy beta then
      let c := (m.map (SurfaceBasisLabel.primaryFactor beta)).prod
      if c = 0 then 0 else c * v₁ beta
    else 0

/-- Reusing a point evaluator changes no rational primary request. -/
theorem rationalPrimary_eq (X : SurfaceTarget) (v₀ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (beta : X.Curve)
    (m : Multiset (SurfaceBasisLabel X)) :
    rationalPrimary X v₀ beta m = SurfaceGenusZero.primaryValue X beta m := by
  rw [h₀]
  simp only [rationalPrimary, SurfaceGenusZero.primaryValue, mul_skip_zero]

/-- Reusing a point evaluator changes no elliptic primary request. -/
theorem ellipticPrimary_eq (X : SurfaceTarget) (v₁ : X.Curve → ℚ)
    (h₁ : v₁ = SurfaceGenusOne.pointValue X) (beta : X.Curve)
    (m : Multiset (SurfaceBasisLabel X)) :
    ellipticPrimary X v₁ beta m = SurfaceGenusOne.primaryValue X beta m := by
  rw [h₁]
  simp only [ellipticPrimary, SurfaceGenusOne.primaryValue, mul_skip_zero]

/-- Rational recursion keeps the original step and replaces only primary terminals. -/
def rationalFuel (X : SurfaceTarget) (v₀ : X.Curve → ℚ) :
    ℕ → SurfaceAncestorKey X → ℚ
  | 0, q => if q.genus = 0 ∧ q.IsPrimary then rationalPrimary X v₀ q.beta q.primaryLabels
      else 0
  | fuel + 1, q => if hg : q.genus = 0 then
      if hp : q.IsPrimary then rationalPrimary X v₀ q.beta q.primaryLabels
      else SurfaceGenusZero.ancestorStep (rationalFuel X v₀ fuel) q hg hp
    else 0

/-- Every fuel approximation agrees, including incompatible numerical queries. -/
theorem rationalFuel_eq (X : SurfaceTarget) (v₀ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (fuel : ℕ) :
    rationalFuel X v₀ fuel = SurfaceGenusZero.ancestorValueFuel X fuel := by
  induction fuel with
  | zero =>
    funext q
    simp only [rationalFuel, SurfaceGenusZero.ancestorValueFuel, rationalPrimary_eq X v₀ h₀]
  | succ fuel ih =>
    funext q
    simp only [rationalFuel, SurfaceGenusZero.ancestorValueFuel,
      rationalPrimary_eq X v₀ h₀, ih]

/-- Supply the same sufficient cotangent fuel as the original rational evaluator. -/
def rationalValue (X : SurfaceTarget) (v₀ : X.Curve → ℚ)
    (q : SurfaceAncestorKey X) : ℚ := rationalFuel X v₀ q.totalPsi q

/-- The full rational ancestor algorithm is preserved at every full class. -/
theorem rationalValue_eq (X : SurfaceTarget) (v₀ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) :
    rationalValue X v₀ = SurfaceGenusZero.ancestorValue X := by
  funext q
  rw [rationalValue, SurfaceGenusZero.ancestorValue, rationalFuel_eq X v₀ h₀]

/-- Keep the original elliptic psi equation while reusing rational primary terminals. -/
def ellipticStep (X : SurfaceTarget) (v₀ : X.Curve → ℚ)
    (next : SurfaceAncestorKey X → ℚ) (q : SurfaceAncestorKey X)
    (hg : q.genus = 1) (hp : ¬q.IsPrimary) : ℚ :=
  ((PsiBoundaryExpansion.genusOneTerms (SurfaceGenusOne.extraCount q)).map fun t ↦
    t.1 * t.2.surfaceEval X
      (fun g S _ h beta k a ↦
        let r := SurfaceAncestorKey.ofLabels g S h beta k a
        if r.genus = 0 then rationalValue X v₀ r else next r)
      q.beta (SurfaceGenusOne.lowerAncestorPowers q hg hp)
        (q.orderedLabels ∘ SurfaceGenusOne.ancestorFrame q hg hp)).sum

/-- Every loop, separating tail and marking occurrence has its original value. -/
theorem ellipticStep_eq (X : SurfaceTarget) (v₀ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (next : SurfaceAncestorKey X → ℚ)
    (q : SurfaceAncestorKey X) (hg : q.genus = 1) (hp : ¬q.IsPrimary) :
    ellipticStep X v₀ next q hg hp = SurfaceGenusOne.ancestorStep next q hg hp := by
  simp only [ellipticStep, SurfaceGenusOne.ancestorStep, SurfaceGenusOne.componentValue,
    rationalValue_eq X v₀ h₀]

/-- Elliptic fuel recursion replaces only the primary point functions in both genera. -/
def ellipticFuel (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ) :
    ℕ → SurfaceAncestorKey X → ℚ
  | 0, q => if q.genus = 1 ∧ q.IsPrimary then ellipticPrimary X v₁ q.beta q.primaryLabels
      else 0
  | fuel + 1, q => if hg : q.genus = 1 then
      if hp : q.IsPrimary then ellipticPrimary X v₁ q.beta q.primaryLabels
      else ellipticStep X v₀ (ellipticFuel X v₀ v₁ fuel) q hg hp
    else 0

/-- The exact comparison needs no dimension, positivity or irreducibility premise. -/
theorem ellipticFuel_eq (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (h₁ : v₁ = SurfaceGenusOne.pointValue X)
    (fuel : ℕ) : ellipticFuel X v₀ v₁ fuel = SurfaceGenusOne.ancestorValueFuel X fuel := by
  induction fuel with
  | zero =>
    funext q
    simp only [ellipticFuel, SurfaceGenusOne.ancestorValueFuel, ellipticPrimary_eq X v₁ h₁]
  | succ fuel ih =>
    funext q
    simp only [ellipticFuel, SurfaceGenusOne.ancestorValueFuel,
      ellipticPrimary_eq X v₁ h₁, ellipticStep_eq X v₀ h₀, ih]

/-- Use exactly the existing total-psi fuel for an elliptic ancestor. -/
def ellipticValue (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    (q : SurfaceAncestorKey X) : ℚ := ellipticFuel X v₀ v₁ q.totalPsi q

/-- All original elliptic ancestor values and their unsupported branches are preserved. -/
theorem ellipticValue_eq (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (h₁ : v₁ = SurfaceGenusOne.pointValue X) :
    ellipticValue X v₀ v₁ = SurfaceGenusOne.ancestorValue X := by
  funext q
  rw [ellipticValue, SurfaceGenusOne.ancestorValue, ellipticFuel_eq X v₀ v₁ h₀ h₁]

/-- The same component dispatcher supplies rational or elliptic ancestors. -/
def componentValue (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    (q : SurfaceAncestorKey X) : ℚ :=
  if q.genus = 0 then rationalValue X v₀ q else ellipticValue X v₀ v₁ q

/-- The complete low-genus scalar component is unchanged, without a query-domain restriction. -/
theorem componentValue_eq (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (h₁ : v₁ = SurfaceGenusOne.pointValue X) :
    componentValue X v₀ v₁ =
      SurfaceGenusOne.componentValue X (SurfaceGenusOne.ancestorValue X) := by
  funext q
  simp only [componentValue, SurfaceGenusOne.componentValue,
    rationalValue_eq X v₀ h₀, ellipticValue_eq X v₀ v₁ h₀ h₁]

end AxiomaticGW.SurfaceLowGenusPointCache

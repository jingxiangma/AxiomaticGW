/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.TermExpansion

/-! # Exact term expansion and equality regressions

These checks exercise cancellation, multiplicities, both sides of the finite
support comparison, and curve functions produced by actual splitting.
-/

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.TermExpansion

open AxiomaticGW

/-- Coefficients of repeated monomials are added exactly. -/
example : RationalTerms.Equivalent ({(1, {0}), (2, {0})} : RationalTerms ℕ)
    {(3, {0})} := by decide +kernel

/-- Complete cancellation is accepted even when the supports differ. -/
example : RationalTerms.Equivalent ({(2, {0}), (-2, {0})} : RationalTerms ℕ) 0 :=
  by decide +kernel

/-- Missing an input monomial is rejected. -/
example : ¬RationalTerms.Equivalent ({(1, {0}), (1, {1})} : RationalTerms ℕ)
    {(1, {0})} := by decide +kernel

/-- An extra output monomial is also rejected. -/
example : ¬RationalTerms.Equivalent ({(1, {0})} : RationalTerms ℕ)
    {(1, {0}), (1, {1})} := by decide +kernel

/-- Changing a sign cannot pass exact coefficient comparison. -/
example : ¬RationalTerms.Equivalent ({(-1, {0})} : RationalTerms ℕ)
    {(1, {0})} := by decide +kernel

/-- A repeated variable is a square, not a single occurrence. -/
example : ¬RationalTerms.Equivalent ({(1, {0, 0})} : RationalTerms ℕ)
    {(1, {0})} := by decide +kernel

/-- Distribution preserves signed coefficients and repeated variables. -/
example : RationalTerms.Equivalent
    (RationalTerms.mul ({(2, {0, 0}), (-1, {1})} : RationalTerms ℕ) {(3, {0})})
    {(6, {0, 0, 0}), (-3, {0, 1})} := by decide +kernel

/-- Query equality must reduce for extensionally equal curve functions. -/
example : SurfaceQuery.points .plane 1 (fun _ ↦ 1) 3 =
    SurfaceQuery.points .plane 1 ![1] 3 := by decide +kernel

/-- The same property is required after tagging a query as a residual variable. -/
example : RationalTerms.Equivalent
    (RationalTerms.term 1 {(.inr (SurfaceQuery.points .plane 1 (fun _ ↦ 1) 3) :
      SurfacePolynomialReduction.Variable .plane)})
    (RationalTerms.term 1 {.inr (SurfaceQuery.points .plane 1 ![1] 3)}) := by decide +kernel

/-- Actual class enumeration supplies a nonliteral function representative. -/
example : ((SurfaceTarget.plane.splittings ![1]).val.map
    (fun s ↦ SurfaceQuery.points .plane 1 s.1 3)).count
      (SurfaceQuery.points .plane 1 ![1] 3) = 1 := by decide +kernel

/-- Equal-energy exceptional classes must remain distinct polynomial variables. -/
example : ¬RationalTerms.Equivalent
    (RationalTerms.term 1 {(.inr (SurfaceQuery.points .blowupTwo 1 ![1, 0, 0] 1) :
      SurfacePolynomialReduction.Variable .blowupTwo)})
    (RationalTerms.term 1 {.inr (SurfaceQuery.points .blowupTwo 1 ![0, 1, 0] 1)}) :=
  by decide +kernel

/-- A nonzero ancestor power is retained through early terminal reduction. -/
private def psiKey : SurfaceAncestorKey .plane :=
  .ofLabels 1 (Fin 1) (by norm_num [StableArity]) 0 (fun _ ↦ 1) (fun _ ↦ .unit)

example : RationalTerms.Equivalent (SurfacePolynomialReduction.primaryTerms psiKey)
    {(1, {.inl psiKey})} := by decide +kernel

end AxiomaticGWTest.Surfaces.TermExpansion

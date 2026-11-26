/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroCompactStep

/-!
# The plane quartic WDVV polynomial

The HHptpt request with eight further points gives
`N₄ - 33 N₁ N₃ - 224 N₂²`. Exact coefficient replay checks the whole compressed
polynomial, and the universal compression theorem ties it to the original
ordered graph request. This identity does not itself assume any invariant value.
-/

@[expose] public section

namespace AxiomaticGW.SurfacePlaneQuartic

open SurfaceGenusZero SurfacePolynomialReduction

/-- The complete requested polynomial, including both ordered split contributions. -/
def terms : RationalTerms (Variable .plane) :=
  RationalTerms.term 1 {pointVariable .plane ![4]} +
    RationalTerms.term (-33) {pointVariable .plane ![1], pointVariable .plane ![3]} +
    RationalTerms.term (-224) {pointVariable .plane ![2], pointVariable .plane ![2]}

/-- Kernel replay of every monomial coefficient against the held quartic request. -/
theorem accepted : RationalTerms.Equivalent
    (WDVV.compactPrimaryTerms .plane 8 ![4] (WDVV.reconstructionLabels .plane)) terms := by
  decide +kernel

/-- The short certificate denotes the entire original ordered-marking expansion. -/
theorem eval_terms {A : Type*} [CommRing A] [Algebra ℚ A]
    (v : Variable .plane → A) :
    RationalTerms.eval v terms = RationalTerms.eval v
      (WDVV.primaryTerms .plane 8 ![4] 0
        (pointLabels (WDVV.reconstructionLabels .plane) 8)) := by
  rw [← RationalTerms.eval_eq_of_equivalent v _ _ accepted, WDVV.eval_compactPrimaryTerms]

end AxiomaticGW.SurfacePlaneQuartic

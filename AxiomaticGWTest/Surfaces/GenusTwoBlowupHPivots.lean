/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.GenusTwoBlowupHPivots

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusTwoBlowupHPivots
open AxiomaticGW SurfaceGenusTwoBlowupHPivots

-- The public interface binds every selected coefficient to the complete held row.
example (X : SurfaceTarget) (i : Fin X.blowups) (beta : X.Curve) :
    coefficient X i beta = RationalTerms.coefficient (row X i beta) {hColumn X beta} :=
  coefficient_eq_full X i beta

-- All five pivots can be used directly at the original normalized-polynomial interface.
example : RationalTerms.coefficient (row .hirzebruchOne 0 ![1, 0])
    {hColumn .hirzebruchOne ![1, 0]} = -1 := by
  rw [← coefficient_eq_full]
  exact hirzebruchOne_exceptional

example : RationalTerms.coefficient (row .hirzebruchOne 0 ![0, 1])
    {hColumn .hirzebruchOne ![0, 1]} = -1 := by
  rw [← coefficient_eq_full]
  exact hirzebruchOne_fiber

example : RationalTerms.coefficient (row .blowupTwo 0 ![1, 0, 0])
    {hColumn .blowupTwo ![1, 0, 0]} = -1 := by
  rw [← coefficient_eq_full]
  exact blowupTwo_firstExceptional

example : RationalTerms.coefficient (row .blowupTwo 0 ![0, 1, 0])
    {hColumn .blowupTwo ![0, 1, 0]} = -1 := by
  rw [← coefficient_eq_full]
  exact blowupTwo_secondExceptional

example : RationalTerms.coefficient (row .blowupTwo 0 ![0, 0, 1])
    {hColumn .blowupTwo ![0, 0, 1]} = -1 := by
  rw [← coefficient_eq_full]
  exact blowupTwo_strictLine

-- Positive energy is required before the natural subtraction gives the dimension count.
example (X : SurfaceTarget) (i : Fin X.blowups) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta) :
    pointCount X beta + 2 = X.effective.energy (sourceCurve X i beta) :=
  pointCount_dimension X i beta hbeta

example : pointCount .hirzebruchOne 0 + 2 ≠
    SurfaceTarget.hirzebruchOne.effective.energy (sourceCurve .hirzebruchOne 0 0) := by
  decide +kernel

-- The E₂ and strict-line columns have equal energy and distinct full-class requests.
example : SurfaceTarget.blowupTwo.effective.energy ![0, 1, 0] =
    SurfaceTarget.blowupTwo.effective.energy ![0, 0, 1] := by decide +kernel

example : hColumn .blowupTwo ![0, 1, 0] ≠ hColumn .blowupTwo ![0, 0, 1] := by
  decide +kernel

end AxiomaticGWTest.Surfaces.GenusTwoBlowupHPivots

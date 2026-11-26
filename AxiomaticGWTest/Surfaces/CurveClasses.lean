/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.CurveClasses

set_option linter.privateModule false

/-!
# Fixed-surface curve-coordinate regressions

These checks exercise integer signs, full-class splitting, and the fixed
anticanonical cutoff. They validate the coordinate models and executable
enumerators, without asserting their geometric realization or GW values.
The finite computations use kernel-checked `decide`, never native evaluation.
-/

namespace AxiomaticGWTest.Surfaces.CurveClasses

open AxiomaticGW SurfaceTarget

/-- A line has anticanonical degree three; the exceptional curve and fiber
on the one-point blowup have degrees one and two. -/
example :
    plane.c1Degree ![1] = 3 ∧
      hirzebruchOne.c1Degree ![1, 0] = 1 ∧
      hirzebruchOne.c1Degree ![0, 1] = 2 := by
  decide

/-- Both exceptional curves and the line through the two points have
anticanonical degree one. -/
example :
    blowupTwo.c1Degree ![1, 0, 0] = 1 ∧
      blowupTwo.c1Degree ![0, 1, 0] = 1 ∧
      blowupTwo.c1Degree ![0, 0, 1] = 1 := by
  decide

/-- The fiber `F = H-E` retains a negative exceptional lattice coefficient. -/
example :
    hirzebruchOne.latticeCoordinates ![0, 1] = ![1, -1] ∧
      hirzebruchOne.generatorCoordinates ![1, -1] = ![0, 1] := by
  decide

/-- The third generator is `L = H-E₁-E₂`, including both minus signs. -/
example :
    blowupTwo.latticeCoordinates ![0, 0, 1] = ![1, -1, -1] ∧
      blowupTwo.generatorCoordinates ![1, -1, -1] = ![0, 0, 1] := by
  decide

/-- Exceptional divisors have self-intersection minus one. -/
example :
    hirzebruchOne.divisorIntersections ![1, 0] 1 = -1 ∧
      blowupTwo.divisorIntersections ![1, 0, 0] 1 = -1 ∧
      blowupTwo.divisorIntersections ![0, 1, 0] 2 = -1 := by
  decide

/-- Linear extension of divisor intersections gives `F²=0` and `L²=-1`. -/
example :
    hirzebruchOne.divisorIntersections ![0, 1] 0 -
        hirzebruchOne.divisorIntersections ![0, 1] 1 = 0 ∧
      blowupTwo.divisorIntersections ![0, 0, 1] 0 -
          blowupTwo.divisorIntersections ![0, 0, 1] 1 -
          blowupTwo.divisorIntersections ![0, 0, 1] 2 = -1 := by
  decide

/-- Equal energy does not identify the two exceptional curve classes. -/
example :
    blowupTwo.effective.energy ![1, 0, 0] =
        blowupTwo.effective.energy ![0, 1, 0] ∧
      (![1, 0, 0] : blowupTwo.Curve) ≠ ![0, 1, 0] ∧
      blowupTwo.latticeCoordinates ![1, 0, 0] ≠
        blowupTwo.latticeCoordinates ![0, 1, 0] := by
  decide

/-- The pullback line is `E₁+E₂+L`, and `H-E₁` is `E₂+L`. -/
example :
    blowupTwo.latticeCoordinates ![1, 1, 1] = ![1, 0, 0] ∧
      blowupTwo.latticeCoordinates ![0, 1, 1] = ![1, -1, 0] ∧
      ((![1, 0, 0], ![0, 1, 1]) : blowupTwo.Curve × blowupTwo.Curve) ∈
        blowupTwo.splittings ![1, 1, 1] := by
  decide

/-- Every ordered splitting of the pullback line, including both zero
splittings and every exceptional component, is present exactly once. -/
example :
    blowupTwo.splittings ![1, 1, 1] =
      {(![0, 0, 0], ![1, 1, 1]),
       (![1, 0, 0], ![0, 1, 1]),
       (![0, 1, 0], ![1, 0, 1]),
       (![0, 0, 1], ![1, 1, 0]),
       (![1, 1, 0], ![0, 0, 1]),
       (![1, 0, 1], ![0, 1, 0]),
       (![0, 1, 1], ![1, 0, 0]),
       (![1, 1, 1], ![0, 0, 0])} := by
  decide

/-- The eight-split assertion also checks deduplication of tuple functions. -/
example : (blowupTwo.splittings ![1, 1, 1]).card = 8 := by
  decide

/-- The cutoff includes the zero class for each fixed target. -/
example :
    (0 : plane.Curve) ∈ plane.bounded 12 ∧
      (0 : hirzebruchOne.Curve) ∈ hirzebruchOne.bounded 12 ∧
      (0 : blowupTwo.Curve) ∈ blowupTwo.bounded 12 := by
  decide

/-- Plane classes are `dH` for `0≤d≤4` at anticanonical degree at most 12. -/
example : (plane.bounded 12).card = 5 := by
  decide

set_option maxRecDepth 10000 in
/-- For `aE+bF`, the count is `∑ b=0..6, (13-2b) = 49`. -/
example : (hirzebruchOne.bounded 12).card = 49 := by
  decide

set_option maxRecDepth 10000 in
/-- Three weight-one generators give `binomial(15,3) = 455` bounded classes. -/
example : (blowupTwo.bounded 12).card = 455 := by
  decide

end AxiomaticGWTest.Surfaces.CurveClasses

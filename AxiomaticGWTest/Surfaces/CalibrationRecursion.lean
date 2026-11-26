/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.GKM.Fixtures.HigherCalibrationReplay

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.CalibrationRecursion
open AxiomaticGW SurfaceDescendant

/-- Calibration constants are distinct from positive-loop zero-class values. -/
example : reconstructedCalibrationMatrix .plane 0 0 = 1 ∧
    reconstructedCalibrationMatrix .plane 0 ![1] = 0 ∧
    reconstructedCalibrationMatrix .plane 3 0 = 0 := by decide +kernel

/-- The divisor correction has a minus sign and acts on the input column. -/
example : reconstructedCalibrationMatrix .plane 2 ![1] .unit .hyperplane = -1 ∧
    reconstructedCalibrationMatrix .plane 2 ![1] .hyperplane .point = 1 := by decide +kernel

/-- The plane-line third coefficient has the three different diagonal entries. -/
example : reconstructedCalibrationMatrix .plane 3 ![1] .unit .unit = 1 ∧
    reconstructedCalibrationMatrix .plane 3 ![1] .hyperplane .hyperplane = -2 ∧
    reconstructedCalibrationMatrix .plane 3 ![1] .point .point = 1 := by decide +kernel

/-- The last supported plane-line power survives, and the next one vanishes. -/
example : reconstructedCalibrationMatrix .plane 5 ![1] .point .unit = 6 ∧
    reconstructedCalibrationMatrix .plane 6 ![1] = 0 := by decide +kernel

/-- A class with zero first coefficient can have nonzero higher descendants. -/
example : firstCalibrationMatrix .plane ![2] = 0 ∧
    reconstructedCalibrationMatrix .plane 4 ![2] .unit .point = 1/2 := by decide +kernel

/-- Multiple exceptional covers retain rational coefficients and full curve coordinates. -/
example : reconstructedCalibrationMatrix .hirzebruchOne 2 ![2,0]
      (.exceptional 0) (.exceptional 0) = 1/2 ∧
    reconstructedCalibrationMatrix .blowupTwo 2 ![0,2,0]
      (.exceptional 0) (.exceptional 0) = 0 ∧
    reconstructedCalibrationMatrix .blowupTwo 2 ![0,2,0]
      (.exceptional 1) (.exceptional 1) = 1/2 := by decide +kernel

/-- Both exceptional columns of the classical anticanonical product are positive. -/
example : anticanonicalCupMatrix .blowupTwo .point (.exceptional 0) = 1 ∧
    anticanonicalCupMatrix .blowupTwo (.exceptional 0) .unit = -1 := by decide +kernel

/-- Native ordinary entries are bound to actual powers, classes and basis labels. -/
example (i row col) : GKM.HigherCalibrationReplay.TwoBlowups.entries i row col =
    reconstructedCalibrationMatrix .blowupTwo
      (GKM.HigherCalibrationReplay.TwoBlowups.requests i).1
      (GKM.HigherCalibrationReplay.TwoBlowups.requests i).2
      (GKM.HigherCalibrationReplay.TwoBlowups.labels row)
      (GKM.HigherCalibrationReplay.TwoBlowups.labels col) :=
  GKM.HigherCalibrationReplay.TwoBlowups.accepted i row col

end AxiomaticGWTest.Surfaces.CalibrationRecursion

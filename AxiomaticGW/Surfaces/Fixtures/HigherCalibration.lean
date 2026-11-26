/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.CalibrationRecursion

/-!
# Held higher-calibration requests for native GKM comparison

These thirty requests cover powers two and three at the ten classes with a
nonzero first coefficient, the remaining plane-line support and its first
zero power, a conic, and double exceptional classes. They retain full curve
coordinates. The ordinary matrix values are checked against the derived
recursion, never against a numerical answer supplied by the producer itself.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceHigherCalibration

/-- Fixed `(inverse-loop power, full effective class)` comparison requests. -/
def requests : (X : SurfaceTarget) → List (ℕ × X.Curve)
  | .plane => [(2, ![1]), (3, ![1]), (4, ![1]), (5, ![1]), (6, ![1]), (4, ![2])]
  | .hirzebruchOne => [(2, ![1,0]), (3, ![1,0]), (2, ![0,1]), (3, ![0,1]),
      (2, ![1,1]), (3, ![1,1]), (2, ![2,0]), (3, ![2,0])]
  | .blowupTwo => [(2, ![1,0,0]), (3, ![1,0,0]), (2, ![0,1,0]), (3, ![0,1,0]),
      (2, ![0,0,1]), (3, ![0,0,1]), (2, ![0,1,1]), (3, ![0,1,1]),
      (2, ![1,0,1]), (3, ![1,0,1]), (2, ![1,1,1]), (3, ![1,1,1]),
      (2, ![2,0,0]), (3, ![2,0,0]), (2, ![0,2,0]), (3, ![0,2,0])]

end AxiomaticGW.SurfaceHigherCalibration

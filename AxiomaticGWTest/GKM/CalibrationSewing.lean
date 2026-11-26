/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.CalibrationSewingGeometry

/-! # Nonzero split contributions in the nonlinear sewing equation -/

@[expose] public section
namespace AxiomaticGWTest.GKM.CalibrationSewing
open AxiomaticGW.GKM.EquivariantCoefficients AxiomaticGW.GKM.EquivariantCalibrationReplay
open AxiomaticGW.GKM.CalibrationSewing

/-- In class 2H both endpoint contributions are 1/2 at the point/point entry. -/
theorem plane_double_tail : interior (row .plane 0) (tables .plane).inverseMetric 2 2 = -1 := by
  have h := congrFun (congrFun (coefficient_zero .plane 0) 2) 2
  change (1/2 : Coefficient) + (-1)^4 * (1/2) + _ = 0 at h
  linear_combination h

/-- The negative half in class 2E cancels a positive interior contribution. -/
theorem exceptional_double_tail :
    interior (row .hirzebruchOne 2) (tables .hirzebruchOne).inverseMetric 2 2 = 1 := by
  have h := congrFun (congrFun (coefficient_zero .hirzebruchOne 2) 2) 2
  change (-1/2 : Coefficient) + (-1)^2 * (-1/2) + _ = 0 at h
  linear_combination h

/-- The marked H,E₁ entry distinguishes the two mixed classes of equal energy. -/
theorem distinct_mixed_classes :
    interior (row .blowupTwo 0) (tables .blowupTwo).inverseMetric 1 2 = 0 ∧
    interior (row .blowupTwo 2) (tables .blowupTwo).inverseMetric 1 2 = 1 := by
  have h := congrFun (congrFun (coefficient_zero .blowupTwo 0) 1) 2
  have k := congrFun (congrFun (coefficient_zero .blowupTwo 2) 1) 2
  change (1 : Coefficient) + (-1)^2 * (-1) + _ = 0 at h
  change (-1 : Coefficient) + (-1)^2 * 0 + _ = 0 at k
  exact ⟨by linear_combination h, by linear_combination k⟩

end AxiomaticGWTest.GKM.CalibrationSewing

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.F1DoubleExceptionalOneMarking
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1DoubleExceptionalOneMarking

/-! # Original genus-two reconstruction against the four one-marked GKM rows at 2E -/

@[expose] public section
namespace AxiomaticGW.GKM.F1DoubleExceptionalOneMarking

/-- The complete ordered native request and its ordinary value agree with mixed reconstruction. -/
theorem accepted (j : Fin 4) :
    SurfaceGenusTwoBlowupDescendants.queryValue? 0 (requests j) = some (values j) := by
  have hq : requests j = BlowupF1DoubleExceptionalOneMarking.requests j := by
    fin_cases j <;> decide +kernel
  rw [hq, BlowupF1DoubleExceptionalOneMarking.accepted]
  fin_cases j <;> decide +kernel

end AxiomaticGW.GKM.F1DoubleExceptionalOneMarking

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.ProperFrame
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineTransfer

/-! # The low-power proper-class calibration of the two rulings -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRulingInterior
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants
open BlowupTwoDoubleLine (terminals)

/-- Each of the 26 proper low-power keys has zero original ancestor value on both rulings. -/
theorem proper_low_values (i : Fin 2) (r : Fin 26) :
    ancestorValueWith terminals (properKey i (lowIndex r)) = 0 := by
  let base := SurfaceGenusTwoBlowupLowPsi.ancestorValueWith terminals
  change ancestorValue base _ = _
  rw [ancestorValue_low base _ rfl (by fin_cases i <;> fin_cases r <;> decide +kernel)]
  fin_cases i <;> fin_cases r <;> decide +kernel

end AxiomaticGW.BlowupTwoRulingInterior

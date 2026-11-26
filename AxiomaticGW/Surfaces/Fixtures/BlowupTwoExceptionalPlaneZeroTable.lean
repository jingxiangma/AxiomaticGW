/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoExceptionalOneMarking

/-! # Canonical lookups on the exceptional face of the two-point blowup

Every effective summand of a class with zero plane degree remains on that
face. The existing exceptional singleton lookup agrees globally with the
original recursion, including at positive plane degree.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoExceptionalPlaneZeroTable
open SurfaceGenusTwoBlowupOrder

/-- Use the same canonical lookup as the two primitive exceptional singletons. -/
abbrev table : State .blowupTwo → ℚ := BlowupTwoExceptionalOneMarking.terminals

theorem table_eq (s : State .blowupTwo) : table s = SurfaceGenusTwoBlowupRecursion.values 0 s := by
  unfold table BlowupTwoExceptionalOneMarking.terminals
  split_ifs with h
  · exact (SurfaceGenusTwoBlowupRecursion.values_boundary 0 s h).symm
  · rfl

end AxiomaticGW.BlowupTwoExceptionalPlaneZeroTable

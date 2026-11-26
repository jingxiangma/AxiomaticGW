/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.IncidenceSquares

/-! # Exceptional-face support of the twenty-eight original genus-two squares

The twelve primitive tails have a foreign exceptional or point insertion. The other sixteen
squares carry the full mixed curve. The same incidence test checks all eleven signed sources
on each marking frame, including each effective splitting and every assignment at its nodes.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoMixedExceptionalInteriorPairs.FaceSquares

set_option maxRecDepth 65536

set_option maxHeartbeats 12000000 in
-- All 308 closed graph evaluations enumerate the effective splittings and dual labels.
/-- Every component assignment on every signed source of the full ancestor frame has a zero
vertex, with the original low-power table on each genus-two vertex. -/
theorem checked (j : Fin 28) (i : Fin 11) :
    check (squareBeta j) (oldMark j) (extraMark j) i = true := by
  fin_cases j <;> fin_cases i <;> decide +kernel

end AxiomaticGW.BlowupTwoMixedExceptionalInteriorPairs.FaceSquares

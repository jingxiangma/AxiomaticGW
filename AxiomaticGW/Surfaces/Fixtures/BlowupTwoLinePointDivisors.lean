/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Assembly
public import AxiomaticGW.Surfaces.GenusTwoBlowupQueryCertificate

/-! # Ordered point and divisor descendants on the strict transform of the line

The point can be the first or the second marking. Both orders are evaluated
with their original descendant powers against the checked energy-one table.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoLinePointDivisors
open SurfaceGenusTwoBlowupDescendants

/-- The divisor carries one cotangent power and the point is primary. -/
def request (d : Fin 3) (pointFirst : Bool) : SurfaceQuery .blowupTwo :=
  let divisor : SurfaceInsertion .blowupTwo := ⟨![.hyperplane, .exceptional 0, .exceptional 1] d, 1⟩
  let pt : SurfaceInsertion .blowupTwo := ⟨.point, 0⟩
  ⟨2, BlowupTwoLineBP.line, if pointFirst then [pt, divisor] else [divisor, pt]⟩

/-- Direct mixed-cotangent reconstruction gives zero for all six ordered requests. -/
theorem value (d : Fin 3) (pointFirst : Bool) : queryValue? 0 (request d pointFirst) = some 0 := by
  rw [← queryValueWith?_eq 0 1 (BlowupTwoLineTable.candidate 0) BlowupTwoLineTable.accepted _
    (show SurfaceTarget.blowupTwo.effective.energy BlowupTwoLineBP.line ≤ 1 by decide +kernel)]
  revert d pointFirst
  decide +kernel

/-- The primary two-point request is also zero in the original mixed evaluator. -/
theorem primary : queryValue? 0 (⟨2, BlowupTwoLineBP.line, [⟨.point, 0⟩, ⟨.point, 0⟩]⟩ :
    SurfaceQuery .blowupTwo) = some 0 := by
  rw [← queryValueWith?_eq 0 1 (BlowupTwoLineTable.candidate 0) BlowupTwoLineTable.accepted _
    (show SurfaceTarget.blowupTwo.effective.energy BlowupTwoLineBP.line ≤ 1 by decide +kernel)]
  decide +kernel

end AxiomaticGW.BlowupTwoLinePointDivisors

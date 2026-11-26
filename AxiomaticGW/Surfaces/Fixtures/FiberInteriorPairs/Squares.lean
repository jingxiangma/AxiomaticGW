/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.FiberInteriorPairs.SquareHead
public import AxiomaticGW.Surfaces.Fixtures.FiberInteriorPairs.FourthPower

/-! # The final cotangent-degree-five fiber square

The original ancestor has the unit at both marks, with powers two and three.
The correction to the pulled-back leading term and all ten boundary sources
complete the 19 square ancestors needed by the calibrated two-marked frame.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoPositiveDivisorPairs SurfaceGenusTwoPositiveSquare

def lastParts : Fin 11 → ℚ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def lastSource (i : Fin 11) : ℚ :=
  pulledSquarePart (Components.FourthPower.components.vertex (ancestorValue low)) 1
    (squareBeta 18) (powers 18) (labels 18) i

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
-- Retain every term of each signed source at the complete fiber class.
private theorem last_parts (i : Fin 11) : lastSource i = lastParts i := by
  fin_cases i <;> decide +kernel

theorem last_square : ancestorValue low (squareKey 18) = 0 := by
  rw [square_framed, pulledSquare_eq_parts, ← component_eq,
    ← Components.FourthPower.components.vertex_eq]
  change (∑ i, lastSource i) = _
  simp only [last_parts]
  decide +kernel

def squareValues : Fin 19 → ℚ := Fin.lastCases 0 headValues

theorem square_values (j : Fin 19) : ancestorValue low (squareKey j) = squareValues j := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · exact last_square
  · simpa only [squareValues, Fin.lastCases_castSucc] using first_squares i

end AxiomaticGW.BlowupF1FiberInteriorPairs

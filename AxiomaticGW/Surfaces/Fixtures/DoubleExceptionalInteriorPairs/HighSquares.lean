/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.DoubleExceptionalInteriorPairs.Frame
public import AxiomaticGW.Surfaces.Fixtures.DoubleExceptionalInteriorPairs.Components

/-! # The three highest two-marked genus-two squares on 2E

The selected insertion is the second descendant of the unit. The extra
marking carries the second descendant of H or E, or the third descendant
of the unit. The eleven signed sources retain every effective splitting
of 2E, including the E + E splitting.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1DoubleExceptionalInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoPositiveDivisorPairs SurfaceGenusTwoPositiveSquare

/-- The complete weighted source on the original marking frame at indices 12, 13 and 14. -/
def highPart (c : CertifiedComponents X) (j : Fin 3) (i : Fin 11) : ℚ :=
  let k := Fin.natAdd 12 j
  pulledSquarePart (c.vertex (ancestorValue low)) 1 (squareBeta k) (powers k) (labels k) i

theorem high_sum (c : CertifiedComponents X) (j : Fin 3) :
    ancestorValue low (squareKey (Fin.natAdd 12 j)) = ∑ i, highPart c j i := by
  rw [square_framed, pulledSquare_eq_parts, ← component_eq, ← c.vertex_eq]
  rfl

/-- The eleven signed contributions for each of the three original high squares. -/
def highParts : Fin 3 → Fin 11 → ℚ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, (155 / 67392), (35 / 33696), (23 / 112320), (-41 / 71604), (35 / 33696), (31 / 2808),
      (749 / 84240), (101 / 5728320), (1 / 8320), (1 / 18720)],
    ![0, 0, 0, 0, (41 / 143208), (-7 / 22464), (-31 / 11232), (-749 / 336960), (-101 / 11456640),
      0, (-1 / 56160)]]

/-- The three complete ancestor values before the ordered mixed-marking transfer. -/
def highValues : Fin 3 → ℚ := ![0, (139 / 5760), (-29 / 5760)]

set_option Elab.async false
set_option maxRecDepth 65536

set_option maxHeartbeats 4000000 in
-- Check each boundary source with every original full-coordinate splitting.
private theorem source0 (k : Fin 11) : highPart Components.components 0 k = highParts 0 k := by
  fin_cases k <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Check each boundary source with every original full-coordinate splitting.
private theorem source1 (k : Fin 11) : highPart Components.components 1 k = highParts 1 k := by
  fin_cases k <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Check each boundary source with every original full-coordinate splitting.
private theorem source2 (k : Fin 11) : highPart Components.components 2 k = highParts 2 k := by
  fin_cases k <;> decide +kernel

theorem high_parts (j : Fin 3) (i : Fin 11) :
    highPart Components.components j i = highParts j i := by
  fin_cases j
  · exact source0 i
  · exact source1 i
  · exact source2 i

/-- Six individual sources contribute to the second/third-unit square on 2E. -/
theorem highest_support (i : Fin 11) :
    highPart Components.components 2 i ≠ 0 ↔ i ∈ ({4, 5, 6, 7, 8, 10} : Finset (Fin 11)) := by
  rw [high_parts]
  fin_cases i <;> decide +kernel

/-- The three highest squares at their original 15-key frame indices. -/
theorem highSquares (j : Fin 3) :
    ancestorValue low (squareKey (Fin.natAdd 12 j)) = highValues j := by
  rw [high_sum Components.components]
  simp only [high_parts]
  fin_cases j <;> decide +kernel

end AxiomaticGW.BlowupF1DoubleExceptionalInteriorPairs

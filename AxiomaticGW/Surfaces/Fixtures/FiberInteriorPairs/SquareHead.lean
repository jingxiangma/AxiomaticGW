/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.FiberInteriorPairs.Frame
public import AxiomaticGW.Surfaces.Fixtures.FiberInteriorPairs.ThirdPower

/-! # Fiber-frame squares of total cotangent degree at most four

These 18 keys suffice for every interior request except the two marking
orders of the second and third descendants of the unit. Each of the eleven
signed sources retains all placements of the extra marking.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoPositiveDivisorPairs SurfaceGenusTwoPositiveSquare

def headParts : Fin 18 → Fin 11 → ℚ :=
  ![![(-1 / 960), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 / 2880), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, (155 / 25272), (35 / 12636), (23 / 28080), 0, 0, 0, 0, 0, 0, 0],
    ![(-1 / 960), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 / 2880), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, (155 / 8424), (35 / 4212), (23 / 9360), 0, 0, 0, 0, 0, 0, 0],
    ![(-1 / 1440), (155 / 50544), (35 / 25272), (23 / 56160), 0, 0, 0, 0, 0, 0, 0],
    ![(-1 / 1440), (155 / 50544), (35 / 25272), (23 / 56160), 0, 0, 0, 0, 0, 0, 0],
    ![0, (155 / 50544), (35 / 25272), (23 / 56160), 0, 0, 0, 0, 0, 0, 0],
    ![0, (1085 / 50544), (245 / 25272), (23 / 6240), (41 / 17901), (-35 / 16848), (-31 / 2106),
        (-749 / 84240), (-101 / 1432080), (-1 / 1040), 0],
    ![0, (155 / 12636), (35 / 6318), (23 / 9360), (41 / 17901), (-35 / 16848), (-31 / 2106), (-749
        / 84240), (-101 / 1432080), (-1 / 1040), 0],
    ![0, (-155 / 8424), (-35 / 4212), 0, (41 / 5967), (-7 / 1404), (-31 / 1404), 0, (-101 /
        477360), (-3 / 1040), 0],
    ![0, (155 / 12636), (35 / 6318), (23 / 9360), (41 / 17901), (-35 / 16848), (-31 / 2106), (-749
        / 84240), (-101 / 1432080), (-1 / 1040), 0],
    ![0, (155 / 50544), (35 / 25272), (23 / 18720), (41 / 17901), (-35 / 16848), (-31 / 2106),
        (-749 / 84240), (-101 / 1432080), (-1 / 1040), 0],
    ![0, (-155 / 8424), (-35 / 4212), 0, (41 / 5967), (-7 / 1404), (-31 / 1404), 0, (-101 /
        477360), (-3 / 1040), 0],
    ![0, (155 / 16848), (35 / 8424), (23 / 18720), 0, 0, 0, 0, 0, 0, 0],
    ![0, (-155 / 8424), (-35 / 4212), (-23 / 14040), (41 / 17901), (-7 / 2808), (-31 / 1404),
        (-749 / 42120), (-101 / 1432080), (-1 / 1040), 0],
    ![0, (-155 / 8424), (-35 / 4212), (-23 / 14040), (41 / 17901), (-7 / 2808), (-31 / 1404),
        (-749 / 42120), (-101 / 1432080), (-1 / 1040), 0]]

def headValues : Fin 18 → ℚ :=
  ![(-1 / 960),
    (-1 / 2880),
    (7 / 720),
    (-1 / 960),
    (-1 / 2880),
    (7 / 240),
    (1 / 240),
    (1 / 240),
    (7 / 1440),
    (1 / 96),
    (-1 / 240),
    (-1 / 20),
    (-1 / 240),
    (-3 / 160),
    (-1 / 20),
    (7 / 480),
    (-5 / 72),
    (-5 / 72)]

private def headSource (j : Fin 18) (i : Fin 11) : ℚ :=
  pulledSquarePart (Components.ThirdPower.components.vertex (ancestorValue low)) 1
    (squareBeta j.castSucc) (powers j.castSucc) (labels j.castSucc) i

set_option Elab.async false
set_option maxRecDepth 65536

set_option maxHeartbeats 4000000 in
-- Replay the signed sources at this curve class with both cotangent powers.
private theorem head0 (i : Fin 11) : headSource 0 i = headParts 0 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay the signed sources at this curve class with both cotangent powers.
private theorem head1 (i : Fin 11) : headSource 1 i = headParts 1 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay the signed sources at this curve class with both cotangent powers.
private theorem head2 (i : Fin 11) : headSource 2 i = headParts 2 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay the signed sources at this curve class with both cotangent powers.
private theorem head3 (i : Fin 11) : headSource 3 i = headParts 3 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay the signed sources at this curve class with both cotangent powers.
private theorem head4 (i : Fin 11) : headSource 4 i = headParts 4 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay the signed sources at this curve class with both cotangent powers.
private theorem head5 (i : Fin 11) : headSource 5 i = headParts 5 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay the signed sources at this curve class with both cotangent powers.
private theorem head6 (i : Fin 11) : headSource 6 i = headParts 6 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay the signed sources at this curve class with both cotangent powers.
private theorem head7 (i : Fin 11) : headSource 7 i = headParts 7 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay the signed sources at this curve class with both cotangent powers.
private theorem head8 (i : Fin 11) : headSource 8 i = headParts 8 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay the signed sources at this curve class with both cotangent powers.
private theorem head9 (i : Fin 11) : headSource 9 i = headParts 9 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay the signed sources at this curve class with both cotangent powers.
private theorem head10 (i : Fin 11) : headSource 10 i = headParts 10 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay the signed sources at this curve class with both cotangent powers.
private theorem head11 (i : Fin 11) : headSource 11 i = headParts 11 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay the signed sources at this curve class with both cotangent powers.
private theorem head12 (i : Fin 11) : headSource 12 i = headParts 12 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay the signed sources at this curve class with both cotangent powers.
private theorem head13 (i : Fin 11) : headSource 13 i = headParts 13 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay the signed sources at this curve class with both cotangent powers.
private theorem head14 (i : Fin 11) : headSource 14 i = headParts 14 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay the signed sources at this curve class with both cotangent powers.
private theorem head15 (i : Fin 11) : headSource 15 i = headParts 15 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay the signed sources at this curve class with both cotangent powers.
private theorem head16 (i : Fin 11) : headSource 16 i = headParts 16 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay the signed sources at this curve class with both cotangent powers.
private theorem head17 (i : Fin 11) : headSource 17 i = headParts 17 i := by
  fin_cases i <;> decide +kernel

private theorem heads (j : Fin 18) (i : Fin 11) : headSource j i = headParts j i := by
  fin_cases j
  · exact head0 i
  · exact head1 i
  · exact head2 i
  · exact head3 i
  · exact head4 i
  · exact head5 i
  · exact head6 i
  · exact head7 i
  · exact head8 i
  · exact head9 i
  · exact head10 i
  · exact head11 i
  · exact head12 i
  · exact head13 i
  · exact head14 i
  · exact head15 i
  · exact head16 i
  · exact head17 i

theorem first_squares (j : Fin 18) :
    ancestorValue low (squareKey j.castSucc) = headValues j := by
  rw [square_framed, pulledSquare_eq_parts, ← component_eq,
    ← Components.ThirdPower.components.vertex_eq]
  change (∑ i, headSource j i) = _
  simp only [heads j]
  fin_cases j <;> decide +kernel

end AxiomaticGW.BlowupF1FiberInteriorPairs

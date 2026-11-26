/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.DoubleExceptionalInteriorPairs.Frame
public import AxiomaticGW.Surfaces.Fixtures.DoubleExceptionalInteriorPairs.Components
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1SecondUnitPair

/-! # The first twelve square ancestors of the two-marked double exceptional frame

The class-zero and primitive second-unit squares use their original two-marked
certificates. Each remaining square sums its eleven signed boundary components,
using full-key certified rational and elliptic vertex values.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1DoubleExceptionalInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoPositiveDivisorPairs SurfaceGenusTwoPositiveSquare

/-- The twelve complete ancestor values in frame order, before the mixed transfer. -/
def lowerValues : Fin 12 → ℚ := ![(-1 / 2880), 0, (1 / 240), (-5 / 576), 0, (-17 / 960),
  0, 0, 0, 0, (-47 / 1440), (101 / 5760)]

set_option Elab.async false
set_option maxRecDepth 65536

private def lowerPart (j : Fin 12) (i : Fin 11) : ℚ :=
  let k := Fin.castAdd 3 j
  pulledSquarePart (Components.components.vertex (ancestorValue low)) 1
    (squareBeta k) (powers k) (labels k) i

private theorem lowerFromParts (j : Fin 12) (v : Fin 11 → ℚ)
    (hp : ∀ i, lowerPart j i = v i) (hs : ∑ i, v i = lowerValues j) :
    ancestorValue low (squareKey (Fin.castAdd 3 j)) = lowerValues j := by
  rw [square_framed, pulledSquare_eq_parts, ← component_eq, ← Components.components.vertex_eq]
  change ∑ i, lowerPart j i = _
  simp only [hp]
  exact hs

private theorem lower0 : ancestorValue low (squareKey (Fin.castAdd 3 (0 : Fin 12))) =
    lowerValues 0 := by
  rw [square_framed]
  rw [show squareBeta (Fin.castAdd 3 (0 : Fin 12)) = 0 by decide +kernel]
  exact BlowupF1SecondUnitPair.square_values 1

private theorem lower1 : ancestorValue low (squareKey (Fin.castAdd 3 (1 : Fin 12))) =
    lowerValues 1 := by
  apply lowerFromParts _ ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  · intro i
    fin_cases i <;> decide +kernel
  · decide +kernel

private theorem lower2 : ancestorValue low (squareKey (Fin.castAdd 3 (2 : Fin 12))) =
    lowerValues 2 := by
  apply lowerFromParts _ ![(-1 / 2880), (155 / 101088), (35 / 50544), (23 / 224640), 0,
    (7 / 33696), (31 / 16848), 0, 0, (1 / 8320), (1 / 56160)]
  · intro i
    fin_cases i <;> decide +kernel
  · decide +kernel

private theorem lower3 : ancestorValue low (squareKey (Fin.castAdd 3 (3 : Fin 12))) =
    lowerValues 3 := by
  apply lowerFromParts _ ![0, (-155 / 67392), (-35 / 33696), (-23 / 224640), (41 / 143208),
    (-7 / 11232), (-155 / 33696), 0, (-101 / 11456640), (-1 / 4160),
    (-1 / 18720)]
  · intro i
    fin_cases i <;> decide +kernel
  · decide +kernel

private theorem lower4 : ancestorValue low (squareKey (Fin.castAdd 3 (4 : Fin 12))) =
    lowerValues 4 := by
  apply lowerFromParts _ ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  · intro i
    fin_cases i <;> decide +kernel
  · decide +kernel

private theorem lower5 : ancestorValue low (squareKey (Fin.castAdd 3 (5 : Fin 12))) =
    lowerValues 5 := by
  rw [square_framed]
  exact BlowupF1SecondUnitPair.square_values 0

private theorem lower6 : ancestorValue low (squareKey (Fin.castAdd 3 (6 : Fin 12))) =
    lowerValues 6 := by
  apply lowerFromParts _ ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  · intro i
    fin_cases i <;> decide +kernel
  · decide +kernel

private theorem lower7 : ancestorValue low (squareKey (Fin.castAdd 3 (7 : Fin 12))) =
    lowerValues 7 := by
  apply lowerFromParts _ ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  · intro i
    fin_cases i <;> decide +kernel
  · decide +kernel

private theorem lower8 : ancestorValue low (squareKey (Fin.castAdd 3 (8 : Fin 12))) =
    lowerValues 8 := by
  apply lowerFromParts _ ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  · intro i
    fin_cases i <;> decide +kernel
  · decide +kernel

private theorem lower9 : ancestorValue low (squareKey (Fin.castAdd 3 (9 : Fin 12))) =
    lowerValues 9 := by
  apply lowerFromParts _ ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  · intro i
    fin_cases i <;> decide +kernel
  · decide +kernel

private theorem lower10 : ancestorValue low (squareKey (Fin.castAdd 3 (10 : Fin 12))) =
    lowerValues 10 := by
  apply lowerFromParts _ ![0, (-775 / 101088), (-175 / 50544), (-23 / 44928), (41 / 71604),
    (-7 / 4212), (-31 / 2106), (-749 / 168480), (-101 / 5728320),
    (-1 / 1664), (-7 / 56160)]
  · intro i
    fin_cases i <;> decide +kernel
  · decide +kernel

private theorem lower11 : ancestorValue low (squareKey (Fin.castAdd 3 (11 : Fin 12))) =
    lowerValues 11 := by
  apply lowerFromParts _ ![0, (155 / 50544), (35 / 25272), 0, (-205 / 143208), (7 / 3744),
    (31 / 2592), 0, (101 / 2291328), (1 / 2080), (1 / 6240)]
  · intro i
    fin_cases i <;> decide +kernel
  · decide +kernel

/-- The zero-class, primitive, and first six double exceptional squares on the original frame. -/
theorem lower_squares (j : Fin 12) :
    ancestorValue low (squareKey (Fin.castAdd 3 j)) = lowerValues j := by
  fin_cases j
  · exact lower0
  · exact lower1
  · exact lower2
  · exact lower3
  · exact lower4
  · exact lower5
  · exact lower6
  · exact lower7
  · exact lower8
  · exact lower9
  · exact lower10
  · exact lower11

end AxiomaticGW.BlowupF1DoubleExceptionalInteriorPairs

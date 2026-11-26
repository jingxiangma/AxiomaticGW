/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingSingletons.Frame

/-! # Cotangent-degree 1 lower-genus components at both rulings -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRuling.First
open SurfaceGenusTwoPositiveSquare SurfaceLowGenusPointCache

/-- Marked profiles from the double-line square needed at this cotangent degree. -/
def profileIndex (j : Fin 121) : Fin 177 :=
  if h : j.val < 106 then ⟨j.val + 38, by omega⟩
  else ⟨j.val + 56, by omega⟩

/-- The original genus and markings with the actual full ruling coordinate. -/
def key (i : Fin 2) (j : Fin 121) : SurfaceAncestorKey X :=
  rulingKey i (BlowupTwoDoubleLineComponents.First.key (profileIndex j))

/-- Values reconstructed at the ruling classes, in the indicated relative marking order. -/
def values (j : Fin 121) : ℚ :=
  (#[0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 3, 0, 1, 0, 0, 2, 0, 1, 0, 1, 0, 0,
    0, 0, 0, 1, 0, -1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, -2, 0, 0, -1, 1, -1, 0,
    -1, 0, 1, 2, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, -3, -1, 0, -2, 1, 0,
    -1/12, -1/12, -1/12, 0, 0, 0, -1/12, -1/12, -1/12, 0, -1/12, 0, -1/12, 0] :
    Array ℚ)[j.val]'j.isLt

set_option Elab.async false
set_option maxRecDepth 65536

set_option maxHeartbeats 4500000 in
-- Check each full marked key by the original recurrence on each ruling separately.
/-- Both ruling evaluations satisfy the full genus-zero or genus-one boundary equation. -/
theorem accepted (i : Fin 2) (j : Fin 121) :
    values j = stagedValue (initial i).value (key i j) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Possible full keys in each lookup slot for each of the two ruling classes. -/
def indices (i : Fin 2) (s : ℕ) : List (Fin 121) :=
  let buckets : Array (List (Fin 121)) := if i = 0 then
    #[[39, 51, 67, 99], [11, 80, 86], [], [7, 22, 57], [4, 23, 64, 89], [68, 74, 108],
      [0, 33, 60, 110], [9, 42, 72], [16, 78, 118], [37, 90, 98], [2, 109],
      [17, 46, 96], [31, 104], [], [12, 47, 100, 115], [35, 48, 81], [52, 58, 83],
      [5, 15], [18], [8, 25, 34, 61, 69], [49, 73], [84, 93, 107, 116, 119],
      [1, 38, 71], [20, 75, 91], [28, 62, 87, 97, 106], [], [112], [29, 40, 101],
      [76, 82], [113], [53], [44, 55], [70, 102], [26], [10, 30, 50], [14, 85, 111],
      [56, 65, 92, 114], [3, 21], [63, 88], [13, 24, 32, 43, 59, 94], [79], [41, 117],
      [6, 36, 77], [19, 54], [95, 105], [45], [27, 66, 103, 120]]
  else
    #[[1, 109], [14, 45, 92], [31, 85], [], [11, 48, 82, 112], [23, 47, 101], [59, 63],
      [4, 18], [15, 55], [9, 36, 41, 53, 78], [49, 72], [30, 102, 105, 107, 116, 118],
      [2, 26, 67], [20, 66, 97], [39, 56, 87, 91, 106], [], [83, 115], [24, 32, 81],
      [68, 100], [110], [61], [44], [77, 84], [38], [10, 51], [17, 104, 114],
      [62, 65, 96, 111], [3, 22], [58, 89], [13, 29, 40, 43, 52], [74], [34, 117],
      [6, 25, 70], [16, 60], [90, 93], [46], [37, 75, 86, 120], [28, 50, 71, 80],
      [12, 99, 103], [], [7, 21, 64, 94], [5, 35, 57, 88], [76, 79, 108],
      [0, 42, 54, 113], [8, 33, 73], [19, 69, 119], [27, 95, 98]]
  (buckets[s]?).getD []

/-- The slot filter retains every checked full key on both charts. -/
theorem index_complete (i : Fin 2) (j : Fin 121) : j ∈ indices i (slot (key i j)) := by
  revert i j
  decide +kernel

/-- Complete certified backend through cotangent degree 1 on the indicated ruling. -/
def backend (i : Fin 2) : CertifiedComponents X :=
  fullLayer i (initial i) 1 fun s ↦
    (indices i s).map fun j ↦ (initial i).entry (key i j) (values j) (accepted i j)

end AxiomaticGW.BlowupTwoRuling.First

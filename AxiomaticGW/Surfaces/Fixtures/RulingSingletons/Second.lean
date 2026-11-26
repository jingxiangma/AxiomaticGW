/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingSingletons.First

/-! # Cotangent-degree 2 lower-genus components at both rulings -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRuling.Second
open SurfaceGenusTwoPositiveSquare SurfaceLowGenusPointCache

/-- Marked profiles from the double-line square needed at this cotangent degree. -/
def profileIndex (j : Fin 65) : Fin 75 :=
  if h : j.val < 22 then ⟨j.val + 0, by omega⟩
  else ⟨j.val + 10, by omega⟩

/-- The original genus and markings with the actual full ruling coordinate. -/
def key (i : Fin 2) (j : Fin 65) : SurfaceAncestorKey X :=
  rulingKey i (BlowupTwoDoubleLineComponents.Second.key (profileIndex j))

/-- Values reconstructed at the ruling classes, in the indicated relative marking order. -/
def values (j : Fin 65) : ℚ :=
  (#[0, 0, 1, 2, 0, 0, 0, 1, 2, 2, 2, 0, 0, 0, 0, 2, 4, 0, 0, 0, -2, -4, -1/12, 0, -1/12,
    -1/6, 0, -1/6, -1/24, -1/24, 1/24, -1/4, 0, -1/12, 1/6, -1/24, 1/6, 1/12, 0, 1/12,
    1/12, 0, 1/12, -1/24, -1/12, -1/24, 1/8, -1/24, 5/24, 1/12, 0, 1/4, 1/6, -1/24, 1/6,
    -1/6, 0, -1/6, 0, 1/6, -1/24, 1/6, -1/12, -1/24, 1/6] : Array ℚ)[j.val]'j.isLt

set_option Elab.async false
set_option maxRecDepth 65536

set_option maxHeartbeats 4500000 in
-- Check each full marked key by the original recurrence on each ruling separately.
/-- Both ruling evaluations satisfy the full genus-zero or genus-one boundary equation. -/
theorem accepted (i : Fin 2) (j : Fin 65) :
    values j = stagedValue (First.backend i).value (key i j) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Possible full keys in each lookup slot for each of the two ruling classes. -/
def indices (i : Fin 2) (s : ℕ) : List (Fin 65) :=
  let buckets : Array (List (Fin 65)) := if i = 0 then
    #[[33], [6, 46], [9, 11, 24, 38], [40, 56, 63], [45, 49], [4], [19, 26, 35],
      [21, 48], [], [59], [17, 53], [], [], [], [], [], [57, 64], [10, 29, 41], [50],
      [5, 27], [2, 23, 31], [], [44], [0, 60], [], [13, 37, 47], [], [58], [7], [34],
      [16, 42], [18, 39, 51], [], [20, 52], [3, 15, 32], [36], [55, 61], [1, 62], [],
      [25, 54], [28], [], [8], [22], [], [12, 43], [14, 30]]
  else
    #[[17, 45], [], [], [], [], [], [56, 62], [10, 30, 51], [42], [8, 26], [2, 24, 31],
      [], [54], [0, 61], [], [11, 39, 46], [], [58], [4], [34], [21, 50], [19, 41, 47],
      [], [15, 43], [3, 20, 33], [35], [55, 60], [1, 64], [], [25, 44], [28], [], [5],
      [22], [], [14, 52], [12, 29], [32], [9, 37], [6, 13, 23, 48], [49, 57, 63],
      [40, 53], [7], [18, 27, 36], [16, 38], [], [59]]
  (buckets[s]?).getD []

/-- The slot filter retains every checked full key on both charts. -/
theorem index_complete (i : Fin 2) (j : Fin 65) : j ∈ indices i (slot (key i j)) := by
  revert i j
  decide +kernel

/-- Complete certified backend through cotangent degree 2 on the indicated ruling. -/
def backend (i : Fin 2) : CertifiedComponents X :=
  fullLayer i (First.backend i) 2 fun s ↦
    (indices i s).map fun j ↦ (First.backend i).entry (key i j) (values j) (accepted i j)

end AxiomaticGW.BlowupTwoRuling.Second

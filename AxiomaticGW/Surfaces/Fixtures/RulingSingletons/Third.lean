/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingSingletons.Second

/-! # Cotangent-degree 3 lower-genus components at both rulings -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRuling.Third
open SurfaceGenusTwoPositiveSquare SurfaceLowGenusPointCache

/-- Marked profiles from the double-line square needed at this cotangent degree. -/
def profileIndex (j : Fin 9) : Fin 9 :=
  j

/-- The original genus and markings with the actual full ruling coordinate. -/
def key (i : Fin 2) (j : Fin 9) : SurfaceAncestorKey X :=
  rulingKey i (BlowupTwoDoubleLineComponents.Third.key (profileIndex j))

/-- Values reconstructed at the ruling classes, in the indicated relative marking order. -/
def values (j : Fin 9) : ℚ :=
  (#[0, 0, 1/6, 1/3, -1/12, -1/6, 1/6, 1/3, 0] : Array ℚ)[j.val]'j.isLt

set_option Elab.async false
set_option maxRecDepth 65536

set_option maxHeartbeats 4500000 in
-- Check each full marked key by the original recurrence on each ruling separately.
/-- Both ruling evaluations satisfy the full genus-zero or genus-one boundary equation. -/
theorem accepted (i : Fin 2) (j : Fin 9) :
    values j = stagedValue (Second.backend i).value (key i j) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Possible full keys in each lookup slot for each of the two ruling classes. -/
def indices (i : Fin 2) (s : ℕ) : List (Fin 9) :=
  let buckets : Array (List (Fin 9)) := if i = 0 then
    #[[], [4], [], [], [], [], [3], [], [], [], [], [], [], [], [], [], [2], [], [],
      [0], [], [], [8], [], [6], [1], [], [], [], [], [], [], [], [], [], [], [5], [7],
      [], [], [], [], [], [], [], [], []]
  else
    #[[], [], [], [], [], [], [2], [], [], [0], [], [], [8], [], [4], [1], [], [], [],
      [], [], [], [], [], [], [], [7], [5], [], [], [], [], [], [], [], [], [], [], [6],
      [], [], [], [], [3], [], [], []]
  (buckets[s]?).getD []

/-- The slot filter retains every checked full key on both charts. -/
theorem index_complete (i : Fin 2) (j : Fin 9) : j ∈ indices i (slot (key i j)) := by
  revert i j
  decide +kernel

/-- Complete certified backend through cotangent degree 3 on the indicated ruling. -/
def backend (i : Fin 2) : CertifiedComponents X :=
  fullLayer i (Second.backend i) 3 fun s ↦
    (indices i s).map fun j ↦ (Second.backend i).entry (key i j) (values j) (accepted i j)

end AxiomaticGW.BlowupTwoRuling.Third

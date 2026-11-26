/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.BPFrame
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoRulingOneMarking

/-! # Certified genus-two singleton vertices on every subclass of either ruling

A genus-two vertex in a stable two-marked boundary graph can meet a rational
tail at a single flag. The lookup below preserves the original recursion on
all other keys. Its entries are ancestors before descendant calibration.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRuling.SingletonVertices
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants
open BlowupTwoDoubleLine (terminals)

/-- The unchanged low-cotangent canonical base. -/
abbrev low := SurfaceGenusTwoBlowupLowPsi.ancestorValueWith terminals

/-- The basis singleton at the matching dimension on one of the four subclasses. -/
def key (i : Fin 2) (s : Fin 4) (j : Fin 5) : SurfaceAncestorKey X :=
  oneMarkingKey (BP.subcurve i s) (label i j)
    ((![2, 3, 3, 4] : Fin 4 → ℕ) s - (label i j).codimension)

/-- The constant-curve, exceptional, strict-line and ruling ancestor rows. -/
def values (s : Fin 4) : Fin 5 → ℚ :=
  ![![49/5760, -1/960, -1/2880, -1/2880, 0],
    ![1/240, 0, -13/2880, 0, 0],
    ![1/240, 13/2880, 13/2880, 13/2880, 0], leadingValues] s

/-- Each singleton entry is reconstructed by its original genus-two evaluator. -/
theorem accepted (i : Fin 2) (s : Fin 4) (j : Fin 5) :
    ancestorValue low (key i s j) = values s j := by
  fin_cases s
  · fin_cases j
    · exact tail_values i 0
    · exact tail_values i 1
    · exact tail_values i 2
    · exact tail_values i 3
    · exact tail_values i 4
  · fin_cases j
    · exact (BlowupTwoExceptionalOneMarking.exceptional_ancestors low i).1
    · exact tail_values i 7
    · exact tail_values i 8
    · exact tail_values i 9
    · exact tail_values i 10
  · fin_cases j
    · exact BlowupTwoLineOneMarking.high_ancestors low 0
    · exact BlowupTwoLineOneMarking.high_ancestors low 1
    · exact tail_values i 5
    · fin_cases i
      · exact BlowupTwoLineOneMarking.high_ancestors low 3
      · exact BlowupTwoLineOneMarking.high_ancestors low 2
    · exact tail_values i 6
  · exact high_ancestors low i j

/-- All twenty pairs of effective subclass and basis label. -/
def positions : List (Fin 4 × Fin 5) :=
  (List.finRange 4).flatMap fun s ↦ (List.finRange 5).map fun j ↦ (s, j)

/-- Match a complete singleton key, keeping original evaluation on a miss. -/
def next (i : Fin 2) (q : SurfaceAncestorKey X) : ℚ :=
  match positions.find? (fun p ↦ decide (q = key i p.1 p.2)) with
  | some p => values p.1 p.2
  | none => ancestorValue low q

/-- Replaying these singleton flags leaves every original ancestor unchanged. -/
theorem next_eq (i : Fin 2) : next i = ancestorValue low := by
  funext q
  unfold next
  split
  · rename_i p hp
    have hb := List.find?_some (p := fun t : Fin 4 × Fin 5 ↦ decide (q = key i t.1 t.2)) hp
    have hq : q = key i p.1 p.2 := of_decide_eq_true hb
    rw [hq, accepted]
  · rfl

end AxiomaticGW.BlowupTwoRuling.SingletonVertices

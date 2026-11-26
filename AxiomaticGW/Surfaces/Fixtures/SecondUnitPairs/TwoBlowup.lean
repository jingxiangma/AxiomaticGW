/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoPairTerms
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1SecondUnitPair
public import AxiomaticGW.Surfaces.Fixtures.SecondUnitPairs.TwoBlowupCache
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Assembly

/-! # Ordered two-marked genus-two requests with a second descendant of the unit

All sparse calibration rows are checked against the original two-mark transfer.
The contribution of each pulled square retains the leading correction and
the ten original boundary sources with all their attached markings.
-/

@[expose] public section
namespace AxiomaticGW.GenusTwoSecondUnitPairs.TwoBlowup
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants
open SurfaceGenusTwoPositiveDivisorPairs SurfaceGenusTwoPositiveSquare
set_option Elab.async false
set_option maxRecDepth 65536

abbrev target := SurfaceTarget.blowupTwo
private abbrev low :=
  SurfaceGenusTwoBlowupLowPsi.ancestorValueWith (BlowupTwoLineTable.candidate 0)

private def beta : Fin 15 → target.Curve :=
  ![![0, 0, 0],
    ![0, 0, 0],
    ![0, 0, 0],
    ![0, 0, 1],
    ![0, 0, 1],
    ![0, 0, 1],
    ![0, 0, 1],
    ![0, 1, 0],
    ![0, 1, 0],
    ![0, 1, 0],
    ![0, 1, 0],
    ![1, 0, 0],
    ![1, 0, 0],
    ![1, 0, 0],
    ![1, 0, 0]]

private def mark : Fin 15 → SurfaceInsertion target :=
  ![⟨.hyperplane, 0⟩,
    ⟨.exceptional 0, 0⟩,
    ⟨.exceptional 1, 0⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 1, 1⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 1, 1⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 1, 1⟩,
    ⟨.unit, 2⟩]

private def highKey (j : Fin 15) : SurfaceAncestorKey target :=
  pairKey (beta j) ⟨.unit, 2⟩ (mark j)

private def power (j : Fin 15) : Option (Fin 1) → ℕ :=
  fun k ↦ Option.elim k (mark j).psi (fun _ ↦ 0)

private def states (j : Fin 15) : Option (Fin 1) → SurfaceBasisLabel target :=
  fun k ↦ Option.elim k (mark j).label (fun _ ↦ .unit)

private theorem framed (j : Fin 15) :
    ancestorValue low (highKey j) =
      pulledSquare (vertex (ancestorValue low)) 1 (beta j) (power j) (states j) := by
  fin_cases j
  all_goals
    rw [ancestorValue_pulledSquare low _ rfl (by decide +kernel) (by decide +kernel), ← vertex_eq]
    congr 1 <;> decide +kernel

private def entries : Fin 15 → Fin 11 → ℚ :=
  ![![(-1 / 960), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 / 2880), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 / 2880), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, (155 / 33696), (35 / 16848), (23 / 44928), 0, (7 / 16848), (31 / 5616),
      (749 / 168480), 0, (1 / 8320), (1 / 56160)],
    ![0, (155 / 33696), (35 / 16848), (23 / 44928), 0, (7 / 16848), (31 / 5616),
      (749 / 168480), 0, (1 / 8320), (1 / 56160)],
    ![0, (155 / 33696), (35 / 16848), (23 / 44928), 0, (7 / 16848), (31 / 5616),
      (749 / 168480), 0, (1 / 8320), (1 / 56160)],
    ![0, (155 / 67392), (35 / 33696), (23 / 112320), (-41 / 143208), (49 / 67392),
      (31 / 3744), (749 / 112320), (101 / 11456640), (1 / 8320), (1 / 28080)],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, (-155 / 33696), (-35 / 16848), (-23 / 44928), 0, (-7 / 16848), (-31 / 5616),
      (-749 / 168480), 0, (-1 / 8320), (-1 / 56160)],
    ![0, (155 / 67392), (35 / 33696), (23 / 112320), (-41 / 143208), (49 / 67392),
      (31 / 3744), (749 / 112320), (101 / 11456640), (1 / 8320), (1 / 28080)],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, (-155 / 33696), (-35 / 16848), (-23 / 44928), 0, (-7 / 16848), (-31 / 5616),
      (-749 / 168480), 0, (-1 / 8320), (-1 / 56160)],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, (155 / 67392), (35 / 33696), (23 / 112320), (-41 / 143208), (49 / 67392),
      (31 / 3744), (749 / 112320), (101 / 11456640), (1 / 8320), (1 / 28080)]]

private def highValues : Fin 15 → ℚ :=
  ![(-1 / 960),
    (-1 / 2880),
    (-1 / 2880),
    (17 / 960),
    (17 / 960),
    (17 / 960),
    (11 / 576),
    0,
    0,
    (-17 / 960),
    (11 / 576),
    0,
    (-17 / 960),
    0,
    (11 / 576)]

private def source (j : Fin 15) (i : Fin 11) : ℚ :=
  pulledSquarePart (cachedComponent TwoBlowupCache.pool (ancestorValue low)) 1
    (beta j) (power j) (states j) i

private theorem of_parts (r : Fin 15) (h : ∀ i, source r i = entries r i) :
    pulledSquare (vertex (ancestorValue low)) 1 (beta r) (power r) (states r) = highValues r := by
  rw [pulledSquare_eq_parts, ← component_eq, ← cachedComponent_eq TwoBlowupCache.pool]
  change (∑ i, source r i) = _
  simp only [h]
  fin_cases r <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay each source at its complete curve, marking powers and basis assignments.
private theorem graph0 (i : Fin 11) : source 0 i = entries 0 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay each source at its complete curve, marking powers and basis assignments.
private theorem graph1 (i : Fin 11) : source 1 i = entries 1 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay each source at its complete curve, marking powers and basis assignments.
private theorem graph2 (i : Fin 11) : source 2 i = entries 2 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay each source at its complete curve, marking powers and basis assignments.
private theorem graph3 (i : Fin 11) : source 3 i = entries 3 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay each source at its complete curve, marking powers and basis assignments.
private theorem graph4 (i : Fin 11) : source 4 i = entries 4 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay each source at its complete curve, marking powers and basis assignments.
private theorem graph5 (i : Fin 11) : source 5 i = entries 5 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay each source at its complete curve, marking powers and basis assignments.
private theorem graph6 (i : Fin 11) : source 6 i = entries 6 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay each source at its complete curve, marking powers and basis assignments.
private theorem graph7 (i : Fin 11) : source 7 i = entries 7 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay each source at its complete curve, marking powers and basis assignments.
private theorem graph8 (i : Fin 11) : source 8 i = entries 8 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay each source at its complete curve, marking powers and basis assignments.
private theorem graph9 (i : Fin 11) : source 9 i = entries 9 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay each source at its complete curve, marking powers and basis assignments.
private theorem graph10 (i : Fin 11) : source 10 i = entries 10 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay each source at its complete curve, marking powers and basis assignments.
private theorem graph11 (i : Fin 11) : source 11 i = entries 11 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay each source at its complete curve, marking powers and basis assignments.
private theorem graph12 (i : Fin 11) : source 12 i = entries 12 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay each source at its complete curve, marking powers and basis assignments.
private theorem graph13 (i : Fin 11) : source 13 i = entries 13 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay each source at its complete curve, marking powers and basis assignments.
private theorem graph14 (i : Fin 11) : source 14 i = entries 14 i := by
  fin_cases i <;> decide +kernel

private theorem squares (j : Fin 15) : ancestorValue low (highKey j) = highValues j := by
  rw [framed]
  fin_cases j
  · exact of_parts 0 graph0
  · exact of_parts 1 graph1
  · exact of_parts 2 graph2
  · exact of_parts 3 graph3
  · exact of_parts 4 graph4
  · exact of_parts 5 graph5
  · exact of_parts 6 graph6
  · exact of_parts 7 graph7
  · exact of_parts 8 graph8
  · exact of_parts 9 graph9
  · exact of_parts 10 graph10
  · exact of_parts 11 graph11
  · exact of_parts 12 graph12
  · exact of_parts 13 graph13
  · exact of_parts 14 graph14

private def lowKey : Fin 9 → SurfaceAncestorKey target :=
  ![pairKey (X := target) ![0, 0, 0] ⟨.hyperplane, 0⟩ ⟨.hyperplane, 1⟩,
    pairKey (X := target) ![0, 0, 0] ⟨.hyperplane, 0⟩ ⟨.exceptional 0, 1⟩,
    pairKey (X := target) ![0, 0, 0] ⟨.hyperplane, 0⟩ ⟨.exceptional 1, 1⟩,
    pairKey (X := target) ![0, 0, 0] ⟨.exceptional 0, 0⟩ ⟨.hyperplane, 1⟩,
    pairKey (X := target) ![0, 0, 0] ⟨.exceptional 0, 0⟩ ⟨.exceptional 0, 1⟩,
    pairKey (X := target) ![0, 0, 0] ⟨.exceptional 0, 0⟩ ⟨.exceptional 1, 1⟩,
    pairKey (X := target) ![0, 0, 0] ⟨.exceptional 1, 0⟩ ⟨.hyperplane, 1⟩,
    pairKey (X := target) ![0, 0, 0] ⟨.exceptional 1, 0⟩ ⟨.exceptional 0, 1⟩,
    pairKey (X := target) ![0, 0, 0] ⟨.exceptional 1, 0⟩ ⟨.exceptional 1, 1⟩]

private def lowValues : Fin 9 → ℚ :=
  ![0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0]

private theorem low_values (j : Fin 9) : ancestorValue low (lowKey j) = lowValues j := by
  rw [ancestorValue_low low _ (by fin_cases j <;> rfl) (by fin_cases j <;> decide +kernel)]
  fin_cases j <;> decide +kernel

private def key : Fin 24 → SurfaceAncestorKey target :=
  Fin.addCases (m := 15) (n := 9) highKey lowKey

private def number : Fin 24 → ℚ :=
  Fin.addCases (m := 15) (n := 9) highValues lowValues

private theorem checked (j : Fin 24) :
    ancestorValueWith (BlowupTwoLineTable.candidate 0) (key j) = number j := by
  change ancestorValue low (key j) = number j
  refine Fin.addCases (m := 15) (n := 9) (fun i ↦ ?_) (fun i ↦ ?_) j
  · simpa only [key, number, Fin.addCases_left] using squares i
  · simpa only [key, number, Fin.addCases_right] using low_values i

def curve : Fin 21 → target.Curve :=
  ![![1, 0, 0],
    ![1, 0, 0],
    ![1, 0, 0],
    ![1, 0, 0],
    ![1, 0, 0],
    ![1, 0, 0],
    ![1, 0, 0],
    ![0, 1, 0],
    ![0, 1, 0],
    ![0, 1, 0],
    ![0, 1, 0],
    ![0, 1, 0],
    ![0, 1, 0],
    ![0, 1, 0],
    ![0, 0, 1],
    ![0, 0, 1],
    ![0, 0, 1],
    ![0, 0, 1],
    ![0, 0, 1],
    ![0, 0, 1],
    ![0, 0, 1]]

def first : Fin 21 → SurfaceInsertion target :=
  ![⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 1, 1⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 1, 1⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 1, 1⟩]

def second : Fin 21 → SurfaceInsertion target :=
  ![⟨.unit, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 1, 1⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 1, 1⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 1, 1⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩]

/-- The complete ordered requests on the full effective classes. -/
def requests (j : Fin 21) : SurfaceQuery target := ⟨2, curve j, [first j, second j]⟩

private def row : Fin 21 → List (ℚ × Fin 24) :=
  ![[(-1, 1), (-1, 1), (1, 14)],
    [(-1, 18), (1, 11)],
    [(-1, 19), (-1, 1), (1, 12)],
    [(-1, 20), (1, 13)],
    [(-1, 18), (1, 11)],
    [(-1, 19), (-1, 1), (1, 12)],
    [(-1, 20), (1, 13)],
    [(-1, 2), (-1, 2), (1, 10)],
    [(-1, 21), (1, 7)],
    [(-1, 22), (1, 8)],
    [(-1, 23), (-1, 2), (1, 9)],
    [(-1, 21), (1, 7)],
    [(-1, 22), (1, 8)],
    [(-1, 23), (-1, 2), (1, 9)],
    [(-1, 0), (-1, 0), (1, 1), (1, 1), (1, 2), (1, 2), (1, 6)],
    [(-1, 15), (-1, 1), (-1, 2), (1, 0), (1, 18), (1, 21), (1, 3)],
    [(-1, 16), (-1, 1), (-1, 2), (1, 0), (1, 19), (1, 22), (1, 4)],
    [(-1, 17), (-1, 1), (-1, 2), (1, 0), (1, 20), (1, 23), (1, 5)],
    [(-1, 15), (-1, 1), (-1, 2), (1, 0), (1, 18), (1, 21), (1, 3)],
    [(-1, 16), (-1, 1), (-1, 2), (1, 0), (1, 19), (1, 22), (1, 4)],
    [(-1, 17), (-1, 1), (-1, 2), (1, 0), (1, 20), (1, 23), (1, 5)]]

/-- Exact values computed from the signed mixed transfer. -/
def values : Fin 21 → ℚ :=
  ![(19 / 960),
    0,
    (-5 / 288),
    0,
    0,
    (-5 / 288),
    0,
    (19 / 960),
    0,
    0,
    (-5 / 288),
    0,
    0,
    (-5 / 288),
    (19 / 960),
    (5 / 288),
    (5 / 288),
    (5 / 288),
    (5 / 288),
    (5 / 288),
    (5 / 288)]

private theorem mixed (j : Fin 21) :
    pairMixed (curve j) (first j) (second j) = pairExpression key (row j) := by
  fin_cases j <;> decide +kernel

/-- The original descendant reconstruction gives the indicated value on every request. -/
theorem accepted (j : Fin 21) : queryValue? 0 (requests j) = some (values j) := by
  rw [← queryValueWith?_eq_of_table 0 1 (BlowupTwoLineTable.candidate 0)
    (fun s hs ↦ (BlowupTwoLineTable.values_eq s hs).symm) (requests j)
      (by fin_cases j <;> decide +kernel)]
  unfold requests
  rw [queryValueWith?_pair, mixed, eval_pairExpression]
  simp only [checked]
  fin_cases j <;> decide +kernel

end AxiomaticGW.GenusTwoSecondUnitPairs.TwoBlowup

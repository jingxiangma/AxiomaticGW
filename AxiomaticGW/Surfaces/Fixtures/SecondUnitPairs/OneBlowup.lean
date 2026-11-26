/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoPairTerms
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1SecondUnitPair
public import AxiomaticGW.Surfaces.Fixtures.SecondUnitPairs.OneBlowupCache

/-! # Ordered two-marked genus-two requests with a second descendant of the unit

All sparse calibration rows are checked against the original two-mark transfer.
The contribution of each pulled square retains the leading correction and
the ten original boundary sources with all their attached markings.
-/

@[expose] public section
namespace AxiomaticGW.GenusTwoSecondUnitPairs.OneBlowup
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants
open SurfaceGenusTwoPositiveDivisorPairs SurfaceGenusTwoPositiveSquare
set_option Elab.async false
set_option maxRecDepth 65536

abbrev target := SurfaceTarget.hirzebruchOne
private abbrev low :=
  SurfaceGenusTwoBlowupLowPsi.ancestorValueWith BlowupF1ExceptionalOneMarkingRequest.boundary

private def beta : Fin 4 → target.Curve :=
  ![![0, 0],
    ![1, 0],
    ![1, 0],
    ![1, 0]]

private def mark : Fin 4 → SurfaceInsertion target :=
  ![⟨.exceptional 0, 0⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.unit, 2⟩]

private def highKey (j : Fin 4) : SurfaceAncestorKey target :=
  pairKey (beta j) ⟨.unit, 2⟩ (mark j)

private def power (j : Fin 4) : Option (Fin 1) → ℕ :=
  fun k ↦ Option.elim k (mark j).psi (fun _ ↦ 0)

private def states (j : Fin 4) : Option (Fin 1) → SurfaceBasisLabel target :=
  fun k ↦ Option.elim k (mark j).label (fun _ ↦ .unit)

private theorem framed (j : Fin 4) :
    ancestorValue low (highKey j) =
      pulledSquare (vertex (ancestorValue low)) 1 (beta j) (power j) (states j) := by
  fin_cases j
  all_goals
    rw [ancestorValue_pulledSquare low _ rfl (by decide +kernel) (by decide +kernel), ← vertex_eq]
    congr 1 <;> decide +kernel

private def entries : Fin 4 → Fin 11 → ℚ :=
  ![![(-1 / 2880), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, (-155 / 33696), (-35 / 16848), (-23 / 44928), 0, (-7 / 16848), (-31 / 5616),
      (-749 / 168480), 0, (-1 / 8320), (-1 / 56160)],
    ![0, (155 / 67392), (35 / 33696), (23 / 112320), (-41 / 143208), (49 / 67392),
      (31 / 3744), (749 / 112320), (101 / 11456640), (1 / 8320), (1 / 28080)]]

private def highValues : Fin 4 → ℚ :=
  ![(-1 / 2880),
    0,
    (-17 / 960),
    (11 / 576)]

private def source (j : Fin 4) (i : Fin 11) : ℚ :=
  pulledSquarePart (cachedComponent OneBlowupCache.pool (ancestorValue low)) 1
    (beta j) (power j) (states j) i

private theorem of_parts (r : Fin 4) (h : ∀ i, source r i = entries r i) :
    pulledSquare (vertex (ancestorValue low)) 1 (beta r) (power r) (states r) = highValues r := by
  rw [pulledSquare_eq_parts, ← component_eq, ← cachedComponent_eq OneBlowupCache.pool]
  change (∑ i, source r i) = _
  simp only [h]
  fin_cases r <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay each source at its complete curve, marking powers and basis assignments.
private theorem graph1 (i : Fin 11) : source 1 i = entries 1 i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Replay each source at its complete curve, marking powers and basis assignments.
private theorem graph3 (i : Fin 11) : source 3 i = entries 3 i := by
  fin_cases i <;> decide +kernel

private theorem squares (j : Fin 4) : ancestorValue low (highKey j) = highValues j := by
  rw [framed]
  fin_cases j
  · change pulledSquare (vertex (ancestorValue low)) 1 (beta 0) (power 0) (states 0) = highValues 0
    rw [show beta 0 = 0 by decide +kernel]
    exact BlowupF1SecondUnitPair.square_values 1
  · exact of_parts 1 graph1
  · exact BlowupF1SecondUnitPair.square_values 0
  · exact of_parts 3 graph3

private def lowKey : Fin 2 → SurfaceAncestorKey target :=
  ![pairKey (X := target) ![0, 0] ⟨.exceptional 0, 0⟩ ⟨.hyperplane, 1⟩,
    pairKey (X := target) ![0, 0] ⟨.exceptional 0, 0⟩ ⟨.exceptional 0, 1⟩]

private def lowValues : Fin 2 → ℚ :=
  ![0,
    0]

private theorem low_values (j : Fin 2) : ancestorValue low (lowKey j) = lowValues j := by
  rw [ancestorValue_low low _ (by fin_cases j <;> rfl) (by fin_cases j <;> decide +kernel)]
  fin_cases j <;> decide +kernel

private def key : Fin 6 → SurfaceAncestorKey target :=
  Fin.addCases (m := 4) (n := 2) highKey lowKey

private def number : Fin 6 → ℚ :=
  Fin.addCases (m := 4) (n := 2) highValues lowValues

private theorem checked (j : Fin 6) :
    ancestorValueWith BlowupF1ExceptionalOneMarkingRequest.boundary (key j) = number j := by
  change ancestorValue low (key j) = number j
  refine Fin.addCases (m := 4) (n := 2) (fun i ↦ ?_) (fun i ↦ ?_) j
  · simpa only [key, number, Fin.addCases_left] using squares i
  · simpa only [key, number, Fin.addCases_right] using low_values i

def curve : Fin 5 → target.Curve :=
  ![![1, 0],
    ![1, 0],
    ![1, 0],
    ![1, 0],
    ![1, 0]]

def first : Fin 5 → SurfaceInsertion target :=
  ![⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 1⟩]

def second : Fin 5 → SurfaceInsertion target :=
  ![⟨.unit, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 2⟩]

/-- The complete ordered requests on the full effective classes. -/
def requests (j : Fin 5) : SurfaceQuery target := ⟨2, curve j, [first j, second j]⟩

private def row : Fin 5 → List (ℚ × Fin 6) :=
  ![[(-1, 0), (-1, 0), (1, 3)],
    [(-1, 4), (1, 1)],
    [(-1, 5), (-1, 0), (1, 2)],
    [(-1, 4), (1, 1)],
    [(-1, 5), (-1, 0), (1, 2)]]

/-- Exact values computed from the signed mixed transfer. -/
def values : Fin 5 → ℚ :=
  ![(19 / 960),
    0,
    (-5 / 288),
    0,
    (-5 / 288)]

private theorem mixed (j : Fin 5) :
    pairMixed (curve j) (first j) (second j) = pairExpression key (row j) := by
  fin_cases j <;> decide +kernel

/-- The original descendant reconstruction gives the indicated value on every request. -/
theorem accepted (j : Fin 5) : queryValue? 0 (requests j) = some (values j) := by
  rw [← queryValueWith?_eq_of_table 0 1 BlowupF1ExceptionalOneMarkingRequest.boundary
    BlowupF1ExceptionalOneMarkingRequest.boundary_eq_values (requests j)
      (by fin_cases j <;> decide +kernel)]
  unfold requests
  rw [queryValueWith?_pair, mixed, eval_pairExpression]
  simp only [checked]
  fin_cases j <;> decide +kernel

end AxiomaticGW.GenusTwoSecondUnitPairs.OneBlowup

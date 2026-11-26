/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.DoubleExceptionalInteriorPairs.Frame
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberTable

/-! # Full mixed calibration for the interior two-marked F₁ double exceptional frame

The indices are zero-based positions in the 64-row manifest. The ordered
requests retain both marking occurrences, including equal surface labels.
The calibration rows are the original full-class mixed transfer polynomials.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1DoubleExceptionalInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

def index : Fin 18 → Fin 64 :=
  ![2,
    3,
    8,
    9,
    13,
    14,
    21,
    22,
    26,
    27,
    30,
    31,
    37,
    38,
    42,
    43,
    46,
    47]

def first : Fin 18 → SurfaceInsertion X :=
  ![⟨.unit, 2⟩,
    ⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
    ⟨.unit, 3⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 0, 2⟩]

def second : Fin 18 → SurfaceInsertion X :=
  ![⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 0, 1⟩]

/-- The full ordered stable-map insertion data in the class (2,0). -/
def requests (j : Fin 18) : SurfaceQuery X := ⟨2, ![2, 0], [first j, second j]⟩

/-- All 15 squares, two products and five low-power terminals appearing in the transfer. -/
def key : Fin 22 → SurfaceAncestorKey X :=
  Fin.addCases (m := 15) (n := 7) squareKey (Fin.addCases (m := 2) (n := 5) productKey lowKey)

def row : Fin 18 → List (ℚ × Fin 22) :=
  ![[(-1, 5), (-1, 3), (-2, 4), (1, 19), (1, 14), (2, 17), ((3 / 4), 0)],
    [(-1, 5), (-1, 3), (-2, 4), (1, 19), (1, 14), (2, 17), ((3 / 4), 0)],
    [(-1, 1), (1, 12)],
    [(-1, 15), (-2, 20), (1, 8), ((3 / 4), 18)],
    [(-1, 5), (-1, 2), (-1, 4), (1, 19), (1, 17), (1, 13), ((1 / 2), 0)],
    [(-1, 16), (-1, 3), (-2, 21), (1, 19), (1, 11), (2, 17), ((3 / 4), 19)],
    [(-1, 15), (-2, 20), (1, 8), ((3 / 4), 18)],
    [(-1, 1), (1, 12)],
    [(1, 6)],
    [(1, 6)],
    [(-1, 15), (-1, 20), (1, 7), ((1 / 2), 18)],
    [(-1, 1), (1, 9)],
    [(-1, 16), (-1, 3), (-2, 21), (1, 19), (1, 11), (2, 17), ((3 / 4), 19)],
    [(-1, 5), (-1, 2), (-1, 4), (1, 19), (1, 17), (1, 13), ((1 / 2), 0)],
    [(-1, 1), (1, 9)],
    [(-1, 15), (-1, 20), (1, 7), ((1 / 2), 18)],
    [(-1, 16), (-1, 2), (-1, 21), (1, 19), (1, 17), (1, 10), ((1 / 2), 19)],
    [(-1, 16), (-1, 2), (-1, 21), (1, 19), (1, 17), (1, 10), ((1 / 2), 19)]]

theorem original_transfer (j : Fin 18) :
    pairMixed (![2, 0] : X.Curve) (first j) (second j) = pairExpression key (row j) := by
  fin_cases j <;> decide +kernel

/-- The original mixed evaluator reduces to signed linear combinations of these 22 keys. -/
theorem query_from_ancestors (j : Fin 18) :
    queryValue? 0 (requests j) =
      some (((row j).map (fun t ↦ t.1 * ancestorValueWith boundary (key t.2))).sum) := by
  rw [← queryValueWith?_eq_of_table 0 2 boundary
    (fun s hs ↦ (BlowupF1FiberTable.values_eq s hs).symm)
    (requests j) (by fin_cases j <;> decide +kernel)]
  unfold requests
  rw [queryValueWith?_pair, original_transfer, eval_pairExpression]

end AxiomaticGW.BlowupF1DoubleExceptionalInteriorPairs

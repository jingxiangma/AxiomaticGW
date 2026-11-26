/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.FiberInteriorPairs.Frame
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberTable

/-! # Full mixed calibration for the interior two-marked F₁ fiber frame

The indices are zero-based positions in the 64-row manifest. The ordered
requests retain both marking occurrences, including equal surface labels.
The calibration rows are the original full-class mixed transfer polynomials.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

def index : Fin 32 → Fin 64 :=
  ![2,
    3,
    8,
    9,
    13,
    14,
    18,
    19,
    21,
    22,
    26,
    27,
    30,
    31,
    34,
    35,
    37,
    38,
    42,
    43,
    46,
    47,
    50,
    51,
    52,
    53,
    56,
    57,
    59,
    60,
    62,
    63]

def first : Fin 32 → SurfaceInsertion X :=
  ![⟨.unit, 2⟩,
    ⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
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
    ⟨.hyperplane, 1⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.point, 0⟩,
    ⟨.point, 1⟩,
    ⟨.point, 0⟩,
    ⟨.point, 1⟩,
    ⟨.point, 0⟩,
    ⟨.point, 1⟩,
    ⟨.point, 0⟩,
    ⟨.point, 1⟩]

def second : Fin 32 → SurfaceInsertion X :=
  ![⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.point, 1⟩,
    ⟨.point, 0⟩,
    ⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.point, 1⟩,
    ⟨.point, 0⟩,
    ⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.point, 1⟩,
    ⟨.point, 0⟩,
    ⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.point, 1⟩,
    ⟨.point, 0⟩]

/-- The full ordered stable-map insertion data in the fiber class (0,1). -/
def requests (j : Fin 32) : SurfaceQuery X := ⟨2, ![0, 1], [first j, second j]⟩

/-- All 19 squares, four products and nine low-power terminals appearing in the transfer. -/
def key : Fin 32 → SurfaceAncestorKey X :=
  Fin.addCases (m := 19) (n := 13) squareKey (Fin.addCases (m := 4) (n := 9) productKey lowKey)

def row : Fin 32 → List (ℚ × Fin 32) :=
  ![[(-1, 2), (-1, 3), (-1, 5), (-1, 4), (1, 18)],
    [(-1, 2), (-1, 3), (-1, 5), (-1, 4), (1, 18)],
    [(-1, 0), (1, 5), (1, 4), (1, 16)],
    [(-1, 25), (-1, 19), (-1, 28), (1, 2), (1, 11)],
    [(-1, 1), (1, 3), (1, 5), (1, 17)],
    [(-1, 26), (-1, 20), (-1, 29), (1, 2), (1, 14)],
    [(-1, 23), (-1, 4), (1, 3), (1, 15)],
    [(-1, 24), (-1, 27), (-1, 30), (1, 8)],
    [(-1, 25), (-1, 19), (-1, 28), (1, 2), (1, 11)],
    [(-1, 0), (1, 5), (1, 4), (1, 16)],
    [(1, 0), (1, 19), (1, 28), (1, 9)],
    [(1, 0), (1, 19), (1, 28), (1, 9)],
    [(1, 1), (1, 25), (1, 19), (1, 10)],
    [(1, 0), (1, 20), (1, 29), (1, 12)],
    [(-1, 28), (1, 23), (1, 25), (1, 21)],
    [(1, 27), (1, 30), (1, 6)],
    [(-1, 26), (-1, 20), (-1, 29), (1, 2), (1, 14)],
    [(-1, 1), (1, 3), (1, 5), (1, 17)],
    [(1, 0), (1, 20), (1, 29), (1, 12)],
    [(1, 1), (1, 25), (1, 19), (1, 10)],
    [(1, 1), (1, 26), (1, 20), (1, 13)],
    [(1, 1), (1, 26), (1, 20), (1, 13)],
    [(-1, 29), (1, 23), (1, 26), (1, 22)],
    [(1, 24), (1, 30), (1, 7)],
    [(-1, 24), (-1, 27), (-1, 30), (1, 8)],
    [(-1, 23), (-1, 4), (1, 3), (1, 15)],
    [(1, 27), (1, 30), (1, 6)],
    [(-1, 28), (1, 23), (1, 25), (1, 21)],
    [(1, 24), (1, 30), (1, 7)],
    [(-1, 29), (1, 23), (1, 26), (1, 22)],
    [(-1, 27), (1, 24), (1, 31)],
    [(-1, 27), (1, 24), (1, 31)]]

theorem original_transfer (j : Fin 32) :
    pairMixed (![0, 1] : X.Curve) (first j) (second j) = pairExpression key (row j) := by
  fin_cases j <;> decide +kernel

/-- The original mixed evaluator reduces to signed linear combinations of these 32 keys. -/
theorem query_from_ancestors (j : Fin 32) :
    queryValue? 0 (requests j) =
      some (((row j).map (fun t ↦ t.1 * ancestorValueWith boundary (key t.2))).sum) := by
  rw [← queryValueWith?_eq_of_table 0 2 boundary
    (fun s hs ↦ (BlowupF1FiberTable.values_eq s hs).symm)
    (requests j) (by fin_cases j <;> decide +kernel)]
  unfold requests
  rw [queryValueWith?_pair, original_transfer, eval_pairExpression]

end AxiomaticGW.BlowupF1FiberInteriorPairs

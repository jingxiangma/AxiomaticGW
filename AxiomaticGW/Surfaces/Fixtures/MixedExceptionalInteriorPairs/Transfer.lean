/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.Frame

/-! # Full mixed calibration for the interior two-marked E₁ + E₂ frame

The indices are zero-based positions in the 100-row manifest. The ordered
requests retain both marking occurrences, including equal surface labels.
The calibration rows are the original full-class mixed transfer polynomials.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoMixedExceptionalInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

/-- Distinct zero-based positions in the complete ordered two-marked manifest. -/
def index (j : Fin 32) : Fin 100 :=
  (#[2, 3, 8, 9, 13, 14, 18, 19, 26, 27, 31, 32, 35, 36, 39, 40,
    46, 47, 51, 52, 55, 56, 59, 60, 66, 67, 71, 72, 75, 76, 79, 80] :
    Array (Fin 100))[j.val]'j.isLt

theorem index_injective : Function.Injective index := by decide +kernel

def first (j : Fin 32) : SurfaceInsertion X :=
  (#[⟨.unit, 2⟩,
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
    ⟨.exceptional 1, 1⟩,
    ⟨.exceptional 1, 2⟩,
    ⟨.exceptional 1, 1⟩,
    ⟨.exceptional 1, 2⟩,
    ⟨.exceptional 1, 1⟩,
    ⟨.exceptional 1, 2⟩,
    ⟨.exceptional 1, 1⟩,
    ⟨.exceptional 1, 2⟩] :
    Array (SurfaceInsertion X))[j.val]'j.isLt

def second (j : Fin 32) : SurfaceInsertion X :=
  (#[⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 1, 2⟩,
    ⟨.exceptional 1, 1⟩,
    ⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 1, 2⟩,
    ⟨.exceptional 1, 1⟩,
    ⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 1, 2⟩,
    ⟨.exceptional 1, 1⟩,
    ⟨.unit, 3⟩,
    ⟨.unit, 2⟩,
    ⟨.hyperplane, 2⟩,
    ⟨.hyperplane, 1⟩,
    ⟨.exceptional 0, 2⟩,
    ⟨.exceptional 0, 1⟩,
    ⟨.exceptional 1, 2⟩,
    ⟨.exceptional 1, 1⟩] :
    Array (SurfaceInsertion X))[j.val]'j.isLt

/-- The full ordered stable-map insertion data in the class E₁ + E₂. -/
def requests (j : Fin 32) : SurfaceQuery X := ⟨2, ![1, 1, 0], [first j, second j]⟩

/-- All 28 squares, six products and ten low-power terminals appearing in the transfer. -/
def key : Fin 44 → SurfaceAncestorKey X :=
  Fin.addCases (m := 28) (n := 16) squareKey (Fin.addCases (m := 6) (n := 10) productKey lowKey)

def row (j : Fin 32) : List (ℚ × Fin 44) :=
  (#[[(-1, 5), (-1, 3), (-1, 11), (-1, 9), (-2, 4), (-2, 10), (1, 35), (1, 37),
      (1, 27), (2, 34), (2, 36)],
    [(-1, 5), (-1, 3), (-1, 11), (-1, 9), (-2, 4), (-2, 10), (1, 35), (1, 37),
      (1, 27), (2, 34), (2, 36)],
    [(-1, 0), (-1, 6), (1, 24)],
    [(-1, 28), (-1, 31), (-2, 38), (-2, 41), (1, 15)],
    [(-1, 5), (-1, 1), (-1, 4), (-1, 7), (1, 37), (1, 36), (1, 25)],
    [(-1, 29), (-1, 3), (-1, 32), (-2, 39), (-2, 42), (1, 35), (1, 19), (2, 34)],
    [(-1, 2), (-1, 11), (-1, 8), (-1, 10), (1, 35), (1, 34), (1, 26)],
    [(-1, 30), (-1, 33), (-1, 9), (-2, 40), (-2, 43), (1, 37), (1, 23), (2, 36)],
    [(-1, 28), (-1, 31), (-2, 38), (-2, 41), (1, 15)],
    [(-1, 0), (-1, 6), (1, 24)],
    [(1, 12)],
    [(1, 12)],
    [(-1, 28), (-1, 38), (1, 13)],
    [(-1, 0), (1, 16)],
    [(-1, 31), (-1, 41), (1, 14)],
    [(-1, 6), (1, 20)],
    [(-1, 29), (-1, 3), (-1, 32), (-2, 39), (-2, 42), (1, 35), (1, 19), (2, 34)],
    [(-1, 5), (-1, 1), (-1, 4), (-1, 7), (1, 37), (1, 36), (1, 25)],
    [(-1, 0), (1, 16)],
    [(-1, 28), (-1, 38), (1, 13)],
    [(-1, 29), (-1, 1), (-1, 39), (1, 17)],
    [(-1, 29), (-1, 1), (-1, 39), (1, 17)],
    [(-1, 2), (-1, 32), (-1, 42), (1, 35), (1, 34), (1, 18)],
    [(-1, 30), (-1, 40), (-1, 7), (1, 37), (1, 36), (1, 21)],
    [(-1, 30), (-1, 33), (-1, 9), (-2, 40), (-2, 43), (1, 37), (1, 23), (2, 36)],
    [(-1, 2), (-1, 11), (-1, 8), (-1, 10), (1, 35), (1, 34), (1, 26)],
    [(-1, 6), (1, 20)],
    [(-1, 31), (-1, 41), (1, 14)],
    [(-1, 30), (-1, 40), (-1, 7), (1, 37), (1, 36), (1, 21)],
    [(-1, 2), (-1, 32), (-1, 42), (1, 35), (1, 34), (1, 18)],
    [(-1, 33), (-1, 8), (-1, 43), (1, 22)],
    [(-1, 33), (-1, 8), (-1, 43), (1, 22)]] :
    Array (List (ℚ × Fin 44)))[j.val]'j.isLt

theorem original_transfer (j : Fin 32) :
    pairMixed (![1, 1, 0] : X.Curve) (first j) (second j) = pairExpression key (row j) := by
  fin_cases j <;> decide +kernel

/-- The original mixed evaluator reduces to signed linear combinations of these 44 keys. -/
theorem query_from_ancestors (j : Fin 32) :
    queryValue? 0 (requests j) =
      some (((row j).map (fun t ↦ t.1 * ancestorValueWith boundary (key t.2))).sum) := by
  rw [← queryValueWith?_eq_of_table 0 2 boundary
    (fun s _ ↦ BlowupTwoExceptionalPlaneZeroTable.table_eq s)
    (requests j) (by fin_cases j <;> decide +kernel)]
  unfold requests
  rw [queryValueWith?_pair, original_transfer, eval_pairExpression]

end AxiomaticGW.BlowupTwoMixedExceptionalInteriorPairs

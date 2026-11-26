/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalInteriorPairs.Frame

/-! # The full original calibrated transfer on the doubled exceptional interior pairs -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleExceptionalInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants
open BlowupTwoMixedExceptionalInteriorPairs (first second)
open BlowupTwoDoubleExceptionalDivisor (beta)

/-- The same ordered marked shapes as every energy-two Bl₂ class, at the indicated full class. -/
def requests (i : Fin 2) (j : Fin 32) : SurfaceQuery X := ⟨2, beta i, [first j, second j]⟩

/-- All sixteen full-class squares followed by the seventeen proper-class tails. -/
def key (i : Fin 2) : Fin 33 → SurfaceAncestorKey X :=
  Fin.addCases (m := 16) (n := 17) (squareKey i) (tailKey i)

/-- Calibration coefficients in the first exceptional chart. -/
def baseRows (j : Fin 32) : List (ℚ × Fin 33) :=
  (#[[(1, 15), (2, 16), (1, 18), (3/4, 20), (-1, 24), (-2, 28), (-1, 32)],
    [(1, 15), (2, 16), (1, 18), (3/4, 20), (-1, 24), (-2, 28), (-1, 32)],
    [(1, 12), (-1, 21)],
    [(1, 3), (3/4, 17), (-2, 25), (-1, 29)],
    [(1, 13), (1, 16), (1, 18), (1/2, 20), (-1, 22), (-1, 28), (-1, 32)],
    [(1, 7), (2, 16), (3/4, 18), (1, 18), (-1, 24), (-2, 26), (-1, 30)],
    [(1, 14), (-1, 23)],
    [(1, 11), (3/4, 19), (-2, 27), (-1, 31)],
    [(1, 3), (3/4, 17), (-2, 25), (-1, 29)],
    [(1, 12), (-1, 21)],
    [(1, 0)],
    [(1, 0)],
    [(1, 1), (1/2, 17), (-1, 25), (-1, 29)],
    [(1, 4), (-1, 21)],
    [(1, 2)],
    [(1, 8)],
    [(1, 7), (2, 16), (3/4, 18), (1, 18), (-1, 24), (-2, 26), (-1, 30)],
    [(1, 13), (1, 16), (1, 18), (1/2, 20), (-1, 22), (-1, 28), (-1, 32)],
    [(1, 4), (-1, 21)],
    [(1, 1), (1/2, 17), (-1, 25), (-1, 29)],
    [(1, 5), (1, 16), (1/2, 18), (1, 18), (-1, 22), (-1, 26), (-1, 30)],
    [(1, 5), (1, 16), (1/2, 18), (1, 18), (-1, 22), (-1, 26), (-1, 30)],
    [(1, 6), (-1, 23)],
    [(1, 9), (1/2, 19), (-1, 27), (-1, 31)],
    [(1, 11), (3/4, 19), (-2, 27), (-1, 31)],
    [(1, 14), (-1, 23)],
    [(1, 8)],
    [(1, 2)],
    [(1, 9), (1/2, 19), (-1, 27), (-1, 31)],
    [(1, 6), (-1, 23)],
    [(1, 10)],
    [(1, 10)]] : Array (List (ℚ × Fin 33)))[j.val]'j.isLt

/-- The incoming absolute labels choose a row, relative to the indicated exceptional axis. -/
def row (i : Fin 2) (j : Fin 32) : List (ℚ × Fin 33) :=
  if i = 0 then baseRows j else baseRows ((#[0, 0, 2, 3, 6, 7, 4, 5, 3, 2, 10, 10, 14, 15, 12, 13,
    7, 6, 15, 14, 30, 30, 23, 22, 5, 4, 13, 12, 22, 23, 20, 20] : Array (Fin 32))[j.val]'j.isLt)

/-- The mixed descendant polynomial contains its full-class square and these exact tails. -/
theorem original_transfer (i : Fin 2) (j : Fin 32) :
    pairMixed (beta i) (first j) (second j) = pairExpression (key i) (row i j) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem query_from_ancestors (i : Fin 2) (j : Fin 32) : queryValue? 0 (requests i j) =
    some (((row i j).map (fun t ↦ t.1 * ancestorValueWith boundary (key i t.2))).sum) := by
  rw [← queryValueWith?_eq_of_table 0 2 boundary
    (fun s _ ↦ BlowupTwoExceptionalPlaneZeroTable.table_eq s) (requests i j)
    (by fin_cases i <;> fin_cases j <;> decide +kernel)]
  unfold requests
  rw [queryValueWith?_pair, original_transfer, eval_pairExpression]

end AxiomaticGW.BlowupTwoDoubleExceptionalInteriorPairs

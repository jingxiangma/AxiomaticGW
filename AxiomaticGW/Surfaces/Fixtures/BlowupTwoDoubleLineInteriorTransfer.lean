/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineOneMarking
public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.Transfer

/-! # Original calibrated transfer of the point-free interior of twice the strict line

The 32 ordered pairs share sixteen full-class ancestors. Their remaining terms use fifteen
constant-curve and twenty-five primitive-line keys. The marking slots and coefficients below
are checked against both orders of the mixed two-marked transfer.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleLineInterior
open SurfaceGenusTwo SurfaceGenusTwoPositiveDivisorPairs SurfaceGenusTwoBlowupDescendants
open BlowupTwoDoubleLine (curve terminals terminals_eq)
open BlowupTwoMixedExceptionalInteriorPairs (first second)

abbrev X := SurfaceTarget.blowupTwo
abbrev low := SurfaceGenusTwoBlowupLowPsi.ancestorValueWith terminals

/-- The positive, point-free ordered marking shapes at the full strict-line double cover. -/
def requests (j : Fin 32) : SurfaceQuery X := ⟨2, curve, [first j, second j]⟩

/-- The sixteen full-class keys, fifteen constant keys and twenty-five primitive keys. -/
def key (k : Fin 56) : SurfaceAncestorKey X :=
  (#[pairKey (X := X) curve ⟨.hyperplane, 1⟩ ⟨.hyperplane, 2⟩,
    pairKey (X := X) curve ⟨.hyperplane, 1⟩ ⟨.exceptional 0, 2⟩,
    pairKey (X := X) curve ⟨.hyperplane, 1⟩ ⟨.exceptional 1, 2⟩,
    pairKey (X := X) curve ⟨.hyperplane, 1⟩ ⟨.unit, 3⟩,
    pairKey (X := X) curve ⟨.exceptional 0, 1⟩ ⟨.hyperplane, 2⟩,
    pairKey (X := X) curve ⟨.exceptional 0, 1⟩ ⟨.exceptional 0, 2⟩,
    pairKey (X := X) curve ⟨.exceptional 0, 1⟩ ⟨.exceptional 1, 2⟩,
    pairKey (X := X) curve ⟨.exceptional 0, 1⟩ ⟨.unit, 3⟩,
    pairKey (X := X) curve ⟨.exceptional 1, 1⟩ ⟨.hyperplane, 2⟩,
    pairKey (X := X) curve ⟨.exceptional 1, 1⟩ ⟨.exceptional 0, 2⟩,
    pairKey (X := X) curve ⟨.exceptional 1, 1⟩ ⟨.exceptional 1, 2⟩,
    pairKey (X := X) curve ⟨.exceptional 1, 1⟩ ⟨.unit, 3⟩,
    pairKey (X := X) curve ⟨.unit, 2⟩ ⟨.hyperplane, 2⟩,
    pairKey (X := X) curve ⟨.unit, 2⟩ ⟨.exceptional 0, 2⟩,
    pairKey (X := X) curve ⟨.unit, 2⟩ ⟨.exceptional 1, 2⟩,
    pairKey (X := X) curve ⟨.unit, 2⟩ ⟨.unit, 3⟩,
    pairKey (X := X) 0 ⟨.hyperplane, 0⟩ ⟨.point, 0⟩,
    pairKey (X := X) 0 ⟨.hyperplane, 0⟩ ⟨.hyperplane, 1⟩,
    pairKey (X := X) 0 ⟨.hyperplane, 0⟩ ⟨.exceptional 0, 1⟩,
    pairKey (X := X) 0 ⟨.hyperplane, 0⟩ ⟨.exceptional 1, 1⟩,
    pairKey (X := X) 0 ⟨.hyperplane, 0⟩ ⟨.unit, 2⟩,
    pairKey (X := X) 0 ⟨.exceptional 0, 0⟩ ⟨.point, 0⟩,
    pairKey (X := X) 0 ⟨.exceptional 0, 0⟩ ⟨.hyperplane, 1⟩,
    pairKey (X := X) 0 ⟨.exceptional 0, 0⟩ ⟨.exceptional 0, 1⟩,
    pairKey (X := X) 0 ⟨.exceptional 0, 0⟩ ⟨.exceptional 1, 1⟩,
    pairKey (X := X) 0 ⟨.exceptional 0, 0⟩ ⟨.unit, 2⟩,
    pairKey (X := X) 0 ⟨.exceptional 1, 0⟩ ⟨.point, 0⟩,
    pairKey (X := X) 0 ⟨.exceptional 1, 0⟩ ⟨.hyperplane, 1⟩,
    pairKey (X := X) 0 ⟨.exceptional 1, 0⟩ ⟨.exceptional 0, 1⟩,
    pairKey (X := X) 0 ⟨.exceptional 1, 0⟩ ⟨.exceptional 1, 1⟩,
    pairKey (X := X) 0 ⟨.exceptional 1, 0⟩ ⟨.unit, 2⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.hyperplane, 0⟩ ⟨.hyperplane, 2⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.hyperplane, 0⟩ ⟨.exceptional 0, 2⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.hyperplane, 0⟩ ⟨.exceptional 1, 2⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.hyperplane, 0⟩ ⟨.unit, 3⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.exceptional 0, 0⟩ ⟨.hyperplane, 2⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.exceptional 0, 0⟩ ⟨.exceptional 0, 2⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.exceptional 0, 0⟩ ⟨.exceptional 1, 2⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.exceptional 0, 0⟩ ⟨.unit, 3⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.exceptional 1, 0⟩ ⟨.hyperplane, 2⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.exceptional 1, 0⟩ ⟨.exceptional 0, 2⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.exceptional 1, 0⟩ ⟨.exceptional 1, 2⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.exceptional 1, 0⟩ ⟨.unit, 3⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.point, 0⟩ ⟨.hyperplane, 1⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.point, 0⟩ ⟨.exceptional 0, 1⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.point, 0⟩ ⟨.exceptional 1, 1⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.point, 0⟩ ⟨.unit, 2⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.hyperplane, 1⟩ ⟨.hyperplane, 1⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.hyperplane, 1⟩ ⟨.exceptional 0, 1⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.hyperplane, 1⟩ ⟨.exceptional 1, 1⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.hyperplane, 1⟩ ⟨.unit, 2⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.exceptional 0, 1⟩ ⟨.exceptional 0, 1⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.exceptional 0, 1⟩ ⟨.exceptional 1, 1⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.exceptional 0, 1⟩ ⟨.unit, 2⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.exceptional 1, 1⟩ ⟨.exceptional 1, 1⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.exceptional 1, 1⟩ ⟨.unit, 2⟩] :
    Array (SurfaceAncestorKey X))[k.val]'k.isLt

/-- Coefficient row of the original transfer for each unordered shape. -/
def coefficients (r : Fin 16) : List (ℚ × Fin 56) :=
  (#[[(1, 15), (2, 16), (1, 17), (-1, 18), (-1, 19), (3/4, 20), (-2, 21), (-1, 22), (1, 23),
      (1, 24), (-3/4, 25), (-2, 26), (-1, 27), (1, 28), (1, 29), (-3/4, 30), (-1, 34), (1, 38),
      (1, 42), (-2, 46), (-1, 50), (1, 53), (1, 55)],
    [(1, 12), (-1, 16), (-1, 17), (1, 18), (1, 19), (-1/2, 20), (1, 21), (1, 22), (-1, 23),
      (-1, 24), (1/2, 25), (1, 26), (1, 27), (-1, 28), (-1, 29), (1/2, 30), (-1, 31), (1, 35),
      (1, 39), (1, 46), (1, 50), (-1, 53), (-1, 55)],
    [(1, 3), (-2, 16), (-1, 17), (3/4, 17), (1, 18), (1, 19), (2, 21), (-3/4, 22), (1, 22),
      (-1, 23), (-1, 24), (2, 26), (-3/4, 27), (1, 27), (-1, 28), (-1, 29), (1, 34), (-1, 38),
      (-1, 42), (-2, 43), (-1, 47), (1, 48), (1, 49)],
    [(1, 13), (-1, 16), (-1, 17), (1, 18), (1, 19), (-1/2, 20), (1, 21), (1, 22), (-1, 23),
      (-1, 24), (1/2, 25), (1, 26), (1, 27), (-1, 28), (-1, 29), (1/2, 30), (-1, 32), (1, 36),
      (1, 40), (1, 46), (1, 50), (-1, 53), (-1, 55)],
    [(1, 7), (-2, 16), (-1, 17), (3/4, 18), (1, 18), (1, 19), (2, 21), (1, 22), (-1, 23),
      (-3/4, 23), (-1, 24), (2, 26), (1, 27), (-1, 28), (-3/4, 28), (-1, 29), (1, 34), (-1, 38),
      (-1, 42), (-2, 44), (-1, 48), (1, 51), (1, 52)],
    [(1, 14), (-1, 16), (-1, 17), (1, 18), (1, 19), (-1/2, 20), (1, 21), (1, 22), (-1, 23),
      (-1, 24), (1/2, 25), (1, 26), (1, 27), (-1, 28), (-1, 29), (1/2, 30), (-1, 33), (1, 37),
      (1, 41), (1, 46), (1, 50), (-1, 53), (-1, 55)],
    [(1, 11), (-2, 16), (-1, 17), (1, 18), (3/4, 19), (1, 19), (2, 21), (1, 22), (-1, 23), (-1, 24),
      (-3/4, 24), (2, 26), (1, 27), (-1, 28), (-1, 29), (-3/4, 29), (1, 34), (-1, 38), (-1, 42),
      (-2, 45), (-1, 49), (1, 52), (1, 54)],
    [(1, 0), (1, 16), (-1/2, 17), (1, 17), (-1, 18), (-1, 19), (-1, 21), (-1, 22), (1/2, 22),
      (1, 23), (1, 24), (-1, 26), (-1, 27), (1/2, 27), (1, 28), (1, 29), (1, 31), (-1, 35),
      (-1, 39), (1, 43), (1, 47), (-1, 48), (-1, 49)],
    [(1, 1), (1, 16), (-1/2, 17), (1, 17), (-1, 18), (-1, 19), (-1, 21), (-1, 22), (1/2, 22),
      (1, 23), (1, 24), (-1, 26), (-1, 27), (1/2, 27), (1, 28), (1, 29), (1, 32), (-1, 36),
      (-1, 40), (1, 43), (1, 47), (-1, 48), (-1, 49)],
    [(1, 4), (1, 16), (1, 17), (-1, 18), (-1/2, 18), (-1, 19), (-1, 21), (-1, 22), (1/2, 23),
      (1, 23), (1, 24), (-1, 26), (-1, 27), (1/2, 28), (1, 28), (1, 29), (1, 31), (-1, 35),
      (-1, 39), (1, 44), (1, 48), (-1, 51), (-1, 52)],
    [(1, 2), (1, 16), (-1/2, 17), (1, 17), (-1, 18), (-1, 19), (-1, 21), (-1, 22), (1/2, 22),
      (1, 23), (1, 24), (-1, 26), (-1, 27), (1/2, 27), (1, 28), (1, 29), (1, 33), (-1, 37),
      (-1, 41), (1, 43), (1, 47), (-1, 48), (-1, 49)],
    [(1, 8), (1, 16), (1, 17), (-1, 18), (-1, 19), (-1/2, 19), (-1, 21), (-1, 22), (1, 23),
      (1/2, 24), (1, 24), (-1, 26), (-1, 27), (1, 28), (1/2, 29), (1, 29), (1, 31), (-1, 35),
      (-1, 39), (1, 45), (1, 49), (-1, 52), (-1, 54)],
    [(1, 5), (1, 16), (1, 17), (-1, 18), (-1/2, 18), (-1, 19), (-1, 21), (-1, 22), (1/2, 23),
      (1, 23), (1, 24), (-1, 26), (-1, 27), (1/2, 28), (1, 28), (1, 29), (1, 32), (-1, 36),
      (-1, 40), (1, 44), (1, 48), (-1, 51), (-1, 52)],
    [(1, 6), (1, 16), (1, 17), (-1, 18), (-1/2, 18), (-1, 19), (-1, 21), (-1, 22), (1/2, 23),
      (1, 23), (1, 24), (-1, 26), (-1, 27), (1/2, 28), (1, 28), (1, 29), (1, 33), (-1, 37),
      (-1, 41), (1, 44), (1, 48), (-1, 51), (-1, 52)],
    [(1, 9), (1, 16), (1, 17), (-1, 18), (-1, 19), (-1/2, 19), (-1, 21), (-1, 22), (1, 23),
      (1/2, 24), (1, 24), (-1, 26), (-1, 27), (1, 28), (1/2, 29), (1, 29), (1, 32), (-1, 36),
      (-1, 40), (1, 45), (1, 49), (-1, 52), (-1, 54)],
    [(1, 10), (1, 16), (1, 17), (-1, 18), (-1, 19), (-1/2, 19), (-1, 21), (-1, 22), (1, 23),
      (1/2, 24), (1, 24), (-1, 26), (-1, 27), (1, 28), (1/2, 29), (1, 29), (1, 33), (-1, 37),
      (-1, 41), (1, 45), (1, 49), (-1, 52), (-1, 54)]] :
    Array (List (ℚ × Fin 56)))[r.val]'r.isLt

/-- Both ordered requests select the same polynomial. -/
def shape (j : Fin 32) : Fin 16 :=
  (#[0, 0, 1, 2, 3, 4, 5, 6, 2, 1, 7, 7, 8, 9, 10, 11,
    4, 3, 9, 8, 12, 12, 13, 14, 6, 5, 11, 10, 14, 13, 15, 15] : Array (Fin 16))[j.val]'j.isLt

/-- The finite polynomial is exactly the original two-marked mixed calibration in class 2L. -/
theorem transfer (j : Fin 32) : pairMixed curve (first j) (second j) =
    pairExpression key (coefficients (shape j)) := by
  fin_cases j <;> decide +kernel

/-- Evaluate the original Bl₂ descendant directly from the 56 independently specified ancestors. -/
theorem query_from_ancestors (j : Fin 32) : queryValue? 0 (requests j) =
    some (((coefficients (shape j)).map (fun t ↦ t.1 * ancestorValueWith terminals (key t.2))).sum)
    := by
  rw [← queryValueWith?_eq_of_table 0 2 terminals (fun s _ ↦ terminals_eq s) _
    (by change X.effective.energy curve ≤ 2; decide +kernel)]
  unfold requests
  rw [queryValueWith?_pair, transfer, eval_pairExpression]

end AxiomaticGW.BlowupTwoDoubleLineInterior

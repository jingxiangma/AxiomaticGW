/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.DoubleExceptionalInteriorPairs.Terminals
public import AxiomaticGW.Surfaces.Fixtures.DoubleExceptionalInteriorPairs.LowerSquares
public import AxiomaticGW.Surfaces.Fixtures.DoubleExceptionalInteriorPairs.HighSquares

/-! # The eighteen point-free interior two-marked requests on the class 2E of F₁

These requests carry positive cotangent powers on both markings and contain
neither a string nor a dilaton insertion. Their original mixed calibration
contains fifteen squares, two primitive first-divisor products, and five
low-power terminals. The square contractions include every effective splitting
of the double exceptional class.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1DoubleExceptionalInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

/-- The values of all fifteen squares in the order of the original ancestor frame. -/
def squareValues : Fin 15 → ℚ :=
  Fin.addCases (m := 12) (n := 3) lowerValues highValues

theorem square_values (j : Fin 15) : ancestorValue low (squareKey j) = squareValues j := by
  refine Fin.addCases (m := 12) (n := 3) (fun i ↦ ?_) (fun i ↦ ?_) j
  · simpa only [squareValues, Fin.addCases_left] using lower_squares i
  · simpa only [squareValues, Fin.addCases_right] using highSquares i

/-- The values of the square, product, and low-power ancestors in the reconstruction. -/
def ancestorValues : Fin 22 → ℚ :=
  Fin.addCases (m := 15) (n := 7) squareValues (Fin.addCases (m := 2) (n := 5) productValues 0)

theorem ancestor_values (j : Fin 22) : ancestorValue low (key j) = ancestorValues j := by
  refine Fin.addCases (m := 15) (n := 7) (fun i ↦ ?_) (fun i ↦ ?_) j
  · simpa only [key, ancestorValues, Fin.addCases_left] using square_values i
  · simp only [key, ancestorValues, Fin.addCases_right]
    refine Fin.addCases (m := 2) (n := 5) (fun k ↦ ?_) (fun k ↦ ?_) i
    · simpa only [Fin.addCases_left] using product_values k
    · simpa only [Fin.addCases_right, Pi.zero_apply] using low_values k

/-- The exact descendant values for the two markings, in their original order. -/
def values : Fin 18 → ℚ :=
  ![(27 / 1280), (27 / 1280), 0, 0, (3 / 80), (37 / 1920), 0, 0, 0,
    0, 0, 0, (37 / 1920), (3 / 80), 0, 0, (-7 / 160), (-7 / 160)]

/-- The full mixed descendant evaluator gives the reconstructed value at every ordered request. -/
theorem accepted (j : Fin 18) : queryValue? 0 (requests j) = some (values j) := by
  rw [query_from_ancestors]
  change some (((row j).map (fun t ↦ t.1 * ancestorValue low (key t.2))).sum) = _
  simp only [ancestor_values]
  fin_cases j <;> decide +kernel

end AxiomaticGW.BlowupF1DoubleExceptionalInteriorPairs

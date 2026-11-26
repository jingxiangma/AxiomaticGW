/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalInteriorPairs.AllowedSquares
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalInteriorPairs.ForbiddenSquares
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalInteriorPairs.Tails
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalInteriorPairs.Transfer

/-! # All 64 genuine positive-cotangent interior pairs on 2E₁ and 2E₂

The evaluated descendant uses the original complete mixed calibration on each curve,
including its constant and primitive ancestor terms. Four of sixteen full-class square
profiles survive on each axis. Every surviving graph uses the complete effective splittings.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleExceptionalInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants
open BlowupTwoMixedExceptionalInteriorPairs (first second)

private theorem square_values (i : Fin 2) (j : Fin 16) :
    ancestorValue low (squareKey i j) = squareValues j := by
  have cover : ∀ j : Fin 16, (∃ r, allowedSquare r = j) ∨ ∃ r, forbidden r = j := by decide +kernel
  rcases cover j with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · exact allowed_values i r
  · rw [forbidden_values]
    fin_cases r <;> decide +kernel

private def ancestorValues (i : Fin 2) : Fin 33 → ℚ :=
  Fin.addCases (m := 16) (n := 17) squareValues (tailValues i)

private theorem ancestor_values (i : Fin 2) (j : Fin 33) :
    ancestorValueWith boundary (key i j) = ancestorValues i j := by
  change ancestorValue low (key i j) = _
  refine Fin.addCases (m := 16) (n := 17) (fun k ↦ ?_) (fun k ↦ ?_) j
  · simpa only [key, ancestorValues, Fin.addCases_left] using square_values i k
  · simpa only [key, ancestorValues, Fin.addCases_right] using tail_values i k

/-- Ordinary genus-two descendants at the indicated ordered marks. Only unit and the divisor
of the supporting exceptional axis occur in a nonzero value. -/
def values (i : Fin 2) (j : Fin 32) : ℚ :=
  match (first j).label, (second j).label with
  | .unit, .unit => 27/1280
  | .unit, .exceptional k =>
      if k = i then (if (first j).psi = 2 then 3/80 else 37/1920) else 0
  | .exceptional k, .unit =>
      if k = i then (if (second j).psi = 2 then 3/80 else 37/1920) else 0
  | .exceptional k, .exceptional l => if k = i ∧ l = i then -7/160 else 0
  | _, _ => 0

/-- All 64 original ordered requests have the displayed ordinary mixed-reconstruction values. -/
theorem accepted (i : Fin 2) (j : Fin 32) : queryValue? 0 (requests i j) = some (values i j) := by
  rw [query_from_ancestors]
  simp only [ancestor_values]
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Arithmetic witness for the original geometric reconstruction theorem. -/
theorem checked (i : Fin 2) (j : Fin 32) : CheckedDescendant 0 (requests i j) (values i j) :=
  .mixed (accepted i j)

/-- Each ordered insertion list and complete curve belongs to the fixed bounded benchmark. -/
theorem domain (i : Fin 2) (j : Fin 32) : FewMarkingQuery (requests i j) := by
  unfold FewMarkingQuery
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Ordinary geometric values under the same geometric inputs as the original reconstruction. -/
theorem accepted_from_geometry (i : Fin 2) (j : Fin 32) :
    type_of% (@SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry
      (X := X) (i := 0) (q := requests i j) (hg := rfl) (hv := checked i j)) :=
  @SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry
    (X := X) (i := 0) (q := requests i j) (hg := rfl) (hv := checked i j)

end AxiomaticGW.BlowupTwoDoubleExceptionalInteriorPairs

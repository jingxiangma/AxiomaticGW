/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingSingletons.Frame
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineTransfer
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoBlowupTwoOneMarkingSquareValues

/-! # Genus-two calibration in the two rulings of the two-point blowup

Both positive primitive summands of each pencil occur in the one-marking
ancestor-to-descendant transfer. All other proper terms lie in class zero.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRuling
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants SurfaceDescendant
open BlowupTwoDoubleLine (terminals terminals_eq)
open BlowupTwoLineBP (line)

/-- Dimension-compatible singleton at any basis label in the indicated full ruling class. -/
def request (i : Fin 2) (a : SurfaceBasisLabel X) : SurfaceQuery X :=
  ⟨2, curve i, [⟨a, 4 - a.codimension⟩]⟩

/-- Keys of the proper-class contributions, including the strict line and the exceptional
component of the reducible fiber. -/
def tailKey (i : Fin 2) : Fin 11 → SurfaceAncestorKey X :=
  let e := X.exceptionalCurve i
  ![oneMarkingKey 0 .unit 2, oneMarkingKey 0 .hyperplane 1,
    oneMarkingKey 0 (.exceptional i) 1, oneMarkingKey 0 (.exceptional i.rev) 1,
    oneMarkingKey 0 .point 0, oneMarkingKey line (.exceptional i) 2,
    oneMarkingKey line .point 1, oneMarkingKey e .hyperplane 2,
    oneMarkingKey e (.exceptional i) 2, oneMarkingKey e (.exceptional i.rev) 2,
    oneMarkingKey e .point 1]

/-- Calibration coefficients in the relative order of the five surface labels. -/
def coefficients : Fin 5 → Fin 11 → ℚ :=
  ![![-1, -2, 1, 0, -1, -1, -2, -1, 1, 1, -2],
    ![1, 0, 0, 1, -1, 0, 0, 1, -1, -1, 1],
    ![0, -1, 1, 1, -1, -1, -1, 1, -1, -1, 1],
    ![1, 1, 0, 0, 1, 0, 0, 1, -1, -1, 1],
    ![0, 1, 0, -1, 1, 0, 0, 0, 0, 0, 0]]

/-- Signed contribution of the eleven possible proper-class keys. -/
def tails (i : Fin 2) (j : Fin 5) : RationalTerms (SurfaceAncestorKey X) :=
  ∑ r, RationalTerms.term (coefficients j r) {tailKey i r}

/-- The complete mixed polynomial, checked separately at both full ruling classes. -/
theorem transfer (i : Fin 2) (j : Fin 5) :
    oneMarkingTerms (reconstructedCalibrationMatrix X) (curve i) (label i j)
      (4 - (label i j).codimension) 0 =
      RationalTerms.term 1 {oneMarkingKey (curve i) (label i j) (4 - (label i j).codimension)} +
        tails i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Actual proper-class ancestors before multiplication by the calibration coefficients. -/
def tailValues : Fin 11 → ℚ :=
  ![49/5760, -1/960, -1/2880, -1/2880, 0, 13/2880, 0, 0, -13/2880, 0, 0]

set_option maxRecDepth 65536

/-- Reconstruct every proper term from the constant and primitive original equations. -/
theorem tail_values (i : Fin 2) (r : Fin 11) :
    ancestorValueWith terminals (tailKey i r) = tailValues r := by
  let base := SurfaceGenusTwoBlowupLowPsi.ancestorValueWith terminals
  have he := BlowupTwoExceptionalOneMarking.exceptional_ancestors base i
  fin_cases r
  · change ancestorValue base (oneMarkingKey 0 .unit (0 + 2)) = _
    rw [ancestorValue_oneMarking_square]
    decide +kernel
  · fin_cases i <;> decide +kernel
  · fin_cases i <;> decide +kernel
  · fin_cases i <;> decide +kernel
  · fin_cases i <;> decide +kernel
  · fin_cases i
    · exact BlowupTwoLineOneMarking.high_ancestors base 2
    · exact BlowupTwoLineOneMarking.high_ancestors base 3
  · fin_cases i <;> decide +kernel
  · exact he.2.1
  · change ancestorValue base (oneMarkingKey (X.exceptionalCurve i) (.exceptional i) 2) = -13/2880
    rw [he.2.2 i, if_pos rfl]
  · change ancestorValue base (oneMarkingKey (X.exceptionalCurve i) (.exceptional i.rev) 2) = 0
    have h : i ≠ i.rev := by fin_cases i <;> decide
    rw [he.2.2 i.rev, if_neg h]
  · fin_cases i <;> decide +kernel

/-- Total proper-class contributions, including the nonzero unit correction on Bl₂. -/
def tailSums : Fin 5 → ℚ := ![-91/5760, 73/5760, 1/2880, 23/1920, -1/1440]

theorem tails_value (i : Fin 2) (j : Fin 5) :
    RationalTerms.eval (ancestorValueWith terminals) (tails i j) = tailSums j := by
  simp only [tails, RationalTerms.eval_sum, RationalTerms.eval_term, Multiset.map_singleton,
    Multiset.prod_singleton, Algebra.algebraMap_self_apply, tail_values]
  fin_cases j <;> decide +kernel

/-- Leading full-class ancestor plus all constant and primitive transfer corrections. -/
theorem query_eq_leading (i : Fin 2) (j : Fin 5) : queryValue? 0 (request i (label i j)) =
    some (ancestorValue (SurfaceGenusTwoBlowupLowPsi.ancestorValueWith terminals)
      (oneMarkingKey (curve i) (label i j) (4 - (label i j).codimension)) + tailSums j) := by
  rw [← queryValueWith?_eq_of_table 0 2 terminals (fun s _ ↦ terminals_eq s) _
    (by fin_cases i <;> fin_cases j <;> decide +kernel), request, queryValueWith?_oneMarking,
    transfer, RationalTerms.eval_add, RationalTerms.eval_term, Multiset.map_singleton,
    Multiset.prod_singleton, map_one, one_mul, tails_value]
  rfl

end AxiomaticGW.BlowupTwoRuling

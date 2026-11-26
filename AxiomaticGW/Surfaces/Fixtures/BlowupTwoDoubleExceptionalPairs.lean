/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalDivisor
public import AxiomaticGW.Surfaces.GenusTwoMarkedPairLookup

/-! # Twelve ordered nonzero genus-two pairs on the double exceptional axes

The string and dilaton equations remove a unit. The divisor equation for the own
exceptional divisor uses intersection −2 against 2Eᵢ and the cup product Eᵢ² = −pt.
The lower point descendant is evaluated at the same full class.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleExceptionalPairs
open SurfaceDescendant SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants
open BlowupTwoDoubleExceptionalDivisor (beta ancestor_eq_sum squareGraph)
open BlowupTwoExceptionalPlaneZeroTable (table table_eq)

/-- The point descendant occurring in the lowered cup term of the divisor equation. -/
def pointRequest (i : Fin 2) : SurfaceQuery .blowupTwo := ⟨2, beta i, [⟨.point, 2⟩]⟩

set_option Elab.async false
set_option maxRecDepth 65536

set_option maxHeartbeats 1600000 in
-- Both axes retain the entire five-state signed pairing in each contraction.
private theorem point_graph (i : Fin 2) (j : Fin 10) : squareGraph i .point 0 j = 0 := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem point_transfer (i : Fin 2) :
    oneMarkingTerms (reconstructedCalibrationMatrix .blowupTwo) (beta i) .point 2 0 =
      RationalTerms.term 1 {oneMarkingKey (beta i) .point 2} := by
  fin_cases i <;> decide +kernel

/-- The original mixed evaluator also vanishes at this already point-supported singleton. -/
theorem point_accepted (i : Fin 2) : queryValue? 0 (pointRequest i) = some 0 := by
  have hm := ancestor_eq_sum (SurfaceGenusTwoBlowupLowPsi.ancestorValueWith table) i .point 0
  simp only [point_graph, mul_zero, Finset.sum_const_zero] at hm
  change ancestorValueWith table (oneMarkingKey (beta i) .point 2) = 0 at hm
  rw [← queryValueWith?_eq_of_table 0 _ table (fun s _ ↦ table_eq s) _ (le_refl _), pointRequest,
    queryValueWith?_oneMarking, point_transfer, RationalTerms.eval_term, Multiset.map_singleton,
    Multiset.prod_singleton, map_one, one_mul, hm]

/-- String, dilaton, and own-primary-divisor pairs. The distinguished mark comes last
exactly when the Boolean is true. -/
def request (i : Fin 2) (r : Fin 3) (last : Bool) : SurfaceQuery .blowupTwo :=
  let s : SurfaceInsertion .blowupTwo := ⟨.exceptional i, 3⟩
  ![UnitEquation.string.pair last (beta i) s, UnitEquation.dilaton.pair last (beta i) s,
    divisorPair last (beta i) (.exceptional i) s] r

/-- Correlators in the string, dilaton, primary-divisor order. -/
def values : Fin 3 → ℚ := ![3/320, 9/320, -3/160]

/-- Every row retains its original effective class, ordered markings and virtual dimension. -/
theorem domain (i : Fin 2) (r : Fin 3) (last : Bool) : FewMarkingQuery (request i r last) := by
  unfold FewMarkingQuery
  fin_cases i <;> fin_cases r <;> cases last <;> decide +kernel

private def input (i : Fin 2) : Fin 2 → SurfaceQuery .blowupTwo :=
  ![BlowupTwoDoubleExceptionalDivisor.request i, pointRequest i]

private def inputValues : Fin 2 → ℚ := ![3/320, 0]

private theorem input_accepted (i j : Fin 2) :
    queryValue? 0 (input i j) = some (inputValues j) := by
  fin_cases j
  · exact BlowupTwoDoubleExceptionalDivisor.accepted i
  · exact point_accepted i

/-- The actual ordered equation evaluator verifies the twelve original marked requests. -/
theorem checked (i : Fin 2) (r : Fin 3) (last : Bool) :
    CheckedDescendant 0 (request i r last) (values r) := by
  apply markedPairValueWith?_checked 0 (singletonTable?_sound (input_accepted i))
  fin_cases i <;> fin_cases r <;> cases last <;> decide +kernel

/-- Geometric interpretation under the original genus-two reconstruction inputs. -/
theorem accepted_from_geometry (i : Fin 2) (r : Fin 3) (last : Bool) :
    type_of% (@SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry
      (X := .blowupTwo) (i := 0) (q := request i r last) (hg := (domain i r last).1)
      (hv := checked i r last)) :=
  @SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry
    (X := .blowupTwo) (i := 0) (q := request i r last) (hg := (domain i r last).1)
    (hv := checked i r last)

end AxiomaticGW.BlowupTwoDoubleExceptionalPairs

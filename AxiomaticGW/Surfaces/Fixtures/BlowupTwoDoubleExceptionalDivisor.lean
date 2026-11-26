/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalDivisorAncestors
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoExceptionalPlaneZeroTable
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1DoubleExceptionalOneMarking
public import AxiomaticGW.Surfaces.GenusTwoFewMarkings
public import AxiomaticGW.Surfaces.GenusTwoBlowupDescendantReconstruction

/-! # Ordinary genus-two τ₃(Eᵢ) in class 2Eᵢ on the two-point blowup

Each of the two positive calibration degrees leaves a main component in class Eᵢ or
zero. The main square and four remaining ancestors are checked on Bl₂. The comparison
with the corresponding F₁ descendant follows from those two original reconstructions.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleExceptionalDivisor
open SurfaceDescendant SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants
open BlowupTwoExceptionalPlaneZeroTable (table table_eq)

/-- The own-divisor singleton in full effective coordinates. -/
def request (i : Fin 2) : SurfaceQuery .blowupTwo :=
  ⟨2, beta i, [⟨.exceptional i, 3⟩]⟩

/-- Both positive-power requests belong to the fixed few-marking benchmark. -/
theorem domain (i : Fin 2) : FewMarkingQuery (request i) := by
  fin_cases i <;> unfold FewMarkingQuery <;> decide +kernel

/-- Main-component keys left by the two positive exceptional calibration degrees. -/
def tailKey (i : Fin 2) : Fin 4 → SurfaceAncestorKey .blowupTwo :=
  let b := SurfaceTarget.blowupTwo.exceptionalCurve i
  ![oneMarkingKey b (.exceptional i) 2, oneMarkingKey 0 (.exceptional i) 1,
    oneMarkingKey b .point 1, oneMarkingKey 0 .point 0]

/-- Linear combination of the four original non-leading calibration keys. -/
def calibrationTails (i : Fin 2) (a b c d : ℚ) : RationalTerms (SurfaceAncestorKey .blowupTwo) :=
  RationalTerms.term a {tailKey i 0} + RationalTerms.term b {tailKey i 1} +
    RationalTerms.term c {tailKey i 2} + RationalTerms.term d {tailKey i 3}

private abbrev tails (i : Fin 2) := calibrationTails i (-1) (1/2) (-1) (1/4)

set_option maxRecDepth 65536

private theorem transfer (i : Fin 2) :
    oneMarkingTerms (reconstructedCalibrationMatrix .blowupTwo) (beta i) (.exceptional i) 3 0 =
      RationalTerms.term 1 {oneMarkingKey (beta i) (.exceptional i) 3} + tails i := by
  fin_cases i <;> decide +kernel

private def tailValues : Fin 4 → ℚ := ![-13/2880, -1/2880, 0, 0]

private theorem tail_ancestors (i : Fin 2) (r : Fin 4) :
    ancestorValueWith table (tailKey i r) = tailValues r := by
  fin_cases r
  · exact ((BlowupTwoExceptionalOneMarking.exceptional_ancestors
      (SurfaceGenusTwoBlowupLowPsi.ancestorValueWith table) i).2.2 i).trans
        (if_pos rfl)
  all_goals fin_cases i <;> decide +kernel

/-- Evaluate the four calibrated keys in the original lower-class ancestor theory. -/
theorem eval_calibrationTails (i : Fin 2) (a b c d : ℚ) :
    RationalTerms.eval (ancestorValueWith table) (calibrationTails i a b c d) =
      a * (-13/2880) + b * (-1/2880) := by
  simp only [calibrationTails, RationalTerms.eval_add, RationalTerms.eval_term,
    Multiset.map_singleton, Multiset.prod_singleton, Algebra.algebraMap_self_apply, tail_ancestors]
  change _ + _ + c * 0 + d * 0 = _
  rw [mul_zero, mul_zero, add_zero, add_zero]
  rfl

private theorem tails_eq (i : Fin 2) :
    RationalTerms.eval (ancestorValueWith table) (tails i) = 25/5760 := by
  rw [tails, eval_calibrationTails]
  decide +kernel

/-- Both full-class requests reconstruct to 3/320 under the original mixed evaluator. -/
theorem accepted (i : Fin 2) : queryValue? 0 (request i) = some (3/320) := by
  have hm := main_ancestor (SurfaceGenusTwoBlowupLowPsi.ancestorValueWith table) i
  change ancestorValueWith table _ = _ at hm
  rw [← queryValueWith?_eq_of_table 0 _ table (fun s _ ↦ table_eq s) _ (le_refl _),
    request, queryValueWith?_oneMarking, transfer, RationalTerms.eval_add, RationalTerms.eval_term,
    Multiset.map_singleton, Multiset.prod_singleton, map_one, one_mul, hm, tails_eq]
  decide +kernel

/-- Each holds the original arithmetic witness used by the geometric descendant interface. -/
theorem checked (i : Fin 2) : CheckedDescendant 0 (request i) (3/320) := .mixed (accepted i)

/-- The ordinary geometric descendant under the original geometric reconstruction inputs. -/
theorem accepted_from_geometry (i : Fin 2) :
    type_of% (@SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry
      (X := .blowupTwo) (i := 0) (q := request i) (hg := rfl) (hv := checked i)) :=
  @SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry
    (X := .blowupTwo) (i := 0) (q := request i) (hg := rfl) (hv := checked i)

/-- Both target-side calculations agree with the reconstructed F₁ double-exceptional singleton. -/
theorem eq_oneBlowup (i : Fin 2) : queryValue? 0 (request i) =
    queryValue? 0 (BlowupF1DoubleExceptionalOneMarking.requests 2) := by
  rw [accepted, BlowupF1DoubleExceptionalOneMarking.accepted]
  decide +kernel

end AxiomaticGW.BlowupTwoDoubleExceptionalDivisor

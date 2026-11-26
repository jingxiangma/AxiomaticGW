/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoMixedExceptionalOneMarkingAncestors
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoExceptionalPlaneZeroTable

/-! # The five genus-two singletons at E₁ + E₂ on the two-point blowup

The mixed transfer for the unit contains two primitive exceptional tails.
A divisor Eᵢ contributes a tail whose genus-two component lies in the other
exceptional class. The corresponding exceptional-divisor and point ancestors
are evaluated at that full class before the final summation.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoMixedExceptionalOneMarking
open SurfaceDescendant SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants
open BlowupTwoExceptionalPlaneZeroTable (table table_eq)

/-- The complete one-marked frame at full class (1,1,0), in manifest basis order. -/
def requests (j : Fin 5) : SurfaceQuery .blowupTwo :=
  ⟨2, beta, [⟨labels j, 4 - (labels j).codimension⟩]⟩

theorem domain (j : Fin 5) : (requests j).GeometricDomain ∧ (requests j).DimensionCompatible := by
  fin_cases j <;> decide +kernel

/-- The reconstructed ordinary value at each of the five basis states. -/
def values : Fin 5 → ℚ := 0

/-- A primitive calibration leaves a point term and the divisor of the other exceptional curve. -/
private def primitiveTail (i : Fin 2) (c : ℚ) : RationalTerms (SurfaceAncestorKey .blowupTwo) :=
  let b := SurfaceTarget.blowupTwo.exceptionalCurve i
  RationalTerms.term (-1) {oneMarkingKey b (.exceptional i.rev) 2} +
    RationalTerms.term c {oneMarkingKey b .point 1}

private def tails (j : Fin 5) : RationalTerms (SurfaceAncestorKey .blowupTwo) :=
  ![primitiveTail 0 (-2) + primitiveTail 1 (-2), 0, primitiveTail 1 (-1), primitiveTail 0 (-1), 0] j

set_option maxRecDepth 65536

private theorem transfer_terms (j : Fin 5) :
    oneMarkingTerms (reconstructedCalibrationMatrix .blowupTwo) beta (labels j)
      (4 - (labels j).codimension) 0 =
      RationalTerms.term 1 {oneMarkingKey beta (labels j) (4 - (labels j).codimension)} +
        tails j := by
  fin_cases j <;> decide +kernel

private theorem primitiveTail_eval (i : Fin 2) (c : ℚ) :
    RationalTerms.eval (ancestorValueWith table) (primitiveTail i c) = 0 := by
  have hE : ancestorValueWith table
      (oneMarkingKey (SurfaceTarget.blowupTwo.exceptionalCurve i) (.exceptional i.rev) 2) = 0 :=
    ((BlowupTwoExceptionalOneMarking.exceptional_ancestors
      (SurfaceGenusTwoBlowupLowPsi.ancestorValueWith table) i).2.2 i.rev).trans
        (by fin_cases i <;> decide +kernel)
  have hP : ancestorValueWith table
      (oneMarkingKey (SurfaceTarget.blowupTwo.exceptionalCurve i) .point 1) = 0 := by
    fin_cases i <;> decide +kernel
  simp only [primitiveTail, RationalTerms.eval_add, RationalTerms.eval_term, Multiset.map_singleton,
    Multiset.prod_singleton, Algebra.algebraMap_self_apply, hE, hP, mul_zero, zero_add]

private theorem tails_eval (j : Fin 5) :
    RationalTerms.eval (ancestorValueWith table) (tails j) = 0 := by
  fin_cases j
  · change RationalTerms.eval _ (primitiveTail 0 (-2) + primitiveTail 1 (-2)) = 0
    rw [RationalTerms.eval_add, primitiveTail_eval, primitiveTail_eval, add_zero]
  · exact RationalTerms.eval_zero _
  · exact primitiveTail_eval 1 (-1)
  · exact primitiveTail_eval 0 (-1)
  · exact RationalTerms.eval_zero _

/-- Reconstruction of every stable-map descendant in the original ordered singleton frame. -/
theorem accepted (j : Fin 5) : queryValue? 0 (requests j) = some (values j) := by
  have hm := main_ancestors (SurfaceGenusTwoBlowupLowPsi.ancestorValueWith table) j
  change ancestorValueWith table _ = 0 at hm
  rw [← queryValueWith?_eq_of_table 0 _ table (fun s _ ↦ table_eq s) _ (le_refl _),
    requests, queryValueWith?_oneMarking, transfer_terms, RationalTerms.eval_add,
    RationalTerms.eval_term, Multiset.map_singleton, Multiset.prod_singleton, map_one,
    one_mul, hm, tails_eval, add_zero]
  rfl

end AxiomaticGW.BlowupTwoMixedExceptionalOneMarking

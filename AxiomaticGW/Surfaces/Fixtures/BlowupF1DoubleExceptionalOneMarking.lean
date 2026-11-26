/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1DoubleExceptionalOneMarkingAncestors
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1ExceptionalOneMarkingValues
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberTable

/-! # Genus-two one-marked descendants in the class 2E on F₁

A positive calibration tail in class E leaves a genus-two component in class E.
A tail in class 2E leaves it in class zero. The unit and exceptional descendants
receive both corrections. The hyperplane and point receive only their leading ancestor.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1DoubleExceptionalOneMarking
open SurfaceDescendant SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants BlowupF1FiberHReduction

/-- All four basis singletons in full effective coordinates (2, 0). -/
def requests (j : Fin 4) : SurfaceQuery target :=
  ⟨2, doubleExceptional, [⟨labels j, 4 - (labels j).codimension⟩]⟩

/-- Stability and the surface dimension equation hold for every original query. -/
theorem domain (j : Fin 4) : (requests j).GeometricDomain ∧ (requests j).DimensionCompatible := by
  fin_cases j <;> decide +kernel

/-- Reconstructed values in unit, hyperplane, exceptional and point order. -/
def values : Fin 4 → ℚ := ![13/3840, 0, 3/320, 0]

-- Reduce the full rational calibration along both positive exceptional splittings.
set_option maxRecDepth 65536

private def tailKey : Fin 4 → SurfaceAncestorKey target :=
  ![oneMarkingKey exceptional (.exceptional 0) 2, oneMarkingKey 0 (.exceptional 0) 1,
    oneMarkingKey exceptional .point 1, oneMarkingKey 0 .point 0]

private def tailValues : Fin 4 → ℚ := ![-13/2880, -1/2880, 0, 0]

private theorem tail_ancestors (r : Fin 4) : ancestorValueWith boundary (tailKey r) =
    tailValues r := by
  fin_cases r
  · exact (BlowupF1ExceptionalOneMarkingValues.exceptional_ancestors
      (SurfaceGenusTwoBlowupLowPsi.ancestorValueWith boundary)).2.2
  all_goals decide +kernel

private def fourTails (a b c d : ℚ) : RationalTerms (SurfaceAncestorKey target) :=
  RationalTerms.term a {tailKey 0} + RationalTerms.term b {tailKey 1} +
    RationalTerms.term c {tailKey 2} + RationalTerms.term d {tailKey 3}

private def tails (j : Fin 4) : RationalTerms (SurfaceAncestorKey target) :=
  if j = 0 then fourTails (-1) (3/4) (-2) (1/2)
  else if j = 2 then fourTails (-1) (1/2) (-1) (1/4)
  else 0

private theorem transfer_terms (j : Fin 4) :
    oneMarkingTerms (reconstructedCalibrationMatrix target) doubleExceptional (labels j)
      (4 - (labels j).codimension) 0 =
      RationalTerms.term 1
        {oneMarkingKey doubleExceptional (labels j) (4 - (labels j).codimension)} + tails j := by
  fin_cases j <;> decide +kernel

private theorem four_eval (a b c d : ℚ) :
    RationalTerms.eval (ancestorValueWith boundary) (fourTails a b c d) =
      a * tailValues 0 + b * tailValues 1 + c * tailValues 2 + d * tailValues 3 := by
  simp only [fourTails, RationalTerms.eval_add, RationalTerms.eval_term, Multiset.map_singleton,
    Multiset.prod_singleton, Algebra.algebraMap_self_apply, tail_ancestors]

/-- The original mixed evaluator at 2E, with both positive tail degrees and all four powers. -/
theorem accepted (j : Fin 4) : queryValue? 0 (requests j) = some (values j) := by
  have he : target.effective.energy (requests j).beta ≤ 2 := by
    change target.effective.energy doubleExceptional ≤ 2
    decide +kernel
  have hm := main_ancestors (SurfaceGenusTwoBlowupLowPsi.ancestorValueWith boundary) j
  change ancestorValueWith boundary _ = _ at hm
  rw [← queryValueWith?_eq_of_table 0 2 boundary
    (fun s hs ↦ (BlowupF1FiberTable.values_eq s hs).symm) _ he, requests,
    queryValueWith?_oneMarking, transfer_terms, RationalTerms.eval_add, RationalTerms.eval_term,
    Multiset.map_singleton, Multiset.prod_singleton, map_one, one_mul, hm]
  fin_cases j
  · exact (congrArg (fun z ↦ some (mainValues 0 + z)) (four_eval (-1) (3/4) (-2) (1/2))).trans
      (by decide +kernel)
  · exact (congrArg (fun z ↦ some (mainValues 1 + z))
      (RationalTerms.eval_zero (ancestorValueWith boundary))).trans (by decide +kernel)
  · exact (congrArg (fun z ↦ some (mainValues 2 + z)) (four_eval (-1) (1/2) (-1) (1/4))).trans
      (by decide +kernel)
  · exact (congrArg (fun z ↦ some (mainValues 3 + z))
      (RationalTerms.eval_zero (ancestorValueWith boundary))).trans (by decide +kernel)

end AxiomaticGW.BlowupF1DoubleExceptionalOneMarking

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupRecursion

/-! Full-class boundary, original-equation and uniqueness consumers of the blowup algorithm. -/

@[expose] public section
namespace AxiomaticGWTest.SurfaceGenusTwoBlowupRecursion
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
open SurfaceGenusTwoBlowupRecursion

-- Evaluation of an H row retains the original complete L24 source dispatch.
set_option maxRecDepth 20000

/-- The algorithm retains the audited class-zero H seed. -/
theorem class_zero_h : values (X := .blowupTwo) 0 (0, .hyperplane) = -1 / 960 := by
  rw [values_boundary 0 _ rfl, SurfaceGenusTwoBlowupBoundary.value_zero]
  rfl

/-- The canonical table includes the derived primary zero on F1. -/
theorem class_zero_n : values (X := .hirzebruchOne) 0 (0, .primary) = 0 := by
  rw [values_boundary 0 _ rfl, SurfaceGenusTwoBlowupBoundary.value_zero]
  rfl

/-- Both exceptional labels have their own retained class-zero table entry. -/
theorem class_zero_k (j : Fin SurfaceTarget.blowupTwo.blowups) :
    values (X := .blowupTwo) 0 (0, .exceptional j) = -1 / 2880 := by
  rw [values_boundary 0 _ rfl, SurfaceGenusTwoBlowupBoundary.value_zero]
  rfl

/-- Reducible exceptional full classes use the proved boundary in every sector. -/
theorem mixed_exceptional_boundary (family : Family .blowupTwo) :
    values 0 (![2, 3, 0], family) = 0 := by
  rw [values_boundary 0 _ rfl]
  exact SurfaceGenusTwoBlowupBoundary.value_of_ne_zero _
    (by change (![2, 3, 0] : SurfaceTarget.blowupTwo.Curve) ≠ 0; decide +kernel) family

/-- The nominal P0 entry remains zero and dimension-incompatible. -/
theorem class_zero_p_boundary :
    values (X := .hirzebruchOne) 0 (0, .point) = 0 ∧
      ¬ (Family.point.query (0 : SurfaceTarget.hirzebruchOne.Curve)).DimensionCompatible := by
  constructor
  · rw [values_boundary 0 _ rfl, SurfaceGenusTwoBlowupBoundary.value_zero]
    rfl
  · exact SurfaceGenusTwoBlowupBoundary.point_zero_not_dimensionCompatible _

/-- A negative-multiplicity primary state satisfies its complete original four-row equation. -/
theorem negative_multiplicity_primary_equation :
    RationalTerms.eval (canonicalValuation (values (X := .blowupTwo) 0))
      (SurfaceGenusTwoBlowupNRelation.row .blowupTwo 0 ![2, 0, 1]) = 0 := by
  simpa only [row] using values_equations (X := .blowupTwo) 0
    (![2, 0, 1], .primary) (by change 0 < 1; decide +kernel)

/-- Both exceptional descendant rows are satisfied while their labels stay distinct. -/
theorem both_exceptional_equations (j : Fin SurfaceTarget.blowupTwo.blowups) :
    RationalTerms.eval (canonicalValuation (values (X := .blowupTwo) 0))
      (SurfaceGenusTwoBlowupKRow.row .blowupTwo j ![1, 0, 1]) = 0 := by
  simpa only [row] using values_equations (X := .blowupTwo) 0
    (![1, 0, 1], .exceptional j) (by change 0 < 1; decide +kernel)

/-- A common solution of the original BP/L24 equations makes the two shift algorithms agree. -/
theorem two_shifts_from_original_equations (v : Variable .blowupTwo → ℚ)
    (hz : ∀ s : State .blowupTwo, SurfaceTarget.blowupTwo.planeDegree s.1 = 0 →
      v (.inr (s.2.query s.1)) = SurfaceGenusTwoBlowupBoundary.value s.1 s.2)
    (hBP : ∀ n beta a, RationalTerms.eval v
      (SurfaceGenusTwoBlowupNRelation.bpRow .blowupTwo n beta a) = 0)
    (hL : ∀ n beta (a : Fin 4 → SurfaceBasisLabel .blowupTwo), RationalTerms.eval v
      (L24Relation.normalizedGenusTwoTerms .blowupTwo n beta 0
        (SurfaceGenusZero.pointLabels a n)) = 0)
    (s : State .blowupTwo) : values 0 s = values 1 s := by
  have h0 := eq_values_of_equations 0 v hz
    (fun t _ ↦ row_eq_zero_of_original_equations 0 v hBP hL t) s
  have h1 := eq_values_of_equations 1 v hz
    (fun t _ ↦ row_eq_zero_of_original_equations 1 v hBP hL t) s
  exact h0.symm.trans h1

end AxiomaticGWTest.SurfaceGenusTwoBlowupRecursion

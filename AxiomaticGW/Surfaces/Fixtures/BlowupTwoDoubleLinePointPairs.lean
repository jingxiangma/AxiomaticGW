/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineOneMarking
public import AxiomaticGW.Surfaces.GenusTwoPairTerms
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPositiveSquareComponents
public import AxiomaticGW.Surfaces.GenusTwoPulledSquare

/-! # Two-marked point descendants on twice the strict transform of the line

For the five cotangent squares and three first-power products the calibrated transfer has one
full-class ancestor. Every proper-class term is a known zero at 0 or L. The two remaining orders
of the primary point and its first descendant reach the full-class canonical point state.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleLinePointPairs
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants SurfaceGenusTwoPositiveDivisorPairs
open BlowupTwoDoubleLine (curve terminals terminals_eq)
open SurfaceGenusTwoBlowupOrder SurfacePolynomialReduction

abbrev X := SurfaceTarget.blowupTwo
abbrev low := SurfaceGenusTwoBlowupLowPsi.ancestorValueWith terminals

/-- Non-point insertion in the five squares, followed by the three products. -/
def first : Fin 8 → SurfaceInsertion X :=
  ![⟨.unit, 2⟩, ⟨.unit, 3⟩, ⟨.hyperplane, 2⟩, ⟨.exceptional 0, 2⟩, ⟨.exceptional 1, 2⟩,
    ⟨.hyperplane, 1⟩, ⟨.exceptional 0, 1⟩, ⟨.exceptional 1, 1⟩]

/-- A primary point or its first descendant. -/
def point : Fin 8 → SurfaceInsertion X :=
  ![⟨.point, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩,
    ⟨.point, 1⟩, ⟨.point, 1⟩, ⟨.point, 1⟩]

/-- Both orders of each selected pair in the original surface evaluator. -/
def request (j : Fin 8) (last : Bool) : SurfaceQuery X :=
  ⟨2, curve, if last then [first j, point j] else [point j, first j]⟩

/-- Full-curve ancestor of the two insertions. -/
def fullKey (j : Fin 8) : SurfaceAncestorKey X := pairKey curve (first j) (point j)

/-- Proper-class terms in the actual mixed calibration on this frame. -/
def tailKey : Fin 10 → SurfaceAncestorKey X :=
  ![pairKey (X := X) ![0, 0, 0] ⟨.hyperplane, 0⟩ ⟨.point, 0⟩,
    pairKey (X := X) ![0, 0, 0] ⟨.exceptional 0, 0⟩ ⟨.point, 0⟩,
    pairKey (X := X) ![0, 0, 0] ⟨.exceptional 1, 0⟩ ⟨.point, 0⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.hyperplane, 0⟩ ⟨.point, 1⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.exceptional 0, 0⟩ ⟨.point, 1⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.exceptional 1, 0⟩ ⟨.point, 1⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.point, 0⟩ ⟨.point, 0⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.point, 0⟩ ⟨.hyperplane, 1⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.point, 0⟩ ⟨.exceptional 0, 1⟩,
    pairKey (X := X) ![0, 0, 1] ⟨.point, 0⟩ ⟨.exceptional 1, 1⟩]

/-- Coefficients and proper-class key indices for the original mixed transfer. -/
def tails : Fin 8 → List (ℚ × Fin 10) :=
  ![[(-1, 3), (1, 4), (1, 5)],
    [(-1, 7), (-2, 6), (-3/4, 1), (-3/4, 2), (1, 8), (1, 9), (3/4, 0)],
    [(-1/2, 0), (-1, 8), (-1, 9), (1/2, 1), (1/2, 2), (1, 7), (1, 6)],
    [(-1/2, 0), (-1, 8), (-1, 9), (1/2, 1), (1/2, 2), (1, 7), (1, 6)],
    [(-1/2, 0), (-1, 8), (-1, 9), (1/2, 1), (1/2, 2), (1, 7), (1, 6)],
    [(-1, 4), (-1, 5), (1, 3)],
    [(-1, 4), (-1, 5), (1, 3)],
    [(-1, 4), (-1, 5), (1, 3)]]

private theorem tail_values (j : Fin 10) : ancestorValueWith terminals (tailKey j) = 0 := by
  fin_cases j <;> decide +kernel

private theorem transfer (j : Fin 8) (last : Bool) :
    pairMixed curve (if last then first j else point j) (if last then point j else first j) =
      RationalTerms.term 1 {fullKey j} + pairExpression tailKey (tails j) := by
  fin_cases j <;> cases last <;> decide +kernel

/-- The ordered stable-map descendant equals its leading full-curve ancestor in all 16 cases. -/
theorem query_from_ancestor (j : Fin 8) (last : Bool) : queryValue? 0 (request j last) =
    some (ancestorValue low (fullKey j)) := by
  rw [← queryValueWith?_eq_of_table 0 2 terminals (fun s _ ↦ terminals_eq s) _
    (by change X.effective.energy curve ≤ 2; decide +kernel)]
  have hr : request j last = ⟨2, curve, [if last then first j else point j,
      if last then point j else first j]⟩ := by cases last <;> rfl
  rw [hr, queryValueWith?_pair, transfer, RationalTerms.eval_add, eval_pairExpression]
  simp only [RationalTerms.eval_term, Multiset.map_singleton, Multiset.prod_singleton, map_one,
    one_mul, tail_values, mul_zero, List.map_const', List.sum_replicate, nsmul_zero, add_zero]
  rfl

/-- The two remaining point–point requests are exactly the original canonical P state at 2L. -/
theorem point_point (i : Fin 2) : queryValue? 0
    (⟨2, curve, [⟨.point, i.val⟩, ⟨.point, 1-i.val⟩]⟩ : SurfaceQuery X) =
    some (SurfaceGenusTwoBlowupRecursion.values 0 (curve, .point)) := by
  let t := SurfaceGenusTwoBlowupRecursion.values (X := X) 0
  let key := pairKey curve ⟨.point, 0⟩ ⟨.point, 1⟩
  rw [← queryValueWith?_eq_of_table 0 2 t (fun _ _ ↦ rfl) _ (by fin_cases i <;> decide +kernel),
    queryValueWith?_pair]
  rw [show pairMixed curve ⟨.point, i.val⟩ ⟨.point, 1-i.val⟩ = RationalTerms.term 1 {key} by
    fin_cases i <;> decide +kernel]
  simp only [RationalTerms.eval_term, Multiset.map_singleton, Multiset.prod_singleton, map_one,
    one_mul, ancestorValueWith]
  rw [ancestorValue_low _ _ rfl (by decide +kernel), SurfaceGenusTwoBlowupLowPsi.ancestorValueWith,
    show normalizedTerms key = RationalTerms.term 1 {Sum.inr (Family.point.query curve)}
      by decide +kernel]
  simp only [RationalTerms.eval_term, Multiset.map_singleton, Multiset.prod_singleton, map_one,
    one_mul, canonicalValuation_query]
  rfl

end AxiomaticGW.BlowupTwoDoubleLinePointPairs

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineAncestors
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineOneMarkingAncestors
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Assembly

/-! # Actual calibration tails of the genus-two singletons at twice the strict line

The unit and each divisor have eight proper-class terms. The original canonical table
through energy one suffices even though the requests have energy two.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleLine
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants SurfaceDescendant
open BlowupTwoLineBP (line)
open BlowupTwoLineOneMarking (labels)

/-- The original canonical lookup with the verified energy-one table used for proper-class tails. -/
def terminals (s : SurfaceGenusTwoBlowupOrder.State .blowupTwo) : ℚ :=
  if SurfaceTarget.blowupTwo.effective.energy s.1 ≤ 1 then BlowupTwoLineTable.candidate 0 s
  else SurfaceGenusTwoBlowupRecursion.values 0 s

theorem terminals_eq (s : SurfaceGenusTwoBlowupOrder.State .blowupTwo) :
    terminals s = SurfaceGenusTwoBlowupRecursion.values 0 s := by
  unfold terminals
  split_ifs with hs
  · exact (BlowupTwoLineTable.values_eq _ hs).symm
  · rfl

/-- Singleton requests in their unique virtual-dimension powers on 2L. -/
def request (a : SurfaceBasisLabel .blowupTwo) : SurfaceQuery .blowupTwo :=
  ⟨2, curve, [⟨a, 4 - a.codimension⟩]⟩

/-- Three divisors and the point, first on L and then on the constant curve. -/
def tailKey : Fin 8 → SurfaceAncestorKey .blowupTwo :=
  ![oneMarkingKey line .hyperplane 2, oneMarkingKey line (.exceptional 0) 2,
    oneMarkingKey line (.exceptional 1) 2, oneMarkingKey line .point 1,
    oneMarkingKey 0 .hyperplane 1, oneMarkingKey 0 (.exceptional 0) 1,
    oneMarkingKey 0 (.exceptional 1) 1, oneMarkingKey 0 .point 0]

/-- The two possible coefficient rows of the original calibration. -/
def coefficients (j : Fin 4) : Fin 8 → ℚ :=
  if j = 0 then ![-1, 1, 1, -2, 3/4, -3/4, -3/4, 1/2]
  else ![1, -1, -1, 1, -1/2, 1/2, 1/2, -1/4]

/-- The entire remainder, after removing the leading double-class ancestor. -/
def tails (j : Fin 4) : RationalTerms (SurfaceAncestorKey .blowupTwo) :=
  ∑ r, RationalTerms.term (coefficients j r) {tailKey r}

/-- Equality in the original sparse ancestor polynomial, preserving every curve class and sign. -/
theorem transfer (j : Fin 4) : oneMarkingTerms (reconstructedCalibrationMatrix .blowupTwo)
    curve (labels j) (4 - (labels j).codimension) 0 =
    RationalTerms.term 1 {oneMarkingKey curve (labels j) (4 - (labels j).codimension)} +
      tails j := by
  fin_cases j <;> decide +kernel

/-- The eight primitive and constant ancestor values before applying their coefficients. -/
def tailValues : Fin 8 → ℚ := ![13/2880, 13/2880, 13/2880, 0, -1/960, -1/2880, -1/2880, 0]

theorem tail_values (r : Fin 8) : ancestorValueWith terminals (tailKey r) = tailValues r := by
  fin_cases r
  · exact BlowupTwoLineOneMarking.high_ancestors
      (SurfaceGenusTwoBlowupLowPsi.ancestorValueWith terminals) 1
  · exact BlowupTwoLineOneMarking.high_ancestors
      (SurfaceGenusTwoBlowupLowPsi.ancestorValueWith terminals) 2
  · exact BlowupTwoLineOneMarking.high_ancestors
      (SurfaceGenusTwoBlowupLowPsi.ancestorValueWith terminals) 3
  all_goals decide +kernel

/-- The unit uses the opposite divisor signs from a divisor insertion on the strict line. -/
theorem tails_value (j : Fin 4) : RationalTerms.eval (ancestorValueWith terminals) (tails j) =
    if j = 0 then 49/11520 else -25/5760 := by
  simp only [tails, RationalTerms.eval_sum, RationalTerms.eval_term, Multiset.map_singleton,
    Multiset.prod_singleton, Algebra.algebraMap_self_apply, tail_values]
  fin_cases j <;> decide +kernel

/-- Only the complete lower-genus 2L square and known energy-one tails enter each descendant. -/
theorem query_eq_leading (j : Fin 4) : queryValue? 0 (request (labels j)) =
    some (ancestorValue (SurfaceGenusTwoBlowupLowPsi.ancestorValueWith terminals)
      (oneMarkingKey curve (labels j) (4 - (labels j).codimension)) +
      (if j = 0 then 49/11520 else -25/5760)) := by
  rw [← queryValueWith?_eq_of_table 0 2 terminals (fun s _ ↦ terminals_eq s) _
    (by fin_cases j <;> decide +kernel), request, queryValueWith?_oneMarking, transfer,
    RationalTerms.eval_add, RationalTerms.eval_term, Multiset.map_singleton,
    Multiset.prod_singleton, map_one, one_mul, tails_value]
  rfl

end AxiomaticGW.BlowupTwoDoubleLine

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1ExceptionalOneMarkingRequest
public import AxiomaticGW.Surfaces.GenusTwoOneMarkingSquare
public import AxiomaticGW.Surfaces.GenusTwoExceptionalOneMarking

/-!
# One-marking genus-two descendants in the exceptional class of F1

The ten graphs of the square relation determine the positive-power ancestors.
Transferring stable-map cotangent powers adds the class-zero calibration tails.
The resulting rationals are certified for the original terminating evaluator.
Its geometric interpretation uses the hypotheses of the blowup reconstruction theorem.
-/

@[expose] public section

namespace AxiomaticGW.BlowupF1ExceptionalOneMarkingValues
open BlowupF1ExceptionalOneMarkingRequest SurfaceGenusTwo

/-- Values in the held order of the unit, H, E and point queries. -/
def values : Fin 4 → ℚ := ![13 / 2880, 0, -1 / 240, 0]

set_option Elab.async false
set_option maxRecDepth 65536

set_option maxHeartbeats 1600000 in
-- Each entry contracts the ten decorated graphs with the lower-genus evaluator.
/-- The ancestor contributions in the exceptional class, before transfer of the cotangent
powers from stable maps. The square relation makes these independent of the low-psi base. -/
theorem exceptional_ancestors (base : SurfaceAncestorKey .hirzebruchOne → ℚ) :
    ancestorValue base (oneMarkingKey exceptional .unit 3) = 1/240 ∧
    ancestorValue base (oneMarkingKey exceptional .hyperplane 2) = 0 ∧
    ancestorValue base (oneMarkingKey exceptional (.exceptional 0) 2) = -13/2880 := by
  refine ⟨(ancestorValue_oneMarking_square base exceptional .unit 1).trans ?_,
    (ancestorValue_oneMarking_square base exceptional .hyperplane 0).trans ?_,
    (ancestorValue_oneMarking_square base exceptional (.exceptional 0) 0).trans ?_⟩
  all_goals decide +kernel

private theorem exceptionalCurve_eq :
    SurfaceTarget.hirzebruchOne.exceptionalCurve 0 = exceptional := by decide +kernel

/-- All four original queries agree with the reconstructed descendants. -/
theorem accepted (j : Fin 4) : SurfaceGenusTwoBlowupDescendants.queryValue? 0
    (requests j) = some (values j) := by
  rw [← computed_eq_reconstruction]
  have h := exceptional_ancestors (SurfaceGenusTwoBlowupLowPsi.ancestorValueWith boundary)
  fin_cases j
  · have he := queryValueWith?_exceptional boundary 0 .unit
    rw [exceptionalCurve_eq] at he
    refine he.trans (congrArg some ?_)
    change ancestorValue _ (oneMarkingKey exceptional .unit 3) + _ = _
    rw [h.1]
    decide +kernel
  · have he := queryValueWith?_exceptional boundary 0 .hyperplane
    rw [exceptionalCurve_eq] at he
    refine he.trans (congrArg some ?_)
    change ancestorValue _ (oneMarkingKey exceptional .hyperplane 2) + _ = _
    rw [h.2.1]
    decide +kernel
  · have he := queryValueWith?_exceptional boundary 0 (.exceptional 0)
    rw [exceptionalCurve_eq] at he
    refine he.trans (congrArg some ?_)
    change ancestorValue _ (oneMarkingKey exceptional (.exceptional 0) 2) + _ = _
    rw [h.2.2]
    decide +kernel
  · have he := queryValueWith?_exceptional_point boundary 0
    rw [exceptionalCurve_eq] at he
    exact he.trans (by decide +kernel)

/-- The point query is the canonical vanishing exceptional-class state. -/
theorem point_accepted : SurfaceGenusTwoBlowupDescendants.queryValue? 0
    (requests 3) = some (values 3) := accepted 3

end AxiomaticGW.BlowupF1ExceptionalOneMarkingValues

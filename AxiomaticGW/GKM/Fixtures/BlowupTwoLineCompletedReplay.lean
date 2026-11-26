/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.GenusTwoDivisorPairReplay
public import AxiomaticGW.GKM.Fixtures.GenusTwoUnitPairReplay
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Assembly

/-! # Strict-line descendants after the absolute L24 comparison

The original 815-term equation fixes the canonical hyperplane state to zero.
It closes the fifth singleton and the strict-line unit and divisor benchmarks.
-/

@[expose] public section
namespace AxiomaticGW.GKM
open SurfaceGenusTwo

namespace BlowupTwoLineOneMarkingReplay

/-- All five native strict-line singletons agree with the original evaluator. -/
theorem all_accepted (j : Fin 5) :
    SurfaceGenusTwoBlowupDescendants.queryValue? 0 (requests j) = some (values j) := by
  refine Fin.lastCases ?_ high_accepted j
  exact point_agrees_iff.mpr BlowupTwoLineH.hyperplane_value

end BlowupTwoLineOneMarkingReplay

namespace GenusTwoDivisorPairs.StrictLine

/-- All thirty divisor pairs agree, including both signs of the exceptional cup correction. -/
theorem all_accepted (j : Fin 5) (d : Fin 3) (o : Fin 2) :
    FewMarkingQuery (requests j d o) ∧
      divisorPairValue? 0 (requests j d o) = some (values j d o) := by
  simpa only [BlowupTwoLineH.hyperplane_value, mul_zero, add_zero] using comparison j d o

end GenusTwoDivisorPairs.StrictLine

namespace GenusTwoUnitPairs
namespace StrictLinePoint

/-- The ordered string and dilaton pairs over the point first descendant at the strict line. -/
theorem accepted (j : Fin 1) (k : Fin 4) :
    FewMarkingQuery (requests j k) ∧
      unitPairValue? 0 (requests j k) = some (values j k) :=
  accepted_of_point (BlowupTwoLineOneMarkingReplay.all_accepted 4) j k

end StrictLinePoint

namespace StrictLine

/-- All twenty unit pairs, adding the four point rows to the high-power frame. -/
def allRequests (j : Fin 5) (k : Fin 4) : SurfaceQuery .blowupTwo :=
  Fin.lastCases (StrictLinePoint.requests 0 k) (fun n ↦ requests n k) j

/-- Native ordinary values in the complete twenty-request frame. -/
def allValues (j : Fin 5) (k : Fin 4) : ℚ :=
  Fin.lastCases (StrictLinePoint.values 0 k) (fun n ↦ values n k) j

/-- Every ordered pair in the combined frame agrees. -/
theorem all_accepted (j : Fin 5) (k : Fin 4) : FewMarkingQuery (allRequests j k) ∧
    unitPairValue? 0 (allRequests j k) = some (allValues j k) := by
  refine Fin.lastCases ?_ (fun n ↦ ?_) j
  · simpa only [allRequests, allValues, Fin.lastCases_last] using StrictLinePoint.accepted 0 k
  · simpa only [allRequests, allValues, Fin.lastCases_castSucc] using accepted n k

end StrictLine
end GenusTwoUnitPairs
end AxiomaticGW.GKM

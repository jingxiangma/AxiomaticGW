/-
Generated candidate values from Chaudhuri--Das (3.1).
The Getzler relation, rational inputs and geometric base values are shared.
Manifest SHA256: 69221d38c429ad7c466d40c03595ac979469171d719bb533fe4afdbb1d1a4a3d
This digest records provenance; the finite Lean check proves acceptance.
-/
module

public import AxiomaticGW.Surfaces.GenusOneCertificate
public import AxiomaticGW.Surfaces.Fixtures.GenusZeroPlaneTable

@[expose] public section

-- Check rows sequentially to bound kernel replay memory.
set_option Elab.async false

namespace AxiomaticGW.GenusOnePlaneTable

open SurfaceGenusOne

/-- Candidate elliptic point values, keyed by every effective curve coordinate. -/
def values (beta : SurfaceTarget.plane.Curve) : ℚ :=
  match beta 0 with
  | 3 => 1
  | 4 => 225
  | _ => 0

/-- Reuse the same complete full-class requests as the rational table. -/
def classes : List SurfaceTarget.plane.Curve := GenusZeroPlaneTable.classes

theorem covers : classes.toFinset = SurfaceTarget.plane.bounded 12 :=
  GenusZeroPlaneTable.covers

private theorem row_0 :
    checkValue .plane GenusZeroPlaneTable.values values ![0] = true := by
  decide +kernel

private theorem row_1_delta22 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![1] 1
      (GetzlerGraphs.reconstructionLabels .plane) = 0 := by
  decide +kernel

private theorem row_1_delta23 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![1] 1
      (GetzlerGraphs.reconstructionLabels .plane) = 0 := by
  decide +kernel

private theorem row_1_delta24 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![1] 1
      (GetzlerGraphs.reconstructionLabels .plane) = (-1 / 8 : ℚ) := by
  decide +kernel

private theorem row_1_delta34 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![1] 1
      (GetzlerGraphs.reconstructionLabels .plane) = (-1 / 8 : ℚ) := by
  decide +kernel

private theorem row_1_delta03 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![1] 1
      (GetzlerGraphs.reconstructionLabels .plane) = 0 := by
  decide +kernel

private theorem row_1_delta04 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![1] 1
      (GetzlerGraphs.reconstructionLabels .plane) = 3 := by
  decide +kernel

private theorem row_1_deltaBeta :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![1] 1
      (GetzlerGraphs.reconstructionLabels .plane) = 0 := by
  decide +kernel

private theorem row_1 :
    checkValue .plane GenusZeroPlaneTable.values values ![1] = true := by
  have he : SurfaceTarget.plane.effective.energy ![1] = 3 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_1_delta22, row_1_delta23, row_1_delta24, row_1_delta34,
    row_1_delta03, row_1_delta04, row_1_deltaBeta]
  norm_num

private theorem row_2_delta22 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![2] 4
      (GetzlerGraphs.reconstructionLabels .plane) = 0 := by
  decide +kernel

private theorem row_2_delta23 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![2] 4
      (GetzlerGraphs.reconstructionLabels .plane) = 0 := by
  decide +kernel

private theorem row_2_delta24 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![2] 4
      (GetzlerGraphs.reconstructionLabels .plane) = (-7 / 4 : ℚ) := by
  decide +kernel

private theorem row_2_delta34 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![2] 4
      (GetzlerGraphs.reconstructionLabels .plane) = (-7 / 4 : ℚ) := by
  decide +kernel

private theorem row_2_delta03 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![2] 4
      (GetzlerGraphs.reconstructionLabels .plane) = 6 := by
  decide +kernel

private theorem row_2_delta04 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![2] 4
      (GetzlerGraphs.reconstructionLabels .plane) = 54 := by
  decide +kernel

private theorem row_2_deltaBeta :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![2] 4
      (GetzlerGraphs.reconstructionLabels .plane) = 6 := by
  decide +kernel

private theorem row_2 :
    checkValue .plane GenusZeroPlaneTable.values values ![2] = true := by
  have he : SurfaceTarget.plane.effective.energy ![2] = 6 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_2_delta22, row_2_delta23, row_2_delta24, row_2_delta34,
    row_2_delta03, row_2_delta04, row_2_deltaBeta]
  norm_num

private theorem row_3_delta22 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![3] 7
      (GetzlerGraphs.reconstructionLabels .plane) = 0 := by
  decide +kernel

private theorem row_3_delta23 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![3] 7
      (GetzlerGraphs.reconstructionLabels .plane) = 0 := by
  decide +kernel

private theorem row_3_delta24 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![3] 7
      (GetzlerGraphs.reconstructionLabels .plane) = (-207 / 2 : ℚ) := by
  decide +kernel

private theorem row_3_delta34 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![3] 7
      (GetzlerGraphs.reconstructionLabels .plane) = (-207 / 2 : ℚ) := by
  decide +kernel

private theorem row_3_delta03 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![3] 7
      (GetzlerGraphs.reconstructionLabels .plane) = 672 := by
  decide +kernel

private theorem row_3_delta04 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![3] 7
      (GetzlerGraphs.reconstructionLabels .plane) = 3756 := by
  decide +kernel

private theorem row_3_deltaBeta :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![3] 7
      (GetzlerGraphs.reconstructionLabels .plane) = 672 := by
  decide +kernel

private theorem row_3 :
    checkValue .plane GenusZeroPlaneTable.values values ![3] = true := by
  have he : SurfaceTarget.plane.effective.energy ![3] = 9 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (1 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_3_delta22, row_3_delta23, row_3_delta24, row_3_delta34,
    row_3_delta03, row_3_delta04, row_3_deltaBeta]
  norm_num

private theorem row_4_delta22 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![4] 10
      (GetzlerGraphs.reconstructionLabels .plane) = 270 := by
  decide +kernel

private theorem row_4_delta23 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![4] 10
      (GetzlerGraphs.reconstructionLabels .plane) = 315 := by
  decide +kernel

private theorem row_4_delta24 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![4] 10
      (GetzlerGraphs.reconstructionLabels .plane) = -16252 := by
  decide +kernel

private theorem row_4_delta34 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![4] 10
      (GetzlerGraphs.reconstructionLabels .plane) = -16207 := by
  decide +kernel

private theorem row_4_delta03 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![4] 10
      (GetzlerGraphs.reconstructionLabels .plane) = 151992 := by
  decide +kernel

private theorem row_4_delta04 :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![4] 10
      (GetzlerGraphs.reconstructionLabels .plane) = 686472 := by
  decide +kernel

private theorem row_4_deltaBeta :
    dimensionPrunedEval .plane GenusZeroPlaneTable.values
      (fun gamma ↦ if SurfaceTarget.plane.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![4] 10
      (GetzlerGraphs.reconstructionLabels .plane) = 151992 := by
  decide +kernel

private theorem row_4 :
    checkValue .plane GenusZeroPlaneTable.values values ![4] = true := by
  have he : SurfaceTarget.plane.effective.energy ![4] = 12 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (225 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_4_delta22, row_4_delta23, row_4_delta24, row_4_delta34,
    row_4_delta03, row_4_delta04, row_4_deltaBeta]
  norm_num

set_option maxRecDepth 4096 in
/-- Every elliptic equation is checked, including all vanishing classes. -/
theorem rows_checked :
    classes.all (checkValue .plane GenusZeroPlaneTable.values values) = true := by
  simp only [classes, GenusZeroPlaneTable.classes, List.all_cons, List.all_nil,
    row_0, row_1, row_2, row_3, row_4,
    Bool.and_true]

/-- Kernel replay checks both genera throughout the unchanged held bound. -/
theorem accepted : checkBoundedValues .plane 12 GenusZeroPlaneTable.values values = true := by
  apply checkEnumeratedValues_sound .plane 12 classes GenusZeroPlaneTable.values values
  rw [checkEnumeratedValues, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨GenusZeroPlaneTable.accepted, covers, rows_checked⟩

/-- Every covered candidate agrees with the original terminating elliptic evaluator. -/
theorem values_eq (beta : SurfaceTarget.plane.Curve)
    (hbound : SurfaceTarget.plane.effective.energy beta ≤ 12) :
    values beta = pointValue .plane beta :=
  checkBoundedValues_sound .plane 12 GenusZeroPlaneTable.values values accepted beta hbound

end AxiomaticGW.GenusOnePlaneTable

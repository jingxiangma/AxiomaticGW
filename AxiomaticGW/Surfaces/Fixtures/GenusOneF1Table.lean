/-
Generated candidate values from Chaudhuri--Das (3.1).
The Getzler relation, rational inputs and geometric base values are shared.
Manifest SHA256: 69221d38c429ad7c466d40c03595ac979469171d719bb533fe4afdbb1d1a4a3d
This digest records provenance; the finite Lean check proves acceptance.
-/
module

public import AxiomaticGW.Surfaces.GenusOneCertificate
public import AxiomaticGW.Surfaces.Fixtures.GenusZeroF1Table

@[expose] public section

-- Check rows sequentially to bound kernel replay memory.
set_option Elab.async false

namespace AxiomaticGW.GenusOneF1Table

open SurfaceGenusOne

/-- Candidate elliptic point values, keyed by every effective curve coordinate. -/
def values (beta : SurfaceTarget.hirzebruchOne.Curve) : ℚ :=
  match beta 0, beta 1 with
  | 2, 3 => 1
  | 2, 4 => 20
  | 2, 5 => 240
  | 3, 3 => 1
  | 3, 4 => 225
  | 4, 4 => 225
  | _, _ => 0

/-- Reuse the same complete full-class requests as the rational table. -/
def classes : List SurfaceTarget.hirzebruchOne.Curve := GenusZeroF1Table.classes

theorem covers : classes.toFinset = SurfaceTarget.hirzebruchOne.bounded 12 :=
  GenusZeroF1Table.covers

private theorem row_0 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![0, 0] = true := by
  decide +kernel

private theorem row_1 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![1, 0] = true := by
  decide +kernel

private theorem row_2_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 2
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![0, 1] 0
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_2_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 2
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![0, 1] 0
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_2_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 2
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![0, 1] 0
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = (-1 / 12 : ℚ) := by
  decide +kernel

private theorem row_2_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 2
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![0, 1] 0
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = (-1 / 8 : ℚ) := by
  decide +kernel

private theorem row_2_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 2
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![0, 1] 0
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_2_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 2
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![0, 1] 0
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 4 := by
  decide +kernel

private theorem row_2_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 2
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![0, 1] 0
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_2 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![0, 1] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![0, 1] = 2 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_2_delta22, row_2_delta23, row_2_delta24, row_2_delta34,
    row_2_delta03, row_2_delta04, row_2_deltaBeta]
  norm_num

private theorem row_3_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 2
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![2, 0] 0
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_3_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 2
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![2, 0] 0
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_3_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 2
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![2, 0] 0
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_3_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 2
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![2, 0] 0
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_3_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 2
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![2, 0] 0
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_3_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 2
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![2, 0] 0
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_3_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 2
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![2, 0] 0
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_3 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![2, 0] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![2, 0] = 2 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_3_delta22, row_3_delta23, row_3_delta24, row_3_delta34,
    row_3_delta03, row_3_delta04, row_3_deltaBeta]
  norm_num

private theorem row_4_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![1, 1] 1
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_4_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![1, 1] 1
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_4_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![1, 1] 1
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = (-1 / 8 : ℚ) := by
  decide +kernel

private theorem row_4_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![1, 1] 1
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = (-1 / 8 : ℚ) := by
  decide +kernel

private theorem row_4_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![1, 1] 1
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_4_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![1, 1] 1
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 3 := by
  decide +kernel

private theorem row_4_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![1, 1] 1
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_4 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![1, 1] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![1, 1] = 3 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_4_delta22, row_4_delta23, row_4_delta24, row_4_delta34,
    row_4_delta03, row_4_delta04, row_4_deltaBeta]
  norm_num

private theorem row_5_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![3, 0] 1
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_5_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![3, 0] 1
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_5_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![3, 0] 1
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_5_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![3, 0] 1
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_5_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![3, 0] 1
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_5_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![3, 0] 1
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_5_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 3
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![3, 0] 1
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_5 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![3, 0] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![3, 0] = 3 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_5_delta22, row_5_delta23, row_5_delta24, row_5_delta34,
    row_5_delta03, row_5_delta04, row_5_deltaBeta]
  norm_num

private theorem row_6_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![0, 2] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_6_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![0, 2] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_6_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![0, 2] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_6_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![0, 2] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_6_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![0, 2] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_6_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![0, 2] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_6_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![0, 2] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_6 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![0, 2] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![0, 2] = 4 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_6_delta22, row_6_delta23, row_6_delta24, row_6_delta34,
    row_6_delta03, row_6_delta04, row_6_deltaBeta]
  norm_num

private theorem row_7_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![2, 1] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_7_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![2, 1] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_7_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![2, 1] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_7_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![2, 1] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_7_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![2, 1] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_7_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![2, 1] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_7_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![2, 1] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_7 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![2, 1] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![2, 1] = 4 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_7_delta22, row_7_delta23, row_7_delta24, row_7_delta34,
    row_7_delta03, row_7_delta04, row_7_deltaBeta]
  norm_num

private theorem row_8_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![4, 0] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_8_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![4, 0] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_8_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![4, 0] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_8_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![4, 0] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_8_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![4, 0] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_8_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![4, 0] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_8_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 4
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![4, 0] 2
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_8 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![4, 0] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![4, 0] = 4 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_8_delta22, row_8_delta23, row_8_delta24, row_8_delta34,
    row_8_delta03, row_8_delta04, row_8_deltaBeta]
  norm_num

private theorem row_9_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![1, 2] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_9_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![1, 2] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_9_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![1, 2] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = (-35 / 24 : ℚ) := by
  decide +kernel

private theorem row_9_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![1, 2] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = (-13 / 8 : ℚ) := by
  decide +kernel

private theorem row_9_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![1, 2] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 3 := by
  decide +kernel

private theorem row_9_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![1, 2] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 67 := by
  decide +kernel

private theorem row_9_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![1, 2] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 6 := by
  decide +kernel

private theorem row_9 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![1, 2] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![1, 2] = 5 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_9_delta22, row_9_delta23, row_9_delta24, row_9_delta34,
    row_9_delta03, row_9_delta04, row_9_deltaBeta]
  norm_num

private theorem row_10_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![3, 1] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_10_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![3, 1] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_10_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![3, 1] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_10_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![3, 1] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_10_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![3, 1] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_10_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![3, 1] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_10_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![3, 1] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_10 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![3, 1] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![3, 1] = 5 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_10_delta22, row_10_delta23, row_10_delta24, row_10_delta34,
    row_10_delta03, row_10_delta04, row_10_deltaBeta]
  norm_num

private theorem row_11_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![5, 0] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_11_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![5, 0] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_11_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![5, 0] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_11_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![5, 0] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_11_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![5, 0] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_11_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![5, 0] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_11_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 5
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![5, 0] 3
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_11 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![5, 0] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![5, 0] = 5 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_11_delta22, row_11_delta23, row_11_delta24, row_11_delta34,
    row_11_delta03, row_11_delta04, row_11_deltaBeta]
  norm_num

private theorem row_12_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![0, 3] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_12_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![0, 3] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_12_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![0, 3] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_12_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![0, 3] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_12_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![0, 3] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_12_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![0, 3] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_12_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![0, 3] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_12 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![0, 3] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![0, 3] = 6 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_12_delta22, row_12_delta23, row_12_delta24, row_12_delta34,
    row_12_delta03, row_12_delta04, row_12_deltaBeta]
  norm_num

private theorem row_13_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![2, 2] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_13_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![2, 2] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_13_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![2, 2] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = (-7 / 4 : ℚ) := by
  decide +kernel

private theorem row_13_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![2, 2] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = (-7 / 4 : ℚ) := by
  decide +kernel

private theorem row_13_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![2, 2] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 6 := by
  decide +kernel

private theorem row_13_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![2, 2] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 54 := by
  decide +kernel

private theorem row_13_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![2, 2] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 6 := by
  decide +kernel

private theorem row_13 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![2, 2] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![2, 2] = 6 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_13_delta22, row_13_delta23, row_13_delta24, row_13_delta34,
    row_13_delta03, row_13_delta04, row_13_deltaBeta]
  norm_num

private theorem row_14_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![4, 1] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_14_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![4, 1] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_14_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![4, 1] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_14_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![4, 1] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_14_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![4, 1] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_14_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![4, 1] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_14_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![4, 1] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_14 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![4, 1] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![4, 1] = 6 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_14_delta22, row_14_delta23, row_14_delta24, row_14_delta34,
    row_14_delta03, row_14_delta04, row_14_deltaBeta]
  norm_num

private theorem row_15_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![6, 0] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_15_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![6, 0] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_15_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![6, 0] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_15_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![6, 0] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_15_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![6, 0] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_15_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![6, 0] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_15_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 6
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![6, 0] 4
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_15 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![6, 0] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![6, 0] = 6 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_15_delta22, row_15_delta23, row_15_delta24, row_15_delta34,
    row_15_delta03, row_15_delta04, row_15_deltaBeta]
  norm_num

private theorem row_16_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![1, 3] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_16_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![1, 3] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_16_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![1, 3] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = (-203 / 24 : ℚ) := by
  decide +kernel

private theorem row_16_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![1, 3] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = (-211 / 24 : ℚ) := by
  decide +kernel

private theorem row_16_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![1, 3] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 30 := by
  decide +kernel

private theorem row_16_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![1, 3] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 339 := by
  decide +kernel

private theorem row_16_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![1, 3] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 40 := by
  decide +kernel

private theorem row_16 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![1, 3] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![1, 3] = 7 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_16_delta22, row_16_delta23, row_16_delta24, row_16_delta34,
    row_16_delta03, row_16_delta04, row_16_deltaBeta]
  norm_num

private theorem row_17_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![3, 2] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_17_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![3, 2] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_17_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![3, 2] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_17_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![3, 2] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_17_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![3, 2] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_17_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![3, 2] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_17_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![3, 2] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_17 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![3, 2] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![3, 2] = 7 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_17_delta22, row_17_delta23, row_17_delta24, row_17_delta34,
    row_17_delta03, row_17_delta04, row_17_deltaBeta]
  norm_num

private theorem row_18_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![5, 1] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_18_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![5, 1] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_18_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![5, 1] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_18_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![5, 1] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_18_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![5, 1] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_18_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![5, 1] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_18_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![5, 1] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_18 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![5, 1] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![5, 1] = 7 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_18_delta22, row_18_delta23, row_18_delta24, row_18_delta34,
    row_18_delta03, row_18_delta04, row_18_deltaBeta]
  norm_num

private theorem row_19_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![7, 0] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_19_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![7, 0] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_19_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![7, 0] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_19_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![7, 0] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_19_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![7, 0] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_19_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![7, 0] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_19_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 7
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![7, 0] 5
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_19 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![7, 0] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![7, 0] = 7 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_19_delta22, row_19_delta23, row_19_delta24, row_19_delta34,
    row_19_delta03, row_19_delta04, row_19_deltaBeta]
  norm_num

private theorem row_20_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![0, 4] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_20_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![0, 4] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_20_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![0, 4] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_20_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![0, 4] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_20_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![0, 4] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_20_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![0, 4] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_20_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![0, 4] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_20 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![0, 4] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![0, 4] = 8 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_20_delta22, row_20_delta23, row_20_delta24, row_20_delta34,
    row_20_delta03, row_20_delta04, row_20_deltaBeta]
  norm_num

private theorem row_21_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![2, 3] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_21_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![2, 3] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_21_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![2, 3] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = -92 := by
  decide +kernel

private theorem row_21_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![2, 3] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = -97 := by
  decide +kernel

private theorem row_21_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![2, 3] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 516 := by
  decide +kernel

private theorem row_21_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![2, 3] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 4344 := by
  decide +kernel

private theorem row_21_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![2, 3] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 672 := by
  decide +kernel

private theorem row_21 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![2, 3] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![2, 3] = 8 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (1 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_21_delta22, row_21_delta23, row_21_delta24, row_21_delta34,
    row_21_delta03, row_21_delta04, row_21_deltaBeta]
  norm_num

private theorem row_22_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![4, 2] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_22_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![4, 2] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_22_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![4, 2] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_22_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![4, 2] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_22_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![4, 2] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_22_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![4, 2] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_22_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![4, 2] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_22 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![4, 2] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![4, 2] = 8 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_22_delta22, row_22_delta23, row_22_delta24, row_22_delta34,
    row_22_delta03, row_22_delta04, row_22_deltaBeta]
  norm_num

private theorem row_23_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![6, 1] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_23_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![6, 1] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_23_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![6, 1] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_23_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![6, 1] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_23_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![6, 1] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_23_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![6, 1] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_23_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![6, 1] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_23 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![6, 1] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![6, 1] = 8 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_23_delta22, row_23_delta23, row_23_delta24, row_23_delta34,
    row_23_delta03, row_23_delta04, row_23_deltaBeta]
  norm_num

private theorem row_24_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![8, 0] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_24_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![8, 0] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_24_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![8, 0] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_24_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![8, 0] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_24_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![8, 0] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_24_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![8, 0] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_24_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 8
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![8, 0] 6
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_24 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![8, 0] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![8, 0] = 8 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_24_delta22, row_24_delta23, row_24_delta24, row_24_delta34,
    row_24_delta03, row_24_delta04, row_24_deltaBeta]
  norm_num

private theorem row_25_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![1, 4] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_25_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![1, 4] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_25_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![1, 4] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = (-237 / 8 : ℚ) := by
  decide +kernel

private theorem row_25_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![1, 4] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = (-239 / 8 : ℚ) := by
  decide +kernel

private theorem row_25_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![1, 4] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 105 := by
  decide +kernel

private theorem row_25_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![1, 4] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 1059 := by
  decide +kernel

private theorem row_25_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![1, 4] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 126 := by
  decide +kernel

private theorem row_25 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![1, 4] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![1, 4] = 9 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_25_delta22, row_25_delta23, row_25_delta24, row_25_delta34,
    row_25_delta03, row_25_delta04, row_25_deltaBeta]
  norm_num

private theorem row_26_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![3, 3] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_26_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![3, 3] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_26_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![3, 3] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = (-207 / 2 : ℚ) := by
  decide +kernel

private theorem row_26_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![3, 3] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = (-207 / 2 : ℚ) := by
  decide +kernel

private theorem row_26_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![3, 3] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 672 := by
  decide +kernel

private theorem row_26_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![3, 3] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 3756 := by
  decide +kernel

private theorem row_26_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![3, 3] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 672 := by
  decide +kernel

private theorem row_26 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![3, 3] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![3, 3] = 9 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (1 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_26_delta22, row_26_delta23, row_26_delta24, row_26_delta34,
    row_26_delta03, row_26_delta04, row_26_deltaBeta]
  norm_num

private theorem row_27_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![5, 2] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_27_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![5, 2] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_27_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![5, 2] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_27_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![5, 2] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_27_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![5, 2] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_27_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![5, 2] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_27_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![5, 2] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_27 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![5, 2] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![5, 2] = 9 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_27_delta22, row_27_delta23, row_27_delta24, row_27_delta34,
    row_27_delta03, row_27_delta04, row_27_deltaBeta]
  norm_num

private theorem row_28_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![7, 1] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_28_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![7, 1] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_28_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![7, 1] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_28_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![7, 1] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_28_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![7, 1] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_28_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![7, 1] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_28_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![7, 1] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_28 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![7, 1] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![7, 1] = 9 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_28_delta22, row_28_delta23, row_28_delta24, row_28_delta34,
    row_28_delta03, row_28_delta04, row_28_deltaBeta]
  norm_num

private theorem row_29_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![9, 0] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_29_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![9, 0] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_29_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![9, 0] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_29_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![9, 0] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_29_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![9, 0] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_29_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![9, 0] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_29_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 9
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![9, 0] 7
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_29 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![9, 0] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![9, 0] = 9 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_29_delta22, row_29_delta23, row_29_delta24, row_29_delta34,
    row_29_delta03, row_29_delta04, row_29_deltaBeta]
  norm_num

private theorem row_30_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![0, 5] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_30_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![0, 5] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_30_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![0, 5] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_30_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![0, 5] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_30_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![0, 5] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_30_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![0, 5] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_30_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![0, 5] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_30 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![0, 5] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![0, 5] = 10 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_30_delta22, row_30_delta23, row_30_delta24, row_30_delta34,
    row_30_delta03, row_30_delta04, row_30_deltaBeta]
  norm_num

private theorem row_31_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![2, 4] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 32 := by
  decide +kernel

private theorem row_31_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![2, 4] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 39 := by
  decide +kernel

private theorem row_31_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![2, 4] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = -2373 := by
  decide +kernel

private theorem row_31_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![2, 4] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = -2438 := by
  decide +kernel

private theorem row_31_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![2, 4] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 18216 := by
  decide +kernel

private theorem row_31_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![2, 4] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 116376 := by
  decide +kernel

private theorem row_31_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![2, 4] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 21528 := by
  decide +kernel

private theorem row_31 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![2, 4] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![2, 4] = 10 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (20 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_31_delta22, row_31_delta23, row_31_delta24, row_31_delta34,
    row_31_delta03, row_31_delta04, row_31_deltaBeta]
  norm_num

private theorem row_32_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![4, 3] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_32_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![4, 3] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_32_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![4, 3] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_32_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![4, 3] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_32_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![4, 3] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_32_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![4, 3] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_32_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![4, 3] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_32 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![4, 3] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![4, 3] = 10 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_32_delta22, row_32_delta23, row_32_delta24, row_32_delta34,
    row_32_delta03, row_32_delta04, row_32_deltaBeta]
  norm_num

private theorem row_33_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![6, 2] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_33_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![6, 2] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_33_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![6, 2] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_33_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![6, 2] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_33_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![6, 2] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_33_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![6, 2] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_33_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![6, 2] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_33 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![6, 2] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![6, 2] = 10 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_33_delta22, row_33_delta23, row_33_delta24, row_33_delta34,
    row_33_delta03, row_33_delta04, row_33_deltaBeta]
  norm_num

private theorem row_34_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![8, 1] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_34_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![8, 1] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_34_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![8, 1] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_34_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![8, 1] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_34_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![8, 1] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_34_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![8, 1] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_34_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![8, 1] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_34 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![8, 1] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![8, 1] = 10 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_34_delta22, row_34_delta23, row_34_delta24, row_34_delta34,
    row_34_delta03, row_34_delta04, row_34_deltaBeta]
  norm_num

private theorem row_35_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![10, 0] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_35_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![10, 0] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_35_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![10, 0] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_35_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![10, 0] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_35_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![10, 0] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_35_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![10, 0] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_35_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 10
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![10, 0] 8
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_35 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![10, 0] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![10, 0] = 10 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_35_delta22, row_35_delta23, row_35_delta24, row_35_delta34,
    row_35_delta03, row_35_delta04, row_35_deltaBeta]
  norm_num

private theorem row_36_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![1, 5] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_36_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![1, 5] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_36_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![1, 5] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = (-1859 / 24 : ℚ) := by
  decide +kernel

private theorem row_36_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![1, 5] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = (-617 / 8 : ℚ) := by
  decide +kernel

private theorem row_36_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![1, 5] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 252 := by
  decide +kernel

private theorem row_36_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![1, 5] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 2563 := by
  decide +kernel

private theorem row_36_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![1, 5] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 288 := by
  decide +kernel

private theorem row_36 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![1, 5] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![1, 5] = 11 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_36_delta22, row_36_delta23, row_36_delta24, row_36_delta34,
    row_36_delta03, row_36_delta04, row_36_deltaBeta]
  norm_num

private theorem row_37_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![3, 4] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 270 := by
  decide +kernel

private theorem row_37_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![3, 4] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 315 := by
  decide +kernel

private theorem row_37_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![3, 4] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = (-89371 / 6 : ℚ) := by
  decide +kernel

private theorem row_37_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![3, 4] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = (-30689 / 2 : ℚ) := by
  decide +kernel

private theorem row_37_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![3, 4] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 131292 := by
  decide +kernel

private theorem row_37_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![3, 4] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 760436 := by
  decide +kernel

private theorem row_37_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![3, 4] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 151992 := by
  decide +kernel

private theorem row_37 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![3, 4] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![3, 4] = 11 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (225 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_37_delta22, row_37_delta23, row_37_delta24, row_37_delta34,
    row_37_delta03, row_37_delta04, row_37_deltaBeta]
  norm_num

private theorem row_38_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![5, 3] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_38_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![5, 3] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_38_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![5, 3] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_38_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![5, 3] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_38_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![5, 3] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_38_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![5, 3] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_38_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![5, 3] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_38 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![5, 3] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![5, 3] = 11 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_38_delta22, row_38_delta23, row_38_delta24, row_38_delta34,
    row_38_delta03, row_38_delta04, row_38_deltaBeta]
  norm_num

private theorem row_39_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![7, 2] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_39_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![7, 2] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_39_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![7, 2] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_39_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![7, 2] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_39_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![7, 2] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_39_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![7, 2] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_39_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![7, 2] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_39 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![7, 2] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![7, 2] = 11 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_39_delta22, row_39_delta23, row_39_delta24, row_39_delta34,
    row_39_delta03, row_39_delta04, row_39_deltaBeta]
  norm_num

private theorem row_40_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![9, 1] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_40_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![9, 1] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_40_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![9, 1] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_40_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![9, 1] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_40_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![9, 1] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_40_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![9, 1] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_40_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![9, 1] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_40 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![9, 1] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![9, 1] = 11 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_40_delta22, row_40_delta23, row_40_delta24, row_40_delta34,
    row_40_delta03, row_40_delta04, row_40_deltaBeta]
  norm_num

private theorem row_41_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![11, 0] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_41_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![11, 0] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_41_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![11, 0] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_41_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![11, 0] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_41_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![11, 0] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_41_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![11, 0] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_41_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 11
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![11, 0] 9
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_41 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![11, 0] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![11, 0] = 11 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_41_delta22, row_41_delta23, row_41_delta24, row_41_delta34,
    row_41_delta03, row_41_delta04, row_41_deltaBeta]
  norm_num

private theorem row_42_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![0, 6] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_42_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![0, 6] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_42_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![0, 6] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_42_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![0, 6] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_42_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![0, 6] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_42_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![0, 6] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_42_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![0, 6] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_42 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![0, 6] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![0, 6] = 12 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_42_delta22, row_42_delta23, row_42_delta24, row_42_delta34,
    row_42_delta03, row_42_delta04, row_42_deltaBeta]
  norm_num

private theorem row_43_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![2, 5] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 1160 := by
  decide +kernel

private theorem row_43_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![2, 5] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 1280 := by
  decide +kernel

private theorem row_43_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![2, 5] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = -39880 := by
  decide +kernel

private theorem row_43_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![2, 5] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = -40200 := by
  decide +kernel

private theorem row_43_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![2, 5] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 345600 := by
  decide +kernel

private theorem row_43_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![2, 5] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 1939200 := by
  decide +kernel

private theorem row_43_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![2, 5] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 387840 := by
  decide +kernel

private theorem row_43 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![2, 5] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![2, 5] = 12 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (240 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_43_delta22, row_43_delta23, row_43_delta24, row_43_delta34,
    row_43_delta03, row_43_delta04, row_43_deltaBeta]
  norm_num

private theorem row_44_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![4, 4] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 270 := by
  decide +kernel

private theorem row_44_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![4, 4] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 315 := by
  decide +kernel

private theorem row_44_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![4, 4] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = -16252 := by
  decide +kernel

private theorem row_44_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![4, 4] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = -16207 := by
  decide +kernel

private theorem row_44_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![4, 4] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 151992 := by
  decide +kernel

private theorem row_44_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![4, 4] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 686472 := by
  decide +kernel

private theorem row_44_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![4, 4] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 151992 := by
  decide +kernel

private theorem row_44 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![4, 4] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![4, 4] = 12 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (225 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_44_delta22, row_44_delta23, row_44_delta24, row_44_delta34,
    row_44_delta03, row_44_delta04, row_44_deltaBeta]
  norm_num

private theorem row_45_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![6, 3] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_45_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![6, 3] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_45_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![6, 3] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_45_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![6, 3] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_45_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![6, 3] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_45_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![6, 3] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_45_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![6, 3] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_45 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![6, 3] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![6, 3] = 12 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_45_delta22, row_45_delta23, row_45_delta24, row_45_delta34,
    row_45_delta03, row_45_delta04, row_45_deltaBeta]
  norm_num

private theorem row_46_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![8, 2] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_46_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![8, 2] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_46_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![8, 2] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_46_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![8, 2] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_46_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![8, 2] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_46_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![8, 2] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_46_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![8, 2] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_46 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![8, 2] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![8, 2] = 12 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_46_delta22, row_46_delta23, row_46_delta24, row_46_delta34,
    row_46_delta03, row_46_delta04, row_46_deltaBeta]
  norm_num

private theorem row_47_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![10, 1] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_47_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![10, 1] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_47_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![10, 1] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_47_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![10, 1] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_47_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![10, 1] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_47_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![10, 1] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_47_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![10, 1] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_47 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![10, 1] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![10, 1] = 12 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_47_delta22, row_47_delta23, row_47_delta24, row_47_delta34,
    row_47_delta03, row_47_delta04, row_47_deltaBeta]
  norm_num

private theorem row_48_delta22 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta22) (by omega) ![12, 0] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_48_delta23 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta23) (by omega) ![12, 0] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_48_delta24 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta24) (by omega) ![12, 0] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_48_delta34 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta34) (by omega) ![12, 0] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_48_delta03 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta03) (by omega) ![12, 0] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_48_delta04 :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .delta04) (by omega) ![12, 0] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_48_deltaBeta :
    dimensionPrunedEval .hirzebruchOne GenusZeroF1Table.values
      (fun gamma ↦ if SurfaceTarget.hirzebruchOne.effective.energy gamma < 12
        then values gamma else 0)
      (GetzlerGraphs.representativeExpression .deltaBeta) (by omega) ![12, 0] 10
      (GetzlerGraphs.reconstructionLabels .hirzebruchOne) = 0 := by
  decide +kernel

private theorem row_48 :
    checkValue .hirzebruchOne GenusZeroF1Table.values values ![12, 0] = true := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![12, 0] = 12 :=
    by decide +kernel
  rw [checkValue, decide_eq_true_eq, if_neg (by decide +kernel)]
  change (0 : ℚ) = _
  simp only [orbitReconstructionStep, he, Nat.reduceSub,
    row_48_delta22, row_48_delta23, row_48_delta24, row_48_delta34,
    row_48_delta03, row_48_delta04, row_48_deltaBeta]
  norm_num

set_option maxRecDepth 4096 in
/-- Every elliptic equation is checked, including all vanishing classes. -/
theorem rows_checked :
    classes.all (checkValue .hirzebruchOne GenusZeroF1Table.values values) = true := by
  simp only [classes, GenusZeroF1Table.classes, List.all_cons, List.all_nil,
    row_0, row_1, row_2, row_3, row_4, row_5, row_6, row_7,
    row_8, row_9, row_10, row_11, row_12, row_13, row_14, row_15,
    row_16, row_17, row_18, row_19, row_20, row_21, row_22, row_23,
    row_24, row_25, row_26, row_27, row_28, row_29, row_30, row_31,
    row_32, row_33, row_34, row_35, row_36, row_37, row_38, row_39,
    row_40, row_41, row_42, row_43, row_44, row_45, row_46, row_47,
    row_48,
    Bool.and_true]

/-- Kernel replay checks both genera throughout the unchanged held bound. -/
theorem accepted : checkBoundedValues .hirzebruchOne 12 GenusZeroF1Table.values values = true := by
  apply checkEnumeratedValues_sound .hirzebruchOne 12 classes GenusZeroF1Table.values values
  rw [checkEnumeratedValues, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨GenusZeroF1Table.accepted, covers, rows_checked⟩

/-- Every covered candidate agrees with the original terminating elliptic evaluator. -/
theorem values_eq (beta : SurfaceTarget.hirzebruchOne.Curve)
    (hbound : SurfaceTarget.hirzebruchOne.effective.energy beta ≤ 12) :
    values beta = pointValue .hirzebruchOne beta :=
  checkBoundedValues_sound .hirzebruchOne 12 GenusZeroF1Table.values values accepted beta hbound

end AxiomaticGW.GenusOneF1Table

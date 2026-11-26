/-
Generated complete plane genus-two component replay at degree 4.
Input SHA256: 57005f5bcae74824f37f767b60009ff006ba5a25a84ef4c9fac6e0672e07d93c
All original diagrams and six marking assignments are checked, including zeros.
These are candidate computations until this Lean module compiles.
-/
module

public import AxiomaticGW.Surfaces.PlaneGenusTwoScalarSymmetry
public import AxiomaticGW.Surfaces.PlaneGenusTwoFirstCoefficients

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 20000

namespace AxiomaticGW.GenusTwoPlaneDegree4Scalars
open BelorousskiPandharipande

-- Select the actual finite-vector branch before evaluating its contents.
attribute [local cbv_eval] Matrix.cons_val_zero Matrix.cons_val_succ
attribute [local cbv_eval] Matrix.cons_val_zero' Matrix.cons_val_succ'

private def constant_0_parts : Fin 16 → Fin 6 → ℚ :=
  ![
    ![(1345717 / 8), (1345717 / 8), (1345717 / 8), (1345717 / 8), (1345717 / 8), (1345717 / 8)],
    ![(98982 / 5), 14742, (98982 / 5), 14742, 14742, 14742],
    ![(-1214136 / 5), (-1214136 / 5), (-1214136 / 5), -79326, (-1214136 / 5), -79326],
    ![0, 0, 0, 0, 0, 0],
    ![14742, 14742, 14742, 14742, 14742, 14742],
    ![0, 0, 0, 0, 0, 0],
    ![39663, 39663, 39663, (607068 / 5), 39663, (607068 / 5)],
    ![(-6804557 / 24), (-6804557 / 24), (-6804557 / 24),
      (-6804557 / 24), (-6804557 / 24), (-6804557 / 24)],
    ![(-72657 / 5), -11232, (-72657 / 5), -11232, -11232, -11232],
    ![(174798 / 5), (174798 / 5), (174798 / 5), 25623, (174798 / 5), 25623],
    ![(-330858 / 5), (-330858 / 5), (-330858 / 5), (-330858 / 5), (-330858 / 5), (-330858 / 5)],
    ![14976, 14976, 14976, 14976, 14976, 14976],
    ![(-699192 / 5), -102492, (-699192 / 5), -102492, -102492, -102492],
    ![(2880396 / 5), (2880396 / 5), (2880396 / 5), 316026, (2880396 / 5), 316026],
    ![-17082, -17082, -17082, -17082, -17082, -17082],
    ![-49023, -49023, -49023, (-895248 / 5), -49023, (-895248 / 5)]
  ]

private theorem constant_0_marking (k : Fin 16) (e f : Fin 6)
    (h : (![.hyperplane, .hyperplane, .point] : Fin 3 → SurfaceBasisLabel .plane) ∘
      labelPermutation e =
      ![.hyperplane, .hyperplane, .point] ∘ labelPermutation f) :
    planeShiftedConstantPart 4 0 k e = planeShiftedConstantPart 4 0 k f := by
  exact planePointConstantPart_eq_of_labels 13 ![5]
    ![.hyperplane, .hyperplane, .point] k e f h

set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_0_0 : planeShiftedConstantPart 4 0 0 0 =
    (1345717 / 8) := by cbv
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_0_1 : planeShiftedConstantPart 4 0 0 1 =
    (1345717 / 8) := by cbv
private theorem constant_0_part_0_2 : planeShiftedConstantPart 4 0 0 2 =
    (1345717 / 8) := by
  exact (constant_0_marking 0 2 0 (by decide +kernel)).trans
    constant_0_part_0_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_0_3 : planeShiftedConstantPart 4 0 0 3 =
    (1345717 / 8) := by cbv
private theorem constant_0_part_0_4 : planeShiftedConstantPart 4 0 0 4 =
    (1345717 / 8) := by
  exact (constant_0_marking 0 4 1 (by decide +kernel)).trans
    constant_0_part_0_1
private theorem constant_0_part_0_5 : planeShiftedConstantPart 4 0 0 5 =
    (1345717 / 8) := by
  exact (constant_0_marking 0 5 3 (by decide +kernel)).trans
    constant_0_part_0_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_1_0 : planeShiftedConstantPart 4 0 1 0 =
    (98982 / 5) := by cbv
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_1_1 : planeShiftedConstantPart 4 0 1 1 =
    14742 := by cbv
private theorem constant_0_part_1_2 : planeShiftedConstantPart 4 0 1 2 =
    (98982 / 5) := by
  exact (constant_0_marking 1 2 0 (by decide +kernel)).trans
    constant_0_part_1_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_1_3 : planeShiftedConstantPart 4 0 1 3 =
    14742 := by cbv
private theorem constant_0_part_1_4 : planeShiftedConstantPart 4 0 1 4 =
    14742 := by
  exact (constant_0_marking 1 4 1 (by decide +kernel)).trans
    constant_0_part_1_1
private theorem constant_0_part_1_5 : planeShiftedConstantPart 4 0 1 5 =
    14742 := by
  exact (constant_0_marking 1 5 3 (by decide +kernel)).trans
    constant_0_part_1_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_2_0 : planeShiftedConstantPart 4 0 2 0 =
    (-1214136 / 5) := by cbv
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_2_1 : planeShiftedConstantPart 4 0 2 1 =
    (-1214136 / 5) := by cbv
private theorem constant_0_part_2_2 : planeShiftedConstantPart 4 0 2 2 =
    (-1214136 / 5) := by
  exact (constant_0_marking 2 2 0 (by decide +kernel)).trans
    constant_0_part_2_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_2_3 : planeShiftedConstantPart 4 0 2 3 =
    -79326 := by cbv
private theorem constant_0_part_2_4 : planeShiftedConstantPart 4 0 2 4 =
    (-1214136 / 5) := by
  exact (constant_0_marking 2 4 1 (by decide +kernel)).trans
    constant_0_part_2_1
private theorem constant_0_part_2_5 : planeShiftedConstantPart 4 0 2 5 =
    -79326 := by
  exact (constant_0_marking 2 5 3 (by decide +kernel)).trans
    constant_0_part_2_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_3_0 : planeShiftedConstantPart 4 0 3 0 =
    0 := by cbv
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_3_1 : planeShiftedConstantPart 4 0 3 1 =
    0 := by cbv
private theorem constant_0_part_3_2 : planeShiftedConstantPart 4 0 3 2 =
    0 := by
  exact (constant_0_marking 3 2 0 (by decide +kernel)).trans
    constant_0_part_3_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_3_3 : planeShiftedConstantPart 4 0 3 3 =
    0 := by cbv
private theorem constant_0_part_3_4 : planeShiftedConstantPart 4 0 3 4 =
    0 := by
  exact (constant_0_marking 3 4 1 (by decide +kernel)).trans
    constant_0_part_3_1
private theorem constant_0_part_3_5 : planeShiftedConstantPart 4 0 3 5 =
    0 := by
  exact (constant_0_marking 3 5 3 (by decide +kernel)).trans
    constant_0_part_3_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_4_0 : planeShiftedConstantPart 4 0 4 0 =
    14742 := by cbv
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_4_1 : planeShiftedConstantPart 4 0 4 1 =
    14742 := by cbv
private theorem constant_0_part_4_2 : planeShiftedConstantPart 4 0 4 2 =
    14742 := by
  exact (constant_0_marking 4 2 0 (by decide +kernel)).trans
    constant_0_part_4_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_4_3 : planeShiftedConstantPart 4 0 4 3 =
    14742 := by cbv
private theorem constant_0_part_4_4 : planeShiftedConstantPart 4 0 4 4 =
    14742 := by
  exact (constant_0_marking 4 4 1 (by decide +kernel)).trans
    constant_0_part_4_1
private theorem constant_0_part_4_5 : planeShiftedConstantPart 4 0 4 5 =
    14742 := by
  exact (constant_0_marking 4 5 3 (by decide +kernel)).trans
    constant_0_part_4_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_5_0 : planeShiftedConstantPart 4 0 5 0 =
    0 := by cbv
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_5_1 : planeShiftedConstantPart 4 0 5 1 =
    0 := by cbv
private theorem constant_0_part_5_2 : planeShiftedConstantPart 4 0 5 2 =
    0 := by
  exact (constant_0_marking 5 2 0 (by decide +kernel)).trans
    constant_0_part_5_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_5_3 : planeShiftedConstantPart 4 0 5 3 =
    0 := by cbv
private theorem constant_0_part_5_4 : planeShiftedConstantPart 4 0 5 4 =
    0 := by
  exact (constant_0_marking 5 4 1 (by decide +kernel)).trans
    constant_0_part_5_1
private theorem constant_0_part_5_5 : planeShiftedConstantPart 4 0 5 5 =
    0 := by
  exact (constant_0_marking 5 5 3 (by decide +kernel)).trans
    constant_0_part_5_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_6_0 : planeShiftedConstantPart 4 0 6 0 =
    39663 := by cbv
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_6_1 : planeShiftedConstantPart 4 0 6 1 =
    39663 := by cbv
private theorem constant_0_part_6_2 : planeShiftedConstantPart 4 0 6 2 =
    39663 := by
  exact (constant_0_marking 6 2 0 (by decide +kernel)).trans
    constant_0_part_6_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_6_3 : planeShiftedConstantPart 4 0 6 3 =
    (607068 / 5) := by cbv
private theorem constant_0_part_6_4 : planeShiftedConstantPart 4 0 6 4 =
    39663 := by
  exact (constant_0_marking 6 4 1 (by decide +kernel)).trans
    constant_0_part_6_1
private theorem constant_0_part_6_5 : planeShiftedConstantPart 4 0 6 5 =
    (607068 / 5) := by
  exact (constant_0_marking 6 5 3 (by decide +kernel)).trans
    constant_0_part_6_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_7_0 : planeShiftedConstantPart 4 0 7 0 =
    (-6804557 / 24) := by cbv
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_7_1 : planeShiftedConstantPart 4 0 7 1 =
    (-6804557 / 24) := by cbv
private theorem constant_0_part_7_2 : planeShiftedConstantPart 4 0 7 2 =
    (-6804557 / 24) := by
  exact (constant_0_marking 7 2 0 (by decide +kernel)).trans
    constant_0_part_7_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_7_3 : planeShiftedConstantPart 4 0 7 3 =
    (-6804557 / 24) := by cbv
private theorem constant_0_part_7_4 : planeShiftedConstantPart 4 0 7 4 =
    (-6804557 / 24) := by
  exact (constant_0_marking 7 4 1 (by decide +kernel)).trans
    constant_0_part_7_1
private theorem constant_0_part_7_5 : planeShiftedConstantPart 4 0 7 5 =
    (-6804557 / 24) := by
  exact (constant_0_marking 7 5 3 (by decide +kernel)).trans
    constant_0_part_7_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_8_0 : planeShiftedConstantPart 4 0 8 0 =
    (-72657 / 5) := by cbv
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_8_1 : planeShiftedConstantPart 4 0 8 1 =
    -11232 := by cbv
private theorem constant_0_part_8_2 : planeShiftedConstantPart 4 0 8 2 =
    (-72657 / 5) := by
  exact (constant_0_marking 8 2 0 (by decide +kernel)).trans
    constant_0_part_8_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_8_3 : planeShiftedConstantPart 4 0 8 3 =
    -11232 := by cbv
private theorem constant_0_part_8_4 : planeShiftedConstantPart 4 0 8 4 =
    -11232 := by
  exact (constant_0_marking 8 4 1 (by decide +kernel)).trans
    constant_0_part_8_1
private theorem constant_0_part_8_5 : planeShiftedConstantPart 4 0 8 5 =
    -11232 := by
  exact (constant_0_marking 8 5 3 (by decide +kernel)).trans
    constant_0_part_8_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_9_0 : planeShiftedConstantPart 4 0 9 0 =
    (174798 / 5) := by cbv
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_9_1 : planeShiftedConstantPart 4 0 9 1 =
    (174798 / 5) := by cbv
private theorem constant_0_part_9_2 : planeShiftedConstantPart 4 0 9 2 =
    (174798 / 5) := by
  exact (constant_0_marking 9 2 0 (by decide +kernel)).trans
    constant_0_part_9_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_9_3 : planeShiftedConstantPart 4 0 9 3 =
    25623 := by cbv
private theorem constant_0_part_9_4 : planeShiftedConstantPart 4 0 9 4 =
    (174798 / 5) := by
  exact (constant_0_marking 9 4 1 (by decide +kernel)).trans
    constant_0_part_9_1
private theorem constant_0_part_9_5 : planeShiftedConstantPart 4 0 9 5 =
    25623 := by
  exact (constant_0_marking 9 5 3 (by decide +kernel)).trans
    constant_0_part_9_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_10_0 : planeShiftedConstantPart 4 0 10 0 =
    (-330858 / 5) := by cbv
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_10_1 : planeShiftedConstantPart 4 0 10 1 =
    (-330858 / 5) := by cbv
private theorem constant_0_part_10_2 : planeShiftedConstantPart 4 0 10 2 =
    (-330858 / 5) := by
  exact (constant_0_marking 10 2 0 (by decide +kernel)).trans
    constant_0_part_10_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_10_3 : planeShiftedConstantPart 4 0 10 3 =
    (-330858 / 5) := by cbv
private theorem constant_0_part_10_4 : planeShiftedConstantPart 4 0 10 4 =
    (-330858 / 5) := by
  exact (constant_0_marking 10 4 1 (by decide +kernel)).trans
    constant_0_part_10_1
private theorem constant_0_part_10_5 : planeShiftedConstantPart 4 0 10 5 =
    (-330858 / 5) := by
  exact (constant_0_marking 10 5 3 (by decide +kernel)).trans
    constant_0_part_10_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_11_0 : planeShiftedConstantPart 4 0 11 0 =
    14976 := by cbv
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_11_1 : planeShiftedConstantPart 4 0 11 1 =
    14976 := by cbv
private theorem constant_0_part_11_2 : planeShiftedConstantPart 4 0 11 2 =
    14976 := by
  exact (constant_0_marking 11 2 0 (by decide +kernel)).trans
    constant_0_part_11_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_11_3 : planeShiftedConstantPart 4 0 11 3 =
    14976 := by cbv
private theorem constant_0_part_11_4 : planeShiftedConstantPart 4 0 11 4 =
    14976 := by
  exact (constant_0_marking 11 4 1 (by decide +kernel)).trans
    constant_0_part_11_1
private theorem constant_0_part_11_5 : planeShiftedConstantPart 4 0 11 5 =
    14976 := by
  exact (constant_0_marking 11 5 3 (by decide +kernel)).trans
    constant_0_part_11_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_12_0 : planeShiftedConstantPart 4 0 12 0 =
    (-699192 / 5) := by cbv
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_12_1 : planeShiftedConstantPart 4 0 12 1 =
    -102492 := by cbv
private theorem constant_0_part_12_2 : planeShiftedConstantPart 4 0 12 2 =
    (-699192 / 5) := by
  exact (constant_0_marking 12 2 0 (by decide +kernel)).trans
    constant_0_part_12_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_12_3 : planeShiftedConstantPart 4 0 12 3 =
    -102492 := by cbv
private theorem constant_0_part_12_4 : planeShiftedConstantPart 4 0 12 4 =
    -102492 := by
  exact (constant_0_marking 12 4 1 (by decide +kernel)).trans
    constant_0_part_12_1
private theorem constant_0_part_12_5 : planeShiftedConstantPart 4 0 12 5 =
    -102492 := by
  exact (constant_0_marking 12 5 3 (by decide +kernel)).trans
    constant_0_part_12_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_13_0 : planeShiftedConstantPart 4 0 13 0 =
    (2880396 / 5) := by cbv
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_13_1 : planeShiftedConstantPart 4 0 13 1 =
    (2880396 / 5) := by cbv
private theorem constant_0_part_13_2 : planeShiftedConstantPart 4 0 13 2 =
    (2880396 / 5) := by
  exact (constant_0_marking 13 2 0 (by decide +kernel)).trans
    constant_0_part_13_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_13_3 : planeShiftedConstantPart 4 0 13 3 =
    316026 := by cbv
private theorem constant_0_part_13_4 : planeShiftedConstantPart 4 0 13 4 =
    (2880396 / 5) := by
  exact (constant_0_marking 13 4 1 (by decide +kernel)).trans
    constant_0_part_13_1
private theorem constant_0_part_13_5 : planeShiftedConstantPart 4 0 13 5 =
    316026 := by
  exact (constant_0_marking 13 5 3 (by decide +kernel)).trans
    constant_0_part_13_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_14_0 : planeShiftedConstantPart 4 0 14 0 =
    -17082 := by cbv
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_14_1 : planeShiftedConstantPart 4 0 14 1 =
    -17082 := by cbv
private theorem constant_0_part_14_2 : planeShiftedConstantPart 4 0 14 2 =
    -17082 := by
  exact (constant_0_marking 14 2 0 (by decide +kernel)).trans
    constant_0_part_14_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_14_3 : planeShiftedConstantPart 4 0 14 3 =
    -17082 := by cbv
private theorem constant_0_part_14_4 : planeShiftedConstantPart 4 0 14 4 =
    -17082 := by
  exact (constant_0_marking 14 4 1 (by decide +kernel)).trans
    constant_0_part_14_1
private theorem constant_0_part_14_5 : planeShiftedConstantPart 4 0 14 5 =
    -17082 := by
  exact (constant_0_marking 14 5 3 (by decide +kernel)).trans
    constant_0_part_14_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_15_0 : planeShiftedConstantPart 4 0 15 0 =
    -49023 := by cbv
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_15_1 : planeShiftedConstantPart 4 0 15 1 =
    -49023 := by cbv
private theorem constant_0_part_15_2 : planeShiftedConstantPart 4 0 15 2 =
    -49023 := by
  exact (constant_0_marking 15 2 0 (by decide +kernel)).trans
    constant_0_part_15_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_0_part_15_3 : planeShiftedConstantPart 4 0 15 3 =
    (-895248 / 5) := by cbv
private theorem constant_0_part_15_4 : planeShiftedConstantPart 4 0 15 4 =
    -49023 := by
  exact (constant_0_marking 15 4 1 (by decide +kernel)).trans
    constant_0_part_15_1
private theorem constant_0_part_15_5 : planeShiftedConstantPart 4 0 15 5 =
    (-895248 / 5) := by
  exact (constant_0_marking 15 5 3 (by decide +kernel)).trans
    constant_0_part_15_3

private theorem constant_0_parts_checked (k : Fin 16) (e : Fin 6) :
    planeShiftedConstantPart 4 0 k e = constant_0_parts k e := by
  fin_cases k <;> fin_cases e
  · exact constant_0_part_0_0
  · exact constant_0_part_0_1
  · exact constant_0_part_0_2
  · exact constant_0_part_0_3
  · exact constant_0_part_0_4
  · exact constant_0_part_0_5
  · exact constant_0_part_1_0
  · exact constant_0_part_1_1
  · exact constant_0_part_1_2
  · exact constant_0_part_1_3
  · exact constant_0_part_1_4
  · exact constant_0_part_1_5
  · exact constant_0_part_2_0
  · exact constant_0_part_2_1
  · exact constant_0_part_2_2
  · exact constant_0_part_2_3
  · exact constant_0_part_2_4
  · exact constant_0_part_2_5
  · exact constant_0_part_3_0
  · exact constant_0_part_3_1
  · exact constant_0_part_3_2
  · exact constant_0_part_3_3
  · exact constant_0_part_3_4
  · exact constant_0_part_3_5
  · exact constant_0_part_4_0
  · exact constant_0_part_4_1
  · exact constant_0_part_4_2
  · exact constant_0_part_4_3
  · exact constant_0_part_4_4
  · exact constant_0_part_4_5
  · exact constant_0_part_5_0
  · exact constant_0_part_5_1
  · exact constant_0_part_5_2
  · exact constant_0_part_5_3
  · exact constant_0_part_5_4
  · exact constant_0_part_5_5
  · exact constant_0_part_6_0
  · exact constant_0_part_6_1
  · exact constant_0_part_6_2
  · exact constant_0_part_6_3
  · exact constant_0_part_6_4
  · exact constant_0_part_6_5
  · exact constant_0_part_7_0
  · exact constant_0_part_7_1
  · exact constant_0_part_7_2
  · exact constant_0_part_7_3
  · exact constant_0_part_7_4
  · exact constant_0_part_7_5
  · exact constant_0_part_8_0
  · exact constant_0_part_8_1
  · exact constant_0_part_8_2
  · exact constant_0_part_8_3
  · exact constant_0_part_8_4
  · exact constant_0_part_8_5
  · exact constant_0_part_9_0
  · exact constant_0_part_9_1
  · exact constant_0_part_9_2
  · exact constant_0_part_9_3
  · exact constant_0_part_9_4
  · exact constant_0_part_9_5
  · exact constant_0_part_10_0
  · exact constant_0_part_10_1
  · exact constant_0_part_10_2
  · exact constant_0_part_10_3
  · exact constant_0_part_10_4
  · exact constant_0_part_10_5
  · exact constant_0_part_11_0
  · exact constant_0_part_11_1
  · exact constant_0_part_11_2
  · exact constant_0_part_11_3
  · exact constant_0_part_11_4
  · exact constant_0_part_11_5
  · exact constant_0_part_12_0
  · exact constant_0_part_12_1
  · exact constant_0_part_12_2
  · exact constant_0_part_12_3
  · exact constant_0_part_12_4
  · exact constant_0_part_12_5
  · exact constant_0_part_13_0
  · exact constant_0_part_13_1
  · exact constant_0_part_13_2
  · exact constant_0_part_13_3
  · exact constant_0_part_13_4
  · exact constant_0_part_13_5
  · exact constant_0_part_14_0
  · exact constant_0_part_14_1
  · exact constant_0_part_14_2
  · exact constant_0_part_14_3
  · exact constant_0_part_14_4
  · exact constant_0_part_14_5
  · exact constant_0_part_15_0
  · exact constant_0_part_15_1
  · exact constant_0_part_15_2
  · exact constant_0_part_15_3
  · exact constant_0_part_15_4
  · exact constant_0_part_15_5

private theorem constant_0 : planeShiftedConstantFast 4 0 =
    (333281 / 2) := by
  rw [planeShiftedConstantFast_eq_sum_parts]
  simp_rw [constant_0_parts_checked]
  decide +kernel

private def coefficient_0_0_1_parts : Fin 4 → Fin 6 → ℚ :=
  ![
    ![0, 0, 0, 0, 0, 0],
    ![21826000, 21826000, 21826000, 21826000, 21826000, 21826000],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0]
  ]

private theorem coefficient_0_0_1_marking (k : Fin 4) (e f : Fin 6)
    (h : (![.hyperplane, .hyperplane, .point] : Fin 3 → SurfaceBasisLabel .plane) ∘
      labelPermutation e =
      ![.hyperplane, .hyperplane, .point] ∘ labelPermutation f) :
    planeEarlierCoefficientPart 4 0 0 1 k e = planeEarlierCoefficientPart 4 0 0 1 k f := by
  exact planePointCoefficientPart_eq_of_labels 13 5
    ![.hyperplane, .hyperplane, .point] (Sum.inr (planeCanonicalQueries 0 1)) k e f h

set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_0_1_part_0_0 : planeEarlierCoefficientPart 4 0 0 1 0 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_0_1_part_0_1 : planeEarlierCoefficientPart 4 0 0 1 0 1 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_0_1_part_0_2 : planeEarlierCoefficientPart 4 0 0 1 0 2 =
    0 := by
  exact (coefficient_0_0_1_marking 0 2 0 (by decide +kernel)).trans
    coefficient_0_0_1_part_0_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_0_1_part_0_3 : planeEarlierCoefficientPart 4 0 0 1 0 3 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_0_1_part_0_4 : planeEarlierCoefficientPart 4 0 0 1 0 4 =
    0 := by
  exact (coefficient_0_0_1_marking 0 4 1 (by decide +kernel)).trans
    coefficient_0_0_1_part_0_1
private theorem coefficient_0_0_1_part_0_5 : planeEarlierCoefficientPart 4 0 0 1 0 5 =
    0 := by
  exact (coefficient_0_0_1_marking 0 5 3 (by decide +kernel)).trans
    coefficient_0_0_1_part_0_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_0_1_part_1_0 : planeEarlierCoefficientPart 4 0 0 1 1 0 =
    21826000 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_0_1_part_1_1 : planeEarlierCoefficientPart 4 0 0 1 1 1 =
    21826000 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_0_1_part_1_2 : planeEarlierCoefficientPart 4 0 0 1 1 2 =
    21826000 := by
  exact (coefficient_0_0_1_marking 1 2 0 (by decide +kernel)).trans
    coefficient_0_0_1_part_1_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_0_1_part_1_3 : planeEarlierCoefficientPart 4 0 0 1 1 3 =
    21826000 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_0_1_part_1_4 : planeEarlierCoefficientPart 4 0 0 1 1 4 =
    21826000 := by
  exact (coefficient_0_0_1_marking 1 4 1 (by decide +kernel)).trans
    coefficient_0_0_1_part_1_1
private theorem coefficient_0_0_1_part_1_5 : planeEarlierCoefficientPart 4 0 0 1 1 5 =
    21826000 := by
  exact (coefficient_0_0_1_marking 1 5 3 (by decide +kernel)).trans
    coefficient_0_0_1_part_1_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_0_1_part_2_0 : planeEarlierCoefficientPart 4 0 0 1 2 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_0_1_part_2_1 : planeEarlierCoefficientPart 4 0 0 1 2 1 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_0_1_part_2_2 : planeEarlierCoefficientPart 4 0 0 1 2 2 =
    0 := by
  exact (coefficient_0_0_1_marking 2 2 0 (by decide +kernel)).trans
    coefficient_0_0_1_part_2_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_0_1_part_2_3 : planeEarlierCoefficientPart 4 0 0 1 2 3 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_0_1_part_2_4 : planeEarlierCoefficientPart 4 0 0 1 2 4 =
    0 := by
  exact (coefficient_0_0_1_marking 2 4 1 (by decide +kernel)).trans
    coefficient_0_0_1_part_2_1
private theorem coefficient_0_0_1_part_2_5 : planeEarlierCoefficientPart 4 0 0 1 2 5 =
    0 := by
  exact (coefficient_0_0_1_marking 2 5 3 (by decide +kernel)).trans
    coefficient_0_0_1_part_2_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_0_1_part_3_0 : planeEarlierCoefficientPart 4 0 0 1 3 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_0_1_part_3_1 : planeEarlierCoefficientPart 4 0 0 1 3 1 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_0_1_part_3_2 : planeEarlierCoefficientPart 4 0 0 1 3 2 =
    0 := by
  exact (coefficient_0_0_1_marking 3 2 0 (by decide +kernel)).trans
    coefficient_0_0_1_part_3_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_0_1_part_3_3 : planeEarlierCoefficientPart 4 0 0 1 3 3 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_0_1_part_3_4 : planeEarlierCoefficientPart 4 0 0 1 3 4 =
    0 := by
  exact (coefficient_0_0_1_marking 3 4 1 (by decide +kernel)).trans
    coefficient_0_0_1_part_3_1
private theorem coefficient_0_0_1_part_3_5 : planeEarlierCoefficientPart 4 0 0 1 3 5 =
    0 := by
  exact (coefficient_0_0_1_marking 3 5 3 (by decide +kernel)).trans
    coefficient_0_0_1_part_3_3

private theorem coefficient_0_0_1_parts_checked (k : Fin 4) (e : Fin 6) :
    planeEarlierCoefficientPart 4 0 0 1 k e = coefficient_0_0_1_parts k e := by
  fin_cases k <;> fin_cases e
  · exact coefficient_0_0_1_part_0_0
  · exact coefficient_0_0_1_part_0_1
  · exact coefficient_0_0_1_part_0_2
  · exact coefficient_0_0_1_part_0_3
  · exact coefficient_0_0_1_part_0_4
  · exact coefficient_0_0_1_part_0_5
  · exact coefficient_0_0_1_part_1_0
  · exact coefficient_0_0_1_part_1_1
  · exact coefficient_0_0_1_part_1_2
  · exact coefficient_0_0_1_part_1_3
  · exact coefficient_0_0_1_part_1_4
  · exact coefficient_0_0_1_part_1_5
  · exact coefficient_0_0_1_part_2_0
  · exact coefficient_0_0_1_part_2_1
  · exact coefficient_0_0_1_part_2_2
  · exact coefficient_0_0_1_part_2_3
  · exact coefficient_0_0_1_part_2_4
  · exact coefficient_0_0_1_part_2_5
  · exact coefficient_0_0_1_part_3_0
  · exact coefficient_0_0_1_part_3_1
  · exact coefficient_0_0_1_part_3_2
  · exact coefficient_0_0_1_part_3_3
  · exact coefficient_0_0_1_part_3_4
  · exact coefficient_0_0_1_part_3_5

private theorem coefficient_0_0_1 : planeEarlierCoefficient 4 0 0 1 =
    130956000 := by
  rw [planeEarlierCoefficient_eq_sum_parts]
  simp_rw [coefficient_0_0_1_parts_checked]
  decide +kernel

private def coefficient_0_3_1_parts : Fin 4 → Fin 6 → ℚ :=
  ![
    ![0, 0, 0, 0, 0, 0],
    ![11440, 11440, 11440, 11440, 11440, 11440],
    ![25740, 25740, 25740, 0, 25740, 0],
    ![-25740, -25740, -25740, -30888, -25740, -30888]
  ]

private theorem coefficient_0_3_1_marking (k : Fin 4) (e f : Fin 6)
    (h : (![.hyperplane, .hyperplane, .point] : Fin 3 → SurfaceBasisLabel .plane) ∘
      labelPermutation e =
      ![.hyperplane, .hyperplane, .point] ∘ labelPermutation f) :
    planeEarlierCoefficientPart 4 0 3 1 k e = planeEarlierCoefficientPart 4 0 3 1 k f := by
  exact planePointCoefficientPart_eq_of_labels 13 5
    ![.hyperplane, .hyperplane, .point] (Sum.inr (planeCanonicalQueries 3 1)) k e f h

set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_1_part_0_0 : planeEarlierCoefficientPart 4 0 3 1 0 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_1_part_0_1 : planeEarlierCoefficientPart 4 0 3 1 0 1 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_3_1_part_0_2 : planeEarlierCoefficientPart 4 0 3 1 0 2 =
    0 := by
  exact (coefficient_0_3_1_marking 0 2 0 (by decide +kernel)).trans
    coefficient_0_3_1_part_0_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_1_part_0_3 : planeEarlierCoefficientPart 4 0 3 1 0 3 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_3_1_part_0_4 : planeEarlierCoefficientPart 4 0 3 1 0 4 =
    0 := by
  exact (coefficient_0_3_1_marking 0 4 1 (by decide +kernel)).trans
    coefficient_0_3_1_part_0_1
private theorem coefficient_0_3_1_part_0_5 : planeEarlierCoefficientPart 4 0 3 1 0 5 =
    0 := by
  exact (coefficient_0_3_1_marking 0 5 3 (by decide +kernel)).trans
    coefficient_0_3_1_part_0_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_1_part_1_0 : planeEarlierCoefficientPart 4 0 3 1 1 0 =
    11440 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_1_part_1_1 : planeEarlierCoefficientPart 4 0 3 1 1 1 =
    11440 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_3_1_part_1_2 : planeEarlierCoefficientPart 4 0 3 1 1 2 =
    11440 := by
  exact (coefficient_0_3_1_marking 1 2 0 (by decide +kernel)).trans
    coefficient_0_3_1_part_1_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_1_part_1_3 : planeEarlierCoefficientPart 4 0 3 1 1 3 =
    11440 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_3_1_part_1_4 : planeEarlierCoefficientPart 4 0 3 1 1 4 =
    11440 := by
  exact (coefficient_0_3_1_marking 1 4 1 (by decide +kernel)).trans
    coefficient_0_3_1_part_1_1
private theorem coefficient_0_3_1_part_1_5 : planeEarlierCoefficientPart 4 0 3 1 1 5 =
    11440 := by
  exact (coefficient_0_3_1_marking 1 5 3 (by decide +kernel)).trans
    coefficient_0_3_1_part_1_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_1_part_2_0 : planeEarlierCoefficientPart 4 0 3 1 2 0 =
    25740 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_1_part_2_1 : planeEarlierCoefficientPart 4 0 3 1 2 1 =
    25740 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_3_1_part_2_2 : planeEarlierCoefficientPart 4 0 3 1 2 2 =
    25740 := by
  exact (coefficient_0_3_1_marking 2 2 0 (by decide +kernel)).trans
    coefficient_0_3_1_part_2_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_1_part_2_3 : planeEarlierCoefficientPart 4 0 3 1 2 3 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_3_1_part_2_4 : planeEarlierCoefficientPart 4 0 3 1 2 4 =
    25740 := by
  exact (coefficient_0_3_1_marking 2 4 1 (by decide +kernel)).trans
    coefficient_0_3_1_part_2_1
private theorem coefficient_0_3_1_part_2_5 : planeEarlierCoefficientPart 4 0 3 1 2 5 =
    0 := by
  exact (coefficient_0_3_1_marking 2 5 3 (by decide +kernel)).trans
    coefficient_0_3_1_part_2_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_1_part_3_0 : planeEarlierCoefficientPart 4 0 3 1 3 0 =
    -25740 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_1_part_3_1 : planeEarlierCoefficientPart 4 0 3 1 3 1 =
    -25740 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_3_1_part_3_2 : planeEarlierCoefficientPart 4 0 3 1 3 2 =
    -25740 := by
  exact (coefficient_0_3_1_marking 3 2 0 (by decide +kernel)).trans
    coefficient_0_3_1_part_3_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_1_part_3_3 : planeEarlierCoefficientPart 4 0 3 1 3 3 =
    -30888 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_3_1_part_3_4 : planeEarlierCoefficientPart 4 0 3 1 3 4 =
    -25740 := by
  exact (coefficient_0_3_1_marking 3 4 1 (by decide +kernel)).trans
    coefficient_0_3_1_part_3_1
private theorem coefficient_0_3_1_part_3_5 : planeEarlierCoefficientPart 4 0 3 1 3 5 =
    -30888 := by
  exact (coefficient_0_3_1_marking 3 5 3 (by decide +kernel)).trans
    coefficient_0_3_1_part_3_3

private theorem coefficient_0_3_1_parts_checked (k : Fin 4) (e : Fin 6) :
    planeEarlierCoefficientPart 4 0 3 1 k e = coefficient_0_3_1_parts k e := by
  fin_cases k <;> fin_cases e
  · exact coefficient_0_3_1_part_0_0
  · exact coefficient_0_3_1_part_0_1
  · exact coefficient_0_3_1_part_0_2
  · exact coefficient_0_3_1_part_0_3
  · exact coefficient_0_3_1_part_0_4
  · exact coefficient_0_3_1_part_0_5
  · exact coefficient_0_3_1_part_1_0
  · exact coefficient_0_3_1_part_1_1
  · exact coefficient_0_3_1_part_1_2
  · exact coefficient_0_3_1_part_1_3
  · exact coefficient_0_3_1_part_1_4
  · exact coefficient_0_3_1_part_1_5
  · exact coefficient_0_3_1_part_2_0
  · exact coefficient_0_3_1_part_2_1
  · exact coefficient_0_3_1_part_2_2
  · exact coefficient_0_3_1_part_2_3
  · exact coefficient_0_3_1_part_2_4
  · exact coefficient_0_3_1_part_2_5
  · exact coefficient_0_3_1_part_3_0
  · exact coefficient_0_3_1_part_3_1
  · exact coefficient_0_3_1_part_3_2
  · exact coefficient_0_3_1_part_3_3
  · exact coefficient_0_3_1_part_3_4
  · exact coefficient_0_3_1_part_3_5

private theorem coefficient_0_3_1 : planeEarlierCoefficient 4 0 3 1 =
    6864 := by
  rw [planeEarlierCoefficient_eq_sum_parts]
  simp_rw [coefficient_0_3_1_parts_checked]
  decide +kernel

private def coefficient_0_3_2_parts : Fin 4 → Fin 6 → ℚ :=
  ![
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 92664, 0, 92664],
    ![0, 0, 0, 0, 0, 0]
  ]

private theorem coefficient_0_3_2_marking (k : Fin 4) (e f : Fin 6)
    (h : (![.hyperplane, .hyperplane, .point] : Fin 3 → SurfaceBasisLabel .plane) ∘
      labelPermutation e =
      ![.hyperplane, .hyperplane, .point] ∘ labelPermutation f) :
    planeEarlierCoefficientPart 4 0 3 2 k e = planeEarlierCoefficientPart 4 0 3 2 k f := by
  exact planePointCoefficientPart_eq_of_labels 13 5
    ![.hyperplane, .hyperplane, .point] (Sum.inr (planeCanonicalQueries 3 2)) k e f h

set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_2_part_0_0 : planeEarlierCoefficientPart 4 0 3 2 0 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_2_part_0_1 : planeEarlierCoefficientPart 4 0 3 2 0 1 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_3_2_part_0_2 : planeEarlierCoefficientPart 4 0 3 2 0 2 =
    0 := by
  exact (coefficient_0_3_2_marking 0 2 0 (by decide +kernel)).trans
    coefficient_0_3_2_part_0_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_2_part_0_3 : planeEarlierCoefficientPart 4 0 3 2 0 3 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_3_2_part_0_4 : planeEarlierCoefficientPart 4 0 3 2 0 4 =
    0 := by
  exact (coefficient_0_3_2_marking 0 4 1 (by decide +kernel)).trans
    coefficient_0_3_2_part_0_1
private theorem coefficient_0_3_2_part_0_5 : planeEarlierCoefficientPart 4 0 3 2 0 5 =
    0 := by
  exact (coefficient_0_3_2_marking 0 5 3 (by decide +kernel)).trans
    coefficient_0_3_2_part_0_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_2_part_1_0 : planeEarlierCoefficientPart 4 0 3 2 1 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_2_part_1_1 : planeEarlierCoefficientPart 4 0 3 2 1 1 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_3_2_part_1_2 : planeEarlierCoefficientPart 4 0 3 2 1 2 =
    0 := by
  exact (coefficient_0_3_2_marking 1 2 0 (by decide +kernel)).trans
    coefficient_0_3_2_part_1_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_2_part_1_3 : planeEarlierCoefficientPart 4 0 3 2 1 3 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_3_2_part_1_4 : planeEarlierCoefficientPart 4 0 3 2 1 4 =
    0 := by
  exact (coefficient_0_3_2_marking 1 4 1 (by decide +kernel)).trans
    coefficient_0_3_2_part_1_1
private theorem coefficient_0_3_2_part_1_5 : planeEarlierCoefficientPart 4 0 3 2 1 5 =
    0 := by
  exact (coefficient_0_3_2_marking 1 5 3 (by decide +kernel)).trans
    coefficient_0_3_2_part_1_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_2_part_2_0 : planeEarlierCoefficientPart 4 0 3 2 2 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_2_part_2_1 : planeEarlierCoefficientPart 4 0 3 2 2 1 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_3_2_part_2_2 : planeEarlierCoefficientPart 4 0 3 2 2 2 =
    0 := by
  exact (coefficient_0_3_2_marking 2 2 0 (by decide +kernel)).trans
    coefficient_0_3_2_part_2_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_2_part_2_3 : planeEarlierCoefficientPart 4 0 3 2 2 3 =
    92664 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_3_2_part_2_4 : planeEarlierCoefficientPart 4 0 3 2 2 4 =
    0 := by
  exact (coefficient_0_3_2_marking 2 4 1 (by decide +kernel)).trans
    coefficient_0_3_2_part_2_1
private theorem coefficient_0_3_2_part_2_5 : planeEarlierCoefficientPart 4 0 3 2 2 5 =
    92664 := by
  exact (coefficient_0_3_2_marking 2 5 3 (by decide +kernel)).trans
    coefficient_0_3_2_part_2_3
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_2_part_3_0 : planeEarlierCoefficientPart 4 0 3 2 3 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_2_part_3_1 : planeEarlierCoefficientPart 4 0 3 2 3 1 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_3_2_part_3_2 : planeEarlierCoefficientPart 4 0 3 2 3 2 =
    0 := by
  exact (coefficient_0_3_2_marking 3 2 0 (by decide +kernel)).trans
    coefficient_0_3_2_part_3_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_0_3_2_part_3_3 : planeEarlierCoefficientPart 4 0 3 2 3 3 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_0_3_2_part_3_4 : planeEarlierCoefficientPart 4 0 3 2 3 4 =
    0 := by
  exact (coefficient_0_3_2_marking 3 4 1 (by decide +kernel)).trans
    coefficient_0_3_2_part_3_1
private theorem coefficient_0_3_2_part_3_5 : planeEarlierCoefficientPart 4 0 3 2 3 5 =
    0 := by
  exact (coefficient_0_3_2_marking 3 5 3 (by decide +kernel)).trans
    coefficient_0_3_2_part_3_3

private theorem coefficient_0_3_2_parts_checked (k : Fin 4) (e : Fin 6) :
    planeEarlierCoefficientPart 4 0 3 2 k e = coefficient_0_3_2_parts k e := by
  fin_cases k <;> fin_cases e
  · exact coefficient_0_3_2_part_0_0
  · exact coefficient_0_3_2_part_0_1
  · exact coefficient_0_3_2_part_0_2
  · exact coefficient_0_3_2_part_0_3
  · exact coefficient_0_3_2_part_0_4
  · exact coefficient_0_3_2_part_0_5
  · exact coefficient_0_3_2_part_1_0
  · exact coefficient_0_3_2_part_1_1
  · exact coefficient_0_3_2_part_1_2
  · exact coefficient_0_3_2_part_1_3
  · exact coefficient_0_3_2_part_1_4
  · exact coefficient_0_3_2_part_1_5
  · exact coefficient_0_3_2_part_2_0
  · exact coefficient_0_3_2_part_2_1
  · exact coefficient_0_3_2_part_2_2
  · exact coefficient_0_3_2_part_2_3
  · exact coefficient_0_3_2_part_2_4
  · exact coefficient_0_3_2_part_2_5
  · exact coefficient_0_3_2_part_3_0
  · exact coefficient_0_3_2_part_3_1
  · exact coefficient_0_3_2_part_3_2
  · exact coefficient_0_3_2_part_3_3
  · exact coefficient_0_3_2_part_3_4
  · exact coefficient_0_3_2_part_3_5

private theorem coefficient_0_3_2 : planeEarlierCoefficient 4 0 3 2 =
    185328 := by
  rw [planeEarlierCoefficient_eq_sum_parts]
  simp_rw [coefficient_0_3_2_parts_checked]
  decide +kernel

private def constant_1_parts : Fin 16 → Fin 6 → ℚ :=
  ![
    ![(270353 / 8), (270353 / 8), (270353 / 8), (270353 / 8), (270353 / 8), (270353 / 8)],
    ![3402, 3402, 3402, 3402, 1728, 1728],
    ![-49680, -49680, -18306, -18306, -18306, -18306],
    ![0, 0, 0, 0, 0, 0],
    ![1728, 1728, 1728, 1728, 1728, 1728],
    ![0, 0, 0, 0, 0, 0],
    ![3942, 3942, 9153, 9153, 9153, 9153],
    ![(-1361833 / 24), (-1361833 / 24), (-1361833 / 24),
      (-1361833 / 24), (-1361833 / 24), (-1361833 / 24)],
    ![-2592, -2592, -2592, -2592, -1458, -1458],
    ![(36531 / 5), (36531 / 5), 5913, 5913, 5913, 5913],
    ![(-66771 / 5), (-66771 / 5), (-66771 / 5), (-66771 / 5), (-66771 / 5), (-66771 / 5)],
    ![1944, 1944, 1944, 1944, 1944, 1944],
    ![-23652, -23652, -23652, -23652, -11448, -11448],
    ![(583272 / 5), (583272 / 5), 66222, 66222, 66222, 66222],
    ![-1908, -1908, -1908, -1908, -1908, -1908],
    ![-4662, -4662, -11313, -11313, -11313, -11313]
  ]

private theorem constant_1_marking (k : Fin 16) (e f : Fin 6)
    (h : (![.hyperplane, .point, .point] : Fin 3 → SurfaceBasisLabel .plane) ∘
      labelPermutation e =
      ![.hyperplane, .point, .point] ∘ labelPermutation f) :
    planeShiftedConstantPart 4 1 k e = planeShiftedConstantPart 4 1 k f := by
  exact planePointConstantPart_eq_of_labels 12 ![5]
    ![.hyperplane, .point, .point] k e f h

set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_0_0 : planeShiftedConstantPart 4 1 0 0 =
    (270353 / 8) := by cbv
private theorem constant_1_part_0_1 : planeShiftedConstantPart 4 1 0 1 =
    (270353 / 8) := by
  exact (constant_1_marking 0 1 0 (by decide +kernel)).trans
    constant_1_part_0_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_0_2 : planeShiftedConstantPart 4 1 0 2 =
    (270353 / 8) := by cbv
private theorem constant_1_part_0_3 : planeShiftedConstantPart 4 1 0 3 =
    (270353 / 8) := by
  exact (constant_1_marking 0 3 2 (by decide +kernel)).trans
    constant_1_part_0_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_0_4 : planeShiftedConstantPart 4 1 0 4 =
    (270353 / 8) := by cbv
private theorem constant_1_part_0_5 : planeShiftedConstantPart 4 1 0 5 =
    (270353 / 8) := by
  exact (constant_1_marking 0 5 4 (by decide +kernel)).trans
    constant_1_part_0_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_1_0 : planeShiftedConstantPart 4 1 1 0 =
    3402 := by cbv
private theorem constant_1_part_1_1 : planeShiftedConstantPart 4 1 1 1 =
    3402 := by
  exact (constant_1_marking 1 1 0 (by decide +kernel)).trans
    constant_1_part_1_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_1_2 : planeShiftedConstantPart 4 1 1 2 =
    3402 := by cbv
private theorem constant_1_part_1_3 : planeShiftedConstantPart 4 1 1 3 =
    3402 := by
  exact (constant_1_marking 1 3 2 (by decide +kernel)).trans
    constant_1_part_1_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_1_4 : planeShiftedConstantPart 4 1 1 4 =
    1728 := by cbv
private theorem constant_1_part_1_5 : planeShiftedConstantPart 4 1 1 5 =
    1728 := by
  exact (constant_1_marking 1 5 4 (by decide +kernel)).trans
    constant_1_part_1_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_2_0 : planeShiftedConstantPart 4 1 2 0 =
    -49680 := by cbv
private theorem constant_1_part_2_1 : planeShiftedConstantPart 4 1 2 1 =
    -49680 := by
  exact (constant_1_marking 2 1 0 (by decide +kernel)).trans
    constant_1_part_2_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_2_2 : planeShiftedConstantPart 4 1 2 2 =
    -18306 := by cbv
private theorem constant_1_part_2_3 : planeShiftedConstantPart 4 1 2 3 =
    -18306 := by
  exact (constant_1_marking 2 3 2 (by decide +kernel)).trans
    constant_1_part_2_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_2_4 : planeShiftedConstantPart 4 1 2 4 =
    -18306 := by cbv
private theorem constant_1_part_2_5 : planeShiftedConstantPart 4 1 2 5 =
    -18306 := by
  exact (constant_1_marking 2 5 4 (by decide +kernel)).trans
    constant_1_part_2_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_3_0 : planeShiftedConstantPart 4 1 3 0 =
    0 := by cbv
private theorem constant_1_part_3_1 : planeShiftedConstantPart 4 1 3 1 =
    0 := by
  exact (constant_1_marking 3 1 0 (by decide +kernel)).trans
    constant_1_part_3_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_3_2 : planeShiftedConstantPart 4 1 3 2 =
    0 := by cbv
private theorem constant_1_part_3_3 : planeShiftedConstantPart 4 1 3 3 =
    0 := by
  exact (constant_1_marking 3 3 2 (by decide +kernel)).trans
    constant_1_part_3_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_3_4 : planeShiftedConstantPart 4 1 3 4 =
    0 := by cbv
private theorem constant_1_part_3_5 : planeShiftedConstantPart 4 1 3 5 =
    0 := by
  exact (constant_1_marking 3 5 4 (by decide +kernel)).trans
    constant_1_part_3_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_4_0 : planeShiftedConstantPart 4 1 4 0 =
    1728 := by cbv
private theorem constant_1_part_4_1 : planeShiftedConstantPart 4 1 4 1 =
    1728 := by
  exact (constant_1_marking 4 1 0 (by decide +kernel)).trans
    constant_1_part_4_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_4_2 : planeShiftedConstantPart 4 1 4 2 =
    1728 := by cbv
private theorem constant_1_part_4_3 : planeShiftedConstantPart 4 1 4 3 =
    1728 := by
  exact (constant_1_marking 4 3 2 (by decide +kernel)).trans
    constant_1_part_4_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_4_4 : planeShiftedConstantPart 4 1 4 4 =
    1728 := by cbv
private theorem constant_1_part_4_5 : planeShiftedConstantPart 4 1 4 5 =
    1728 := by
  exact (constant_1_marking 4 5 4 (by decide +kernel)).trans
    constant_1_part_4_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_5_0 : planeShiftedConstantPart 4 1 5 0 =
    0 := by cbv
private theorem constant_1_part_5_1 : planeShiftedConstantPart 4 1 5 1 =
    0 := by
  exact (constant_1_marking 5 1 0 (by decide +kernel)).trans
    constant_1_part_5_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_5_2 : planeShiftedConstantPart 4 1 5 2 =
    0 := by cbv
private theorem constant_1_part_5_3 : planeShiftedConstantPart 4 1 5 3 =
    0 := by
  exact (constant_1_marking 5 3 2 (by decide +kernel)).trans
    constant_1_part_5_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_5_4 : planeShiftedConstantPart 4 1 5 4 =
    0 := by cbv
private theorem constant_1_part_5_5 : planeShiftedConstantPart 4 1 5 5 =
    0 := by
  exact (constant_1_marking 5 5 4 (by decide +kernel)).trans
    constant_1_part_5_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_6_0 : planeShiftedConstantPart 4 1 6 0 =
    3942 := by cbv
private theorem constant_1_part_6_1 : planeShiftedConstantPart 4 1 6 1 =
    3942 := by
  exact (constant_1_marking 6 1 0 (by decide +kernel)).trans
    constant_1_part_6_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_6_2 : planeShiftedConstantPart 4 1 6 2 =
    9153 := by cbv
private theorem constant_1_part_6_3 : planeShiftedConstantPart 4 1 6 3 =
    9153 := by
  exact (constant_1_marking 6 3 2 (by decide +kernel)).trans
    constant_1_part_6_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_6_4 : planeShiftedConstantPart 4 1 6 4 =
    9153 := by cbv
private theorem constant_1_part_6_5 : planeShiftedConstantPart 4 1 6 5 =
    9153 := by
  exact (constant_1_marking 6 5 4 (by decide +kernel)).trans
    constant_1_part_6_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_7_0 : planeShiftedConstantPart 4 1 7 0 =
    (-1361833 / 24) := by cbv
private theorem constant_1_part_7_1 : planeShiftedConstantPart 4 1 7 1 =
    (-1361833 / 24) := by
  exact (constant_1_marking 7 1 0 (by decide +kernel)).trans
    constant_1_part_7_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_7_2 : planeShiftedConstantPart 4 1 7 2 =
    (-1361833 / 24) := by cbv
private theorem constant_1_part_7_3 : planeShiftedConstantPart 4 1 7 3 =
    (-1361833 / 24) := by
  exact (constant_1_marking 7 3 2 (by decide +kernel)).trans
    constant_1_part_7_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_7_4 : planeShiftedConstantPart 4 1 7 4 =
    (-1361833 / 24) := by cbv
private theorem constant_1_part_7_5 : planeShiftedConstantPart 4 1 7 5 =
    (-1361833 / 24) := by
  exact (constant_1_marking 7 5 4 (by decide +kernel)).trans
    constant_1_part_7_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_8_0 : planeShiftedConstantPart 4 1 8 0 =
    -2592 := by cbv
private theorem constant_1_part_8_1 : planeShiftedConstantPart 4 1 8 1 =
    -2592 := by
  exact (constant_1_marking 8 1 0 (by decide +kernel)).trans
    constant_1_part_8_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_8_2 : planeShiftedConstantPart 4 1 8 2 =
    -2592 := by cbv
private theorem constant_1_part_8_3 : planeShiftedConstantPart 4 1 8 3 =
    -2592 := by
  exact (constant_1_marking 8 3 2 (by decide +kernel)).trans
    constant_1_part_8_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_8_4 : planeShiftedConstantPart 4 1 8 4 =
    -1458 := by cbv
private theorem constant_1_part_8_5 : planeShiftedConstantPart 4 1 8 5 =
    -1458 := by
  exact (constant_1_marking 8 5 4 (by decide +kernel)).trans
    constant_1_part_8_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_9_0 : planeShiftedConstantPart 4 1 9 0 =
    (36531 / 5) := by cbv
private theorem constant_1_part_9_1 : planeShiftedConstantPart 4 1 9 1 =
    (36531 / 5) := by
  exact (constant_1_marking 9 1 0 (by decide +kernel)).trans
    constant_1_part_9_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_9_2 : planeShiftedConstantPart 4 1 9 2 =
    5913 := by cbv
private theorem constant_1_part_9_3 : planeShiftedConstantPart 4 1 9 3 =
    5913 := by
  exact (constant_1_marking 9 3 2 (by decide +kernel)).trans
    constant_1_part_9_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_9_4 : planeShiftedConstantPart 4 1 9 4 =
    5913 := by cbv
private theorem constant_1_part_9_5 : planeShiftedConstantPart 4 1 9 5 =
    5913 := by
  exact (constant_1_marking 9 5 4 (by decide +kernel)).trans
    constant_1_part_9_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_10_0 : planeShiftedConstantPart 4 1 10 0 =
    (-66771 / 5) := by cbv
private theorem constant_1_part_10_1 : planeShiftedConstantPart 4 1 10 1 =
    (-66771 / 5) := by
  exact (constant_1_marking 10 1 0 (by decide +kernel)).trans
    constant_1_part_10_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_10_2 : planeShiftedConstantPart 4 1 10 2 =
    (-66771 / 5) := by cbv
private theorem constant_1_part_10_3 : planeShiftedConstantPart 4 1 10 3 =
    (-66771 / 5) := by
  exact (constant_1_marking 10 3 2 (by decide +kernel)).trans
    constant_1_part_10_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_10_4 : planeShiftedConstantPart 4 1 10 4 =
    (-66771 / 5) := by cbv
private theorem constant_1_part_10_5 : planeShiftedConstantPart 4 1 10 5 =
    (-66771 / 5) := by
  exact (constant_1_marking 10 5 4 (by decide +kernel)).trans
    constant_1_part_10_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_11_0 : planeShiftedConstantPart 4 1 11 0 =
    1944 := by cbv
private theorem constant_1_part_11_1 : planeShiftedConstantPart 4 1 11 1 =
    1944 := by
  exact (constant_1_marking 11 1 0 (by decide +kernel)).trans
    constant_1_part_11_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_11_2 : planeShiftedConstantPart 4 1 11 2 =
    1944 := by cbv
private theorem constant_1_part_11_3 : planeShiftedConstantPart 4 1 11 3 =
    1944 := by
  exact (constant_1_marking 11 3 2 (by decide +kernel)).trans
    constant_1_part_11_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_11_4 : planeShiftedConstantPart 4 1 11 4 =
    1944 := by cbv
private theorem constant_1_part_11_5 : planeShiftedConstantPart 4 1 11 5 =
    1944 := by
  exact (constant_1_marking 11 5 4 (by decide +kernel)).trans
    constant_1_part_11_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_12_0 : planeShiftedConstantPart 4 1 12 0 =
    -23652 := by cbv
private theorem constant_1_part_12_1 : planeShiftedConstantPart 4 1 12 1 =
    -23652 := by
  exact (constant_1_marking 12 1 0 (by decide +kernel)).trans
    constant_1_part_12_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_12_2 : planeShiftedConstantPart 4 1 12 2 =
    -23652 := by cbv
private theorem constant_1_part_12_3 : planeShiftedConstantPart 4 1 12 3 =
    -23652 := by
  exact (constant_1_marking 12 3 2 (by decide +kernel)).trans
    constant_1_part_12_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_12_4 : planeShiftedConstantPart 4 1 12 4 =
    -11448 := by cbv
private theorem constant_1_part_12_5 : planeShiftedConstantPart 4 1 12 5 =
    -11448 := by
  exact (constant_1_marking 12 5 4 (by decide +kernel)).trans
    constant_1_part_12_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_13_0 : planeShiftedConstantPart 4 1 13 0 =
    (583272 / 5) := by cbv
private theorem constant_1_part_13_1 : planeShiftedConstantPart 4 1 13 1 =
    (583272 / 5) := by
  exact (constant_1_marking 13 1 0 (by decide +kernel)).trans
    constant_1_part_13_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_13_2 : planeShiftedConstantPart 4 1 13 2 =
    66222 := by cbv
private theorem constant_1_part_13_3 : planeShiftedConstantPart 4 1 13 3 =
    66222 := by
  exact (constant_1_marking 13 3 2 (by decide +kernel)).trans
    constant_1_part_13_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_13_4 : planeShiftedConstantPart 4 1 13 4 =
    66222 := by cbv
private theorem constant_1_part_13_5 : planeShiftedConstantPart 4 1 13 5 =
    66222 := by
  exact (constant_1_marking 13 5 4 (by decide +kernel)).trans
    constant_1_part_13_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_14_0 : planeShiftedConstantPart 4 1 14 0 =
    -1908 := by cbv
private theorem constant_1_part_14_1 : planeShiftedConstantPart 4 1 14 1 =
    -1908 := by
  exact (constant_1_marking 14 1 0 (by decide +kernel)).trans
    constant_1_part_14_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_14_2 : planeShiftedConstantPart 4 1 14 2 =
    -1908 := by cbv
private theorem constant_1_part_14_3 : planeShiftedConstantPart 4 1 14 3 =
    -1908 := by
  exact (constant_1_marking 14 3 2 (by decide +kernel)).trans
    constant_1_part_14_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_14_4 : planeShiftedConstantPart 4 1 14 4 =
    -1908 := by cbv
private theorem constant_1_part_14_5 : planeShiftedConstantPart 4 1 14 5 =
    -1908 := by
  exact (constant_1_marking 14 5 4 (by decide +kernel)).trans
    constant_1_part_14_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_15_0 : planeShiftedConstantPart 4 1 15 0 =
    -4662 := by cbv
private theorem constant_1_part_15_1 : planeShiftedConstantPart 4 1 15 1 =
    -4662 := by
  exact (constant_1_marking 15 1 0 (by decide +kernel)).trans
    constant_1_part_15_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_15_2 : planeShiftedConstantPart 4 1 15 2 =
    -11313 := by cbv
private theorem constant_1_part_15_3 : planeShiftedConstantPart 4 1 15 3 =
    -11313 := by
  exact (constant_1_marking 15 3 2 (by decide +kernel)).trans
    constant_1_part_15_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_1_part_15_4 : planeShiftedConstantPart 4 1 15 4 =
    -11313 := by cbv
private theorem constant_1_part_15_5 : planeShiftedConstantPart 4 1 15 5 =
    -11313 := by
  exact (constant_1_marking 15 5 4 (by decide +kernel)).trans
    constant_1_part_15_4

private theorem constant_1_parts_checked (k : Fin 16) (e : Fin 6) :
    planeShiftedConstantPart 4 1 k e = constant_1_parts k e := by
  fin_cases k <;> fin_cases e
  · exact constant_1_part_0_0
  · exact constant_1_part_0_1
  · exact constant_1_part_0_2
  · exact constant_1_part_0_3
  · exact constant_1_part_0_4
  · exact constant_1_part_0_5
  · exact constant_1_part_1_0
  · exact constant_1_part_1_1
  · exact constant_1_part_1_2
  · exact constant_1_part_1_3
  · exact constant_1_part_1_4
  · exact constant_1_part_1_5
  · exact constant_1_part_2_0
  · exact constant_1_part_2_1
  · exact constant_1_part_2_2
  · exact constant_1_part_2_3
  · exact constant_1_part_2_4
  · exact constant_1_part_2_5
  · exact constant_1_part_3_0
  · exact constant_1_part_3_1
  · exact constant_1_part_3_2
  · exact constant_1_part_3_3
  · exact constant_1_part_3_4
  · exact constant_1_part_3_5
  · exact constant_1_part_4_0
  · exact constant_1_part_4_1
  · exact constant_1_part_4_2
  · exact constant_1_part_4_3
  · exact constant_1_part_4_4
  · exact constant_1_part_4_5
  · exact constant_1_part_5_0
  · exact constant_1_part_5_1
  · exact constant_1_part_5_2
  · exact constant_1_part_5_3
  · exact constant_1_part_5_4
  · exact constant_1_part_5_5
  · exact constant_1_part_6_0
  · exact constant_1_part_6_1
  · exact constant_1_part_6_2
  · exact constant_1_part_6_3
  · exact constant_1_part_6_4
  · exact constant_1_part_6_5
  · exact constant_1_part_7_0
  · exact constant_1_part_7_1
  · exact constant_1_part_7_2
  · exact constant_1_part_7_3
  · exact constant_1_part_7_4
  · exact constant_1_part_7_5
  · exact constant_1_part_8_0
  · exact constant_1_part_8_1
  · exact constant_1_part_8_2
  · exact constant_1_part_8_3
  · exact constant_1_part_8_4
  · exact constant_1_part_8_5
  · exact constant_1_part_9_0
  · exact constant_1_part_9_1
  · exact constant_1_part_9_2
  · exact constant_1_part_9_3
  · exact constant_1_part_9_4
  · exact constant_1_part_9_5
  · exact constant_1_part_10_0
  · exact constant_1_part_10_1
  · exact constant_1_part_10_2
  · exact constant_1_part_10_3
  · exact constant_1_part_10_4
  · exact constant_1_part_10_5
  · exact constant_1_part_11_0
  · exact constant_1_part_11_1
  · exact constant_1_part_11_2
  · exact constant_1_part_11_3
  · exact constant_1_part_11_4
  · exact constant_1_part_11_5
  · exact constant_1_part_12_0
  · exact constant_1_part_12_1
  · exact constant_1_part_12_2
  · exact constant_1_part_12_3
  · exact constant_1_part_12_4
  · exact constant_1_part_12_5
  · exact constant_1_part_13_0
  · exact constant_1_part_13_1
  · exact constant_1_part_13_2
  · exact constant_1_part_13_3
  · exact constant_1_part_13_4
  · exact constant_1_part_13_5
  · exact constant_1_part_14_0
  · exact constant_1_part_14_1
  · exact constant_1_part_14_2
  · exact constant_1_part_14_3
  · exact constant_1_part_14_4
  · exact constant_1_part_14_5
  · exact constant_1_part_15_0
  · exact constant_1_part_15_1
  · exact constant_1_part_15_2
  · exact constant_1_part_15_3
  · exact constant_1_part_15_4
  · exact constant_1_part_15_5

private theorem constant_1 : planeShiftedConstantFast 4 1 =
    (65677 / 2) := by
  rw [planeShiftedConstantFast_eq_sum_parts]
  simp_rw [constant_1_parts_checked]
  decide +kernel

private def coefficient_1_0_1_parts : Fin 4 → Fin 6 → ℚ :=
  ![
    ![0, 0, 0, 0, 0, 0],
    ![4365200, 4365200, 4365200, 4365200, 4365200, 4365200],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0]
  ]

private theorem coefficient_1_0_1_marking (k : Fin 4) (e f : Fin 6)
    (h : (![.hyperplane, .point, .point] : Fin 3 → SurfaceBasisLabel .plane) ∘
      labelPermutation e =
      ![.hyperplane, .point, .point] ∘ labelPermutation f) :
    planeEarlierCoefficientPart 4 1 0 1 k e = planeEarlierCoefficientPart 4 1 0 1 k f := by
  exact planePointCoefficientPart_eq_of_labels 12 5
    ![.hyperplane, .point, .point] (Sum.inr (planeCanonicalQueries 0 1)) k e f h

set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_0_1_part_0_0 : planeEarlierCoefficientPart 4 1 0 1 0 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_0_1_part_0_1 : planeEarlierCoefficientPart 4 1 0 1 0 1 =
    0 := by
  exact (coefficient_1_0_1_marking 0 1 0 (by decide +kernel)).trans
    coefficient_1_0_1_part_0_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_0_1_part_0_2 : planeEarlierCoefficientPart 4 1 0 1 0 2 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_0_1_part_0_3 : planeEarlierCoefficientPart 4 1 0 1 0 3 =
    0 := by
  exact (coefficient_1_0_1_marking 0 3 2 (by decide +kernel)).trans
    coefficient_1_0_1_part_0_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_0_1_part_0_4 : planeEarlierCoefficientPart 4 1 0 1 0 4 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_0_1_part_0_5 : planeEarlierCoefficientPart 4 1 0 1 0 5 =
    0 := by
  exact (coefficient_1_0_1_marking 0 5 4 (by decide +kernel)).trans
    coefficient_1_0_1_part_0_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_0_1_part_1_0 : planeEarlierCoefficientPart 4 1 0 1 1 0 =
    4365200 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_0_1_part_1_1 : planeEarlierCoefficientPart 4 1 0 1 1 1 =
    4365200 := by
  exact (coefficient_1_0_1_marking 1 1 0 (by decide +kernel)).trans
    coefficient_1_0_1_part_1_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_0_1_part_1_2 : planeEarlierCoefficientPart 4 1 0 1 1 2 =
    4365200 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_0_1_part_1_3 : planeEarlierCoefficientPart 4 1 0 1 1 3 =
    4365200 := by
  exact (coefficient_1_0_1_marking 1 3 2 (by decide +kernel)).trans
    coefficient_1_0_1_part_1_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_0_1_part_1_4 : planeEarlierCoefficientPart 4 1 0 1 1 4 =
    4365200 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_0_1_part_1_5 : planeEarlierCoefficientPart 4 1 0 1 1 5 =
    4365200 := by
  exact (coefficient_1_0_1_marking 1 5 4 (by decide +kernel)).trans
    coefficient_1_0_1_part_1_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_0_1_part_2_0 : planeEarlierCoefficientPart 4 1 0 1 2 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_0_1_part_2_1 : planeEarlierCoefficientPart 4 1 0 1 2 1 =
    0 := by
  exact (coefficient_1_0_1_marking 2 1 0 (by decide +kernel)).trans
    coefficient_1_0_1_part_2_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_0_1_part_2_2 : planeEarlierCoefficientPart 4 1 0 1 2 2 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_0_1_part_2_3 : planeEarlierCoefficientPart 4 1 0 1 2 3 =
    0 := by
  exact (coefficient_1_0_1_marking 2 3 2 (by decide +kernel)).trans
    coefficient_1_0_1_part_2_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_0_1_part_2_4 : planeEarlierCoefficientPart 4 1 0 1 2 4 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_0_1_part_2_5 : planeEarlierCoefficientPart 4 1 0 1 2 5 =
    0 := by
  exact (coefficient_1_0_1_marking 2 5 4 (by decide +kernel)).trans
    coefficient_1_0_1_part_2_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_0_1_part_3_0 : planeEarlierCoefficientPart 4 1 0 1 3 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_0_1_part_3_1 : planeEarlierCoefficientPart 4 1 0 1 3 1 =
    0 := by
  exact (coefficient_1_0_1_marking 3 1 0 (by decide +kernel)).trans
    coefficient_1_0_1_part_3_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_0_1_part_3_2 : planeEarlierCoefficientPart 4 1 0 1 3 2 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_0_1_part_3_3 : planeEarlierCoefficientPart 4 1 0 1 3 3 =
    0 := by
  exact (coefficient_1_0_1_marking 3 3 2 (by decide +kernel)).trans
    coefficient_1_0_1_part_3_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_0_1_part_3_4 : planeEarlierCoefficientPart 4 1 0 1 3 4 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_0_1_part_3_5 : planeEarlierCoefficientPart 4 1 0 1 3 5 =
    0 := by
  exact (coefficient_1_0_1_marking 3 5 4 (by decide +kernel)).trans
    coefficient_1_0_1_part_3_4

private theorem coefficient_1_0_1_parts_checked (k : Fin 4) (e : Fin 6) :
    planeEarlierCoefficientPart 4 1 0 1 k e = coefficient_1_0_1_parts k e := by
  fin_cases k <;> fin_cases e
  · exact coefficient_1_0_1_part_0_0
  · exact coefficient_1_0_1_part_0_1
  · exact coefficient_1_0_1_part_0_2
  · exact coefficient_1_0_1_part_0_3
  · exact coefficient_1_0_1_part_0_4
  · exact coefficient_1_0_1_part_0_5
  · exact coefficient_1_0_1_part_1_0
  · exact coefficient_1_0_1_part_1_1
  · exact coefficient_1_0_1_part_1_2
  · exact coefficient_1_0_1_part_1_3
  · exact coefficient_1_0_1_part_1_4
  · exact coefficient_1_0_1_part_1_5
  · exact coefficient_1_0_1_part_2_0
  · exact coefficient_1_0_1_part_2_1
  · exact coefficient_1_0_1_part_2_2
  · exact coefficient_1_0_1_part_2_3
  · exact coefficient_1_0_1_part_2_4
  · exact coefficient_1_0_1_part_2_5
  · exact coefficient_1_0_1_part_3_0
  · exact coefficient_1_0_1_part_3_1
  · exact coefficient_1_0_1_part_3_2
  · exact coefficient_1_0_1_part_3_3
  · exact coefficient_1_0_1_part_3_4
  · exact coefficient_1_0_1_part_3_5

private theorem coefficient_1_0_1 : planeEarlierCoefficient 4 1 0 1 =
    26191200 := by
  rw [planeEarlierCoefficient_eq_sum_parts]
  simp_rw [coefficient_1_0_1_parts_checked]
  decide +kernel

private def coefficient_1_3_1_parts : Fin 4 → Fin 6 → ℚ :=
  ![
    ![0, 0, 0, 0, 0, 0],
    ![1760, 1760, 1760, 1760, 1760, 1760],
    ![3960, 3960, 0, 0, 0, 0],
    ![-3960, -3960, -5940, -5940, -5940, -5940]
  ]

private theorem coefficient_1_3_1_marking (k : Fin 4) (e f : Fin 6)
    (h : (![.hyperplane, .point, .point] : Fin 3 → SurfaceBasisLabel .plane) ∘
      labelPermutation e =
      ![.hyperplane, .point, .point] ∘ labelPermutation f) :
    planeEarlierCoefficientPart 4 1 3 1 k e = planeEarlierCoefficientPart 4 1 3 1 k f := by
  exact planePointCoefficientPart_eq_of_labels 12 5
    ![.hyperplane, .point, .point] (Sum.inr (planeCanonicalQueries 3 1)) k e f h

set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_1_part_0_0 : planeEarlierCoefficientPart 4 1 3 1 0 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_1_part_0_1 : planeEarlierCoefficientPart 4 1 3 1 0 1 =
    0 := by
  exact (coefficient_1_3_1_marking 0 1 0 (by decide +kernel)).trans
    coefficient_1_3_1_part_0_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_1_part_0_2 : planeEarlierCoefficientPart 4 1 3 1 0 2 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_1_part_0_3 : planeEarlierCoefficientPart 4 1 3 1 0 3 =
    0 := by
  exact (coefficient_1_3_1_marking 0 3 2 (by decide +kernel)).trans
    coefficient_1_3_1_part_0_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_1_part_0_4 : planeEarlierCoefficientPart 4 1 3 1 0 4 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_1_part_0_5 : planeEarlierCoefficientPart 4 1 3 1 0 5 =
    0 := by
  exact (coefficient_1_3_1_marking 0 5 4 (by decide +kernel)).trans
    coefficient_1_3_1_part_0_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_1_part_1_0 : planeEarlierCoefficientPart 4 1 3 1 1 0 =
    1760 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_1_part_1_1 : planeEarlierCoefficientPart 4 1 3 1 1 1 =
    1760 := by
  exact (coefficient_1_3_1_marking 1 1 0 (by decide +kernel)).trans
    coefficient_1_3_1_part_1_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_1_part_1_2 : planeEarlierCoefficientPart 4 1 3 1 1 2 =
    1760 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_1_part_1_3 : planeEarlierCoefficientPart 4 1 3 1 1 3 =
    1760 := by
  exact (coefficient_1_3_1_marking 1 3 2 (by decide +kernel)).trans
    coefficient_1_3_1_part_1_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_1_part_1_4 : planeEarlierCoefficientPart 4 1 3 1 1 4 =
    1760 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_1_part_1_5 : planeEarlierCoefficientPart 4 1 3 1 1 5 =
    1760 := by
  exact (coefficient_1_3_1_marking 1 5 4 (by decide +kernel)).trans
    coefficient_1_3_1_part_1_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_1_part_2_0 : planeEarlierCoefficientPart 4 1 3 1 2 0 =
    3960 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_1_part_2_1 : planeEarlierCoefficientPart 4 1 3 1 2 1 =
    3960 := by
  exact (coefficient_1_3_1_marking 2 1 0 (by decide +kernel)).trans
    coefficient_1_3_1_part_2_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_1_part_2_2 : planeEarlierCoefficientPart 4 1 3 1 2 2 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_1_part_2_3 : planeEarlierCoefficientPart 4 1 3 1 2 3 =
    0 := by
  exact (coefficient_1_3_1_marking 2 3 2 (by decide +kernel)).trans
    coefficient_1_3_1_part_2_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_1_part_2_4 : planeEarlierCoefficientPart 4 1 3 1 2 4 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_1_part_2_5 : planeEarlierCoefficientPart 4 1 3 1 2 5 =
    0 := by
  exact (coefficient_1_3_1_marking 2 5 4 (by decide +kernel)).trans
    coefficient_1_3_1_part_2_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_1_part_3_0 : planeEarlierCoefficientPart 4 1 3 1 3 0 =
    -3960 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_1_part_3_1 : planeEarlierCoefficientPart 4 1 3 1 3 1 =
    -3960 := by
  exact (coefficient_1_3_1_marking 3 1 0 (by decide +kernel)).trans
    coefficient_1_3_1_part_3_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_1_part_3_2 : planeEarlierCoefficientPart 4 1 3 1 3 2 =
    -5940 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_1_part_3_3 : planeEarlierCoefficientPart 4 1 3 1 3 3 =
    -5940 := by
  exact (coefficient_1_3_1_marking 3 3 2 (by decide +kernel)).trans
    coefficient_1_3_1_part_3_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_1_part_3_4 : planeEarlierCoefficientPart 4 1 3 1 3 4 =
    -5940 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_1_part_3_5 : planeEarlierCoefficientPart 4 1 3 1 3 5 =
    -5940 := by
  exact (coefficient_1_3_1_marking 3 5 4 (by decide +kernel)).trans
    coefficient_1_3_1_part_3_4

private theorem coefficient_1_3_1_parts_checked (k : Fin 4) (e : Fin 6) :
    planeEarlierCoefficientPart 4 1 3 1 k e = coefficient_1_3_1_parts k e := by
  fin_cases k <;> fin_cases e
  · exact coefficient_1_3_1_part_0_0
  · exact coefficient_1_3_1_part_0_1
  · exact coefficient_1_3_1_part_0_2
  · exact coefficient_1_3_1_part_0_3
  · exact coefficient_1_3_1_part_0_4
  · exact coefficient_1_3_1_part_0_5
  · exact coefficient_1_3_1_part_1_0
  · exact coefficient_1_3_1_part_1_1
  · exact coefficient_1_3_1_part_1_2
  · exact coefficient_1_3_1_part_1_3
  · exact coefficient_1_3_1_part_1_4
  · exact coefficient_1_3_1_part_1_5
  · exact coefficient_1_3_1_part_2_0
  · exact coefficient_1_3_1_part_2_1
  · exact coefficient_1_3_1_part_2_2
  · exact coefficient_1_3_1_part_2_3
  · exact coefficient_1_3_1_part_2_4
  · exact coefficient_1_3_1_part_2_5
  · exact coefficient_1_3_1_part_3_0
  · exact coefficient_1_3_1_part_3_1
  · exact coefficient_1_3_1_part_3_2
  · exact coefficient_1_3_1_part_3_3
  · exact coefficient_1_3_1_part_3_4
  · exact coefficient_1_3_1_part_3_5

private theorem coefficient_1_3_1 : planeEarlierCoefficient 4 1 3 1 =
    -13200 := by
  rw [planeEarlierCoefficient_eq_sum_parts]
  simp_rw [coefficient_1_3_1_parts_checked]
  decide +kernel

private def coefficient_1_3_2_parts : Fin 4 → Fin 6 → ℚ :=
  ![
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 17820, 17820, 17820, 17820],
    ![0, 0, 0, 0, 0, 0]
  ]

private theorem coefficient_1_3_2_marking (k : Fin 4) (e f : Fin 6)
    (h : (![.hyperplane, .point, .point] : Fin 3 → SurfaceBasisLabel .plane) ∘
      labelPermutation e =
      ![.hyperplane, .point, .point] ∘ labelPermutation f) :
    planeEarlierCoefficientPart 4 1 3 2 k e = planeEarlierCoefficientPart 4 1 3 2 k f := by
  exact planePointCoefficientPart_eq_of_labels 12 5
    ![.hyperplane, .point, .point] (Sum.inr (planeCanonicalQueries 3 2)) k e f h

set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_2_part_0_0 : planeEarlierCoefficientPart 4 1 3 2 0 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_2_part_0_1 : planeEarlierCoefficientPart 4 1 3 2 0 1 =
    0 := by
  exact (coefficient_1_3_2_marking 0 1 0 (by decide +kernel)).trans
    coefficient_1_3_2_part_0_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_2_part_0_2 : planeEarlierCoefficientPart 4 1 3 2 0 2 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_2_part_0_3 : planeEarlierCoefficientPart 4 1 3 2 0 3 =
    0 := by
  exact (coefficient_1_3_2_marking 0 3 2 (by decide +kernel)).trans
    coefficient_1_3_2_part_0_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_2_part_0_4 : planeEarlierCoefficientPart 4 1 3 2 0 4 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_2_part_0_5 : planeEarlierCoefficientPart 4 1 3 2 0 5 =
    0 := by
  exact (coefficient_1_3_2_marking 0 5 4 (by decide +kernel)).trans
    coefficient_1_3_2_part_0_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_2_part_1_0 : planeEarlierCoefficientPart 4 1 3 2 1 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_2_part_1_1 : planeEarlierCoefficientPart 4 1 3 2 1 1 =
    0 := by
  exact (coefficient_1_3_2_marking 1 1 0 (by decide +kernel)).trans
    coefficient_1_3_2_part_1_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_2_part_1_2 : planeEarlierCoefficientPart 4 1 3 2 1 2 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_2_part_1_3 : planeEarlierCoefficientPart 4 1 3 2 1 3 =
    0 := by
  exact (coefficient_1_3_2_marking 1 3 2 (by decide +kernel)).trans
    coefficient_1_3_2_part_1_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_2_part_1_4 : planeEarlierCoefficientPart 4 1 3 2 1 4 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_2_part_1_5 : planeEarlierCoefficientPart 4 1 3 2 1 5 =
    0 := by
  exact (coefficient_1_3_2_marking 1 5 4 (by decide +kernel)).trans
    coefficient_1_3_2_part_1_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_2_part_2_0 : planeEarlierCoefficientPart 4 1 3 2 2 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_2_part_2_1 : planeEarlierCoefficientPart 4 1 3 2 2 1 =
    0 := by
  exact (coefficient_1_3_2_marking 2 1 0 (by decide +kernel)).trans
    coefficient_1_3_2_part_2_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_2_part_2_2 : planeEarlierCoefficientPart 4 1 3 2 2 2 =
    17820 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_2_part_2_3 : planeEarlierCoefficientPart 4 1 3 2 2 3 =
    17820 := by
  exact (coefficient_1_3_2_marking 2 3 2 (by decide +kernel)).trans
    coefficient_1_3_2_part_2_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_2_part_2_4 : planeEarlierCoefficientPart 4 1 3 2 2 4 =
    17820 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_2_part_2_5 : planeEarlierCoefficientPart 4 1 3 2 2 5 =
    17820 := by
  exact (coefficient_1_3_2_marking 2 5 4 (by decide +kernel)).trans
    coefficient_1_3_2_part_2_4
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_2_part_3_0 : planeEarlierCoefficientPart 4 1 3 2 3 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_2_part_3_1 : planeEarlierCoefficientPart 4 1 3 2 3 1 =
    0 := by
  exact (coefficient_1_3_2_marking 3 1 0 (by decide +kernel)).trans
    coefficient_1_3_2_part_3_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_2_part_3_2 : planeEarlierCoefficientPart 4 1 3 2 3 2 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_2_part_3_3 : planeEarlierCoefficientPart 4 1 3 2 3 3 =
    0 := by
  exact (coefficient_1_3_2_marking 3 3 2 (by decide +kernel)).trans
    coefficient_1_3_2_part_3_2
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_1_3_2_part_3_4 : planeEarlierCoefficientPart 4 1 3 2 3 4 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_1_3_2_part_3_5 : planeEarlierCoefficientPart 4 1 3 2 3 5 =
    0 := by
  exact (coefficient_1_3_2_marking 3 5 4 (by decide +kernel)).trans
    coefficient_1_3_2_part_3_4

private theorem coefficient_1_3_2_parts_checked (k : Fin 4) (e : Fin 6) :
    planeEarlierCoefficientPart 4 1 3 2 k e = coefficient_1_3_2_parts k e := by
  fin_cases k <;> fin_cases e
  · exact coefficient_1_3_2_part_0_0
  · exact coefficient_1_3_2_part_0_1
  · exact coefficient_1_3_2_part_0_2
  · exact coefficient_1_3_2_part_0_3
  · exact coefficient_1_3_2_part_0_4
  · exact coefficient_1_3_2_part_0_5
  · exact coefficient_1_3_2_part_1_0
  · exact coefficient_1_3_2_part_1_1
  · exact coefficient_1_3_2_part_1_2
  · exact coefficient_1_3_2_part_1_3
  · exact coefficient_1_3_2_part_1_4
  · exact coefficient_1_3_2_part_1_5
  · exact coefficient_1_3_2_part_2_0
  · exact coefficient_1_3_2_part_2_1
  · exact coefficient_1_3_2_part_2_2
  · exact coefficient_1_3_2_part_2_3
  · exact coefficient_1_3_2_part_2_4
  · exact coefficient_1_3_2_part_2_5
  · exact coefficient_1_3_2_part_3_0
  · exact coefficient_1_3_2_part_3_1
  · exact coefficient_1_3_2_part_3_2
  · exact coefficient_1_3_2_part_3_3
  · exact coefficient_1_3_2_part_3_4
  · exact coefficient_1_3_2_part_3_5

private theorem coefficient_1_3_2 : planeEarlierCoefficient 4 1 3 2 =
    71280 := by
  rw [planeEarlierCoefficient_eq_sum_parts]
  simp_rw [coefficient_1_3_2_parts_checked]
  decide +kernel

private def constant_2_parts : Fin 16 → Fin 6 → ℚ :=
  ![
    ![(54301 / 8), (54301 / 8), (54301 / 8), (54301 / 8), (54301 / 8), (54301 / 8)],
    ![432, 432, 432, 432, 432, 432],
    ![-4158, -4158, -4158, -4158, -4158, -4158],
    ![0, 0, 0, 0, 0, 0],
    ![(297 / 2), (297 / 2), (297 / 2), (297 / 2), (297 / 2), (297 / 2)],
    ![0, 0, 0, 0, 0, 0],
    ![(1971 / 2), (1971 / 2), (1971 / 2), (1971 / 2), (1971 / 2), (1971 / 2)],
    ![(-272561 / 24), (-272561 / 24), (-272561 / 24),
      (-272561 / 24), (-272561 / 24), (-272561 / 24)],
    ![(-729 / 2), (-729 / 2), (-729 / 2), (-729 / 2), (-729 / 2), (-729 / 2)],
    ![(2673 / 2), (2673 / 2), (2673 / 2), (2673 / 2), (2673 / 2), (2673 / 2)],
    ![(-26847 / 10), (-26847 / 10), (-26847 / 10), (-26847 / 10), (-26847 / 10), (-26847 / 10)],
    ![198, 198, 198, 198, 198, 198],
    ![-2862, -2862, -2862, -2862, -2862, -2862],
    ![(69336 / 5), (69336 / 5), (69336 / 5), (69336 / 5), (69336 / 5), (69336 / 5)],
    ![(-297 / 2), (-297 / 2), (-297 / 2), (-297 / 2), (-297 / 2), (-297 / 2)],
    ![(-2331 / 2), (-2331 / 2), (-2331 / 2), (-2331 / 2), (-2331 / 2), (-2331 / 2)]
  ]

private theorem constant_2_marking (k : Fin 16) (e f : Fin 6)
    (h : (![.point, .point, .point] : Fin 3 → SurfaceBasisLabel .plane) ∘
      labelPermutation e =
      ![.point, .point, .point] ∘ labelPermutation f) :
    planeShiftedConstantPart 4 2 k e = planeShiftedConstantPart 4 2 k f := by
  exact planePointConstantPart_eq_of_labels 11 ![5]
    ![.point, .point, .point] k e f h

set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_2_part_0_0 : planeShiftedConstantPart 4 2 0 0 =
    (54301 / 8) := by cbv
private theorem constant_2_part_0_1 : planeShiftedConstantPart 4 2 0 1 =
    (54301 / 8) := by
  exact (constant_2_marking 0 1 0 (by decide +kernel)).trans
    constant_2_part_0_0
private theorem constant_2_part_0_2 : planeShiftedConstantPart 4 2 0 2 =
    (54301 / 8) := by
  exact (constant_2_marking 0 2 0 (by decide +kernel)).trans
    constant_2_part_0_0
private theorem constant_2_part_0_3 : planeShiftedConstantPart 4 2 0 3 =
    (54301 / 8) := by
  exact (constant_2_marking 0 3 0 (by decide +kernel)).trans
    constant_2_part_0_0
private theorem constant_2_part_0_4 : planeShiftedConstantPart 4 2 0 4 =
    (54301 / 8) := by
  exact (constant_2_marking 0 4 0 (by decide +kernel)).trans
    constant_2_part_0_0
private theorem constant_2_part_0_5 : planeShiftedConstantPart 4 2 0 5 =
    (54301 / 8) := by
  exact (constant_2_marking 0 5 0 (by decide +kernel)).trans
    constant_2_part_0_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_2_part_1_0 : planeShiftedConstantPart 4 2 1 0 =
    432 := by cbv
private theorem constant_2_part_1_1 : planeShiftedConstantPart 4 2 1 1 =
    432 := by
  exact (constant_2_marking 1 1 0 (by decide +kernel)).trans
    constant_2_part_1_0
private theorem constant_2_part_1_2 : planeShiftedConstantPart 4 2 1 2 =
    432 := by
  exact (constant_2_marking 1 2 0 (by decide +kernel)).trans
    constant_2_part_1_0
private theorem constant_2_part_1_3 : planeShiftedConstantPart 4 2 1 3 =
    432 := by
  exact (constant_2_marking 1 3 0 (by decide +kernel)).trans
    constant_2_part_1_0
private theorem constant_2_part_1_4 : planeShiftedConstantPart 4 2 1 4 =
    432 := by
  exact (constant_2_marking 1 4 0 (by decide +kernel)).trans
    constant_2_part_1_0
private theorem constant_2_part_1_5 : planeShiftedConstantPart 4 2 1 5 =
    432 := by
  exact (constant_2_marking 1 5 0 (by decide +kernel)).trans
    constant_2_part_1_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_2_part_2_0 : planeShiftedConstantPart 4 2 2 0 =
    -4158 := by cbv
private theorem constant_2_part_2_1 : planeShiftedConstantPart 4 2 2 1 =
    -4158 := by
  exact (constant_2_marking 2 1 0 (by decide +kernel)).trans
    constant_2_part_2_0
private theorem constant_2_part_2_2 : planeShiftedConstantPart 4 2 2 2 =
    -4158 := by
  exact (constant_2_marking 2 2 0 (by decide +kernel)).trans
    constant_2_part_2_0
private theorem constant_2_part_2_3 : planeShiftedConstantPart 4 2 2 3 =
    -4158 := by
  exact (constant_2_marking 2 3 0 (by decide +kernel)).trans
    constant_2_part_2_0
private theorem constant_2_part_2_4 : planeShiftedConstantPart 4 2 2 4 =
    -4158 := by
  exact (constant_2_marking 2 4 0 (by decide +kernel)).trans
    constant_2_part_2_0
private theorem constant_2_part_2_5 : planeShiftedConstantPart 4 2 2 5 =
    -4158 := by
  exact (constant_2_marking 2 5 0 (by decide +kernel)).trans
    constant_2_part_2_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_2_part_3_0 : planeShiftedConstantPart 4 2 3 0 =
    0 := by cbv
private theorem constant_2_part_3_1 : planeShiftedConstantPart 4 2 3 1 =
    0 := by
  exact (constant_2_marking 3 1 0 (by decide +kernel)).trans
    constant_2_part_3_0
private theorem constant_2_part_3_2 : planeShiftedConstantPart 4 2 3 2 =
    0 := by
  exact (constant_2_marking 3 2 0 (by decide +kernel)).trans
    constant_2_part_3_0
private theorem constant_2_part_3_3 : planeShiftedConstantPart 4 2 3 3 =
    0 := by
  exact (constant_2_marking 3 3 0 (by decide +kernel)).trans
    constant_2_part_3_0
private theorem constant_2_part_3_4 : planeShiftedConstantPart 4 2 3 4 =
    0 := by
  exact (constant_2_marking 3 4 0 (by decide +kernel)).trans
    constant_2_part_3_0
private theorem constant_2_part_3_5 : planeShiftedConstantPart 4 2 3 5 =
    0 := by
  exact (constant_2_marking 3 5 0 (by decide +kernel)).trans
    constant_2_part_3_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_2_part_4_0 : planeShiftedConstantPart 4 2 4 0 =
    (297 / 2) := by cbv
private theorem constant_2_part_4_1 : planeShiftedConstantPart 4 2 4 1 =
    (297 / 2) := by
  exact (constant_2_marking 4 1 0 (by decide +kernel)).trans
    constant_2_part_4_0
private theorem constant_2_part_4_2 : planeShiftedConstantPart 4 2 4 2 =
    (297 / 2) := by
  exact (constant_2_marking 4 2 0 (by decide +kernel)).trans
    constant_2_part_4_0
private theorem constant_2_part_4_3 : planeShiftedConstantPart 4 2 4 3 =
    (297 / 2) := by
  exact (constant_2_marking 4 3 0 (by decide +kernel)).trans
    constant_2_part_4_0
private theorem constant_2_part_4_4 : planeShiftedConstantPart 4 2 4 4 =
    (297 / 2) := by
  exact (constant_2_marking 4 4 0 (by decide +kernel)).trans
    constant_2_part_4_0
private theorem constant_2_part_4_5 : planeShiftedConstantPart 4 2 4 5 =
    (297 / 2) := by
  exact (constant_2_marking 4 5 0 (by decide +kernel)).trans
    constant_2_part_4_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_2_part_5_0 : planeShiftedConstantPart 4 2 5 0 =
    0 := by cbv
private theorem constant_2_part_5_1 : planeShiftedConstantPart 4 2 5 1 =
    0 := by
  exact (constant_2_marking 5 1 0 (by decide +kernel)).trans
    constant_2_part_5_0
private theorem constant_2_part_5_2 : planeShiftedConstantPart 4 2 5 2 =
    0 := by
  exact (constant_2_marking 5 2 0 (by decide +kernel)).trans
    constant_2_part_5_0
private theorem constant_2_part_5_3 : planeShiftedConstantPart 4 2 5 3 =
    0 := by
  exact (constant_2_marking 5 3 0 (by decide +kernel)).trans
    constant_2_part_5_0
private theorem constant_2_part_5_4 : planeShiftedConstantPart 4 2 5 4 =
    0 := by
  exact (constant_2_marking 5 4 0 (by decide +kernel)).trans
    constant_2_part_5_0
private theorem constant_2_part_5_5 : planeShiftedConstantPart 4 2 5 5 =
    0 := by
  exact (constant_2_marking 5 5 0 (by decide +kernel)).trans
    constant_2_part_5_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_2_part_6_0 : planeShiftedConstantPart 4 2 6 0 =
    (1971 / 2) := by cbv
private theorem constant_2_part_6_1 : planeShiftedConstantPart 4 2 6 1 =
    (1971 / 2) := by
  exact (constant_2_marking 6 1 0 (by decide +kernel)).trans
    constant_2_part_6_0
private theorem constant_2_part_6_2 : planeShiftedConstantPart 4 2 6 2 =
    (1971 / 2) := by
  exact (constant_2_marking 6 2 0 (by decide +kernel)).trans
    constant_2_part_6_0
private theorem constant_2_part_6_3 : planeShiftedConstantPart 4 2 6 3 =
    (1971 / 2) := by
  exact (constant_2_marking 6 3 0 (by decide +kernel)).trans
    constant_2_part_6_0
private theorem constant_2_part_6_4 : planeShiftedConstantPart 4 2 6 4 =
    (1971 / 2) := by
  exact (constant_2_marking 6 4 0 (by decide +kernel)).trans
    constant_2_part_6_0
private theorem constant_2_part_6_5 : planeShiftedConstantPart 4 2 6 5 =
    (1971 / 2) := by
  exact (constant_2_marking 6 5 0 (by decide +kernel)).trans
    constant_2_part_6_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_2_part_7_0 : planeShiftedConstantPart 4 2 7 0 =
    (-272561 / 24) := by cbv
private theorem constant_2_part_7_1 : planeShiftedConstantPart 4 2 7 1 =
    (-272561 / 24) := by
  exact (constant_2_marking 7 1 0 (by decide +kernel)).trans
    constant_2_part_7_0
private theorem constant_2_part_7_2 : planeShiftedConstantPart 4 2 7 2 =
    (-272561 / 24) := by
  exact (constant_2_marking 7 2 0 (by decide +kernel)).trans
    constant_2_part_7_0
private theorem constant_2_part_7_3 : planeShiftedConstantPart 4 2 7 3 =
    (-272561 / 24) := by
  exact (constant_2_marking 7 3 0 (by decide +kernel)).trans
    constant_2_part_7_0
private theorem constant_2_part_7_4 : planeShiftedConstantPart 4 2 7 4 =
    (-272561 / 24) := by
  exact (constant_2_marking 7 4 0 (by decide +kernel)).trans
    constant_2_part_7_0
private theorem constant_2_part_7_5 : planeShiftedConstantPart 4 2 7 5 =
    (-272561 / 24) := by
  exact (constant_2_marking 7 5 0 (by decide +kernel)).trans
    constant_2_part_7_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_2_part_8_0 : planeShiftedConstantPart 4 2 8 0 =
    (-729 / 2) := by cbv
private theorem constant_2_part_8_1 : planeShiftedConstantPart 4 2 8 1 =
    (-729 / 2) := by
  exact (constant_2_marking 8 1 0 (by decide +kernel)).trans
    constant_2_part_8_0
private theorem constant_2_part_8_2 : planeShiftedConstantPart 4 2 8 2 =
    (-729 / 2) := by
  exact (constant_2_marking 8 2 0 (by decide +kernel)).trans
    constant_2_part_8_0
private theorem constant_2_part_8_3 : planeShiftedConstantPart 4 2 8 3 =
    (-729 / 2) := by
  exact (constant_2_marking 8 3 0 (by decide +kernel)).trans
    constant_2_part_8_0
private theorem constant_2_part_8_4 : planeShiftedConstantPart 4 2 8 4 =
    (-729 / 2) := by
  exact (constant_2_marking 8 4 0 (by decide +kernel)).trans
    constant_2_part_8_0
private theorem constant_2_part_8_5 : planeShiftedConstantPart 4 2 8 5 =
    (-729 / 2) := by
  exact (constant_2_marking 8 5 0 (by decide +kernel)).trans
    constant_2_part_8_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_2_part_9_0 : planeShiftedConstantPart 4 2 9 0 =
    (2673 / 2) := by cbv
private theorem constant_2_part_9_1 : planeShiftedConstantPart 4 2 9 1 =
    (2673 / 2) := by
  exact (constant_2_marking 9 1 0 (by decide +kernel)).trans
    constant_2_part_9_0
private theorem constant_2_part_9_2 : planeShiftedConstantPart 4 2 9 2 =
    (2673 / 2) := by
  exact (constant_2_marking 9 2 0 (by decide +kernel)).trans
    constant_2_part_9_0
private theorem constant_2_part_9_3 : planeShiftedConstantPart 4 2 9 3 =
    (2673 / 2) := by
  exact (constant_2_marking 9 3 0 (by decide +kernel)).trans
    constant_2_part_9_0
private theorem constant_2_part_9_4 : planeShiftedConstantPart 4 2 9 4 =
    (2673 / 2) := by
  exact (constant_2_marking 9 4 0 (by decide +kernel)).trans
    constant_2_part_9_0
private theorem constant_2_part_9_5 : planeShiftedConstantPart 4 2 9 5 =
    (2673 / 2) := by
  exact (constant_2_marking 9 5 0 (by decide +kernel)).trans
    constant_2_part_9_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_2_part_10_0 : planeShiftedConstantPart 4 2 10 0 =
    (-26847 / 10) := by cbv
private theorem constant_2_part_10_1 : planeShiftedConstantPart 4 2 10 1 =
    (-26847 / 10) := by
  exact (constant_2_marking 10 1 0 (by decide +kernel)).trans
    constant_2_part_10_0
private theorem constant_2_part_10_2 : planeShiftedConstantPart 4 2 10 2 =
    (-26847 / 10) := by
  exact (constant_2_marking 10 2 0 (by decide +kernel)).trans
    constant_2_part_10_0
private theorem constant_2_part_10_3 : planeShiftedConstantPart 4 2 10 3 =
    (-26847 / 10) := by
  exact (constant_2_marking 10 3 0 (by decide +kernel)).trans
    constant_2_part_10_0
private theorem constant_2_part_10_4 : planeShiftedConstantPart 4 2 10 4 =
    (-26847 / 10) := by
  exact (constant_2_marking 10 4 0 (by decide +kernel)).trans
    constant_2_part_10_0
private theorem constant_2_part_10_5 : planeShiftedConstantPart 4 2 10 5 =
    (-26847 / 10) := by
  exact (constant_2_marking 10 5 0 (by decide +kernel)).trans
    constant_2_part_10_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_2_part_11_0 : planeShiftedConstantPart 4 2 11 0 =
    198 := by cbv
private theorem constant_2_part_11_1 : planeShiftedConstantPart 4 2 11 1 =
    198 := by
  exact (constant_2_marking 11 1 0 (by decide +kernel)).trans
    constant_2_part_11_0
private theorem constant_2_part_11_2 : planeShiftedConstantPart 4 2 11 2 =
    198 := by
  exact (constant_2_marking 11 2 0 (by decide +kernel)).trans
    constant_2_part_11_0
private theorem constant_2_part_11_3 : planeShiftedConstantPart 4 2 11 3 =
    198 := by
  exact (constant_2_marking 11 3 0 (by decide +kernel)).trans
    constant_2_part_11_0
private theorem constant_2_part_11_4 : planeShiftedConstantPart 4 2 11 4 =
    198 := by
  exact (constant_2_marking 11 4 0 (by decide +kernel)).trans
    constant_2_part_11_0
private theorem constant_2_part_11_5 : planeShiftedConstantPart 4 2 11 5 =
    198 := by
  exact (constant_2_marking 11 5 0 (by decide +kernel)).trans
    constant_2_part_11_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_2_part_12_0 : planeShiftedConstantPart 4 2 12 0 =
    -2862 := by cbv
private theorem constant_2_part_12_1 : planeShiftedConstantPart 4 2 12 1 =
    -2862 := by
  exact (constant_2_marking 12 1 0 (by decide +kernel)).trans
    constant_2_part_12_0
private theorem constant_2_part_12_2 : planeShiftedConstantPart 4 2 12 2 =
    -2862 := by
  exact (constant_2_marking 12 2 0 (by decide +kernel)).trans
    constant_2_part_12_0
private theorem constant_2_part_12_3 : planeShiftedConstantPart 4 2 12 3 =
    -2862 := by
  exact (constant_2_marking 12 3 0 (by decide +kernel)).trans
    constant_2_part_12_0
private theorem constant_2_part_12_4 : planeShiftedConstantPart 4 2 12 4 =
    -2862 := by
  exact (constant_2_marking 12 4 0 (by decide +kernel)).trans
    constant_2_part_12_0
private theorem constant_2_part_12_5 : planeShiftedConstantPart 4 2 12 5 =
    -2862 := by
  exact (constant_2_marking 12 5 0 (by decide +kernel)).trans
    constant_2_part_12_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_2_part_13_0 : planeShiftedConstantPart 4 2 13 0 =
    (69336 / 5) := by cbv
private theorem constant_2_part_13_1 : planeShiftedConstantPart 4 2 13 1 =
    (69336 / 5) := by
  exact (constant_2_marking 13 1 0 (by decide +kernel)).trans
    constant_2_part_13_0
private theorem constant_2_part_13_2 : planeShiftedConstantPart 4 2 13 2 =
    (69336 / 5) := by
  exact (constant_2_marking 13 2 0 (by decide +kernel)).trans
    constant_2_part_13_0
private theorem constant_2_part_13_3 : planeShiftedConstantPart 4 2 13 3 =
    (69336 / 5) := by
  exact (constant_2_marking 13 3 0 (by decide +kernel)).trans
    constant_2_part_13_0
private theorem constant_2_part_13_4 : planeShiftedConstantPart 4 2 13 4 =
    (69336 / 5) := by
  exact (constant_2_marking 13 4 0 (by decide +kernel)).trans
    constant_2_part_13_0
private theorem constant_2_part_13_5 : planeShiftedConstantPart 4 2 13 5 =
    (69336 / 5) := by
  exact (constant_2_marking 13 5 0 (by decide +kernel)).trans
    constant_2_part_13_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_2_part_14_0 : planeShiftedConstantPart 4 2 14 0 =
    (-297 / 2) := by cbv
private theorem constant_2_part_14_1 : planeShiftedConstantPart 4 2 14 1 =
    (-297 / 2) := by
  exact (constant_2_marking 14 1 0 (by decide +kernel)).trans
    constant_2_part_14_0
private theorem constant_2_part_14_2 : planeShiftedConstantPart 4 2 14 2 =
    (-297 / 2) := by
  exact (constant_2_marking 14 2 0 (by decide +kernel)).trans
    constant_2_part_14_0
private theorem constant_2_part_14_3 : planeShiftedConstantPart 4 2 14 3 =
    (-297 / 2) := by
  exact (constant_2_marking 14 3 0 (by decide +kernel)).trans
    constant_2_part_14_0
private theorem constant_2_part_14_4 : planeShiftedConstantPart 4 2 14 4 =
    (-297 / 2) := by
  exact (constant_2_marking 14 4 0 (by decide +kernel)).trans
    constant_2_part_14_0
private theorem constant_2_part_14_5 : planeShiftedConstantPart 4 2 14 5 =
    (-297 / 2) := by
  exact (constant_2_marking 14 5 0 (by decide +kernel)).trans
    constant_2_part_14_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem constant_2_part_15_0 : planeShiftedConstantPart 4 2 15 0 =
    (-2331 / 2) := by cbv
private theorem constant_2_part_15_1 : planeShiftedConstantPart 4 2 15 1 =
    (-2331 / 2) := by
  exact (constant_2_marking 15 1 0 (by decide +kernel)).trans
    constant_2_part_15_0
private theorem constant_2_part_15_2 : planeShiftedConstantPart 4 2 15 2 =
    (-2331 / 2) := by
  exact (constant_2_marking 15 2 0 (by decide +kernel)).trans
    constant_2_part_15_0
private theorem constant_2_part_15_3 : planeShiftedConstantPart 4 2 15 3 =
    (-2331 / 2) := by
  exact (constant_2_marking 15 3 0 (by decide +kernel)).trans
    constant_2_part_15_0
private theorem constant_2_part_15_4 : planeShiftedConstantPart 4 2 15 4 =
    (-2331 / 2) := by
  exact (constant_2_marking 15 4 0 (by decide +kernel)).trans
    constant_2_part_15_0
private theorem constant_2_part_15_5 : planeShiftedConstantPart 4 2 15 5 =
    (-2331 / 2) := by
  exact (constant_2_marking 15 5 0 (by decide +kernel)).trans
    constant_2_part_15_0

private theorem constant_2_parts_checked (k : Fin 16) (e : Fin 6) :
    planeShiftedConstantPart 4 2 k e = constant_2_parts k e := by
  fin_cases k <;> fin_cases e
  · exact constant_2_part_0_0
  · exact constant_2_part_0_1
  · exact constant_2_part_0_2
  · exact constant_2_part_0_3
  · exact constant_2_part_0_4
  · exact constant_2_part_0_5
  · exact constant_2_part_1_0
  · exact constant_2_part_1_1
  · exact constant_2_part_1_2
  · exact constant_2_part_1_3
  · exact constant_2_part_1_4
  · exact constant_2_part_1_5
  · exact constant_2_part_2_0
  · exact constant_2_part_2_1
  · exact constant_2_part_2_2
  · exact constant_2_part_2_3
  · exact constant_2_part_2_4
  · exact constant_2_part_2_5
  · exact constant_2_part_3_0
  · exact constant_2_part_3_1
  · exact constant_2_part_3_2
  · exact constant_2_part_3_3
  · exact constant_2_part_3_4
  · exact constant_2_part_3_5
  · exact constant_2_part_4_0
  · exact constant_2_part_4_1
  · exact constant_2_part_4_2
  · exact constant_2_part_4_3
  · exact constant_2_part_4_4
  · exact constant_2_part_4_5
  · exact constant_2_part_5_0
  · exact constant_2_part_5_1
  · exact constant_2_part_5_2
  · exact constant_2_part_5_3
  · exact constant_2_part_5_4
  · exact constant_2_part_5_5
  · exact constant_2_part_6_0
  · exact constant_2_part_6_1
  · exact constant_2_part_6_2
  · exact constant_2_part_6_3
  · exact constant_2_part_6_4
  · exact constant_2_part_6_5
  · exact constant_2_part_7_0
  · exact constant_2_part_7_1
  · exact constant_2_part_7_2
  · exact constant_2_part_7_3
  · exact constant_2_part_7_4
  · exact constant_2_part_7_5
  · exact constant_2_part_8_0
  · exact constant_2_part_8_1
  · exact constant_2_part_8_2
  · exact constant_2_part_8_3
  · exact constant_2_part_8_4
  · exact constant_2_part_8_5
  · exact constant_2_part_9_0
  · exact constant_2_part_9_1
  · exact constant_2_part_9_2
  · exact constant_2_part_9_3
  · exact constant_2_part_9_4
  · exact constant_2_part_9_5
  · exact constant_2_part_10_0
  · exact constant_2_part_10_1
  · exact constant_2_part_10_2
  · exact constant_2_part_10_3
  · exact constant_2_part_10_4
  · exact constant_2_part_10_5
  · exact constant_2_part_11_0
  · exact constant_2_part_11_1
  · exact constant_2_part_11_2
  · exact constant_2_part_11_3
  · exact constant_2_part_11_4
  · exact constant_2_part_11_5
  · exact constant_2_part_12_0
  · exact constant_2_part_12_1
  · exact constant_2_part_12_2
  · exact constant_2_part_12_3
  · exact constant_2_part_12_4
  · exact constant_2_part_12_5
  · exact constant_2_part_13_0
  · exact constant_2_part_13_1
  · exact constant_2_part_13_2
  · exact constant_2_part_13_3
  · exact constant_2_part_13_4
  · exact constant_2_part_13_5
  · exact constant_2_part_14_0
  · exact constant_2_part_14_1
  · exact constant_2_part_14_2
  · exact constant_2_part_14_3
  · exact constant_2_part_14_4
  · exact constant_2_part_14_5
  · exact constant_2_part_15_0
  · exact constant_2_part_15_1
  · exact constant_2_part_15_2
  · exact constant_2_part_15_3
  · exact constant_2_part_15_4
  · exact constant_2_part_15_5

private theorem constant_2 : planeShiftedConstantFast 4 2 =
    (12185 / 2) := by
  rw [planeShiftedConstantFast_eq_sum_parts]
  simp_rw [constant_2_parts_checked]
  decide +kernel

private def coefficient_2_0_1_parts : Fin 4 → Fin 6 → ℚ :=
  ![
    ![0, 0, 0, 0, 0, 0],
    ![873040, 873040, 873040, 873040, 873040, 873040],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0]
  ]

private theorem coefficient_2_0_1_marking (k : Fin 4) (e f : Fin 6)
    (h : (![.point, .point, .point] : Fin 3 → SurfaceBasisLabel .plane) ∘
      labelPermutation e =
      ![.point, .point, .point] ∘ labelPermutation f) :
    planeEarlierCoefficientPart 4 2 0 1 k e = planeEarlierCoefficientPart 4 2 0 1 k f := by
  exact planePointCoefficientPart_eq_of_labels 11 5
    ![.point, .point, .point] (Sum.inr (planeCanonicalQueries 0 1)) k e f h

set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_2_0_1_part_0_0 : planeEarlierCoefficientPart 4 2 0 1 0 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_2_0_1_part_0_1 : planeEarlierCoefficientPart 4 2 0 1 0 1 =
    0 := by
  exact (coefficient_2_0_1_marking 0 1 0 (by decide +kernel)).trans
    coefficient_2_0_1_part_0_0
private theorem coefficient_2_0_1_part_0_2 : planeEarlierCoefficientPart 4 2 0 1 0 2 =
    0 := by
  exact (coefficient_2_0_1_marking 0 2 0 (by decide +kernel)).trans
    coefficient_2_0_1_part_0_0
private theorem coefficient_2_0_1_part_0_3 : planeEarlierCoefficientPart 4 2 0 1 0 3 =
    0 := by
  exact (coefficient_2_0_1_marking 0 3 0 (by decide +kernel)).trans
    coefficient_2_0_1_part_0_0
private theorem coefficient_2_0_1_part_0_4 : planeEarlierCoefficientPart 4 2 0 1 0 4 =
    0 := by
  exact (coefficient_2_0_1_marking 0 4 0 (by decide +kernel)).trans
    coefficient_2_0_1_part_0_0
private theorem coefficient_2_0_1_part_0_5 : planeEarlierCoefficientPart 4 2 0 1 0 5 =
    0 := by
  exact (coefficient_2_0_1_marking 0 5 0 (by decide +kernel)).trans
    coefficient_2_0_1_part_0_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_2_0_1_part_1_0 : planeEarlierCoefficientPart 4 2 0 1 1 0 =
    873040 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_2_0_1_part_1_1 : planeEarlierCoefficientPart 4 2 0 1 1 1 =
    873040 := by
  exact (coefficient_2_0_1_marking 1 1 0 (by decide +kernel)).trans
    coefficient_2_0_1_part_1_0
private theorem coefficient_2_0_1_part_1_2 : planeEarlierCoefficientPart 4 2 0 1 1 2 =
    873040 := by
  exact (coefficient_2_0_1_marking 1 2 0 (by decide +kernel)).trans
    coefficient_2_0_1_part_1_0
private theorem coefficient_2_0_1_part_1_3 : planeEarlierCoefficientPart 4 2 0 1 1 3 =
    873040 := by
  exact (coefficient_2_0_1_marking 1 3 0 (by decide +kernel)).trans
    coefficient_2_0_1_part_1_0
private theorem coefficient_2_0_1_part_1_4 : planeEarlierCoefficientPart 4 2 0 1 1 4 =
    873040 := by
  exact (coefficient_2_0_1_marking 1 4 0 (by decide +kernel)).trans
    coefficient_2_0_1_part_1_0
private theorem coefficient_2_0_1_part_1_5 : planeEarlierCoefficientPart 4 2 0 1 1 5 =
    873040 := by
  exact (coefficient_2_0_1_marking 1 5 0 (by decide +kernel)).trans
    coefficient_2_0_1_part_1_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_2_0_1_part_2_0 : planeEarlierCoefficientPart 4 2 0 1 2 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_2_0_1_part_2_1 : planeEarlierCoefficientPart 4 2 0 1 2 1 =
    0 := by
  exact (coefficient_2_0_1_marking 2 1 0 (by decide +kernel)).trans
    coefficient_2_0_1_part_2_0
private theorem coefficient_2_0_1_part_2_2 : planeEarlierCoefficientPart 4 2 0 1 2 2 =
    0 := by
  exact (coefficient_2_0_1_marking 2 2 0 (by decide +kernel)).trans
    coefficient_2_0_1_part_2_0
private theorem coefficient_2_0_1_part_2_3 : planeEarlierCoefficientPart 4 2 0 1 2 3 =
    0 := by
  exact (coefficient_2_0_1_marking 2 3 0 (by decide +kernel)).trans
    coefficient_2_0_1_part_2_0
private theorem coefficient_2_0_1_part_2_4 : planeEarlierCoefficientPart 4 2 0 1 2 4 =
    0 := by
  exact (coefficient_2_0_1_marking 2 4 0 (by decide +kernel)).trans
    coefficient_2_0_1_part_2_0
private theorem coefficient_2_0_1_part_2_5 : planeEarlierCoefficientPart 4 2 0 1 2 5 =
    0 := by
  exact (coefficient_2_0_1_marking 2 5 0 (by decide +kernel)).trans
    coefficient_2_0_1_part_2_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_2_0_1_part_3_0 : planeEarlierCoefficientPart 4 2 0 1 3 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_2_0_1_part_3_1 : planeEarlierCoefficientPart 4 2 0 1 3 1 =
    0 := by
  exact (coefficient_2_0_1_marking 3 1 0 (by decide +kernel)).trans
    coefficient_2_0_1_part_3_0
private theorem coefficient_2_0_1_part_3_2 : planeEarlierCoefficientPart 4 2 0 1 3 2 =
    0 := by
  exact (coefficient_2_0_1_marking 3 2 0 (by decide +kernel)).trans
    coefficient_2_0_1_part_3_0
private theorem coefficient_2_0_1_part_3_3 : planeEarlierCoefficientPart 4 2 0 1 3 3 =
    0 := by
  exact (coefficient_2_0_1_marking 3 3 0 (by decide +kernel)).trans
    coefficient_2_0_1_part_3_0
private theorem coefficient_2_0_1_part_3_4 : planeEarlierCoefficientPart 4 2 0 1 3 4 =
    0 := by
  exact (coefficient_2_0_1_marking 3 4 0 (by decide +kernel)).trans
    coefficient_2_0_1_part_3_0
private theorem coefficient_2_0_1_part_3_5 : planeEarlierCoefficientPart 4 2 0 1 3 5 =
    0 := by
  exact (coefficient_2_0_1_marking 3 5 0 (by decide +kernel)).trans
    coefficient_2_0_1_part_3_0

private theorem coefficient_2_0_1_parts_checked (k : Fin 4) (e : Fin 6) :
    planeEarlierCoefficientPart 4 2 0 1 k e = coefficient_2_0_1_parts k e := by
  fin_cases k <;> fin_cases e
  · exact coefficient_2_0_1_part_0_0
  · exact coefficient_2_0_1_part_0_1
  · exact coefficient_2_0_1_part_0_2
  · exact coefficient_2_0_1_part_0_3
  · exact coefficient_2_0_1_part_0_4
  · exact coefficient_2_0_1_part_0_5
  · exact coefficient_2_0_1_part_1_0
  · exact coefficient_2_0_1_part_1_1
  · exact coefficient_2_0_1_part_1_2
  · exact coefficient_2_0_1_part_1_3
  · exact coefficient_2_0_1_part_1_4
  · exact coefficient_2_0_1_part_1_5
  · exact coefficient_2_0_1_part_2_0
  · exact coefficient_2_0_1_part_2_1
  · exact coefficient_2_0_1_part_2_2
  · exact coefficient_2_0_1_part_2_3
  · exact coefficient_2_0_1_part_2_4
  · exact coefficient_2_0_1_part_2_5
  · exact coefficient_2_0_1_part_3_0
  · exact coefficient_2_0_1_part_3_1
  · exact coefficient_2_0_1_part_3_2
  · exact coefficient_2_0_1_part_3_3
  · exact coefficient_2_0_1_part_3_4
  · exact coefficient_2_0_1_part_3_5

private theorem coefficient_2_0_1 : planeEarlierCoefficient 4 2 0 1 =
    5238240 := by
  rw [planeEarlierCoefficient_eq_sum_parts]
  simp_rw [coefficient_2_0_1_parts_checked]
  decide +kernel

private def coefficient_2_3_1_parts : Fin 4 → Fin 6 → ℚ :=
  ![
    ![0, 0, 0, 0, 0, 0],
    ![220, 220, 220, 220, 220, 220],
    ![0, 0, 0, 0, 0, 0],
    ![-990, -990, -990, -990, -990, -990]
  ]

private theorem coefficient_2_3_1_marking (k : Fin 4) (e f : Fin 6)
    (h : (![.point, .point, .point] : Fin 3 → SurfaceBasisLabel .plane) ∘
      labelPermutation e =
      ![.point, .point, .point] ∘ labelPermutation f) :
    planeEarlierCoefficientPart 4 2 3 1 k e = planeEarlierCoefficientPart 4 2 3 1 k f := by
  exact planePointCoefficientPart_eq_of_labels 11 5
    ![.point, .point, .point] (Sum.inr (planeCanonicalQueries 3 1)) k e f h

set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_2_3_1_part_0_0 : planeEarlierCoefficientPart 4 2 3 1 0 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_2_3_1_part_0_1 : planeEarlierCoefficientPart 4 2 3 1 0 1 =
    0 := by
  exact (coefficient_2_3_1_marking 0 1 0 (by decide +kernel)).trans
    coefficient_2_3_1_part_0_0
private theorem coefficient_2_3_1_part_0_2 : planeEarlierCoefficientPart 4 2 3 1 0 2 =
    0 := by
  exact (coefficient_2_3_1_marking 0 2 0 (by decide +kernel)).trans
    coefficient_2_3_1_part_0_0
private theorem coefficient_2_3_1_part_0_3 : planeEarlierCoefficientPart 4 2 3 1 0 3 =
    0 := by
  exact (coefficient_2_3_1_marking 0 3 0 (by decide +kernel)).trans
    coefficient_2_3_1_part_0_0
private theorem coefficient_2_3_1_part_0_4 : planeEarlierCoefficientPart 4 2 3 1 0 4 =
    0 := by
  exact (coefficient_2_3_1_marking 0 4 0 (by decide +kernel)).trans
    coefficient_2_3_1_part_0_0
private theorem coefficient_2_3_1_part_0_5 : planeEarlierCoefficientPart 4 2 3 1 0 5 =
    0 := by
  exact (coefficient_2_3_1_marking 0 5 0 (by decide +kernel)).trans
    coefficient_2_3_1_part_0_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_2_3_1_part_1_0 : planeEarlierCoefficientPart 4 2 3 1 1 0 =
    220 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_2_3_1_part_1_1 : planeEarlierCoefficientPart 4 2 3 1 1 1 =
    220 := by
  exact (coefficient_2_3_1_marking 1 1 0 (by decide +kernel)).trans
    coefficient_2_3_1_part_1_0
private theorem coefficient_2_3_1_part_1_2 : planeEarlierCoefficientPart 4 2 3 1 1 2 =
    220 := by
  exact (coefficient_2_3_1_marking 1 2 0 (by decide +kernel)).trans
    coefficient_2_3_1_part_1_0
private theorem coefficient_2_3_1_part_1_3 : planeEarlierCoefficientPart 4 2 3 1 1 3 =
    220 := by
  exact (coefficient_2_3_1_marking 1 3 0 (by decide +kernel)).trans
    coefficient_2_3_1_part_1_0
private theorem coefficient_2_3_1_part_1_4 : planeEarlierCoefficientPart 4 2 3 1 1 4 =
    220 := by
  exact (coefficient_2_3_1_marking 1 4 0 (by decide +kernel)).trans
    coefficient_2_3_1_part_1_0
private theorem coefficient_2_3_1_part_1_5 : planeEarlierCoefficientPart 4 2 3 1 1 5 =
    220 := by
  exact (coefficient_2_3_1_marking 1 5 0 (by decide +kernel)).trans
    coefficient_2_3_1_part_1_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_2_3_1_part_2_0 : planeEarlierCoefficientPart 4 2 3 1 2 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_2_3_1_part_2_1 : planeEarlierCoefficientPart 4 2 3 1 2 1 =
    0 := by
  exact (coefficient_2_3_1_marking 2 1 0 (by decide +kernel)).trans
    coefficient_2_3_1_part_2_0
private theorem coefficient_2_3_1_part_2_2 : planeEarlierCoefficientPart 4 2 3 1 2 2 =
    0 := by
  exact (coefficient_2_3_1_marking 2 2 0 (by decide +kernel)).trans
    coefficient_2_3_1_part_2_0
private theorem coefficient_2_3_1_part_2_3 : planeEarlierCoefficientPart 4 2 3 1 2 3 =
    0 := by
  exact (coefficient_2_3_1_marking 2 3 0 (by decide +kernel)).trans
    coefficient_2_3_1_part_2_0
private theorem coefficient_2_3_1_part_2_4 : planeEarlierCoefficientPart 4 2 3 1 2 4 =
    0 := by
  exact (coefficient_2_3_1_marking 2 4 0 (by decide +kernel)).trans
    coefficient_2_3_1_part_2_0
private theorem coefficient_2_3_1_part_2_5 : planeEarlierCoefficientPart 4 2 3 1 2 5 =
    0 := by
  exact (coefficient_2_3_1_marking 2 5 0 (by decide +kernel)).trans
    coefficient_2_3_1_part_2_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_2_3_1_part_3_0 : planeEarlierCoefficientPart 4 2 3 1 3 0 =
    -990 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_2_3_1_part_3_1 : planeEarlierCoefficientPart 4 2 3 1 3 1 =
    -990 := by
  exact (coefficient_2_3_1_marking 3 1 0 (by decide +kernel)).trans
    coefficient_2_3_1_part_3_0
private theorem coefficient_2_3_1_part_3_2 : planeEarlierCoefficientPart 4 2 3 1 3 2 =
    -990 := by
  exact (coefficient_2_3_1_marking 3 2 0 (by decide +kernel)).trans
    coefficient_2_3_1_part_3_0
private theorem coefficient_2_3_1_part_3_3 : planeEarlierCoefficientPart 4 2 3 1 3 3 =
    -990 := by
  exact (coefficient_2_3_1_marking 3 3 0 (by decide +kernel)).trans
    coefficient_2_3_1_part_3_0
private theorem coefficient_2_3_1_part_3_4 : planeEarlierCoefficientPart 4 2 3 1 3 4 =
    -990 := by
  exact (coefficient_2_3_1_marking 3 4 0 (by decide +kernel)).trans
    coefficient_2_3_1_part_3_0
private theorem coefficient_2_3_1_part_3_5 : planeEarlierCoefficientPart 4 2 3 1 3 5 =
    -990 := by
  exact (coefficient_2_3_1_marking 3 5 0 (by decide +kernel)).trans
    coefficient_2_3_1_part_3_0

private theorem coefficient_2_3_1_parts_checked (k : Fin 4) (e : Fin 6) :
    planeEarlierCoefficientPart 4 2 3 1 k e = coefficient_2_3_1_parts k e := by
  fin_cases k <;> fin_cases e
  · exact coefficient_2_3_1_part_0_0
  · exact coefficient_2_3_1_part_0_1
  · exact coefficient_2_3_1_part_0_2
  · exact coefficient_2_3_1_part_0_3
  · exact coefficient_2_3_1_part_0_4
  · exact coefficient_2_3_1_part_0_5
  · exact coefficient_2_3_1_part_1_0
  · exact coefficient_2_3_1_part_1_1
  · exact coefficient_2_3_1_part_1_2
  · exact coefficient_2_3_1_part_1_3
  · exact coefficient_2_3_1_part_1_4
  · exact coefficient_2_3_1_part_1_5
  · exact coefficient_2_3_1_part_2_0
  · exact coefficient_2_3_1_part_2_1
  · exact coefficient_2_3_1_part_2_2
  · exact coefficient_2_3_1_part_2_3
  · exact coefficient_2_3_1_part_2_4
  · exact coefficient_2_3_1_part_2_5
  · exact coefficient_2_3_1_part_3_0
  · exact coefficient_2_3_1_part_3_1
  · exact coefficient_2_3_1_part_3_2
  · exact coefficient_2_3_1_part_3_3
  · exact coefficient_2_3_1_part_3_4
  · exact coefficient_2_3_1_part_3_5

private theorem coefficient_2_3_1 : planeEarlierCoefficient 4 2 3 1 =
    -4620 := by
  rw [planeEarlierCoefficient_eq_sum_parts]
  simp_rw [coefficient_2_3_1_parts_checked]
  decide +kernel

private def coefficient_2_3_2_parts : Fin 4 → Fin 6 → ℚ :=
  ![
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![2970, 2970, 2970, 2970, 2970, 2970],
    ![0, 0, 0, 0, 0, 0]
  ]

private theorem coefficient_2_3_2_marking (k : Fin 4) (e f : Fin 6)
    (h : (![.point, .point, .point] : Fin 3 → SurfaceBasisLabel .plane) ∘
      labelPermutation e =
      ![.point, .point, .point] ∘ labelPermutation f) :
    planeEarlierCoefficientPart 4 2 3 2 k e = planeEarlierCoefficientPart 4 2 3 2 k f := by
  exact planePointCoefficientPart_eq_of_labels 11 5
    ![.point, .point, .point] (Sum.inr (planeCanonicalQueries 3 2)) k e f h

set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_2_3_2_part_0_0 : planeEarlierCoefficientPart 4 2 3 2 0 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_2_3_2_part_0_1 : planeEarlierCoefficientPart 4 2 3 2 0 1 =
    0 := by
  exact (coefficient_2_3_2_marking 0 1 0 (by decide +kernel)).trans
    coefficient_2_3_2_part_0_0
private theorem coefficient_2_3_2_part_0_2 : planeEarlierCoefficientPart 4 2 3 2 0 2 =
    0 := by
  exact (coefficient_2_3_2_marking 0 2 0 (by decide +kernel)).trans
    coefficient_2_3_2_part_0_0
private theorem coefficient_2_3_2_part_0_3 : planeEarlierCoefficientPart 4 2 3 2 0 3 =
    0 := by
  exact (coefficient_2_3_2_marking 0 3 0 (by decide +kernel)).trans
    coefficient_2_3_2_part_0_0
private theorem coefficient_2_3_2_part_0_4 : planeEarlierCoefficientPart 4 2 3 2 0 4 =
    0 := by
  exact (coefficient_2_3_2_marking 0 4 0 (by decide +kernel)).trans
    coefficient_2_3_2_part_0_0
private theorem coefficient_2_3_2_part_0_5 : planeEarlierCoefficientPart 4 2 3 2 0 5 =
    0 := by
  exact (coefficient_2_3_2_marking 0 5 0 (by decide +kernel)).trans
    coefficient_2_3_2_part_0_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_2_3_2_part_1_0 : planeEarlierCoefficientPart 4 2 3 2 1 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_2_3_2_part_1_1 : planeEarlierCoefficientPart 4 2 3 2 1 1 =
    0 := by
  exact (coefficient_2_3_2_marking 1 1 0 (by decide +kernel)).trans
    coefficient_2_3_2_part_1_0
private theorem coefficient_2_3_2_part_1_2 : planeEarlierCoefficientPart 4 2 3 2 1 2 =
    0 := by
  exact (coefficient_2_3_2_marking 1 2 0 (by decide +kernel)).trans
    coefficient_2_3_2_part_1_0
private theorem coefficient_2_3_2_part_1_3 : planeEarlierCoefficientPart 4 2 3 2 1 3 =
    0 := by
  exact (coefficient_2_3_2_marking 1 3 0 (by decide +kernel)).trans
    coefficient_2_3_2_part_1_0
private theorem coefficient_2_3_2_part_1_4 : planeEarlierCoefficientPart 4 2 3 2 1 4 =
    0 := by
  exact (coefficient_2_3_2_marking 1 4 0 (by decide +kernel)).trans
    coefficient_2_3_2_part_1_0
private theorem coefficient_2_3_2_part_1_5 : planeEarlierCoefficientPart 4 2 3 2 1 5 =
    0 := by
  exact (coefficient_2_3_2_marking 1 5 0 (by decide +kernel)).trans
    coefficient_2_3_2_part_1_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_2_3_2_part_2_0 : planeEarlierCoefficientPart 4 2 3 2 2 0 =
    2970 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_2_3_2_part_2_1 : planeEarlierCoefficientPart 4 2 3 2 2 1 =
    2970 := by
  exact (coefficient_2_3_2_marking 2 1 0 (by decide +kernel)).trans
    coefficient_2_3_2_part_2_0
private theorem coefficient_2_3_2_part_2_2 : planeEarlierCoefficientPart 4 2 3 2 2 2 =
    2970 := by
  exact (coefficient_2_3_2_marking 2 2 0 (by decide +kernel)).trans
    coefficient_2_3_2_part_2_0
private theorem coefficient_2_3_2_part_2_3 : planeEarlierCoefficientPart 4 2 3 2 2 3 =
    2970 := by
  exact (coefficient_2_3_2_marking 2 3 0 (by decide +kernel)).trans
    coefficient_2_3_2_part_2_0
private theorem coefficient_2_3_2_part_2_4 : planeEarlierCoefficientPart 4 2 3 2 2 4 =
    2970 := by
  exact (coefficient_2_3_2_marking 2 4 0 (by decide +kernel)).trans
    coefficient_2_3_2_part_2_0
private theorem coefficient_2_3_2_part_2_5 : planeEarlierCoefficientPart 4 2 3 2 2 5 =
    2970 := by
  exact (coefficient_2_3_2_marking 2 5 0 (by decide +kernel)).trans
    coefficient_2_3_2_part_2_0
set_option maxHeartbeats 1000000 in
-- Kernel replay of one complete finite graph contribution.
set_option cbv.maxSteps 1000000 in
private theorem coefficient_2_3_2_part_3_0 : planeEarlierCoefficientPart 4 2 3 2 3 0 =
    0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  decide +kernel
private theorem coefficient_2_3_2_part_3_1 : planeEarlierCoefficientPart 4 2 3 2 3 1 =
    0 := by
  exact (coefficient_2_3_2_marking 3 1 0 (by decide +kernel)).trans
    coefficient_2_3_2_part_3_0
private theorem coefficient_2_3_2_part_3_2 : planeEarlierCoefficientPart 4 2 3 2 3 2 =
    0 := by
  exact (coefficient_2_3_2_marking 3 2 0 (by decide +kernel)).trans
    coefficient_2_3_2_part_3_0
private theorem coefficient_2_3_2_part_3_3 : planeEarlierCoefficientPart 4 2 3 2 3 3 =
    0 := by
  exact (coefficient_2_3_2_marking 3 3 0 (by decide +kernel)).trans
    coefficient_2_3_2_part_3_0
private theorem coefficient_2_3_2_part_3_4 : planeEarlierCoefficientPart 4 2 3 2 3 4 =
    0 := by
  exact (coefficient_2_3_2_marking 3 4 0 (by decide +kernel)).trans
    coefficient_2_3_2_part_3_0
private theorem coefficient_2_3_2_part_3_5 : planeEarlierCoefficientPart 4 2 3 2 3 5 =
    0 := by
  exact (coefficient_2_3_2_marking 3 5 0 (by decide +kernel)).trans
    coefficient_2_3_2_part_3_0

private theorem coefficient_2_3_2_parts_checked (k : Fin 4) (e : Fin 6) :
    planeEarlierCoefficientPart 4 2 3 2 k e = coefficient_2_3_2_parts k e := by
  fin_cases k <;> fin_cases e
  · exact coefficient_2_3_2_part_0_0
  · exact coefficient_2_3_2_part_0_1
  · exact coefficient_2_3_2_part_0_2
  · exact coefficient_2_3_2_part_0_3
  · exact coefficient_2_3_2_part_0_4
  · exact coefficient_2_3_2_part_0_5
  · exact coefficient_2_3_2_part_1_0
  · exact coefficient_2_3_2_part_1_1
  · exact coefficient_2_3_2_part_1_2
  · exact coefficient_2_3_2_part_1_3
  · exact coefficient_2_3_2_part_1_4
  · exact coefficient_2_3_2_part_1_5
  · exact coefficient_2_3_2_part_2_0
  · exact coefficient_2_3_2_part_2_1
  · exact coefficient_2_3_2_part_2_2
  · exact coefficient_2_3_2_part_2_3
  · exact coefficient_2_3_2_part_2_4
  · exact coefficient_2_3_2_part_2_5
  · exact coefficient_2_3_2_part_3_0
  · exact coefficient_2_3_2_part_3_1
  · exact coefficient_2_3_2_part_3_2
  · exact coefficient_2_3_2_part_3_3
  · exact coefficient_2_3_2_part_3_4
  · exact coefficient_2_3_2_part_3_5

private theorem coefficient_2_3_2 : planeEarlierCoefficient 4 2 3 2 =
    17820 := by
  rw [planeEarlierCoefficient_eq_sum_parts]
  simp_rw [coefficient_2_3_2_parts_checked]
  decide +kernel

/-- All complete constants in HHP/HPP/PPP order. -/
theorem constants (i : Fin 3) :
    planeShiftedConstantFast 4 i = (![(333281 / 2), (65677 / 2), (12185 / 2)] : Fin 3 → ℚ) i := by
  fin_cases i
  · exact constant_0
  · exact constant_1
  · exact constant_2

/-- The full signed coefficient of this nonzero earlier entry. -/
theorem coefficients_0_1 (i : Fin 3) :
    planeEarlierCoefficient 4 i 0 1 =
      (![130956000, 26191200, 5238240] : Fin 3 → ℚ) i := by
  fin_cases i
  · exact coefficient_0_0_1
  · exact coefficient_1_0_1
  · exact coefficient_2_0_1

/-- The full signed coefficient of this nonzero earlier entry. -/
theorem coefficients_3_1 (i : Fin 3) :
    planeEarlierCoefficient 4 i 3 1 =
      (![6864, -13200, -4620] : Fin 3 → ℚ) i := by
  fin_cases i
  · exact coefficient_0_3_1
  · exact coefficient_1_3_1
  · exact coefficient_2_3_1

/-- The full signed coefficient of this nonzero earlier entry. -/
theorem coefficients_3_2 (i : Fin 3) :
    planeEarlierCoefficient 4 i 3 2 =
      (![185328, 71280, 17820] : Fin 3 → ℚ) i := by
  fin_cases i
  · exact coefficient_0_3_2
  · exact coefficient_1_3_2
  · exact coefficient_2_3_2

end AxiomaticGW.GenusTwoPlaneDegree4Scalars

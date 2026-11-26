/-
Generated complete plane genus-two component replay at degree 2.
Input SHA256: 57005f5bcae74824f37f767b60009ff006ba5a25a84ef4c9fac6e0672e07d93c
All original diagrams and six marking assignments are checked, including zeros.
These are candidate computations until this Lean module compiles.
-/
module

public import AxiomaticGW.Surfaces.PlaneGenusTwoScalarParts

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 20000

namespace AxiomaticGW.GenusTwoPlaneDegree2Scalars
open BelorousskiPandharipande

private def constant_0_parts : Fin 16 → Fin 6 → ℚ :=
  ![
    ![(243 / 80), (243 / 80), (243 / 80), (243 / 80), (243 / 80), (243 / 80)],
    ![0, 0, 0, 0, 0, 0],
    ![(-9 / 10), (-9 / 10), (-9 / 10), 0, (-9 / 10), 0],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, (9 / 20), 0, (9 / 20)],
    ![(-243 / 80), (-243 / 80), (-243 / 80), (-243 / 80), (-243 / 80), (-243 / 80)],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![(-9 / 40), (-9 / 40), (-9 / 40), (-9 / 40), (-9 / 40), (-9 / 40)],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![(9 / 5), (9 / 5), (9 / 5), (9 / 10), (9 / 5), (9 / 10)],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, (-9 / 20), 0, (-9 / 20)]
  ]

private theorem constant_0_part_0_0 : planeShiftedConstantPart 2 0 0 0 =
    (243 / 80) := by decide +kernel
private theorem constant_0_part_0_1 : planeShiftedConstantPart 2 0 0 1 =
    (243 / 80) := by decide +kernel
private theorem constant_0_part_0_2 : planeShiftedConstantPart 2 0 0 2 =
    (243 / 80) := by decide +kernel
private theorem constant_0_part_0_3 : planeShiftedConstantPart 2 0 0 3 =
    (243 / 80) := by decide +kernel
private theorem constant_0_part_0_4 : planeShiftedConstantPart 2 0 0 4 =
    (243 / 80) := by decide +kernel
private theorem constant_0_part_0_5 : planeShiftedConstantPart 2 0 0 5 =
    (243 / 80) := by decide +kernel
private theorem constant_0_part_1_0 : planeShiftedConstantPart 2 0 1 0 =
    0 := by decide +kernel
private theorem constant_0_part_1_1 : planeShiftedConstantPart 2 0 1 1 =
    0 := by decide +kernel
private theorem constant_0_part_1_2 : planeShiftedConstantPart 2 0 1 2 =
    0 := by decide +kernel
private theorem constant_0_part_1_3 : planeShiftedConstantPart 2 0 1 3 =
    0 := by decide +kernel
private theorem constant_0_part_1_4 : planeShiftedConstantPart 2 0 1 4 =
    0 := by decide +kernel
private theorem constant_0_part_1_5 : planeShiftedConstantPart 2 0 1 5 =
    0 := by decide +kernel
private theorem constant_0_part_2_0 : planeShiftedConstantPart 2 0 2 0 =
    (-9 / 10) := by decide +kernel
private theorem constant_0_part_2_1 : planeShiftedConstantPart 2 0 2 1 =
    (-9 / 10) := by decide +kernel
private theorem constant_0_part_2_2 : planeShiftedConstantPart 2 0 2 2 =
    (-9 / 10) := by decide +kernel
private theorem constant_0_part_2_3 : planeShiftedConstantPart 2 0 2 3 =
    0 := by decide +kernel
private theorem constant_0_part_2_4 : planeShiftedConstantPart 2 0 2 4 =
    (-9 / 10) := by decide +kernel
private theorem constant_0_part_2_5 : planeShiftedConstantPart 2 0 2 5 =
    0 := by decide +kernel
private theorem constant_0_part_3_0 : planeShiftedConstantPart 2 0 3 0 =
    0 := by decide +kernel
private theorem constant_0_part_3_1 : planeShiftedConstantPart 2 0 3 1 =
    0 := by decide +kernel
private theorem constant_0_part_3_2 : planeShiftedConstantPart 2 0 3 2 =
    0 := by decide +kernel
private theorem constant_0_part_3_3 : planeShiftedConstantPart 2 0 3 3 =
    0 := by decide +kernel
private theorem constant_0_part_3_4 : planeShiftedConstantPart 2 0 3 4 =
    0 := by decide +kernel
private theorem constant_0_part_3_5 : planeShiftedConstantPart 2 0 3 5 =
    0 := by decide +kernel
private theorem constant_0_part_4_0 : planeShiftedConstantPart 2 0 4 0 =
    0 := by decide +kernel
private theorem constant_0_part_4_1 : planeShiftedConstantPart 2 0 4 1 =
    0 := by decide +kernel
private theorem constant_0_part_4_2 : planeShiftedConstantPart 2 0 4 2 =
    0 := by decide +kernel
private theorem constant_0_part_4_3 : planeShiftedConstantPart 2 0 4 3 =
    0 := by decide +kernel
private theorem constant_0_part_4_4 : planeShiftedConstantPart 2 0 4 4 =
    0 := by decide +kernel
private theorem constant_0_part_4_5 : planeShiftedConstantPart 2 0 4 5 =
    0 := by decide +kernel
private theorem constant_0_part_5_0 : planeShiftedConstantPart 2 0 5 0 =
    0 := by decide +kernel
private theorem constant_0_part_5_1 : planeShiftedConstantPart 2 0 5 1 =
    0 := by decide +kernel
private theorem constant_0_part_5_2 : planeShiftedConstantPart 2 0 5 2 =
    0 := by decide +kernel
private theorem constant_0_part_5_3 : planeShiftedConstantPart 2 0 5 3 =
    0 := by decide +kernel
private theorem constant_0_part_5_4 : planeShiftedConstantPart 2 0 5 4 =
    0 := by decide +kernel
private theorem constant_0_part_5_5 : planeShiftedConstantPart 2 0 5 5 =
    0 := by decide +kernel
private theorem constant_0_part_6_0 : planeShiftedConstantPart 2 0 6 0 =
    0 := by decide +kernel
private theorem constant_0_part_6_1 : planeShiftedConstantPart 2 0 6 1 =
    0 := by decide +kernel
private theorem constant_0_part_6_2 : planeShiftedConstantPart 2 0 6 2 =
    0 := by decide +kernel
private theorem constant_0_part_6_3 : planeShiftedConstantPart 2 0 6 3 =
    (9 / 20) := by decide +kernel
private theorem constant_0_part_6_4 : planeShiftedConstantPart 2 0 6 4 =
    0 := by decide +kernel
private theorem constant_0_part_6_5 : planeShiftedConstantPart 2 0 6 5 =
    (9 / 20) := by decide +kernel
private theorem constant_0_part_7_0 : planeShiftedConstantPart 2 0 7 0 =
    (-243 / 80) := by decide +kernel
private theorem constant_0_part_7_1 : planeShiftedConstantPart 2 0 7 1 =
    (-243 / 80) := by decide +kernel
private theorem constant_0_part_7_2 : planeShiftedConstantPart 2 0 7 2 =
    (-243 / 80) := by decide +kernel
private theorem constant_0_part_7_3 : planeShiftedConstantPart 2 0 7 3 =
    (-243 / 80) := by decide +kernel
private theorem constant_0_part_7_4 : planeShiftedConstantPart 2 0 7 4 =
    (-243 / 80) := by decide +kernel
private theorem constant_0_part_7_5 : planeShiftedConstantPart 2 0 7 5 =
    (-243 / 80) := by decide +kernel
private theorem constant_0_part_8_0 : planeShiftedConstantPart 2 0 8 0 =
    0 := by decide +kernel
private theorem constant_0_part_8_1 : planeShiftedConstantPart 2 0 8 1 =
    0 := by decide +kernel
private theorem constant_0_part_8_2 : planeShiftedConstantPart 2 0 8 2 =
    0 := by decide +kernel
private theorem constant_0_part_8_3 : planeShiftedConstantPart 2 0 8 3 =
    0 := by decide +kernel
private theorem constant_0_part_8_4 : planeShiftedConstantPart 2 0 8 4 =
    0 := by decide +kernel
private theorem constant_0_part_8_5 : planeShiftedConstantPart 2 0 8 5 =
    0 := by decide +kernel
private theorem constant_0_part_9_0 : planeShiftedConstantPart 2 0 9 0 =
    0 := by decide +kernel
private theorem constant_0_part_9_1 : planeShiftedConstantPart 2 0 9 1 =
    0 := by decide +kernel
private theorem constant_0_part_9_2 : planeShiftedConstantPart 2 0 9 2 =
    0 := by decide +kernel
private theorem constant_0_part_9_3 : planeShiftedConstantPart 2 0 9 3 =
    0 := by decide +kernel
private theorem constant_0_part_9_4 : planeShiftedConstantPart 2 0 9 4 =
    0 := by decide +kernel
private theorem constant_0_part_9_5 : planeShiftedConstantPart 2 0 9 5 =
    0 := by decide +kernel
private theorem constant_0_part_10_0 : planeShiftedConstantPart 2 0 10 0 =
    (-9 / 40) := by decide +kernel
private theorem constant_0_part_10_1 : planeShiftedConstantPart 2 0 10 1 =
    (-9 / 40) := by decide +kernel
private theorem constant_0_part_10_2 : planeShiftedConstantPart 2 0 10 2 =
    (-9 / 40) := by decide +kernel
private theorem constant_0_part_10_3 : planeShiftedConstantPart 2 0 10 3 =
    (-9 / 40) := by decide +kernel
private theorem constant_0_part_10_4 : planeShiftedConstantPart 2 0 10 4 =
    (-9 / 40) := by decide +kernel
private theorem constant_0_part_10_5 : planeShiftedConstantPart 2 0 10 5 =
    (-9 / 40) := by decide +kernel
private theorem constant_0_part_11_0 : planeShiftedConstantPart 2 0 11 0 =
    0 := by decide +kernel
private theorem constant_0_part_11_1 : planeShiftedConstantPart 2 0 11 1 =
    0 := by decide +kernel
private theorem constant_0_part_11_2 : planeShiftedConstantPart 2 0 11 2 =
    0 := by decide +kernel
private theorem constant_0_part_11_3 : planeShiftedConstantPart 2 0 11 3 =
    0 := by decide +kernel
private theorem constant_0_part_11_4 : planeShiftedConstantPart 2 0 11 4 =
    0 := by decide +kernel
private theorem constant_0_part_11_5 : planeShiftedConstantPart 2 0 11 5 =
    0 := by decide +kernel
private theorem constant_0_part_12_0 : planeShiftedConstantPart 2 0 12 0 =
    0 := by decide +kernel
private theorem constant_0_part_12_1 : planeShiftedConstantPart 2 0 12 1 =
    0 := by decide +kernel
private theorem constant_0_part_12_2 : planeShiftedConstantPart 2 0 12 2 =
    0 := by decide +kernel
private theorem constant_0_part_12_3 : planeShiftedConstantPart 2 0 12 3 =
    0 := by decide +kernel
private theorem constant_0_part_12_4 : planeShiftedConstantPart 2 0 12 4 =
    0 := by decide +kernel
private theorem constant_0_part_12_5 : planeShiftedConstantPart 2 0 12 5 =
    0 := by decide +kernel
private theorem constant_0_part_13_0 : planeShiftedConstantPart 2 0 13 0 =
    (9 / 5) := by decide +kernel
private theorem constant_0_part_13_1 : planeShiftedConstantPart 2 0 13 1 =
    (9 / 5) := by decide +kernel
private theorem constant_0_part_13_2 : planeShiftedConstantPart 2 0 13 2 =
    (9 / 5) := by decide +kernel
private theorem constant_0_part_13_3 : planeShiftedConstantPart 2 0 13 3 =
    (9 / 10) := by decide +kernel
private theorem constant_0_part_13_4 : planeShiftedConstantPart 2 0 13 4 =
    (9 / 5) := by decide +kernel
private theorem constant_0_part_13_5 : planeShiftedConstantPart 2 0 13 5 =
    (9 / 10) := by decide +kernel
private theorem constant_0_part_14_0 : planeShiftedConstantPart 2 0 14 0 =
    0 := by decide +kernel
private theorem constant_0_part_14_1 : planeShiftedConstantPart 2 0 14 1 =
    0 := by decide +kernel
private theorem constant_0_part_14_2 : planeShiftedConstantPart 2 0 14 2 =
    0 := by decide +kernel
private theorem constant_0_part_14_3 : planeShiftedConstantPart 2 0 14 3 =
    0 := by decide +kernel
private theorem constant_0_part_14_4 : planeShiftedConstantPart 2 0 14 4 =
    0 := by decide +kernel
private theorem constant_0_part_14_5 : planeShiftedConstantPart 2 0 14 5 =
    0 := by decide +kernel
private theorem constant_0_part_15_0 : planeShiftedConstantPart 2 0 15 0 =
    0 := by decide +kernel
private theorem constant_0_part_15_1 : planeShiftedConstantPart 2 0 15 1 =
    0 := by decide +kernel
private theorem constant_0_part_15_2 : planeShiftedConstantPart 2 0 15 2 =
    0 := by decide +kernel
private theorem constant_0_part_15_3 : planeShiftedConstantPart 2 0 15 3 =
    (-9 / 20) := by decide +kernel
private theorem constant_0_part_15_4 : planeShiftedConstantPart 2 0 15 4 =
    0 := by decide +kernel
private theorem constant_0_part_15_5 : planeShiftedConstantPart 2 0 15 5 =
    (-9 / 20) := by decide +kernel

private theorem constant_0_parts_checked (k : Fin 16) (e : Fin 6) :
    planeShiftedConstantPart 2 0 k e = constant_0_parts k e := by
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

private theorem constant_0 : planeShiftedConstantFast 2 0 =
    (81 / 20) := by
  rw [planeShiftedConstantFast_eq_sum_parts]
  simp_rw [constant_0_parts_checked]
  decide +kernel

private def coefficient_0_0_1_parts : Fin 4 → Fin 6 → ℚ :=
  ![
    ![0, 0, 0, 0, 0, 0],
    ![648, 648, 648, 648, 648, 648],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0]
  ]

private theorem coefficient_0_0_1_part_0_0 : planeEarlierCoefficientPart 2 0 0 1 0 0 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_0_1 : planeEarlierCoefficientPart 2 0 0 1 0 1 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_0_2 : planeEarlierCoefficientPart 2 0 0 1 0 2 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_0_3 : planeEarlierCoefficientPart 2 0 0 1 0 3 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_0_4 : planeEarlierCoefficientPart 2 0 0 1 0 4 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_0_5 : planeEarlierCoefficientPart 2 0 0 1 0 5 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_1_0 : planeEarlierCoefficientPart 2 0 0 1 1 0 =
    648 := by decide +kernel
private theorem coefficient_0_0_1_part_1_1 : planeEarlierCoefficientPart 2 0 0 1 1 1 =
    648 := by decide +kernel
private theorem coefficient_0_0_1_part_1_2 : planeEarlierCoefficientPart 2 0 0 1 1 2 =
    648 := by decide +kernel
private theorem coefficient_0_0_1_part_1_3 : planeEarlierCoefficientPart 2 0 0 1 1 3 =
    648 := by decide +kernel
private theorem coefficient_0_0_1_part_1_4 : planeEarlierCoefficientPart 2 0 0 1 1 4 =
    648 := by decide +kernel
private theorem coefficient_0_0_1_part_1_5 : planeEarlierCoefficientPart 2 0 0 1 1 5 =
    648 := by decide +kernel
private theorem coefficient_0_0_1_part_2_0 : planeEarlierCoefficientPart 2 0 0 1 2 0 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_2_1 : planeEarlierCoefficientPart 2 0 0 1 2 1 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_2_2 : planeEarlierCoefficientPart 2 0 0 1 2 2 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_2_3 : planeEarlierCoefficientPart 2 0 0 1 2 3 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_2_4 : planeEarlierCoefficientPart 2 0 0 1 2 4 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_2_5 : planeEarlierCoefficientPart 2 0 0 1 2 5 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_3_0 : planeEarlierCoefficientPart 2 0 0 1 3 0 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_3_1 : planeEarlierCoefficientPart 2 0 0 1 3 1 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_3_2 : planeEarlierCoefficientPart 2 0 0 1 3 2 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_3_3 : planeEarlierCoefficientPart 2 0 0 1 3 3 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_3_4 : planeEarlierCoefficientPart 2 0 0 1 3 4 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_3_5 : planeEarlierCoefficientPart 2 0 0 1 3 5 =
    0 := by decide +kernel

private theorem coefficient_0_0_1_parts_checked (k : Fin 4) (e : Fin 6) :
    planeEarlierCoefficientPart 2 0 0 1 k e = coefficient_0_0_1_parts k e := by
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

private theorem coefficient_0_0_1 : planeEarlierCoefficient 2 0 0 1 =
    3888 := by
  rw [planeEarlierCoefficient_eq_sum_parts]
  simp_rw [coefficient_0_0_1_parts_checked]
  decide +kernel

private def constant_1_parts : Fin 16 → Fin 6 → ℚ :=
  ![
    ![(81 / 80), (81 / 80), (81 / 80), (81 / 80), (81 / 80), (81 / 80)],
    ![0, 0, 0, 0, 0, 0],
    ![(-3 / 10), (-3 / 10), 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![(-81 / 80), (-81 / 80), (-81 / 80), (-81 / 80), (-81 / 80), (-81 / 80)],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![(-3 / 40), (-3 / 40), (-3 / 40), (-3 / 40), (-3 / 40), (-3 / 40)],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![(3 / 5), (3 / 5), (3 / 10), (3 / 10), (3 / 10), (3 / 10)],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0]
  ]

private theorem constant_1_part_0_0 : planeShiftedConstantPart 2 1 0 0 =
    (81 / 80) := by decide +kernel
private theorem constant_1_part_0_1 : planeShiftedConstantPart 2 1 0 1 =
    (81 / 80) := by decide +kernel
private theorem constant_1_part_0_2 : planeShiftedConstantPart 2 1 0 2 =
    (81 / 80) := by decide +kernel
private theorem constant_1_part_0_3 : planeShiftedConstantPart 2 1 0 3 =
    (81 / 80) := by decide +kernel
private theorem constant_1_part_0_4 : planeShiftedConstantPart 2 1 0 4 =
    (81 / 80) := by decide +kernel
private theorem constant_1_part_0_5 : planeShiftedConstantPart 2 1 0 5 =
    (81 / 80) := by decide +kernel
private theorem constant_1_part_1_0 : planeShiftedConstantPart 2 1 1 0 =
    0 := by decide +kernel
private theorem constant_1_part_1_1 : planeShiftedConstantPart 2 1 1 1 =
    0 := by decide +kernel
private theorem constant_1_part_1_2 : planeShiftedConstantPart 2 1 1 2 =
    0 := by decide +kernel
private theorem constant_1_part_1_3 : planeShiftedConstantPart 2 1 1 3 =
    0 := by decide +kernel
private theorem constant_1_part_1_4 : planeShiftedConstantPart 2 1 1 4 =
    0 := by decide +kernel
private theorem constant_1_part_1_5 : planeShiftedConstantPart 2 1 1 5 =
    0 := by decide +kernel
private theorem constant_1_part_2_0 : planeShiftedConstantPart 2 1 2 0 =
    (-3 / 10) := by decide +kernel
private theorem constant_1_part_2_1 : planeShiftedConstantPart 2 1 2 1 =
    (-3 / 10) := by decide +kernel
private theorem constant_1_part_2_2 : planeShiftedConstantPart 2 1 2 2 =
    0 := by decide +kernel
private theorem constant_1_part_2_3 : planeShiftedConstantPart 2 1 2 3 =
    0 := by decide +kernel
private theorem constant_1_part_2_4 : planeShiftedConstantPart 2 1 2 4 =
    0 := by decide +kernel
private theorem constant_1_part_2_5 : planeShiftedConstantPart 2 1 2 5 =
    0 := by decide +kernel
private theorem constant_1_part_3_0 : planeShiftedConstantPart 2 1 3 0 =
    0 := by decide +kernel
private theorem constant_1_part_3_1 : planeShiftedConstantPart 2 1 3 1 =
    0 := by decide +kernel
private theorem constant_1_part_3_2 : planeShiftedConstantPart 2 1 3 2 =
    0 := by decide +kernel
private theorem constant_1_part_3_3 : planeShiftedConstantPart 2 1 3 3 =
    0 := by decide +kernel
private theorem constant_1_part_3_4 : planeShiftedConstantPart 2 1 3 4 =
    0 := by decide +kernel
private theorem constant_1_part_3_5 : planeShiftedConstantPart 2 1 3 5 =
    0 := by decide +kernel
private theorem constant_1_part_4_0 : planeShiftedConstantPart 2 1 4 0 =
    0 := by decide +kernel
private theorem constant_1_part_4_1 : planeShiftedConstantPart 2 1 4 1 =
    0 := by decide +kernel
private theorem constant_1_part_4_2 : planeShiftedConstantPart 2 1 4 2 =
    0 := by decide +kernel
private theorem constant_1_part_4_3 : planeShiftedConstantPart 2 1 4 3 =
    0 := by decide +kernel
private theorem constant_1_part_4_4 : planeShiftedConstantPart 2 1 4 4 =
    0 := by decide +kernel
private theorem constant_1_part_4_5 : planeShiftedConstantPart 2 1 4 5 =
    0 := by decide +kernel
private theorem constant_1_part_5_0 : planeShiftedConstantPart 2 1 5 0 =
    0 := by decide +kernel
private theorem constant_1_part_5_1 : planeShiftedConstantPart 2 1 5 1 =
    0 := by decide +kernel
private theorem constant_1_part_5_2 : planeShiftedConstantPart 2 1 5 2 =
    0 := by decide +kernel
private theorem constant_1_part_5_3 : planeShiftedConstantPart 2 1 5 3 =
    0 := by decide +kernel
private theorem constant_1_part_5_4 : planeShiftedConstantPart 2 1 5 4 =
    0 := by decide +kernel
private theorem constant_1_part_5_5 : planeShiftedConstantPart 2 1 5 5 =
    0 := by decide +kernel
private theorem constant_1_part_6_0 : planeShiftedConstantPart 2 1 6 0 =
    0 := by decide +kernel
private theorem constant_1_part_6_1 : planeShiftedConstantPart 2 1 6 1 =
    0 := by decide +kernel
private theorem constant_1_part_6_2 : planeShiftedConstantPart 2 1 6 2 =
    0 := by decide +kernel
private theorem constant_1_part_6_3 : planeShiftedConstantPart 2 1 6 3 =
    0 := by decide +kernel
private theorem constant_1_part_6_4 : planeShiftedConstantPart 2 1 6 4 =
    0 := by decide +kernel
private theorem constant_1_part_6_5 : planeShiftedConstantPart 2 1 6 5 =
    0 := by decide +kernel
private theorem constant_1_part_7_0 : planeShiftedConstantPart 2 1 7 0 =
    (-81 / 80) := by decide +kernel
private theorem constant_1_part_7_1 : planeShiftedConstantPart 2 1 7 1 =
    (-81 / 80) := by decide +kernel
private theorem constant_1_part_7_2 : planeShiftedConstantPart 2 1 7 2 =
    (-81 / 80) := by decide +kernel
private theorem constant_1_part_7_3 : planeShiftedConstantPart 2 1 7 3 =
    (-81 / 80) := by decide +kernel
private theorem constant_1_part_7_4 : planeShiftedConstantPart 2 1 7 4 =
    (-81 / 80) := by decide +kernel
private theorem constant_1_part_7_5 : planeShiftedConstantPart 2 1 7 5 =
    (-81 / 80) := by decide +kernel
private theorem constant_1_part_8_0 : planeShiftedConstantPart 2 1 8 0 =
    0 := by decide +kernel
private theorem constant_1_part_8_1 : planeShiftedConstantPart 2 1 8 1 =
    0 := by decide +kernel
private theorem constant_1_part_8_2 : planeShiftedConstantPart 2 1 8 2 =
    0 := by decide +kernel
private theorem constant_1_part_8_3 : planeShiftedConstantPart 2 1 8 3 =
    0 := by decide +kernel
private theorem constant_1_part_8_4 : planeShiftedConstantPart 2 1 8 4 =
    0 := by decide +kernel
private theorem constant_1_part_8_5 : planeShiftedConstantPart 2 1 8 5 =
    0 := by decide +kernel
private theorem constant_1_part_9_0 : planeShiftedConstantPart 2 1 9 0 =
    0 := by decide +kernel
private theorem constant_1_part_9_1 : planeShiftedConstantPart 2 1 9 1 =
    0 := by decide +kernel
private theorem constant_1_part_9_2 : planeShiftedConstantPart 2 1 9 2 =
    0 := by decide +kernel
private theorem constant_1_part_9_3 : planeShiftedConstantPart 2 1 9 3 =
    0 := by decide +kernel
private theorem constant_1_part_9_4 : planeShiftedConstantPart 2 1 9 4 =
    0 := by decide +kernel
private theorem constant_1_part_9_5 : planeShiftedConstantPart 2 1 9 5 =
    0 := by decide +kernel
private theorem constant_1_part_10_0 : planeShiftedConstantPart 2 1 10 0 =
    (-3 / 40) := by decide +kernel
private theorem constant_1_part_10_1 : planeShiftedConstantPart 2 1 10 1 =
    (-3 / 40) := by decide +kernel
private theorem constant_1_part_10_2 : planeShiftedConstantPart 2 1 10 2 =
    (-3 / 40) := by decide +kernel
private theorem constant_1_part_10_3 : planeShiftedConstantPart 2 1 10 3 =
    (-3 / 40) := by decide +kernel
private theorem constant_1_part_10_4 : planeShiftedConstantPart 2 1 10 4 =
    (-3 / 40) := by decide +kernel
private theorem constant_1_part_10_5 : planeShiftedConstantPart 2 1 10 5 =
    (-3 / 40) := by decide +kernel
private theorem constant_1_part_11_0 : planeShiftedConstantPart 2 1 11 0 =
    0 := by decide +kernel
private theorem constant_1_part_11_1 : planeShiftedConstantPart 2 1 11 1 =
    0 := by decide +kernel
private theorem constant_1_part_11_2 : planeShiftedConstantPart 2 1 11 2 =
    0 := by decide +kernel
private theorem constant_1_part_11_3 : planeShiftedConstantPart 2 1 11 3 =
    0 := by decide +kernel
private theorem constant_1_part_11_4 : planeShiftedConstantPart 2 1 11 4 =
    0 := by decide +kernel
private theorem constant_1_part_11_5 : planeShiftedConstantPart 2 1 11 5 =
    0 := by decide +kernel
private theorem constant_1_part_12_0 : planeShiftedConstantPart 2 1 12 0 =
    0 := by decide +kernel
private theorem constant_1_part_12_1 : planeShiftedConstantPart 2 1 12 1 =
    0 := by decide +kernel
private theorem constant_1_part_12_2 : planeShiftedConstantPart 2 1 12 2 =
    0 := by decide +kernel
private theorem constant_1_part_12_3 : planeShiftedConstantPart 2 1 12 3 =
    0 := by decide +kernel
private theorem constant_1_part_12_4 : planeShiftedConstantPart 2 1 12 4 =
    0 := by decide +kernel
private theorem constant_1_part_12_5 : planeShiftedConstantPart 2 1 12 5 =
    0 := by decide +kernel
private theorem constant_1_part_13_0 : planeShiftedConstantPart 2 1 13 0 =
    (3 / 5) := by decide +kernel
private theorem constant_1_part_13_1 : planeShiftedConstantPart 2 1 13 1 =
    (3 / 5) := by decide +kernel
private theorem constant_1_part_13_2 : planeShiftedConstantPart 2 1 13 2 =
    (3 / 10) := by decide +kernel
private theorem constant_1_part_13_3 : planeShiftedConstantPart 2 1 13 3 =
    (3 / 10) := by decide +kernel
private theorem constant_1_part_13_4 : planeShiftedConstantPart 2 1 13 4 =
    (3 / 10) := by decide +kernel
private theorem constant_1_part_13_5 : planeShiftedConstantPart 2 1 13 5 =
    (3 / 10) := by decide +kernel
private theorem constant_1_part_14_0 : planeShiftedConstantPart 2 1 14 0 =
    0 := by decide +kernel
private theorem constant_1_part_14_1 : planeShiftedConstantPart 2 1 14 1 =
    0 := by decide +kernel
private theorem constant_1_part_14_2 : planeShiftedConstantPart 2 1 14 2 =
    0 := by decide +kernel
private theorem constant_1_part_14_3 : planeShiftedConstantPart 2 1 14 3 =
    0 := by decide +kernel
private theorem constant_1_part_14_4 : planeShiftedConstantPart 2 1 14 4 =
    0 := by decide +kernel
private theorem constant_1_part_14_5 : planeShiftedConstantPart 2 1 14 5 =
    0 := by decide +kernel
private theorem constant_1_part_15_0 : planeShiftedConstantPart 2 1 15 0 =
    0 := by decide +kernel
private theorem constant_1_part_15_1 : planeShiftedConstantPart 2 1 15 1 =
    0 := by decide +kernel
private theorem constant_1_part_15_2 : planeShiftedConstantPart 2 1 15 2 =
    0 := by decide +kernel
private theorem constant_1_part_15_3 : planeShiftedConstantPart 2 1 15 3 =
    0 := by decide +kernel
private theorem constant_1_part_15_4 : planeShiftedConstantPart 2 1 15 4 =
    0 := by decide +kernel
private theorem constant_1_part_15_5 : planeShiftedConstantPart 2 1 15 5 =
    0 := by decide +kernel

private theorem constant_1_parts_checked (k : Fin 16) (e : Fin 6) :
    planeShiftedConstantPart 2 1 k e = constant_1_parts k e := by
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

private theorem constant_1 : planeShiftedConstantFast 2 1 =
    (27 / 20) := by
  rw [planeShiftedConstantFast_eq_sum_parts]
  simp_rw [constant_1_parts_checked]
  decide +kernel

private def coefficient_1_0_1_parts : Fin 4 → Fin 6 → ℚ :=
  ![
    ![0, 0, 0, 0, 0, 0],
    ![216, 216, 216, 216, 216, 216],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0]
  ]

private theorem coefficient_1_0_1_part_0_0 : planeEarlierCoefficientPart 2 1 0 1 0 0 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_0_1 : planeEarlierCoefficientPart 2 1 0 1 0 1 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_0_2 : planeEarlierCoefficientPart 2 1 0 1 0 2 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_0_3 : planeEarlierCoefficientPart 2 1 0 1 0 3 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_0_4 : planeEarlierCoefficientPart 2 1 0 1 0 4 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_0_5 : planeEarlierCoefficientPart 2 1 0 1 0 5 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_1_0 : planeEarlierCoefficientPart 2 1 0 1 1 0 =
    216 := by decide +kernel
private theorem coefficient_1_0_1_part_1_1 : planeEarlierCoefficientPart 2 1 0 1 1 1 =
    216 := by decide +kernel
private theorem coefficient_1_0_1_part_1_2 : planeEarlierCoefficientPart 2 1 0 1 1 2 =
    216 := by decide +kernel
private theorem coefficient_1_0_1_part_1_3 : planeEarlierCoefficientPart 2 1 0 1 1 3 =
    216 := by decide +kernel
private theorem coefficient_1_0_1_part_1_4 : planeEarlierCoefficientPart 2 1 0 1 1 4 =
    216 := by decide +kernel
private theorem coefficient_1_0_1_part_1_5 : planeEarlierCoefficientPart 2 1 0 1 1 5 =
    216 := by decide +kernel
private theorem coefficient_1_0_1_part_2_0 : planeEarlierCoefficientPart 2 1 0 1 2 0 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_2_1 : planeEarlierCoefficientPart 2 1 0 1 2 1 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_2_2 : planeEarlierCoefficientPart 2 1 0 1 2 2 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_2_3 : planeEarlierCoefficientPart 2 1 0 1 2 3 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_2_4 : planeEarlierCoefficientPart 2 1 0 1 2 4 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_2_5 : planeEarlierCoefficientPart 2 1 0 1 2 5 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_3_0 : planeEarlierCoefficientPart 2 1 0 1 3 0 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_3_1 : planeEarlierCoefficientPart 2 1 0 1 3 1 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_3_2 : planeEarlierCoefficientPart 2 1 0 1 3 2 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_3_3 : planeEarlierCoefficientPart 2 1 0 1 3 3 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_3_4 : planeEarlierCoefficientPart 2 1 0 1 3 4 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_3_5 : planeEarlierCoefficientPart 2 1 0 1 3 5 =
    0 := by decide +kernel

private theorem coefficient_1_0_1_parts_checked (k : Fin 4) (e : Fin 6) :
    planeEarlierCoefficientPart 2 1 0 1 k e = coefficient_1_0_1_parts k e := by
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

private theorem coefficient_1_0_1 : planeEarlierCoefficient 2 1 0 1 =
    1296 := by
  rw [planeEarlierCoefficient_eq_sum_parts]
  simp_rw [coefficient_1_0_1_parts_checked]
  decide +kernel

private def constant_2_parts : Fin 16 → Fin 6 → ℚ :=
  ![
    ![(27 / 80), (27 / 80), (27 / 80), (27 / 80), (27 / 80), (27 / 80)],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![(-27 / 80), (-27 / 80), (-27 / 80), (-27 / 80), (-27 / 80), (-27 / 80)],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![(-1 / 40), (-1 / 40), (-1 / 40), (-1 / 40), (-1 / 40), (-1 / 40)],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![(1 / 10), (1 / 10), (1 / 10), (1 / 10), (1 / 10), (1 / 10)],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0]
  ]

private theorem constant_2_part_0_0 : planeShiftedConstantPart 2 2 0 0 =
    (27 / 80) := by decide +kernel
private theorem constant_2_part_0_1 : planeShiftedConstantPart 2 2 0 1 =
    (27 / 80) := by decide +kernel
private theorem constant_2_part_0_2 : planeShiftedConstantPart 2 2 0 2 =
    (27 / 80) := by decide +kernel
private theorem constant_2_part_0_3 : planeShiftedConstantPart 2 2 0 3 =
    (27 / 80) := by decide +kernel
private theorem constant_2_part_0_4 : planeShiftedConstantPart 2 2 0 4 =
    (27 / 80) := by decide +kernel
private theorem constant_2_part_0_5 : planeShiftedConstantPart 2 2 0 5 =
    (27 / 80) := by decide +kernel
private theorem constant_2_part_1_0 : planeShiftedConstantPart 2 2 1 0 =
    0 := by decide +kernel
private theorem constant_2_part_1_1 : planeShiftedConstantPart 2 2 1 1 =
    0 := by decide +kernel
private theorem constant_2_part_1_2 : planeShiftedConstantPart 2 2 1 2 =
    0 := by decide +kernel
private theorem constant_2_part_1_3 : planeShiftedConstantPart 2 2 1 3 =
    0 := by decide +kernel
private theorem constant_2_part_1_4 : planeShiftedConstantPart 2 2 1 4 =
    0 := by decide +kernel
private theorem constant_2_part_1_5 : planeShiftedConstantPart 2 2 1 5 =
    0 := by decide +kernel
private theorem constant_2_part_2_0 : planeShiftedConstantPart 2 2 2 0 =
    0 := by decide +kernel
private theorem constant_2_part_2_1 : planeShiftedConstantPart 2 2 2 1 =
    0 := by decide +kernel
private theorem constant_2_part_2_2 : planeShiftedConstantPart 2 2 2 2 =
    0 := by decide +kernel
private theorem constant_2_part_2_3 : planeShiftedConstantPart 2 2 2 3 =
    0 := by decide +kernel
private theorem constant_2_part_2_4 : planeShiftedConstantPart 2 2 2 4 =
    0 := by decide +kernel
private theorem constant_2_part_2_5 : planeShiftedConstantPart 2 2 2 5 =
    0 := by decide +kernel
private theorem constant_2_part_3_0 : planeShiftedConstantPart 2 2 3 0 =
    0 := by decide +kernel
private theorem constant_2_part_3_1 : planeShiftedConstantPart 2 2 3 1 =
    0 := by decide +kernel
private theorem constant_2_part_3_2 : planeShiftedConstantPart 2 2 3 2 =
    0 := by decide +kernel
private theorem constant_2_part_3_3 : planeShiftedConstantPart 2 2 3 3 =
    0 := by decide +kernel
private theorem constant_2_part_3_4 : planeShiftedConstantPart 2 2 3 4 =
    0 := by decide +kernel
private theorem constant_2_part_3_5 : planeShiftedConstantPart 2 2 3 5 =
    0 := by decide +kernel
private theorem constant_2_part_4_0 : planeShiftedConstantPart 2 2 4 0 =
    0 := by decide +kernel
private theorem constant_2_part_4_1 : planeShiftedConstantPart 2 2 4 1 =
    0 := by decide +kernel
private theorem constant_2_part_4_2 : planeShiftedConstantPart 2 2 4 2 =
    0 := by decide +kernel
private theorem constant_2_part_4_3 : planeShiftedConstantPart 2 2 4 3 =
    0 := by decide +kernel
private theorem constant_2_part_4_4 : planeShiftedConstantPart 2 2 4 4 =
    0 := by decide +kernel
private theorem constant_2_part_4_5 : planeShiftedConstantPart 2 2 4 5 =
    0 := by decide +kernel
private theorem constant_2_part_5_0 : planeShiftedConstantPart 2 2 5 0 =
    0 := by decide +kernel
private theorem constant_2_part_5_1 : planeShiftedConstantPart 2 2 5 1 =
    0 := by decide +kernel
private theorem constant_2_part_5_2 : planeShiftedConstantPart 2 2 5 2 =
    0 := by decide +kernel
private theorem constant_2_part_5_3 : planeShiftedConstantPart 2 2 5 3 =
    0 := by decide +kernel
private theorem constant_2_part_5_4 : planeShiftedConstantPart 2 2 5 4 =
    0 := by decide +kernel
private theorem constant_2_part_5_5 : planeShiftedConstantPart 2 2 5 5 =
    0 := by decide +kernel
private theorem constant_2_part_6_0 : planeShiftedConstantPart 2 2 6 0 =
    0 := by decide +kernel
private theorem constant_2_part_6_1 : planeShiftedConstantPart 2 2 6 1 =
    0 := by decide +kernel
private theorem constant_2_part_6_2 : planeShiftedConstantPart 2 2 6 2 =
    0 := by decide +kernel
private theorem constant_2_part_6_3 : planeShiftedConstantPart 2 2 6 3 =
    0 := by decide +kernel
private theorem constant_2_part_6_4 : planeShiftedConstantPart 2 2 6 4 =
    0 := by decide +kernel
private theorem constant_2_part_6_5 : planeShiftedConstantPart 2 2 6 5 =
    0 := by decide +kernel
private theorem constant_2_part_7_0 : planeShiftedConstantPart 2 2 7 0 =
    (-27 / 80) := by decide +kernel
private theorem constant_2_part_7_1 : planeShiftedConstantPart 2 2 7 1 =
    (-27 / 80) := by decide +kernel
private theorem constant_2_part_7_2 : planeShiftedConstantPart 2 2 7 2 =
    (-27 / 80) := by decide +kernel
private theorem constant_2_part_7_3 : planeShiftedConstantPart 2 2 7 3 =
    (-27 / 80) := by decide +kernel
private theorem constant_2_part_7_4 : planeShiftedConstantPart 2 2 7 4 =
    (-27 / 80) := by decide +kernel
private theorem constant_2_part_7_5 : planeShiftedConstantPart 2 2 7 5 =
    (-27 / 80) := by decide +kernel
private theorem constant_2_part_8_0 : planeShiftedConstantPart 2 2 8 0 =
    0 := by decide +kernel
private theorem constant_2_part_8_1 : planeShiftedConstantPart 2 2 8 1 =
    0 := by decide +kernel
private theorem constant_2_part_8_2 : planeShiftedConstantPart 2 2 8 2 =
    0 := by decide +kernel
private theorem constant_2_part_8_3 : planeShiftedConstantPart 2 2 8 3 =
    0 := by decide +kernel
private theorem constant_2_part_8_4 : planeShiftedConstantPart 2 2 8 4 =
    0 := by decide +kernel
private theorem constant_2_part_8_5 : planeShiftedConstantPart 2 2 8 5 =
    0 := by decide +kernel
private theorem constant_2_part_9_0 : planeShiftedConstantPart 2 2 9 0 =
    0 := by decide +kernel
private theorem constant_2_part_9_1 : planeShiftedConstantPart 2 2 9 1 =
    0 := by decide +kernel
private theorem constant_2_part_9_2 : planeShiftedConstantPart 2 2 9 2 =
    0 := by decide +kernel
private theorem constant_2_part_9_3 : planeShiftedConstantPart 2 2 9 3 =
    0 := by decide +kernel
private theorem constant_2_part_9_4 : planeShiftedConstantPart 2 2 9 4 =
    0 := by decide +kernel
private theorem constant_2_part_9_5 : planeShiftedConstantPart 2 2 9 5 =
    0 := by decide +kernel
private theorem constant_2_part_10_0 : planeShiftedConstantPart 2 2 10 0 =
    (-1 / 40) := by decide +kernel
private theorem constant_2_part_10_1 : planeShiftedConstantPart 2 2 10 1 =
    (-1 / 40) := by decide +kernel
private theorem constant_2_part_10_2 : planeShiftedConstantPart 2 2 10 2 =
    (-1 / 40) := by decide +kernel
private theorem constant_2_part_10_3 : planeShiftedConstantPart 2 2 10 3 =
    (-1 / 40) := by decide +kernel
private theorem constant_2_part_10_4 : planeShiftedConstantPart 2 2 10 4 =
    (-1 / 40) := by decide +kernel
private theorem constant_2_part_10_5 : planeShiftedConstantPart 2 2 10 5 =
    (-1 / 40) := by decide +kernel
private theorem constant_2_part_11_0 : planeShiftedConstantPart 2 2 11 0 =
    0 := by decide +kernel
private theorem constant_2_part_11_1 : planeShiftedConstantPart 2 2 11 1 =
    0 := by decide +kernel
private theorem constant_2_part_11_2 : planeShiftedConstantPart 2 2 11 2 =
    0 := by decide +kernel
private theorem constant_2_part_11_3 : planeShiftedConstantPart 2 2 11 3 =
    0 := by decide +kernel
private theorem constant_2_part_11_4 : planeShiftedConstantPart 2 2 11 4 =
    0 := by decide +kernel
private theorem constant_2_part_11_5 : planeShiftedConstantPart 2 2 11 5 =
    0 := by decide +kernel
private theorem constant_2_part_12_0 : planeShiftedConstantPart 2 2 12 0 =
    0 := by decide +kernel
private theorem constant_2_part_12_1 : planeShiftedConstantPart 2 2 12 1 =
    0 := by decide +kernel
private theorem constant_2_part_12_2 : planeShiftedConstantPart 2 2 12 2 =
    0 := by decide +kernel
private theorem constant_2_part_12_3 : planeShiftedConstantPart 2 2 12 3 =
    0 := by decide +kernel
private theorem constant_2_part_12_4 : planeShiftedConstantPart 2 2 12 4 =
    0 := by decide +kernel
private theorem constant_2_part_12_5 : planeShiftedConstantPart 2 2 12 5 =
    0 := by decide +kernel
private theorem constant_2_part_13_0 : planeShiftedConstantPart 2 2 13 0 =
    (1 / 10) := by decide +kernel
private theorem constant_2_part_13_1 : planeShiftedConstantPart 2 2 13 1 =
    (1 / 10) := by decide +kernel
private theorem constant_2_part_13_2 : planeShiftedConstantPart 2 2 13 2 =
    (1 / 10) := by decide +kernel
private theorem constant_2_part_13_3 : planeShiftedConstantPart 2 2 13 3 =
    (1 / 10) := by decide +kernel
private theorem constant_2_part_13_4 : planeShiftedConstantPart 2 2 13 4 =
    (1 / 10) := by decide +kernel
private theorem constant_2_part_13_5 : planeShiftedConstantPart 2 2 13 5 =
    (1 / 10) := by decide +kernel
private theorem constant_2_part_14_0 : planeShiftedConstantPart 2 2 14 0 =
    0 := by decide +kernel
private theorem constant_2_part_14_1 : planeShiftedConstantPart 2 2 14 1 =
    0 := by decide +kernel
private theorem constant_2_part_14_2 : planeShiftedConstantPart 2 2 14 2 =
    0 := by decide +kernel
private theorem constant_2_part_14_3 : planeShiftedConstantPart 2 2 14 3 =
    0 := by decide +kernel
private theorem constant_2_part_14_4 : planeShiftedConstantPart 2 2 14 4 =
    0 := by decide +kernel
private theorem constant_2_part_14_5 : planeShiftedConstantPart 2 2 14 5 =
    0 := by decide +kernel
private theorem constant_2_part_15_0 : planeShiftedConstantPart 2 2 15 0 =
    0 := by decide +kernel
private theorem constant_2_part_15_1 : planeShiftedConstantPart 2 2 15 1 =
    0 := by decide +kernel
private theorem constant_2_part_15_2 : planeShiftedConstantPart 2 2 15 2 =
    0 := by decide +kernel
private theorem constant_2_part_15_3 : planeShiftedConstantPart 2 2 15 3 =
    0 := by decide +kernel
private theorem constant_2_part_15_4 : planeShiftedConstantPart 2 2 15 4 =
    0 := by decide +kernel
private theorem constant_2_part_15_5 : planeShiftedConstantPart 2 2 15 5 =
    0 := by decide +kernel

private theorem constant_2_parts_checked (k : Fin 16) (e : Fin 6) :
    planeShiftedConstantPart 2 2 k e = constant_2_parts k e := by
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

private theorem constant_2 : planeShiftedConstantFast 2 2 =
    (9 / 20) := by
  rw [planeShiftedConstantFast_eq_sum_parts]
  simp_rw [constant_2_parts_checked]
  decide +kernel

private def coefficient_2_0_1_parts : Fin 4 → Fin 6 → ℚ :=
  ![
    ![0, 0, 0, 0, 0, 0],
    ![72, 72, 72, 72, 72, 72],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0]
  ]

private theorem coefficient_2_0_1_part_0_0 : planeEarlierCoefficientPart 2 2 0 1 0 0 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_0_1 : planeEarlierCoefficientPart 2 2 0 1 0 1 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_0_2 : planeEarlierCoefficientPart 2 2 0 1 0 2 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_0_3 : planeEarlierCoefficientPart 2 2 0 1 0 3 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_0_4 : planeEarlierCoefficientPart 2 2 0 1 0 4 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_0_5 : planeEarlierCoefficientPart 2 2 0 1 0 5 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_1_0 : planeEarlierCoefficientPart 2 2 0 1 1 0 =
    72 := by decide +kernel
private theorem coefficient_2_0_1_part_1_1 : planeEarlierCoefficientPart 2 2 0 1 1 1 =
    72 := by decide +kernel
private theorem coefficient_2_0_1_part_1_2 : planeEarlierCoefficientPart 2 2 0 1 1 2 =
    72 := by decide +kernel
private theorem coefficient_2_0_1_part_1_3 : planeEarlierCoefficientPart 2 2 0 1 1 3 =
    72 := by decide +kernel
private theorem coefficient_2_0_1_part_1_4 : planeEarlierCoefficientPart 2 2 0 1 1 4 =
    72 := by decide +kernel
private theorem coefficient_2_0_1_part_1_5 : planeEarlierCoefficientPart 2 2 0 1 1 5 =
    72 := by decide +kernel
private theorem coefficient_2_0_1_part_2_0 : planeEarlierCoefficientPart 2 2 0 1 2 0 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_2_1 : planeEarlierCoefficientPart 2 2 0 1 2 1 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_2_2 : planeEarlierCoefficientPart 2 2 0 1 2 2 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_2_3 : planeEarlierCoefficientPart 2 2 0 1 2 3 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_2_4 : planeEarlierCoefficientPart 2 2 0 1 2 4 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_2_5 : planeEarlierCoefficientPart 2 2 0 1 2 5 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_3_0 : planeEarlierCoefficientPart 2 2 0 1 3 0 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_3_1 : planeEarlierCoefficientPart 2 2 0 1 3 1 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_3_2 : planeEarlierCoefficientPart 2 2 0 1 3 2 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_3_3 : planeEarlierCoefficientPart 2 2 0 1 3 3 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_3_4 : planeEarlierCoefficientPart 2 2 0 1 3 4 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_3_5 : planeEarlierCoefficientPart 2 2 0 1 3 5 =
    0 := by decide +kernel

private theorem coefficient_2_0_1_parts_checked (k : Fin 4) (e : Fin 6) :
    planeEarlierCoefficientPart 2 2 0 1 k e = coefficient_2_0_1_parts k e := by
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

private theorem coefficient_2_0_1 : planeEarlierCoefficient 2 2 0 1 =
    432 := by
  rw [planeEarlierCoefficient_eq_sum_parts]
  simp_rw [coefficient_2_0_1_parts_checked]
  decide +kernel

/-- All complete constants in HHP/HPP/PPP order. -/
theorem constants (i : Fin 3) :
    planeShiftedConstantFast 2 i = (![(81 / 20), (27 / 20), (9 / 20)] : Fin 3 → ℚ) i := by
  fin_cases i
  · exact constant_0
  · exact constant_1
  · exact constant_2

/-- The full signed coefficient of this nonzero earlier entry. -/
theorem coefficients_0_1 (i : Fin 3) :
    planeEarlierCoefficient 2 i 0 1 =
      (![3888, 1296, 432] : Fin 3 → ℚ) i := by
  fin_cases i
  · exact coefficient_0_0_1
  · exact coefficient_1_0_1
  · exact coefficient_2_0_1

end AxiomaticGW.GenusTwoPlaneDegree2Scalars

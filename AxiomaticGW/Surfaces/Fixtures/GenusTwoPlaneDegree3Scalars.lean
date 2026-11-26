/-
Generated complete plane genus-two component replay at degree 3.
Input SHA256: 57005f5bcae74824f37f767b60009ff006ba5a25a84ef4c9fac6e0672e07d93c
All original diagrams and six marking assignments are checked, including zeros.
These are candidate computations until this Lean module compiles.
-/
module

public import AxiomaticGW.Surfaces.PlaneGenusTwoScalarParts

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 20000

namespace AxiomaticGW.GenusTwoPlaneDegree3Scalars
open BelorousskiPandharipande

private def constant_0_parts : Fin 16 → Fin 6 → ℚ :=
  ![
    ![(989 / 2), (989 / 2), (989 / 2), (989 / 2), (989 / 2), (989 / 2)],
    ![(81 / 4), (27 / 2), (81 / 4), (27 / 2), (27 / 2), (27 / 2)],
    ![(-783 / 2), (-783 / 2), (-783 / 2), -81, (-783 / 2), -81],
    ![0, 0, 0, 0, 0, 0],
    ![(27 / 2), (27 / 2), (27 / 2), (27 / 2), (27 / 2), (27 / 2)],
    ![0, 0, 0, 0, 0, 0],
    ![(81 / 2), (81 / 2), (81 / 2), (783 / 4), (81 / 2), (783 / 4)],
    ![(-7933 / 12), (-7933 / 12), (-7933 / 12), (-7933 / 12), (-7933 / 12), (-7933 / 12)],
    ![(-81 / 8), (-27 / 4), (-81 / 8), (-27 / 4), (-27 / 4), (-27 / 4)],
    ![(243 / 8), (243 / 8), (243 / 8), (81 / 4), (243 / 8), (81 / 4)],
    ![(-801 / 8), (-801 / 8), (-801 / 8), (-801 / 8), (-801 / 8), (-801 / 8)],
    ![9, 9, 9, 9, 9, 9],
    ![(-243 / 2), -81, (-243 / 2), -81, -81, -81],
    ![(1683 / 2), (1683 / 2), (1683 / 2), 441, (1683 / 2), 441],
    ![(-27 / 2), (-27 / 2), (-27 / 2), (-27 / 2), (-27 / 2), (-27 / 2)],
    ![(-81 / 2), (-81 / 2), (-81 / 2), (-963 / 4), (-81 / 2), (-963 / 4)]
  ]

private theorem constant_0_part_0_0 : planeShiftedConstantPart 3 0 0 0 =
    (989 / 2) := by decide +kernel
private theorem constant_0_part_0_1 : planeShiftedConstantPart 3 0 0 1 =
    (989 / 2) := by decide +kernel
private theorem constant_0_part_0_2 : planeShiftedConstantPart 3 0 0 2 =
    (989 / 2) := by decide +kernel
private theorem constant_0_part_0_3 : planeShiftedConstantPart 3 0 0 3 =
    (989 / 2) := by decide +kernel
private theorem constant_0_part_0_4 : planeShiftedConstantPart 3 0 0 4 =
    (989 / 2) := by decide +kernel
private theorem constant_0_part_0_5 : planeShiftedConstantPart 3 0 0 5 =
    (989 / 2) := by decide +kernel
private theorem constant_0_part_1_0 : planeShiftedConstantPart 3 0 1 0 =
    (81 / 4) := by decide +kernel
private theorem constant_0_part_1_1 : planeShiftedConstantPart 3 0 1 1 =
    (27 / 2) := by decide +kernel
private theorem constant_0_part_1_2 : planeShiftedConstantPart 3 0 1 2 =
    (81 / 4) := by decide +kernel
private theorem constant_0_part_1_3 : planeShiftedConstantPart 3 0 1 3 =
    (27 / 2) := by decide +kernel
private theorem constant_0_part_1_4 : planeShiftedConstantPart 3 0 1 4 =
    (27 / 2) := by decide +kernel
private theorem constant_0_part_1_5 : planeShiftedConstantPart 3 0 1 5 =
    (27 / 2) := by decide +kernel
private theorem constant_0_part_2_0 : planeShiftedConstantPart 3 0 2 0 =
    (-783 / 2) := by decide +kernel
private theorem constant_0_part_2_1 : planeShiftedConstantPart 3 0 2 1 =
    (-783 / 2) := by decide +kernel
private theorem constant_0_part_2_2 : planeShiftedConstantPart 3 0 2 2 =
    (-783 / 2) := by decide +kernel
private theorem constant_0_part_2_3 : planeShiftedConstantPart 3 0 2 3 =
    -81 := by decide +kernel
private theorem constant_0_part_2_4 : planeShiftedConstantPart 3 0 2 4 =
    (-783 / 2) := by decide +kernel
private theorem constant_0_part_2_5 : planeShiftedConstantPart 3 0 2 5 =
    -81 := by decide +kernel
private theorem constant_0_part_3_0 : planeShiftedConstantPart 3 0 3 0 =
    0 := by decide +kernel
private theorem constant_0_part_3_1 : planeShiftedConstantPart 3 0 3 1 =
    0 := by decide +kernel
private theorem constant_0_part_3_2 : planeShiftedConstantPart 3 0 3 2 =
    0 := by decide +kernel
private theorem constant_0_part_3_3 : planeShiftedConstantPart 3 0 3 3 =
    0 := by decide +kernel
private theorem constant_0_part_3_4 : planeShiftedConstantPart 3 0 3 4 =
    0 := by decide +kernel
private theorem constant_0_part_3_5 : planeShiftedConstantPart 3 0 3 5 =
    0 := by decide +kernel
private theorem constant_0_part_4_0 : planeShiftedConstantPart 3 0 4 0 =
    (27 / 2) := by decide +kernel
private theorem constant_0_part_4_1 : planeShiftedConstantPart 3 0 4 1 =
    (27 / 2) := by decide +kernel
private theorem constant_0_part_4_2 : planeShiftedConstantPart 3 0 4 2 =
    (27 / 2) := by decide +kernel
private theorem constant_0_part_4_3 : planeShiftedConstantPart 3 0 4 3 =
    (27 / 2) := by decide +kernel
private theorem constant_0_part_4_4 : planeShiftedConstantPart 3 0 4 4 =
    (27 / 2) := by decide +kernel
private theorem constant_0_part_4_5 : planeShiftedConstantPart 3 0 4 5 =
    (27 / 2) := by decide +kernel
private theorem constant_0_part_5_0 : planeShiftedConstantPart 3 0 5 0 =
    0 := by decide +kernel
private theorem constant_0_part_5_1 : planeShiftedConstantPart 3 0 5 1 =
    0 := by decide +kernel
private theorem constant_0_part_5_2 : planeShiftedConstantPart 3 0 5 2 =
    0 := by decide +kernel
private theorem constant_0_part_5_3 : planeShiftedConstantPart 3 0 5 3 =
    0 := by decide +kernel
private theorem constant_0_part_5_4 : planeShiftedConstantPart 3 0 5 4 =
    0 := by decide +kernel
private theorem constant_0_part_5_5 : planeShiftedConstantPart 3 0 5 5 =
    0 := by decide +kernel
private theorem constant_0_part_6_0 : planeShiftedConstantPart 3 0 6 0 =
    (81 / 2) := by decide +kernel
private theorem constant_0_part_6_1 : planeShiftedConstantPart 3 0 6 1 =
    (81 / 2) := by decide +kernel
private theorem constant_0_part_6_2 : planeShiftedConstantPart 3 0 6 2 =
    (81 / 2) := by decide +kernel
private theorem constant_0_part_6_3 : planeShiftedConstantPart 3 0 6 3 =
    (783 / 4) := by decide +kernel
private theorem constant_0_part_6_4 : planeShiftedConstantPart 3 0 6 4 =
    (81 / 2) := by decide +kernel
private theorem constant_0_part_6_5 : planeShiftedConstantPart 3 0 6 5 =
    (783 / 4) := by decide +kernel
private theorem constant_0_part_7_0 : planeShiftedConstantPart 3 0 7 0 =
    (-7933 / 12) := by decide +kernel
private theorem constant_0_part_7_1 : planeShiftedConstantPart 3 0 7 1 =
    (-7933 / 12) := by decide +kernel
private theorem constant_0_part_7_2 : planeShiftedConstantPart 3 0 7 2 =
    (-7933 / 12) := by decide +kernel
private theorem constant_0_part_7_3 : planeShiftedConstantPart 3 0 7 3 =
    (-7933 / 12) := by decide +kernel
private theorem constant_0_part_7_4 : planeShiftedConstantPart 3 0 7 4 =
    (-7933 / 12) := by decide +kernel
private theorem constant_0_part_7_5 : planeShiftedConstantPart 3 0 7 5 =
    (-7933 / 12) := by decide +kernel
private theorem constant_0_part_8_0 : planeShiftedConstantPart 3 0 8 0 =
    (-81 / 8) := by decide +kernel
private theorem constant_0_part_8_1 : planeShiftedConstantPart 3 0 8 1 =
    (-27 / 4) := by decide +kernel
private theorem constant_0_part_8_2 : planeShiftedConstantPart 3 0 8 2 =
    (-81 / 8) := by decide +kernel
private theorem constant_0_part_8_3 : planeShiftedConstantPart 3 0 8 3 =
    (-27 / 4) := by decide +kernel
private theorem constant_0_part_8_4 : planeShiftedConstantPart 3 0 8 4 =
    (-27 / 4) := by decide +kernel
private theorem constant_0_part_8_5 : planeShiftedConstantPart 3 0 8 5 =
    (-27 / 4) := by decide +kernel
private theorem constant_0_part_9_0 : planeShiftedConstantPart 3 0 9 0 =
    (243 / 8) := by decide +kernel
private theorem constant_0_part_9_1 : planeShiftedConstantPart 3 0 9 1 =
    (243 / 8) := by decide +kernel
private theorem constant_0_part_9_2 : planeShiftedConstantPart 3 0 9 2 =
    (243 / 8) := by decide +kernel
private theorem constant_0_part_9_3 : planeShiftedConstantPart 3 0 9 3 =
    (81 / 4) := by decide +kernel
private theorem constant_0_part_9_4 : planeShiftedConstantPart 3 0 9 4 =
    (243 / 8) := by decide +kernel
private theorem constant_0_part_9_5 : planeShiftedConstantPart 3 0 9 5 =
    (81 / 4) := by decide +kernel
private theorem constant_0_part_10_0 : planeShiftedConstantPart 3 0 10 0 =
    (-801 / 8) := by decide +kernel
private theorem constant_0_part_10_1 : planeShiftedConstantPart 3 0 10 1 =
    (-801 / 8) := by decide +kernel
private theorem constant_0_part_10_2 : planeShiftedConstantPart 3 0 10 2 =
    (-801 / 8) := by decide +kernel
private theorem constant_0_part_10_3 : planeShiftedConstantPart 3 0 10 3 =
    (-801 / 8) := by decide +kernel
private theorem constant_0_part_10_4 : planeShiftedConstantPart 3 0 10 4 =
    (-801 / 8) := by decide +kernel
private theorem constant_0_part_10_5 : planeShiftedConstantPart 3 0 10 5 =
    (-801 / 8) := by decide +kernel
private theorem constant_0_part_11_0 : planeShiftedConstantPart 3 0 11 0 =
    9 := by decide +kernel
private theorem constant_0_part_11_1 : planeShiftedConstantPart 3 0 11 1 =
    9 := by decide +kernel
private theorem constant_0_part_11_2 : planeShiftedConstantPart 3 0 11 2 =
    9 := by decide +kernel
private theorem constant_0_part_11_3 : planeShiftedConstantPart 3 0 11 3 =
    9 := by decide +kernel
private theorem constant_0_part_11_4 : planeShiftedConstantPart 3 0 11 4 =
    9 := by decide +kernel
private theorem constant_0_part_11_5 : planeShiftedConstantPart 3 0 11 5 =
    9 := by decide +kernel
private theorem constant_0_part_12_0 : planeShiftedConstantPart 3 0 12 0 =
    (-243 / 2) := by decide +kernel
private theorem constant_0_part_12_1 : planeShiftedConstantPart 3 0 12 1 =
    -81 := by decide +kernel
private theorem constant_0_part_12_2 : planeShiftedConstantPart 3 0 12 2 =
    (-243 / 2) := by decide +kernel
private theorem constant_0_part_12_3 : planeShiftedConstantPart 3 0 12 3 =
    -81 := by decide +kernel
private theorem constant_0_part_12_4 : planeShiftedConstantPart 3 0 12 4 =
    -81 := by decide +kernel
private theorem constant_0_part_12_5 : planeShiftedConstantPart 3 0 12 5 =
    -81 := by decide +kernel
private theorem constant_0_part_13_0 : planeShiftedConstantPart 3 0 13 0 =
    (1683 / 2) := by decide +kernel
private theorem constant_0_part_13_1 : planeShiftedConstantPart 3 0 13 1 =
    (1683 / 2) := by decide +kernel
private theorem constant_0_part_13_2 : planeShiftedConstantPart 3 0 13 2 =
    (1683 / 2) := by decide +kernel
private theorem constant_0_part_13_3 : planeShiftedConstantPart 3 0 13 3 =
    441 := by decide +kernel
private theorem constant_0_part_13_4 : planeShiftedConstantPart 3 0 13 4 =
    (1683 / 2) := by decide +kernel
private theorem constant_0_part_13_5 : planeShiftedConstantPart 3 0 13 5 =
    441 := by decide +kernel
private theorem constant_0_part_14_0 : planeShiftedConstantPart 3 0 14 0 =
    (-27 / 2) := by decide +kernel
private theorem constant_0_part_14_1 : planeShiftedConstantPart 3 0 14 1 =
    (-27 / 2) := by decide +kernel
private theorem constant_0_part_14_2 : planeShiftedConstantPart 3 0 14 2 =
    (-27 / 2) := by decide +kernel
private theorem constant_0_part_14_3 : planeShiftedConstantPart 3 0 14 3 =
    (-27 / 2) := by decide +kernel
private theorem constant_0_part_14_4 : planeShiftedConstantPart 3 0 14 4 =
    (-27 / 2) := by decide +kernel
private theorem constant_0_part_14_5 : planeShiftedConstantPart 3 0 14 5 =
    (-27 / 2) := by decide +kernel
private theorem constant_0_part_15_0 : planeShiftedConstantPart 3 0 15 0 =
    (-81 / 2) := by decide +kernel
private theorem constant_0_part_15_1 : planeShiftedConstantPart 3 0 15 1 =
    (-81 / 2) := by decide +kernel
private theorem constant_0_part_15_2 : planeShiftedConstantPart 3 0 15 2 =
    (-81 / 2) := by decide +kernel
private theorem constant_0_part_15_3 : planeShiftedConstantPart 3 0 15 3 =
    (-963 / 4) := by decide +kernel
private theorem constant_0_part_15_4 : planeShiftedConstantPart 3 0 15 4 =
    (-81 / 2) := by decide +kernel
private theorem constant_0_part_15_5 : planeShiftedConstantPart 3 0 15 5 =
    (-963 / 4) := by decide +kernel

private theorem constant_0_parts_checked (k : Fin 16) (e : Fin 6) :
    planeShiftedConstantPart 3 0 k e = constant_0_parts k e := by
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

private theorem constant_0 : planeShiftedConstantFast 3 0 =
    526 := by
  rw [planeShiftedConstantFast_eq_sum_parts]
  simp_rw [constant_0_parts_checked]
  decide +kernel

private def coefficient_0_0_1_parts : Fin 4 → Fin 6 → ℚ :=
  ![
    ![0, 0, 0, 0, 0, 0],
    ![79360, 79360, 79360, 79360, 79360, 79360],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0]
  ]

private theorem coefficient_0_0_1_part_0_0 : planeEarlierCoefficientPart 3 0 0 1 0 0 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_0_1 : planeEarlierCoefficientPart 3 0 0 1 0 1 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_0_2 : planeEarlierCoefficientPart 3 0 0 1 0 2 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_0_3 : planeEarlierCoefficientPart 3 0 0 1 0 3 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_0_4 : planeEarlierCoefficientPart 3 0 0 1 0 4 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_0_5 : planeEarlierCoefficientPart 3 0 0 1 0 5 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_1_0 : planeEarlierCoefficientPart 3 0 0 1 1 0 =
    79360 := by decide +kernel
private theorem coefficient_0_0_1_part_1_1 : planeEarlierCoefficientPart 3 0 0 1 1 1 =
    79360 := by decide +kernel
private theorem coefficient_0_0_1_part_1_2 : planeEarlierCoefficientPart 3 0 0 1 1 2 =
    79360 := by decide +kernel
private theorem coefficient_0_0_1_part_1_3 : planeEarlierCoefficientPart 3 0 0 1 1 3 =
    79360 := by decide +kernel
private theorem coefficient_0_0_1_part_1_4 : planeEarlierCoefficientPart 3 0 0 1 1 4 =
    79360 := by decide +kernel
private theorem coefficient_0_0_1_part_1_5 : planeEarlierCoefficientPart 3 0 0 1 1 5 =
    79360 := by decide +kernel
private theorem coefficient_0_0_1_part_2_0 : planeEarlierCoefficientPart 3 0 0 1 2 0 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_2_1 : planeEarlierCoefficientPart 3 0 0 1 2 1 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_2_2 : planeEarlierCoefficientPart 3 0 0 1 2 2 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_2_3 : planeEarlierCoefficientPart 3 0 0 1 2 3 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_2_4 : planeEarlierCoefficientPart 3 0 0 1 2 4 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_2_5 : planeEarlierCoefficientPart 3 0 0 1 2 5 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_3_0 : planeEarlierCoefficientPart 3 0 0 1 3 0 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_3_1 : planeEarlierCoefficientPart 3 0 0 1 3 1 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_3_2 : planeEarlierCoefficientPart 3 0 0 1 3 2 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_3_3 : planeEarlierCoefficientPart 3 0 0 1 3 3 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_3_4 : planeEarlierCoefficientPart 3 0 0 1 3 4 =
    0 := by decide +kernel
private theorem coefficient_0_0_1_part_3_5 : planeEarlierCoefficientPart 3 0 0 1 3 5 =
    0 := by decide +kernel

private theorem coefficient_0_0_1_parts_checked (k : Fin 4) (e : Fin 6) :
    planeEarlierCoefficientPart 3 0 0 1 k e = coefficient_0_0_1_parts k e := by
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

private theorem coefficient_0_0_1 : planeEarlierCoefficient 3 0 0 1 =
    476160 := by
  rw [planeEarlierCoefficient_eq_sum_parts]
  simp_rw [coefficient_0_0_1_parts_checked]
  decide +kernel

private def constant_1_parts : Fin 16 → Fin 6 → ℚ :=
  ![
    ![(2477 / 20), (2477 / 20), (2477 / 20), (2477 / 20), (2477 / 20), (2477 / 20)],
    ![(81 / 20), (81 / 20), (81 / 20), (81 / 20), (27 / 20), (27 / 20)],
    ![(-999 / 10), (-999 / 10), (-243 / 10), (-243 / 10), (-243 / 10), (-243 / 10)],
    ![0, 0, 0, 0, 0, 0],
    ![(27 / 20), (27 / 20), (27 / 20), (27 / 20), (27 / 20), (27 / 20)],
    ![0, 0, 0, 0, 0, 0],
    ![(81 / 20), (81 / 20), (243 / 20), (243 / 20), (243 / 20), (243 / 20)],
    ![(-19837 / 120), (-19837 / 120), (-19837 / 120),
      (-19837 / 120), (-19837 / 120), (-19837 / 120)],
    ![(-81 / 40), (-81 / 40), (-81 / 40), (-81 / 40), (-27 / 40), (-27 / 40)],
    ![(81 / 10), (81 / 10), (243 / 40), (243 / 40), (243 / 40), (243 / 40)],
    ![(-126 / 5), (-126 / 5), (-126 / 5), (-126 / 5), (-126 / 5), (-126 / 5)],
    ![(9 / 10), (9 / 10), (9 / 10), (9 / 10), (9 / 10), (9 / 10)],
    ![(-243 / 10), (-243 / 10), (-243 / 10), (-243 / 10), (-81 / 10), (-81 / 10)],
    ![(1062 / 5), (1062 / 5), (1143 / 10), (1143 / 10), (1143 / 10), (1143 / 10)],
    ![(-27 / 20), (-27 / 20), (-27 / 20), (-27 / 20), (-27 / 20), (-27 / 20)],
    ![(-81 / 20), (-81 / 20), (-243 / 20), (-243 / 20), (-243 / 20), (-243 / 20)]
  ]

private theorem constant_1_part_0_0 : planeShiftedConstantPart 3 1 0 0 =
    (2477 / 20) := by decide +kernel
private theorem constant_1_part_0_1 : planeShiftedConstantPart 3 1 0 1 =
    (2477 / 20) := by decide +kernel
private theorem constant_1_part_0_2 : planeShiftedConstantPart 3 1 0 2 =
    (2477 / 20) := by decide +kernel
private theorem constant_1_part_0_3 : planeShiftedConstantPart 3 1 0 3 =
    (2477 / 20) := by decide +kernel
private theorem constant_1_part_0_4 : planeShiftedConstantPart 3 1 0 4 =
    (2477 / 20) := by decide +kernel
private theorem constant_1_part_0_5 : planeShiftedConstantPart 3 1 0 5 =
    (2477 / 20) := by decide +kernel
private theorem constant_1_part_1_0 : planeShiftedConstantPart 3 1 1 0 =
    (81 / 20) := by decide +kernel
private theorem constant_1_part_1_1 : planeShiftedConstantPart 3 1 1 1 =
    (81 / 20) := by decide +kernel
private theorem constant_1_part_1_2 : planeShiftedConstantPart 3 1 1 2 =
    (81 / 20) := by decide +kernel
private theorem constant_1_part_1_3 : planeShiftedConstantPart 3 1 1 3 =
    (81 / 20) := by decide +kernel
private theorem constant_1_part_1_4 : planeShiftedConstantPart 3 1 1 4 =
    (27 / 20) := by decide +kernel
private theorem constant_1_part_1_5 : planeShiftedConstantPart 3 1 1 5 =
    (27 / 20) := by decide +kernel
private theorem constant_1_part_2_0 : planeShiftedConstantPart 3 1 2 0 =
    (-999 / 10) := by decide +kernel
private theorem constant_1_part_2_1 : planeShiftedConstantPart 3 1 2 1 =
    (-999 / 10) := by decide +kernel
private theorem constant_1_part_2_2 : planeShiftedConstantPart 3 1 2 2 =
    (-243 / 10) := by decide +kernel
private theorem constant_1_part_2_3 : planeShiftedConstantPart 3 1 2 3 =
    (-243 / 10) := by decide +kernel
private theorem constant_1_part_2_4 : planeShiftedConstantPart 3 1 2 4 =
    (-243 / 10) := by decide +kernel
private theorem constant_1_part_2_5 : planeShiftedConstantPart 3 1 2 5 =
    (-243 / 10) := by decide +kernel
private theorem constant_1_part_3_0 : planeShiftedConstantPart 3 1 3 0 =
    0 := by decide +kernel
private theorem constant_1_part_3_1 : planeShiftedConstantPart 3 1 3 1 =
    0 := by decide +kernel
private theorem constant_1_part_3_2 : planeShiftedConstantPart 3 1 3 2 =
    0 := by decide +kernel
private theorem constant_1_part_3_3 : planeShiftedConstantPart 3 1 3 3 =
    0 := by decide +kernel
private theorem constant_1_part_3_4 : planeShiftedConstantPart 3 1 3 4 =
    0 := by decide +kernel
private theorem constant_1_part_3_5 : planeShiftedConstantPart 3 1 3 5 =
    0 := by decide +kernel
private theorem constant_1_part_4_0 : planeShiftedConstantPart 3 1 4 0 =
    (27 / 20) := by decide +kernel
private theorem constant_1_part_4_1 : planeShiftedConstantPart 3 1 4 1 =
    (27 / 20) := by decide +kernel
private theorem constant_1_part_4_2 : planeShiftedConstantPart 3 1 4 2 =
    (27 / 20) := by decide +kernel
private theorem constant_1_part_4_3 : planeShiftedConstantPart 3 1 4 3 =
    (27 / 20) := by decide +kernel
private theorem constant_1_part_4_4 : planeShiftedConstantPart 3 1 4 4 =
    (27 / 20) := by decide +kernel
private theorem constant_1_part_4_5 : planeShiftedConstantPart 3 1 4 5 =
    (27 / 20) := by decide +kernel
private theorem constant_1_part_5_0 : planeShiftedConstantPart 3 1 5 0 =
    0 := by decide +kernel
private theorem constant_1_part_5_1 : planeShiftedConstantPart 3 1 5 1 =
    0 := by decide +kernel
private theorem constant_1_part_5_2 : planeShiftedConstantPart 3 1 5 2 =
    0 := by decide +kernel
private theorem constant_1_part_5_3 : planeShiftedConstantPart 3 1 5 3 =
    0 := by decide +kernel
private theorem constant_1_part_5_4 : planeShiftedConstantPart 3 1 5 4 =
    0 := by decide +kernel
private theorem constant_1_part_5_5 : planeShiftedConstantPart 3 1 5 5 =
    0 := by decide +kernel
private theorem constant_1_part_6_0 : planeShiftedConstantPart 3 1 6 0 =
    (81 / 20) := by decide +kernel
private theorem constant_1_part_6_1 : planeShiftedConstantPart 3 1 6 1 =
    (81 / 20) := by decide +kernel
private theorem constant_1_part_6_2 : planeShiftedConstantPart 3 1 6 2 =
    (243 / 20) := by decide +kernel
private theorem constant_1_part_6_3 : planeShiftedConstantPart 3 1 6 3 =
    (243 / 20) := by decide +kernel
private theorem constant_1_part_6_4 : planeShiftedConstantPart 3 1 6 4 =
    (243 / 20) := by decide +kernel
private theorem constant_1_part_6_5 : planeShiftedConstantPart 3 1 6 5 =
    (243 / 20) := by decide +kernel
private theorem constant_1_part_7_0 : planeShiftedConstantPart 3 1 7 0 =
    (-19837 / 120) := by decide +kernel
private theorem constant_1_part_7_1 : planeShiftedConstantPart 3 1 7 1 =
    (-19837 / 120) := by decide +kernel
private theorem constant_1_part_7_2 : planeShiftedConstantPart 3 1 7 2 =
    (-19837 / 120) := by decide +kernel
private theorem constant_1_part_7_3 : planeShiftedConstantPart 3 1 7 3 =
    (-19837 / 120) := by decide +kernel
private theorem constant_1_part_7_4 : planeShiftedConstantPart 3 1 7 4 =
    (-19837 / 120) := by decide +kernel
private theorem constant_1_part_7_5 : planeShiftedConstantPart 3 1 7 5 =
    (-19837 / 120) := by decide +kernel
private theorem constant_1_part_8_0 : planeShiftedConstantPart 3 1 8 0 =
    (-81 / 40) := by decide +kernel
private theorem constant_1_part_8_1 : planeShiftedConstantPart 3 1 8 1 =
    (-81 / 40) := by decide +kernel
private theorem constant_1_part_8_2 : planeShiftedConstantPart 3 1 8 2 =
    (-81 / 40) := by decide +kernel
private theorem constant_1_part_8_3 : planeShiftedConstantPart 3 1 8 3 =
    (-81 / 40) := by decide +kernel
private theorem constant_1_part_8_4 : planeShiftedConstantPart 3 1 8 4 =
    (-27 / 40) := by decide +kernel
private theorem constant_1_part_8_5 : planeShiftedConstantPart 3 1 8 5 =
    (-27 / 40) := by decide +kernel
private theorem constant_1_part_9_0 : planeShiftedConstantPart 3 1 9 0 =
    (81 / 10) := by decide +kernel
private theorem constant_1_part_9_1 : planeShiftedConstantPart 3 1 9 1 =
    (81 / 10) := by decide +kernel
private theorem constant_1_part_9_2 : planeShiftedConstantPart 3 1 9 2 =
    (243 / 40) := by decide +kernel
private theorem constant_1_part_9_3 : planeShiftedConstantPart 3 1 9 3 =
    (243 / 40) := by decide +kernel
private theorem constant_1_part_9_4 : planeShiftedConstantPart 3 1 9 4 =
    (243 / 40) := by decide +kernel
private theorem constant_1_part_9_5 : planeShiftedConstantPart 3 1 9 5 =
    (243 / 40) := by decide +kernel
private theorem constant_1_part_10_0 : planeShiftedConstantPart 3 1 10 0 =
    (-126 / 5) := by decide +kernel
private theorem constant_1_part_10_1 : planeShiftedConstantPart 3 1 10 1 =
    (-126 / 5) := by decide +kernel
private theorem constant_1_part_10_2 : planeShiftedConstantPart 3 1 10 2 =
    (-126 / 5) := by decide +kernel
private theorem constant_1_part_10_3 : planeShiftedConstantPart 3 1 10 3 =
    (-126 / 5) := by decide +kernel
private theorem constant_1_part_10_4 : planeShiftedConstantPart 3 1 10 4 =
    (-126 / 5) := by decide +kernel
private theorem constant_1_part_10_5 : planeShiftedConstantPart 3 1 10 5 =
    (-126 / 5) := by decide +kernel
private theorem constant_1_part_11_0 : planeShiftedConstantPart 3 1 11 0 =
    (9 / 10) := by decide +kernel
private theorem constant_1_part_11_1 : planeShiftedConstantPart 3 1 11 1 =
    (9 / 10) := by decide +kernel
private theorem constant_1_part_11_2 : planeShiftedConstantPart 3 1 11 2 =
    (9 / 10) := by decide +kernel
private theorem constant_1_part_11_3 : planeShiftedConstantPart 3 1 11 3 =
    (9 / 10) := by decide +kernel
private theorem constant_1_part_11_4 : planeShiftedConstantPart 3 1 11 4 =
    (9 / 10) := by decide +kernel
private theorem constant_1_part_11_5 : planeShiftedConstantPart 3 1 11 5 =
    (9 / 10) := by decide +kernel
private theorem constant_1_part_12_0 : planeShiftedConstantPart 3 1 12 0 =
    (-243 / 10) := by decide +kernel
private theorem constant_1_part_12_1 : planeShiftedConstantPart 3 1 12 1 =
    (-243 / 10) := by decide +kernel
private theorem constant_1_part_12_2 : planeShiftedConstantPart 3 1 12 2 =
    (-243 / 10) := by decide +kernel
private theorem constant_1_part_12_3 : planeShiftedConstantPart 3 1 12 3 =
    (-243 / 10) := by decide +kernel
private theorem constant_1_part_12_4 : planeShiftedConstantPart 3 1 12 4 =
    (-81 / 10) := by decide +kernel
private theorem constant_1_part_12_5 : planeShiftedConstantPart 3 1 12 5 =
    (-81 / 10) := by decide +kernel
private theorem constant_1_part_13_0 : planeShiftedConstantPart 3 1 13 0 =
    (1062 / 5) := by decide +kernel
private theorem constant_1_part_13_1 : planeShiftedConstantPart 3 1 13 1 =
    (1062 / 5) := by decide +kernel
private theorem constant_1_part_13_2 : planeShiftedConstantPart 3 1 13 2 =
    (1143 / 10) := by decide +kernel
private theorem constant_1_part_13_3 : planeShiftedConstantPart 3 1 13 3 =
    (1143 / 10) := by decide +kernel
private theorem constant_1_part_13_4 : planeShiftedConstantPart 3 1 13 4 =
    (1143 / 10) := by decide +kernel
private theorem constant_1_part_13_5 : planeShiftedConstantPart 3 1 13 5 =
    (1143 / 10) := by decide +kernel
private theorem constant_1_part_14_0 : planeShiftedConstantPart 3 1 14 0 =
    (-27 / 20) := by decide +kernel
private theorem constant_1_part_14_1 : planeShiftedConstantPart 3 1 14 1 =
    (-27 / 20) := by decide +kernel
private theorem constant_1_part_14_2 : planeShiftedConstantPart 3 1 14 2 =
    (-27 / 20) := by decide +kernel
private theorem constant_1_part_14_3 : planeShiftedConstantPart 3 1 14 3 =
    (-27 / 20) := by decide +kernel
private theorem constant_1_part_14_4 : planeShiftedConstantPart 3 1 14 4 =
    (-27 / 20) := by decide +kernel
private theorem constant_1_part_14_5 : planeShiftedConstantPart 3 1 14 5 =
    (-27 / 20) := by decide +kernel
private theorem constant_1_part_15_0 : planeShiftedConstantPart 3 1 15 0 =
    (-81 / 20) := by decide +kernel
private theorem constant_1_part_15_1 : planeShiftedConstantPart 3 1 15 1 =
    (-81 / 20) := by decide +kernel
private theorem constant_1_part_15_2 : planeShiftedConstantPart 3 1 15 2 =
    (-243 / 20) := by decide +kernel
private theorem constant_1_part_15_3 : planeShiftedConstantPart 3 1 15 3 =
    (-243 / 20) := by decide +kernel
private theorem constant_1_part_15_4 : planeShiftedConstantPart 3 1 15 4 =
    (-243 / 20) := by decide +kernel
private theorem constant_1_part_15_5 : planeShiftedConstantPart 3 1 15 5 =
    (-243 / 20) := by decide +kernel

private theorem constant_1_parts_checked (k : Fin 16) (e : Fin 6) :
    planeShiftedConstantPart 3 1 k e = constant_1_parts k e := by
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

private theorem constant_1 : planeShiftedConstantFast 3 1 =
    127 := by
  rw [planeShiftedConstantFast_eq_sum_parts]
  simp_rw [constant_1_parts_checked]
  decide +kernel

private def coefficient_1_0_1_parts : Fin 4 → Fin 6 → ℚ :=
  ![
    ![0, 0, 0, 0, 0, 0],
    ![19840, 19840, 19840, 19840, 19840, 19840],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0]
  ]

private theorem coefficient_1_0_1_part_0_0 : planeEarlierCoefficientPart 3 1 0 1 0 0 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_0_1 : planeEarlierCoefficientPart 3 1 0 1 0 1 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_0_2 : planeEarlierCoefficientPart 3 1 0 1 0 2 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_0_3 : planeEarlierCoefficientPart 3 1 0 1 0 3 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_0_4 : planeEarlierCoefficientPart 3 1 0 1 0 4 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_0_5 : planeEarlierCoefficientPart 3 1 0 1 0 5 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_1_0 : planeEarlierCoefficientPart 3 1 0 1 1 0 =
    19840 := by decide +kernel
private theorem coefficient_1_0_1_part_1_1 : planeEarlierCoefficientPart 3 1 0 1 1 1 =
    19840 := by decide +kernel
private theorem coefficient_1_0_1_part_1_2 : planeEarlierCoefficientPart 3 1 0 1 1 2 =
    19840 := by decide +kernel
private theorem coefficient_1_0_1_part_1_3 : planeEarlierCoefficientPart 3 1 0 1 1 3 =
    19840 := by decide +kernel
private theorem coefficient_1_0_1_part_1_4 : planeEarlierCoefficientPart 3 1 0 1 1 4 =
    19840 := by decide +kernel
private theorem coefficient_1_0_1_part_1_5 : planeEarlierCoefficientPart 3 1 0 1 1 5 =
    19840 := by decide +kernel
private theorem coefficient_1_0_1_part_2_0 : planeEarlierCoefficientPart 3 1 0 1 2 0 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_2_1 : planeEarlierCoefficientPart 3 1 0 1 2 1 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_2_2 : planeEarlierCoefficientPart 3 1 0 1 2 2 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_2_3 : planeEarlierCoefficientPart 3 1 0 1 2 3 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_2_4 : planeEarlierCoefficientPart 3 1 0 1 2 4 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_2_5 : planeEarlierCoefficientPart 3 1 0 1 2 5 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_3_0 : planeEarlierCoefficientPart 3 1 0 1 3 0 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_3_1 : planeEarlierCoefficientPart 3 1 0 1 3 1 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_3_2 : planeEarlierCoefficientPart 3 1 0 1 3 2 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_3_3 : planeEarlierCoefficientPart 3 1 0 1 3 3 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_3_4 : planeEarlierCoefficientPart 3 1 0 1 3 4 =
    0 := by decide +kernel
private theorem coefficient_1_0_1_part_3_5 : planeEarlierCoefficientPart 3 1 0 1 3 5 =
    0 := by decide +kernel

private theorem coefficient_1_0_1_parts_checked (k : Fin 4) (e : Fin 6) :
    planeEarlierCoefficientPart 3 1 0 1 k e = coefficient_1_0_1_parts k e := by
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

private theorem coefficient_1_0_1 : planeEarlierCoefficient 3 1 0 1 =
    119040 := by
  rw [planeEarlierCoefficient_eq_sum_parts]
  simp_rw [coefficient_1_0_1_parts_checked]
  decide +kernel

private def constant_2_parts : Fin 16 → Fin 6 → ℚ :=
  ![
    ![31, 31, 31, 31, 31, 31],
    ![(9 / 20), (9 / 20), (9 / 20), (9 / 20), (9 / 20), (9 / 20)],
    ![(-36 / 5), (-36 / 5), (-36 / 5), (-36 / 5), (-36 / 5), (-36 / 5)],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![(27 / 20), (27 / 20), (27 / 20), (27 / 20), (27 / 20), (27 / 20)],
    ![(-124 / 3), (-124 / 3), (-124 / 3), (-124 / 3), (-124 / 3), (-124 / 3)],
    ![(-9 / 40), (-9 / 40), (-9 / 40), (-9 / 40), (-9 / 40), (-9 / 40)],
    ![(9 / 5), (9 / 5), (9 / 5), (9 / 5), (9 / 5), (9 / 5)],
    ![(-253 / 40), (-253 / 40), (-253 / 40), (-253 / 40), (-253 / 40), (-253 / 40)],
    ![0, 0, 0, 0, 0, 0],
    ![(-27 / 10), (-27 / 10), (-27 / 10), (-27 / 10), (-27 / 10), (-27 / 10)],
    ![(297 / 10), (297 / 10), (297 / 10), (297 / 10), (297 / 10), (297 / 10)],
    ![0, 0, 0, 0, 0, 0],
    ![(-27 / 20), (-27 / 20), (-27 / 20), (-27 / 20), (-27 / 20), (-27 / 20)]
  ]

private theorem constant_2_part_0_0 : planeShiftedConstantPart 3 2 0 0 =
    31 := by decide +kernel
private theorem constant_2_part_0_1 : planeShiftedConstantPart 3 2 0 1 =
    31 := by decide +kernel
private theorem constant_2_part_0_2 : planeShiftedConstantPart 3 2 0 2 =
    31 := by decide +kernel
private theorem constant_2_part_0_3 : planeShiftedConstantPart 3 2 0 3 =
    31 := by decide +kernel
private theorem constant_2_part_0_4 : planeShiftedConstantPart 3 2 0 4 =
    31 := by decide +kernel
private theorem constant_2_part_0_5 : planeShiftedConstantPart 3 2 0 5 =
    31 := by decide +kernel
private theorem constant_2_part_1_0 : planeShiftedConstantPart 3 2 1 0 =
    (9 / 20) := by decide +kernel
private theorem constant_2_part_1_1 : planeShiftedConstantPart 3 2 1 1 =
    (9 / 20) := by decide +kernel
private theorem constant_2_part_1_2 : planeShiftedConstantPart 3 2 1 2 =
    (9 / 20) := by decide +kernel
private theorem constant_2_part_1_3 : planeShiftedConstantPart 3 2 1 3 =
    (9 / 20) := by decide +kernel
private theorem constant_2_part_1_4 : planeShiftedConstantPart 3 2 1 4 =
    (9 / 20) := by decide +kernel
private theorem constant_2_part_1_5 : planeShiftedConstantPart 3 2 1 5 =
    (9 / 20) := by decide +kernel
private theorem constant_2_part_2_0 : planeShiftedConstantPart 3 2 2 0 =
    (-36 / 5) := by decide +kernel
private theorem constant_2_part_2_1 : planeShiftedConstantPart 3 2 2 1 =
    (-36 / 5) := by decide +kernel
private theorem constant_2_part_2_2 : planeShiftedConstantPart 3 2 2 2 =
    (-36 / 5) := by decide +kernel
private theorem constant_2_part_2_3 : planeShiftedConstantPart 3 2 2 3 =
    (-36 / 5) := by decide +kernel
private theorem constant_2_part_2_4 : planeShiftedConstantPart 3 2 2 4 =
    (-36 / 5) := by decide +kernel
private theorem constant_2_part_2_5 : planeShiftedConstantPart 3 2 2 5 =
    (-36 / 5) := by decide +kernel
private theorem constant_2_part_3_0 : planeShiftedConstantPart 3 2 3 0 =
    0 := by decide +kernel
private theorem constant_2_part_3_1 : planeShiftedConstantPart 3 2 3 1 =
    0 := by decide +kernel
private theorem constant_2_part_3_2 : planeShiftedConstantPart 3 2 3 2 =
    0 := by decide +kernel
private theorem constant_2_part_3_3 : planeShiftedConstantPart 3 2 3 3 =
    0 := by decide +kernel
private theorem constant_2_part_3_4 : planeShiftedConstantPart 3 2 3 4 =
    0 := by decide +kernel
private theorem constant_2_part_3_5 : planeShiftedConstantPart 3 2 3 5 =
    0 := by decide +kernel
private theorem constant_2_part_4_0 : planeShiftedConstantPart 3 2 4 0 =
    0 := by decide +kernel
private theorem constant_2_part_4_1 : planeShiftedConstantPart 3 2 4 1 =
    0 := by decide +kernel
private theorem constant_2_part_4_2 : planeShiftedConstantPart 3 2 4 2 =
    0 := by decide +kernel
private theorem constant_2_part_4_3 : planeShiftedConstantPart 3 2 4 3 =
    0 := by decide +kernel
private theorem constant_2_part_4_4 : planeShiftedConstantPart 3 2 4 4 =
    0 := by decide +kernel
private theorem constant_2_part_4_5 : planeShiftedConstantPart 3 2 4 5 =
    0 := by decide +kernel
private theorem constant_2_part_5_0 : planeShiftedConstantPart 3 2 5 0 =
    0 := by decide +kernel
private theorem constant_2_part_5_1 : planeShiftedConstantPart 3 2 5 1 =
    0 := by decide +kernel
private theorem constant_2_part_5_2 : planeShiftedConstantPart 3 2 5 2 =
    0 := by decide +kernel
private theorem constant_2_part_5_3 : planeShiftedConstantPart 3 2 5 3 =
    0 := by decide +kernel
private theorem constant_2_part_5_4 : planeShiftedConstantPart 3 2 5 4 =
    0 := by decide +kernel
private theorem constant_2_part_5_5 : planeShiftedConstantPart 3 2 5 5 =
    0 := by decide +kernel
private theorem constant_2_part_6_0 : planeShiftedConstantPart 3 2 6 0 =
    (27 / 20) := by decide +kernel
private theorem constant_2_part_6_1 : planeShiftedConstantPart 3 2 6 1 =
    (27 / 20) := by decide +kernel
private theorem constant_2_part_6_2 : planeShiftedConstantPart 3 2 6 2 =
    (27 / 20) := by decide +kernel
private theorem constant_2_part_6_3 : planeShiftedConstantPart 3 2 6 3 =
    (27 / 20) := by decide +kernel
private theorem constant_2_part_6_4 : planeShiftedConstantPart 3 2 6 4 =
    (27 / 20) := by decide +kernel
private theorem constant_2_part_6_5 : planeShiftedConstantPart 3 2 6 5 =
    (27 / 20) := by decide +kernel
private theorem constant_2_part_7_0 : planeShiftedConstantPart 3 2 7 0 =
    (-124 / 3) := by decide +kernel
private theorem constant_2_part_7_1 : planeShiftedConstantPart 3 2 7 1 =
    (-124 / 3) := by decide +kernel
private theorem constant_2_part_7_2 : planeShiftedConstantPart 3 2 7 2 =
    (-124 / 3) := by decide +kernel
private theorem constant_2_part_7_3 : planeShiftedConstantPart 3 2 7 3 =
    (-124 / 3) := by decide +kernel
private theorem constant_2_part_7_4 : planeShiftedConstantPart 3 2 7 4 =
    (-124 / 3) := by decide +kernel
private theorem constant_2_part_7_5 : planeShiftedConstantPart 3 2 7 5 =
    (-124 / 3) := by decide +kernel
private theorem constant_2_part_8_0 : planeShiftedConstantPart 3 2 8 0 =
    (-9 / 40) := by decide +kernel
private theorem constant_2_part_8_1 : planeShiftedConstantPart 3 2 8 1 =
    (-9 / 40) := by decide +kernel
private theorem constant_2_part_8_2 : planeShiftedConstantPart 3 2 8 2 =
    (-9 / 40) := by decide +kernel
private theorem constant_2_part_8_3 : planeShiftedConstantPart 3 2 8 3 =
    (-9 / 40) := by decide +kernel
private theorem constant_2_part_8_4 : planeShiftedConstantPart 3 2 8 4 =
    (-9 / 40) := by decide +kernel
private theorem constant_2_part_8_5 : planeShiftedConstantPart 3 2 8 5 =
    (-9 / 40) := by decide +kernel
private theorem constant_2_part_9_0 : planeShiftedConstantPart 3 2 9 0 =
    (9 / 5) := by decide +kernel
private theorem constant_2_part_9_1 : planeShiftedConstantPart 3 2 9 1 =
    (9 / 5) := by decide +kernel
private theorem constant_2_part_9_2 : planeShiftedConstantPart 3 2 9 2 =
    (9 / 5) := by decide +kernel
private theorem constant_2_part_9_3 : planeShiftedConstantPart 3 2 9 3 =
    (9 / 5) := by decide +kernel
private theorem constant_2_part_9_4 : planeShiftedConstantPart 3 2 9 4 =
    (9 / 5) := by decide +kernel
private theorem constant_2_part_9_5 : planeShiftedConstantPart 3 2 9 5 =
    (9 / 5) := by decide +kernel
private theorem constant_2_part_10_0 : planeShiftedConstantPart 3 2 10 0 =
    (-253 / 40) := by decide +kernel
private theorem constant_2_part_10_1 : planeShiftedConstantPart 3 2 10 1 =
    (-253 / 40) := by decide +kernel
private theorem constant_2_part_10_2 : planeShiftedConstantPart 3 2 10 2 =
    (-253 / 40) := by decide +kernel
private theorem constant_2_part_10_3 : planeShiftedConstantPart 3 2 10 3 =
    (-253 / 40) := by decide +kernel
private theorem constant_2_part_10_4 : planeShiftedConstantPart 3 2 10 4 =
    (-253 / 40) := by decide +kernel
private theorem constant_2_part_10_5 : planeShiftedConstantPart 3 2 10 5 =
    (-253 / 40) := by decide +kernel
private theorem constant_2_part_11_0 : planeShiftedConstantPart 3 2 11 0 =
    0 := by decide +kernel
private theorem constant_2_part_11_1 : planeShiftedConstantPart 3 2 11 1 =
    0 := by decide +kernel
private theorem constant_2_part_11_2 : planeShiftedConstantPart 3 2 11 2 =
    0 := by decide +kernel
private theorem constant_2_part_11_3 : planeShiftedConstantPart 3 2 11 3 =
    0 := by decide +kernel
private theorem constant_2_part_11_4 : planeShiftedConstantPart 3 2 11 4 =
    0 := by decide +kernel
private theorem constant_2_part_11_5 : planeShiftedConstantPart 3 2 11 5 =
    0 := by decide +kernel
private theorem constant_2_part_12_0 : planeShiftedConstantPart 3 2 12 0 =
    (-27 / 10) := by decide +kernel
private theorem constant_2_part_12_1 : planeShiftedConstantPart 3 2 12 1 =
    (-27 / 10) := by decide +kernel
private theorem constant_2_part_12_2 : planeShiftedConstantPart 3 2 12 2 =
    (-27 / 10) := by decide +kernel
private theorem constant_2_part_12_3 : planeShiftedConstantPart 3 2 12 3 =
    (-27 / 10) := by decide +kernel
private theorem constant_2_part_12_4 : planeShiftedConstantPart 3 2 12 4 =
    (-27 / 10) := by decide +kernel
private theorem constant_2_part_12_5 : planeShiftedConstantPart 3 2 12 5 =
    (-27 / 10) := by decide +kernel
private theorem constant_2_part_13_0 : planeShiftedConstantPart 3 2 13 0 =
    (297 / 10) := by decide +kernel
private theorem constant_2_part_13_1 : planeShiftedConstantPart 3 2 13 1 =
    (297 / 10) := by decide +kernel
private theorem constant_2_part_13_2 : planeShiftedConstantPart 3 2 13 2 =
    (297 / 10) := by decide +kernel
private theorem constant_2_part_13_3 : planeShiftedConstantPart 3 2 13 3 =
    (297 / 10) := by decide +kernel
private theorem constant_2_part_13_4 : planeShiftedConstantPart 3 2 13 4 =
    (297 / 10) := by decide +kernel
private theorem constant_2_part_13_5 : planeShiftedConstantPart 3 2 13 5 =
    (297 / 10) := by decide +kernel
private theorem constant_2_part_14_0 : planeShiftedConstantPart 3 2 14 0 =
    0 := by decide +kernel
private theorem constant_2_part_14_1 : planeShiftedConstantPart 3 2 14 1 =
    0 := by decide +kernel
private theorem constant_2_part_14_2 : planeShiftedConstantPart 3 2 14 2 =
    0 := by decide +kernel
private theorem constant_2_part_14_3 : planeShiftedConstantPart 3 2 14 3 =
    0 := by decide +kernel
private theorem constant_2_part_14_4 : planeShiftedConstantPart 3 2 14 4 =
    0 := by decide +kernel
private theorem constant_2_part_14_5 : planeShiftedConstantPart 3 2 14 5 =
    0 := by decide +kernel
private theorem constant_2_part_15_0 : planeShiftedConstantPart 3 2 15 0 =
    (-27 / 20) := by decide +kernel
private theorem constant_2_part_15_1 : planeShiftedConstantPart 3 2 15 1 =
    (-27 / 20) := by decide +kernel
private theorem constant_2_part_15_2 : planeShiftedConstantPart 3 2 15 2 =
    (-27 / 20) := by decide +kernel
private theorem constant_2_part_15_3 : planeShiftedConstantPart 3 2 15 3 =
    (-27 / 20) := by decide +kernel
private theorem constant_2_part_15_4 : planeShiftedConstantPart 3 2 15 4 =
    (-27 / 20) := by decide +kernel
private theorem constant_2_part_15_5 : planeShiftedConstantPart 3 2 15 5 =
    (-27 / 20) := by decide +kernel

private theorem constant_2_parts_checked (k : Fin 16) (e : Fin 6) :
    planeShiftedConstantPart 3 2 k e = constant_2_parts k e := by
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

private theorem constant_2 : planeShiftedConstantFast 3 2 =
    31 := by
  rw [planeShiftedConstantFast_eq_sum_parts]
  simp_rw [constant_2_parts_checked]
  decide +kernel

private def coefficient_2_0_1_parts : Fin 4 → Fin 6 → ℚ :=
  ![
    ![0, 0, 0, 0, 0, 0],
    ![4960, 4960, 4960, 4960, 4960, 4960],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0]
  ]

private theorem coefficient_2_0_1_part_0_0 : planeEarlierCoefficientPart 3 2 0 1 0 0 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_0_1 : planeEarlierCoefficientPart 3 2 0 1 0 1 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_0_2 : planeEarlierCoefficientPart 3 2 0 1 0 2 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_0_3 : planeEarlierCoefficientPart 3 2 0 1 0 3 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_0_4 : planeEarlierCoefficientPart 3 2 0 1 0 4 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_0_5 : planeEarlierCoefficientPart 3 2 0 1 0 5 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_1_0 : planeEarlierCoefficientPart 3 2 0 1 1 0 =
    4960 := by decide +kernel
private theorem coefficient_2_0_1_part_1_1 : planeEarlierCoefficientPart 3 2 0 1 1 1 =
    4960 := by decide +kernel
private theorem coefficient_2_0_1_part_1_2 : planeEarlierCoefficientPart 3 2 0 1 1 2 =
    4960 := by decide +kernel
private theorem coefficient_2_0_1_part_1_3 : planeEarlierCoefficientPart 3 2 0 1 1 3 =
    4960 := by decide +kernel
private theorem coefficient_2_0_1_part_1_4 : planeEarlierCoefficientPart 3 2 0 1 1 4 =
    4960 := by decide +kernel
private theorem coefficient_2_0_1_part_1_5 : planeEarlierCoefficientPart 3 2 0 1 1 5 =
    4960 := by decide +kernel
private theorem coefficient_2_0_1_part_2_0 : planeEarlierCoefficientPart 3 2 0 1 2 0 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_2_1 : planeEarlierCoefficientPart 3 2 0 1 2 1 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_2_2 : planeEarlierCoefficientPart 3 2 0 1 2 2 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_2_3 : planeEarlierCoefficientPart 3 2 0 1 2 3 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_2_4 : planeEarlierCoefficientPart 3 2 0 1 2 4 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_2_5 : planeEarlierCoefficientPart 3 2 0 1 2 5 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_3_0 : planeEarlierCoefficientPart 3 2 0 1 3 0 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_3_1 : planeEarlierCoefficientPart 3 2 0 1 3 1 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_3_2 : planeEarlierCoefficientPart 3 2 0 1 3 2 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_3_3 : planeEarlierCoefficientPart 3 2 0 1 3 3 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_3_4 : planeEarlierCoefficientPart 3 2 0 1 3 4 =
    0 := by decide +kernel
private theorem coefficient_2_0_1_part_3_5 : planeEarlierCoefficientPart 3 2 0 1 3 5 =
    0 := by decide +kernel

private theorem coefficient_2_0_1_parts_checked (k : Fin 4) (e : Fin 6) :
    planeEarlierCoefficientPart 3 2 0 1 k e = coefficient_2_0_1_parts k e := by
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

private theorem coefficient_2_0_1 : planeEarlierCoefficient 3 2 0 1 =
    29760 := by
  rw [planeEarlierCoefficient_eq_sum_parts]
  simp_rw [coefficient_2_0_1_parts_checked]
  decide +kernel

/-- All complete constants in HHP/HPP/PPP order. -/
theorem constants (i : Fin 3) :
    planeShiftedConstantFast 3 i = (![526, 127, 31] : Fin 3 → ℚ) i := by
  fin_cases i
  · exact constant_0
  · exact constant_1
  · exact constant_2

/-- The full signed coefficient of this nonzero earlier entry. -/
theorem coefficients_0_1 (i : Fin 3) :
    planeEarlierCoefficient 3 i 0 1 =
      (![476160, 119040, 29760] : Fin 3 → ℚ) i := by
  fin_cases i
  · exact coefficient_0_0_1
  · exact coefficient_1_0_1
  · exact coefficient_2_0_1

end AxiomaticGW.GenusTwoPlaneDegree3Scalars

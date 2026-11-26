/-
Generated exact plane genus-two candidates.
Input SHA256: ccf66a351c974d15aabe21613a4cfa2e90db20aaf28d273765583e50e587b862
Every scalar and the complete table are separately checked by Lean.
-/
module

public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneLineScalars
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneDegree2Scalars
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneDegree3Scalars
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneDegree4Scalars

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 20000

namespace AxiomaticGW.PlaneGenusTwoScalarTable
open BelorousskiPandharipande

/-- Candidates outside the held bound are not certified. -/
def values : ℕ → Fin 3 → ℚ
  | 0 => ![0, (-1 / 960), 0]
  | 1 => ![0, 0, 0]
  | 2 => ![0, 0, 0]
  | 3 => ![0, (-1 / 4), (-1 / 12)]
  | 4 => ![27, 42, (25 / 4)]
  | _ => ![0, 0, 0]

private theorem row_0 : planeCheckCanonicalRow values 0 = true := by
  decide +kernel

private theorem constant_1_0 : planeShiftedConstantFast 1 0 =
    (1 / 10) := GenusTwoPlaneLineScalars.constants 0
private theorem coefficient_1_0_0_1 : planeEarlierCoefficient 1 0 0 1 =
    96 := GenusTwoPlaneLineScalars.coefficients 0
private theorem constant_1_1 : planeShiftedConstantFast 1 1 =
    (1 / 20) := GenusTwoPlaneLineScalars.constants 1
private theorem coefficient_1_1_0_1 : planeEarlierCoefficient 1 1 0 1 =
    48 := GenusTwoPlaneLineScalars.coefficients 1
private theorem constant_1_2 : planeShiftedConstantFast 1 2 =
    (1 / 40) := GenusTwoPlaneLineScalars.constants 2
private theorem coefficient_1_2_0_1 : planeEarlierCoefficient 1 2 0 1 =
    24 := GenusTwoPlaneLineScalars.coefficients 2

private theorem constant_row_1 (i : Fin 3) :
    planeShiftedConstantFast 1 i = (![(1 / 10), (1 / 20), (1 / 40)] : Fin 3 → ℚ) i := by
  fin_cases i
  · exact constant_1_0
  · exact constant_1_1
  · exact constant_1_2

private theorem coefficient_row_1_0_1 (i : Fin 3) :
    planeEarlierCoefficient 1 i 0 1 =
      (![96, 48, 24] : Fin 3 → ℚ) i := by
  fin_cases i
  · exact coefficient_1_0_0_1
  · exact coefficient_1_1_0_1
  · exact coefficient_1_2_0_1

private theorem remainder_1 (i : Fin 3) :
    planeScalarRemainder values 1 i = (![0, 0, 0] : Fin 3 → ℚ) i := by
  norm_num [planeScalarRemainder, Fin.sum_univ_succ, values,
    constant_row_1, coefficient_row_1_0_1]
  fin_cases i <;> norm_num [Matrix.cons_val_two]

private theorem row_1 : planeCheckCanonicalRow values 1 = true := by
  have hr : (fun i ↦ -planeScalarRemainder values 1 i) =
      (fun i ↦ -(![0, 0, 0] : Fin 3 → ℚ) i) := by
    funext i; rw [remainder_1]
  rw [planeCheckCanonicalRow, if_neg (by decide), decide_eq_true_eq, hr]
  decide +kernel

private theorem constant_2_0 : planeShiftedConstantFast 2 0 =
    (81 / 20) := GenusTwoPlaneDegree2Scalars.constants 0
private theorem coefficient_2_0_0_1 : planeEarlierCoefficient 2 0 0 1 =
    3888 := GenusTwoPlaneDegree2Scalars.coefficients_0_1 0
private theorem constant_2_1 : planeShiftedConstantFast 2 1 =
    (27 / 20) := GenusTwoPlaneDegree2Scalars.constants 1
private theorem coefficient_2_1_0_1 : planeEarlierCoefficient 2 1 0 1 =
    1296 := GenusTwoPlaneDegree2Scalars.coefficients_0_1 1
private theorem constant_2_2 : planeShiftedConstantFast 2 2 =
    (9 / 20) := GenusTwoPlaneDegree2Scalars.constants 2
private theorem coefficient_2_2_0_1 : planeEarlierCoefficient 2 2 0 1 =
    432 := GenusTwoPlaneDegree2Scalars.coefficients_0_1 2

private theorem constant_row_2 (i : Fin 3) :
    planeShiftedConstantFast 2 i = (![(81 / 20), (27 / 20), (9 / 20)] : Fin 3 → ℚ) i := by
  fin_cases i
  · exact constant_2_0
  · exact constant_2_1
  · exact constant_2_2

private theorem coefficient_row_2_0_1 (i : Fin 3) :
    planeEarlierCoefficient 2 i 0 1 =
      (![3888, 1296, 432] : Fin 3 → ℚ) i := by
  fin_cases i
  · exact coefficient_2_0_0_1
  · exact coefficient_2_1_0_1
  · exact coefficient_2_2_0_1

private theorem remainder_2 (i : Fin 3) :
    planeScalarRemainder values 2 i = (![0, 0, 0] : Fin 3 → ℚ) i := by
  norm_num [planeScalarRemainder, Fin.sum_univ_succ, values,
    constant_row_2, coefficient_row_2_0_1]
  fin_cases i <;> norm_num [Matrix.cons_val_two]

private theorem row_2 : planeCheckCanonicalRow values 2 = true := by
  have hr : (fun i ↦ -planeScalarRemainder values 2 i) =
      (fun i ↦ -(![0, 0, 0] : Fin 3 → ℚ) i) := by
    funext i; rw [remainder_2]
  rw [planeCheckCanonicalRow, if_neg (by decide), decide_eq_true_eq, hr]
  decide +kernel

private theorem constant_3_0 : planeShiftedConstantFast 3 0 =
    526 := GenusTwoPlaneDegree3Scalars.constants 0
private theorem coefficient_3_0_0_1 : planeEarlierCoefficient 3 0 0 1 =
    476160 := GenusTwoPlaneDegree3Scalars.coefficients_0_1 0
private theorem constant_3_1 : planeShiftedConstantFast 3 1 =
    127 := GenusTwoPlaneDegree3Scalars.constants 1
private theorem coefficient_3_1_0_1 : planeEarlierCoefficient 3 1 0 1 =
    119040 := GenusTwoPlaneDegree3Scalars.coefficients_0_1 1
private theorem constant_3_2 : planeShiftedConstantFast 3 2 =
    31 := GenusTwoPlaneDegree3Scalars.constants 2
private theorem coefficient_3_2_0_1 : planeEarlierCoefficient 3 2 0 1 =
    29760 := GenusTwoPlaneDegree3Scalars.coefficients_0_1 2

private theorem constant_row_3 (i : Fin 3) :
    planeShiftedConstantFast 3 i = (![526, 127, 31] : Fin 3 → ℚ) i := by
  fin_cases i
  · exact constant_3_0
  · exact constant_3_1
  · exact constant_3_2

private theorem coefficient_row_3_0_1 (i : Fin 3) :
    planeEarlierCoefficient 3 i 0 1 =
      (![476160, 119040, 29760] : Fin 3 → ℚ) i := by
  fin_cases i
  · exact coefficient_3_0_0_1
  · exact coefficient_3_1_0_1
  · exact coefficient_3_2_0_1

private theorem remainder_3 (i : Fin 3) :
    planeScalarRemainder values 3 i = (![30, 3, 0] : Fin 3 → ℚ) i := by
  norm_num [planeScalarRemainder, Fin.sum_univ_succ, values,
    constant_row_3, coefficient_row_3_0_1]
  fin_cases i <;> norm_num [Matrix.cons_val_two]

private theorem row_3 : planeCheckCanonicalRow values 3 = true := by
  have hr : (fun i ↦ -planeScalarRemainder values 3 i) =
      (fun i ↦ -(![30, 3, 0] : Fin 3 → ℚ) i) := by
    funext i; rw [remainder_3]
  rw [planeCheckCanonicalRow, if_neg (by decide), decide_eq_true_eq, hr]
  decide +kernel

private theorem constant_4_0 : planeShiftedConstantFast 4 0 =
    (333281 / 2) := GenusTwoPlaneDegree4Scalars.constants 0
private theorem coefficient_4_0_0_1 : planeEarlierCoefficient 4 0 0 1 =
    130956000 := GenusTwoPlaneDegree4Scalars.coefficients_0_1 0
private theorem coefficient_4_0_3_1 : planeEarlierCoefficient 4 0 3 1 =
    6864 := GenusTwoPlaneDegree4Scalars.coefficients_3_1 0
private theorem coefficient_4_0_3_2 : planeEarlierCoefficient 4 0 3 2 =
    185328 := GenusTwoPlaneDegree4Scalars.coefficients_3_2 0
private theorem constant_4_1 : planeShiftedConstantFast 4 1 =
    (65677 / 2) := GenusTwoPlaneDegree4Scalars.constants 1
private theorem coefficient_4_1_0_1 : planeEarlierCoefficient 4 1 0 1 =
    26191200 := GenusTwoPlaneDegree4Scalars.coefficients_0_1 1
private theorem coefficient_4_1_3_1 : planeEarlierCoefficient 4 1 3 1 =
    -13200 := GenusTwoPlaneDegree4Scalars.coefficients_3_1 1
private theorem coefficient_4_1_3_2 : planeEarlierCoefficient 4 1 3 2 =
    71280 := GenusTwoPlaneDegree4Scalars.coefficients_3_2 1
private theorem constant_4_2 : planeShiftedConstantFast 4 2 =
    (12185 / 2) := GenusTwoPlaneDegree4Scalars.constants 2
private theorem coefficient_4_2_0_1 : planeEarlierCoefficient 4 2 0 1 =
    5238240 := GenusTwoPlaneDegree4Scalars.coefficients_0_1 2
private theorem coefficient_4_2_3_1 : planeEarlierCoefficient 4 2 3 1 =
    -4620 := GenusTwoPlaneDegree4Scalars.coefficients_3_1 2
private theorem coefficient_4_2_3_2 : planeEarlierCoefficient 4 2 3 2 =
    17820 := GenusTwoPlaneDegree4Scalars.coefficients_3_2 2

private theorem constant_row_4 (i : Fin 3) :
    planeShiftedConstantFast 4 i = (![(333281 / 2), (65677 / 2), (12185 / 2)] : Fin 3 → ℚ) i := by
  fin_cases i
  · exact constant_4_0
  · exact constant_4_1
  · exact constant_4_2

private theorem coefficient_row_4_0_1 (i : Fin 3) :
    planeEarlierCoefficient 4 i 0 1 =
      (![130956000, 26191200, 5238240] : Fin 3 → ℚ) i := by
  fin_cases i
  · exact coefficient_4_0_0_1
  · exact coefficient_4_1_0_1
  · exact coefficient_4_2_0_1

private theorem coefficient_row_4_3_1 (i : Fin 3) :
    planeEarlierCoefficient 4 i 3 1 =
      (![6864, -13200, -4620] : Fin 3 → ℚ) i := by
  fin_cases i
  · exact coefficient_4_0_3_1
  · exact coefficient_4_1_3_1
  · exact coefficient_4_2_3_1

private theorem coefficient_row_4_3_2 (i : Fin 3) :
    planeEarlierCoefficient 4 i 3 2 =
      (![185328, 71280, 17820] : Fin 3 → ℚ) i := by
  fin_cases i
  · exact coefficient_4_0_3_2
  · exact coefficient_4_1_3_2
  · exact coefficient_4_2_3_2

private theorem remainder_4 (i : Fin 3) :
    planeScalarRemainder values 4 i = (![13068, 2916, 306] : Fin 3 → ℚ) i := by
  norm_num [planeScalarRemainder, Fin.sum_univ_succ, values,
    constant_row_4, coefficient_row_4_0_1, coefficient_row_4_3_1,
    coefficient_row_4_3_2]
  fin_cases i <;> norm_num [Matrix.cons_val_two]

private theorem row_4 : planeCheckCanonicalRow values 4 = true := by
  have hr : (fun i ↦ -planeScalarRemainder values 4 i) =
      (fun i ↦ -(![13068, 2916, 306] : Fin 3 → ℚ) i) := by
    funext i; rw [remainder_4]
  rw [planeCheckCanonicalRow, if_neg (by decide), decide_eq_true_eq, hr]
  decide +kernel

/-- Every degree, including every zero entry, satisfies the original recursion. -/
theorem accepted : planeCheckCanonicalTable 4 values = true := by
  rw [planeCheckCanonicalTable, decide_eq_true_eq]
  intro d
  fin_cases d
  · exact row_0
  · exact row_1
  · exact row_2
  · exact row_3
  · exact row_4

/-- All covered candidates equal the original terminating reconstruction. -/
theorem values_eq (d : ℕ) (hd : d ≤ 4) :
    values d = planeCanonicalValues d :=
  planeCheckCanonicalTable_sound 4 values accepted d hd

/-- Incoming full requests, kept independently of the certified values. -/
def requests : Fin 4 → Fin 3 → SurfaceQuery .plane :=
  ![
    ![⟨2, ![1], [⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩]⟩,
      ⟨2, ![1], [⟨.hyperplane, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩]⟩,
      ⟨2, ![1], [⟨.point, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩]⟩],
    ![⟨2, ![2], [⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩,
      ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩]⟩,
      ⟨2, ![2], [⟨.hyperplane, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩,
      ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩]⟩,
      ⟨2, ![2], [⟨.point, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩,
      ⟨.point, 0⟩, ⟨.point, 0⟩]⟩],
    ![⟨2, ![3], [⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩,
      ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩,
      ⟨.point, 0⟩, ⟨.point, 0⟩]⟩,
      ⟨2, ![3], [⟨.hyperplane, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩,
      ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩,
      ⟨.point, 0⟩, ⟨.point, 0⟩]⟩,
      ⟨2, ![3], [⟨.point, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩,
      ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩,
      ⟨.point, 0⟩]⟩],
    ![⟨2, ![4], [⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩,
      ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩,
      ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩,
      ⟨.point, 0⟩]⟩,
      ⟨2, ![4], [⟨.hyperplane, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩,
      ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩,
      ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩,
      ⟨.point, 0⟩]⟩,
      ⟨2, ![4], [⟨.point, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩,
      ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩,
      ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩]⟩]
  ]

/-- Hold target, full degree, labels and cotangent powers fixed. -/
theorem coverage : ∀ d i, requests d i = planeCanonicalQueries (d.val + 1) i := by
  decide +kernel

/-- Every positive-degree output is bound to its incoming full query. -/
theorem claims : ∀ d i, planeCheckCanonicalClaim 4 values
    (requests d i) (values (d.val + 1) i) = true := by
  intro d i
  rw [planeCheckCanonicalClaim, accepted, Bool.and_true, decide_eq_true_eq]
  exact ⟨⟨d.val + 1, by omega⟩, i, coverage d i, rfl⟩

end AxiomaticGW.PlaneGenusTwoScalarTable

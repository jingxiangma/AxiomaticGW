/-
Generated candidate values from the published Kontsevich--Manin formula (5.18).
The low-energy package is shared with the existing base cases.
Manifest SHA256: d710f97e36fee1f9a30b2e5993af87ee6fb6674c3447b5097c1137d41790ebff
This digest records provenance; the finite Lean check proves acceptance.
-/
module

public import AxiomaticGW.Surfaces.GenusZeroCertificate

@[expose] public section

-- Check rows sequentially to bound kernel replay memory.
set_option Elab.async false

namespace AxiomaticGW.GenusZeroF1Table

open SurfaceGenusZero

/-- Candidate point values, keyed by every effective curve coordinate. -/
def values (beta : SurfaceTarget.hirzebruchOne.Curve) : ℚ :=
  match beta 0, beta 1 with
  | 0, 1 => 1
  | 1, 0 => 1
  | 1, 1 => 1
  | 1, 2 => 1
  | 1, 3 => 1
  | 1, 4 => 1
  | 1, 5 => 1
  | 2, 2 => 1
  | 2, 3 => 12
  | 2, 4 => 96
  | 2, 5 => 640
  | 3, 3 => 12
  | 3, 4 => 620
  | 4, 4 => 620
  | _, _ => 0

/-- Explicit full-coordinate requests, including every zero value. -/
def classes : List SurfaceTarget.hirzebruchOne.Curve :=
  [![0, 0],
   ![1, 0],
   ![0, 1],
   ![2, 0],
   ![1, 1],
   ![3, 0],
   ![0, 2],
   ![2, 1],
   ![4, 0],
   ![1, 2],
   ![3, 1],
   ![5, 0],
   ![0, 3],
   ![2, 2],
   ![4, 1],
   ![6, 0],
   ![1, 3],
   ![3, 2],
   ![5, 1],
   ![7, 0],
   ![0, 4],
   ![2, 3],
   ![4, 2],
   ![6, 1],
   ![8, 0],
   ![1, 4],
   ![3, 3],
   ![5, 2],
   ![7, 1],
   ![9, 0],
   ![0, 5],
   ![2, 4],
   ![4, 3],
   ![6, 2],
   ![8, 1],
   ![10, 0],
   ![1, 5],
   ![3, 4],
   ![5, 3],
   ![7, 2],
   ![9, 1],
   ![11, 0],
   ![0, 6],
   ![2, 5],
   ![4, 4],
   ![6, 3],
   ![8, 2],
   ![10, 1],
   ![12, 0]]

/-- Literal tuples cover exactly the original complete bounded enumeration. -/
theorem covers : classes.toFinset = SurfaceTarget.hirzebruchOne.bounded 12 := by
  -- Adjacent increasing keys prove distinctness without pairwise function comparison.
  let code (beta : SurfaceTarget.hirzebruchOne.Curve) : ℕ :=
    SurfaceTarget.hirzebruchOne.effective.energy beta * 169
      + beta 0 * 13
      + beta 1 * 1
  have hs : (classes.map code).IsChain (· < ·) := by decide +kernel
  have hn : classes.Nodup := List.Nodup.of_map code hs.pairwise.nodup
  have hi : ∀ beta ∈ classes, SurfaceTarget.hirzebruchOne.effective.energy beta ≤ 12 := by
    decide +kernel
  apply Finset.eq_of_subset_of_card_le
  · intro beta hb
    rw [SurfaceTarget.bounded_eq, SurfaceTarget.hirzebruchOne.effective.mem_bounded]
    exact hi beta (List.mem_toFinset.mp hb)
  · rw [List.toFinset_card_of_nodup hn]
    decide +kernel

private theorem row_0 : checkValue .hirzebruchOne values ![0, 0] = true := by
  decide +kernel

private theorem row_1 : checkValue .hirzebruchOne values ![1, 0] = true := by
  decide +kernel

private theorem row_2 : checkValue .hirzebruchOne values ![0, 1] = true := by
  decide +kernel

private theorem row_3 : checkValue .hirzebruchOne values ![2, 0] = true := by
  decide +kernel

private theorem row_4 : checkValue .hirzebruchOne values ![1, 1] = true := by
  decide +kernel

private theorem row_5 : checkValue .hirzebruchOne values ![3, 0] = true := by
  decide +kernel

private theorem row_6 : checkValue .hirzebruchOne values ![0, 2] = true := by
  decide +kernel

private theorem row_7 : checkValue .hirzebruchOne values ![2, 1] = true := by
  decide +kernel

private theorem row_8 : checkValue .hirzebruchOne values ![4, 0] = true := by
  decide +kernel

private theorem row_9 : checkValue .hirzebruchOne values ![1, 2] = true := by
  decide +kernel

private theorem row_10 : checkValue .hirzebruchOne values ![3, 1] = true := by
  decide +kernel

private theorem row_11 : checkValue .hirzebruchOne values ![5, 0] = true := by
  decide +kernel

private theorem row_12 : checkValue .hirzebruchOne values ![0, 3] = true := by
  decide +kernel

private theorem row_13 : checkValue .hirzebruchOne values ![2, 2] = true := by
  decide +kernel

private theorem row_14 : checkValue .hirzebruchOne values ![4, 1] = true := by
  decide +kernel

private theorem row_15 : checkValue .hirzebruchOne values ![6, 0] = true := by
  decide +kernel

private theorem row_16 : checkValue .hirzebruchOne values ![1, 3] = true := by
  decide +kernel

private theorem row_17 : checkValue .hirzebruchOne values ![3, 2] = true := by
  decide +kernel

private theorem row_18 : checkValue .hirzebruchOne values ![5, 1] = true := by
  decide +kernel

private theorem row_19 : checkValue .hirzebruchOne values ![7, 0] = true := by
  decide +kernel

private theorem row_20 : checkValue .hirzebruchOne values ![0, 4] = true := by
  decide +kernel

private theorem row_21 : checkValue .hirzebruchOne values ![2, 3] = true := by
  decide +kernel

private theorem row_22 : checkValue .hirzebruchOne values ![4, 2] = true := by
  decide +kernel

private theorem row_23 : checkValue .hirzebruchOne values ![6, 1] = true := by
  decide +kernel

private theorem row_24 : checkValue .hirzebruchOne values ![8, 0] = true := by
  decide +kernel

private theorem row_25 : checkValue .hirzebruchOne values ![1, 4] = true := by
  decide +kernel

private theorem row_26 : checkValue .hirzebruchOne values ![3, 3] = true := by
  decide +kernel

private theorem row_27 : checkValue .hirzebruchOne values ![5, 2] = true := by
  decide +kernel

private theorem row_28 : checkValue .hirzebruchOne values ![7, 1] = true := by
  decide +kernel

private theorem row_29 : checkValue .hirzebruchOne values ![9, 0] = true := by
  decide +kernel

private theorem row_30 : checkValue .hirzebruchOne values ![0, 5] = true := by
  decide +kernel

private theorem row_31 : checkValue .hirzebruchOne values ![2, 4] = true := by
  decide +kernel

private theorem row_32 : checkValue .hirzebruchOne values ![4, 3] = true := by
  decide +kernel

private theorem row_33 : checkValue .hirzebruchOne values ![6, 2] = true := by
  decide +kernel

private theorem row_34 : checkValue .hirzebruchOne values ![8, 1] = true := by
  decide +kernel

private theorem row_35 : checkValue .hirzebruchOne values ![10, 0] = true := by
  decide +kernel

private theorem row_36 : checkValue .hirzebruchOne values ![1, 5] = true := by
  decide +kernel

private theorem row_37 : checkValue .hirzebruchOne values ![3, 4] = true := by
  decide +kernel

private theorem row_38 : checkValue .hirzebruchOne values ![5, 3] = true := by
  decide +kernel

private theorem row_39 : checkValue .hirzebruchOne values ![7, 2] = true := by
  decide +kernel

private theorem row_40 : checkValue .hirzebruchOne values ![9, 1] = true := by
  decide +kernel

private theorem row_41 : checkValue .hirzebruchOne values ![11, 0] = true := by
  decide +kernel

private theorem row_42 : checkValue .hirzebruchOne values ![0, 6] = true := by
  decide +kernel

private theorem row_43 : checkValue .hirzebruchOne values ![2, 5] = true := by
  decide +kernel

private theorem row_44 : checkValue .hirzebruchOne values ![4, 4] = true := by
  decide +kernel

private theorem row_45 : checkValue .hirzebruchOne values ![6, 3] = true := by
  decide +kernel

private theorem row_46 : checkValue .hirzebruchOne values ![8, 2] = true := by
  decide +kernel

private theorem row_47 : checkValue .hirzebruchOne values ![10, 1] = true := by
  decide +kernel

private theorem row_48 : checkValue .hirzebruchOne values ![12, 0] = true := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- Every candidate equation is checked on literal tuples, including all zeros. -/
theorem rows_checked : classes.all (checkValue .hirzebruchOne values) = true := by
  simp only [classes, List.all_cons, List.all_nil,
    row_0, row_1, row_2, row_3, row_4, row_5, row_6, row_7,
    row_8, row_9, row_10, row_11, row_12, row_13, row_14, row_15,
    row_16, row_17, row_18, row_19, row_20, row_21, row_22, row_23,
    row_24, row_25, row_26, row_27, row_28, row_29, row_30, row_31,
    row_32, row_33, row_34, row_35, row_36, row_37, row_38, row_39,
    row_40, row_41, row_42, row_43, row_44, row_45, row_46, row_47,
    row_48,
    Bool.and_true]

/-- Kernel replay checks every class in the held bound. -/
theorem accepted : checkBoundedValues .hirzebruchOne 12 values = true := by
  apply checkEnumeratedValues_sound .hirzebruchOne 12 classes values
  rw [checkEnumeratedValues, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨covers, rows_checked⟩

/-- Every covered candidate agrees with the original terminating evaluator. -/
theorem values_eq (beta : SurfaceTarget.hirzebruchOne.Curve)
    (hbound : SurfaceTarget.hirzebruchOne.effective.energy beta ≤ 12) :
    values beta = pointValue .hirzebruchOne beta :=
  checkBoundedValues_sound .hirzebruchOne 12 values accepted beta hbound

end AxiomaticGW.GenusZeroF1Table

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

namespace AxiomaticGW.GenusZeroBl2Table

open SurfaceGenusZero

/-- Candidate point values, keyed by every effective curve coordinate. -/
def values (beta : SurfaceTarget.blowupTwo.Curve) : ℚ :=
  match beta 0, beta 1, beta 2 with
  | 0, 0, 1 => 1
  | 0, 1, 0 => 1
  | 0, 1, 1 => 1
  | 1, 0, 0 => 1
  | 1, 0, 1 => 1
  | 1, 1, 1 => 1
  | 1, 1, 2 => 1
  | 1, 2, 2 => 1
  | 1, 2, 3 => 1
  | 1, 3, 3 => 1
  | 1, 3, 4 => 1
  | 1, 4, 4 => 1
  | 1, 4, 5 => 1
  | 1, 5, 5 => 1
  | 1, 5, 6 => 1
  | 2, 1, 2 => 1
  | 2, 1, 3 => 1
  | 2, 2, 2 => 1
  | 2, 2, 3 => 12
  | 2, 2, 4 => 12
  | 2, 3, 3 => 12
  | 2, 3, 4 => 96
  | 2, 3, 5 => 96
  | 2, 4, 4 => 96
  | 2, 4, 5 => 640
  | 2, 4, 6 => 640
  | 2, 5, 5 => 640
  | 3, 1, 3 => 1
  | 3, 1, 4 => 1
  | 3, 2, 3 => 12
  | 3, 2, 4 => 96
  | 3, 2, 5 => 96
  | 3, 3, 3 => 12
  | 3, 3, 4 => 620
  | 3, 3, 5 => 3510
  | 3, 3, 6 => 3510
  | 3, 4, 4 => 620
  | 3, 4, 5 => 18132
  | 4, 1, 4 => 1
  | 4, 1, 5 => 1
  | 4, 2, 4 => 96
  | 4, 2, 5 => 640
  | 4, 2, 6 => 640
  | 4, 3, 4 => 620
  | 4, 3, 5 => 18132
  | 4, 4, 4 => 620
  | 5, 1, 5 => 1
  | 5, 1, 6 => 1
  | 5, 2, 5 => 640
  | _, _, _ => 0

/-- Explicit full-coordinate requests, including every zero value. -/
def classes : List SurfaceTarget.blowupTwo.Curve :=
  [![0, 0, 0],
   ![0, 0, 1],
   ![0, 1, 0],
   ![1, 0, 0],
   ![0, 0, 2],
   ![0, 1, 1],
   ![0, 2, 0],
   ![1, 0, 1],
   ![1, 1, 0],
   ![2, 0, 0],
   ![0, 0, 3],
   ![0, 1, 2],
   ![0, 2, 1],
   ![0, 3, 0],
   ![1, 0, 2],
   ![1, 1, 1],
   ![1, 2, 0],
   ![2, 0, 1],
   ![2, 1, 0],
   ![3, 0, 0],
   ![0, 0, 4],
   ![0, 1, 3],
   ![0, 2, 2],
   ![0, 3, 1],
   ![0, 4, 0],
   ![1, 0, 3],
   ![1, 1, 2],
   ![1, 2, 1],
   ![1, 3, 0],
   ![2, 0, 2],
   ![2, 1, 1],
   ![2, 2, 0],
   ![3, 0, 1],
   ![3, 1, 0],
   ![4, 0, 0],
   ![0, 0, 5],
   ![0, 1, 4],
   ![0, 2, 3],
   ![0, 3, 2],
   ![0, 4, 1],
   ![0, 5, 0],
   ![1, 0, 4],
   ![1, 1, 3],
   ![1, 2, 2],
   ![1, 3, 1],
   ![1, 4, 0],
   ![2, 0, 3],
   ![2, 1, 2],
   ![2, 2, 1],
   ![2, 3, 0],
   ![3, 0, 2],
   ![3, 1, 1],
   ![3, 2, 0],
   ![4, 0, 1],
   ![4, 1, 0],
   ![5, 0, 0],
   ![0, 0, 6],
   ![0, 1, 5],
   ![0, 2, 4],
   ![0, 3, 3],
   ![0, 4, 2],
   ![0, 5, 1],
   ![0, 6, 0],
   ![1, 0, 5],
   ![1, 1, 4],
   ![1, 2, 3],
   ![1, 3, 2],
   ![1, 4, 1],
   ![1, 5, 0],
   ![2, 0, 4],
   ![2, 1, 3],
   ![2, 2, 2],
   ![2, 3, 1],
   ![2, 4, 0],
   ![3, 0, 3],
   ![3, 1, 2],
   ![3, 2, 1],
   ![3, 3, 0],
   ![4, 0, 2],
   ![4, 1, 1],
   ![4, 2, 0],
   ![5, 0, 1],
   ![5, 1, 0],
   ![6, 0, 0],
   ![0, 0, 7],
   ![0, 1, 6],
   ![0, 2, 5],
   ![0, 3, 4],
   ![0, 4, 3],
   ![0, 5, 2],
   ![0, 6, 1],
   ![0, 7, 0],
   ![1, 0, 6],
   ![1, 1, 5],
   ![1, 2, 4],
   ![1, 3, 3],
   ![1, 4, 2],
   ![1, 5, 1],
   ![1, 6, 0],
   ![2, 0, 5],
   ![2, 1, 4],
   ![2, 2, 3],
   ![2, 3, 2],
   ![2, 4, 1],
   ![2, 5, 0],
   ![3, 0, 4],
   ![3, 1, 3],
   ![3, 2, 2],
   ![3, 3, 1],
   ![3, 4, 0],
   ![4, 0, 3],
   ![4, 1, 2],
   ![4, 2, 1],
   ![4, 3, 0],
   ![5, 0, 2],
   ![5, 1, 1],
   ![5, 2, 0],
   ![6, 0, 1],
   ![6, 1, 0],
   ![7, 0, 0],
   ![0, 0, 8],
   ![0, 1, 7],
   ![0, 2, 6],
   ![0, 3, 5],
   ![0, 4, 4],
   ![0, 5, 3],
   ![0, 6, 2],
   ![0, 7, 1],
   ![0, 8, 0],
   ![1, 0, 7],
   ![1, 1, 6],
   ![1, 2, 5],
   ![1, 3, 4],
   ![1, 4, 3],
   ![1, 5, 2],
   ![1, 6, 1],
   ![1, 7, 0],
   ![2, 0, 6],
   ![2, 1, 5],
   ![2, 2, 4],
   ![2, 3, 3],
   ![2, 4, 2],
   ![2, 5, 1],
   ![2, 6, 0],
   ![3, 0, 5],
   ![3, 1, 4],
   ![3, 2, 3],
   ![3, 3, 2],
   ![3, 4, 1],
   ![3, 5, 0],
   ![4, 0, 4],
   ![4, 1, 3],
   ![4, 2, 2],
   ![4, 3, 1],
   ![4, 4, 0],
   ![5, 0, 3],
   ![5, 1, 2],
   ![5, 2, 1],
   ![5, 3, 0],
   ![6, 0, 2],
   ![6, 1, 1],
   ![6, 2, 0],
   ![7, 0, 1],
   ![7, 1, 0],
   ![8, 0, 0],
   ![0, 0, 9],
   ![0, 1, 8],
   ![0, 2, 7],
   ![0, 3, 6],
   ![0, 4, 5],
   ![0, 5, 4],
   ![0, 6, 3],
   ![0, 7, 2],
   ![0, 8, 1],
   ![0, 9, 0],
   ![1, 0, 8],
   ![1, 1, 7],
   ![1, 2, 6],
   ![1, 3, 5],
   ![1, 4, 4],
   ![1, 5, 3],
   ![1, 6, 2],
   ![1, 7, 1],
   ![1, 8, 0],
   ![2, 0, 7],
   ![2, 1, 6],
   ![2, 2, 5],
   ![2, 3, 4],
   ![2, 4, 3],
   ![2, 5, 2],
   ![2, 6, 1],
   ![2, 7, 0],
   ![3, 0, 6],
   ![3, 1, 5],
   ![3, 2, 4],
   ![3, 3, 3],
   ![3, 4, 2],
   ![3, 5, 1],
   ![3, 6, 0],
   ![4, 0, 5],
   ![4, 1, 4],
   ![4, 2, 3],
   ![4, 3, 2],
   ![4, 4, 1],
   ![4, 5, 0],
   ![5, 0, 4],
   ![5, 1, 3],
   ![5, 2, 2],
   ![5, 3, 1],
   ![5, 4, 0],
   ![6, 0, 3],
   ![6, 1, 2],
   ![6, 2, 1],
   ![6, 3, 0],
   ![7, 0, 2],
   ![7, 1, 1],
   ![7, 2, 0],
   ![8, 0, 1],
   ![8, 1, 0],
   ![9, 0, 0],
   ![0, 0, 10],
   ![0, 1, 9],
   ![0, 2, 8],
   ![0, 3, 7],
   ![0, 4, 6],
   ![0, 5, 5],
   ![0, 6, 4],
   ![0, 7, 3],
   ![0, 8, 2],
   ![0, 9, 1],
   ![0, 10, 0],
   ![1, 0, 9],
   ![1, 1, 8],
   ![1, 2, 7],
   ![1, 3, 6],
   ![1, 4, 5],
   ![1, 5, 4],
   ![1, 6, 3],
   ![1, 7, 2],
   ![1, 8, 1],
   ![1, 9, 0],
   ![2, 0, 8],
   ![2, 1, 7],
   ![2, 2, 6],
   ![2, 3, 5],
   ![2, 4, 4],
   ![2, 5, 3],
   ![2, 6, 2],
   ![2, 7, 1],
   ![2, 8, 0],
   ![3, 0, 7],
   ![3, 1, 6],
   ![3, 2, 5],
   ![3, 3, 4],
   ![3, 4, 3],
   ![3, 5, 2],
   ![3, 6, 1],
   ![3, 7, 0],
   ![4, 0, 6],
   ![4, 1, 5],
   ![4, 2, 4],
   ![4, 3, 3],
   ![4, 4, 2],
   ![4, 5, 1],
   ![4, 6, 0],
   ![5, 0, 5],
   ![5, 1, 4],
   ![5, 2, 3],
   ![5, 3, 2],
   ![5, 4, 1],
   ![5, 5, 0],
   ![6, 0, 4],
   ![6, 1, 3],
   ![6, 2, 2],
   ![6, 3, 1],
   ![6, 4, 0],
   ![7, 0, 3],
   ![7, 1, 2],
   ![7, 2, 1],
   ![7, 3, 0],
   ![8, 0, 2],
   ![8, 1, 1],
   ![8, 2, 0],
   ![9, 0, 1],
   ![9, 1, 0],
   ![10, 0, 0],
   ![0, 0, 11],
   ![0, 1, 10],
   ![0, 2, 9],
   ![0, 3, 8],
   ![0, 4, 7],
   ![0, 5, 6],
   ![0, 6, 5],
   ![0, 7, 4],
   ![0, 8, 3],
   ![0, 9, 2],
   ![0, 10, 1],
   ![0, 11, 0],
   ![1, 0, 10],
   ![1, 1, 9],
   ![1, 2, 8],
   ![1, 3, 7],
   ![1, 4, 6],
   ![1, 5, 5],
   ![1, 6, 4],
   ![1, 7, 3],
   ![1, 8, 2],
   ![1, 9, 1],
   ![1, 10, 0],
   ![2, 0, 9],
   ![2, 1, 8],
   ![2, 2, 7],
   ![2, 3, 6],
   ![2, 4, 5],
   ![2, 5, 4],
   ![2, 6, 3],
   ![2, 7, 2],
   ![2, 8, 1],
   ![2, 9, 0],
   ![3, 0, 8],
   ![3, 1, 7],
   ![3, 2, 6],
   ![3, 3, 5],
   ![3, 4, 4],
   ![3, 5, 3],
   ![3, 6, 2],
   ![3, 7, 1],
   ![3, 8, 0],
   ![4, 0, 7],
   ![4, 1, 6],
   ![4, 2, 5],
   ![4, 3, 4],
   ![4, 4, 3],
   ![4, 5, 2],
   ![4, 6, 1],
   ![4, 7, 0],
   ![5, 0, 6],
   ![5, 1, 5],
   ![5, 2, 4],
   ![5, 3, 3],
   ![5, 4, 2],
   ![5, 5, 1],
   ![5, 6, 0],
   ![6, 0, 5],
   ![6, 1, 4],
   ![6, 2, 3],
   ![6, 3, 2],
   ![6, 4, 1],
   ![6, 5, 0],
   ![7, 0, 4],
   ![7, 1, 3],
   ![7, 2, 2],
   ![7, 3, 1],
   ![7, 4, 0],
   ![8, 0, 3],
   ![8, 1, 2],
   ![8, 2, 1],
   ![8, 3, 0],
   ![9, 0, 2],
   ![9, 1, 1],
   ![9, 2, 0],
   ![10, 0, 1],
   ![10, 1, 0],
   ![11, 0, 0],
   ![0, 0, 12],
   ![0, 1, 11],
   ![0, 2, 10],
   ![0, 3, 9],
   ![0, 4, 8],
   ![0, 5, 7],
   ![0, 6, 6],
   ![0, 7, 5],
   ![0, 8, 4],
   ![0, 9, 3],
   ![0, 10, 2],
   ![0, 11, 1],
   ![0, 12, 0],
   ![1, 0, 11],
   ![1, 1, 10],
   ![1, 2, 9],
   ![1, 3, 8],
   ![1, 4, 7],
   ![1, 5, 6],
   ![1, 6, 5],
   ![1, 7, 4],
   ![1, 8, 3],
   ![1, 9, 2],
   ![1, 10, 1],
   ![1, 11, 0],
   ![2, 0, 10],
   ![2, 1, 9],
   ![2, 2, 8],
   ![2, 3, 7],
   ![2, 4, 6],
   ![2, 5, 5],
   ![2, 6, 4],
   ![2, 7, 3],
   ![2, 8, 2],
   ![2, 9, 1],
   ![2, 10, 0],
   ![3, 0, 9],
   ![3, 1, 8],
   ![3, 2, 7],
   ![3, 3, 6],
   ![3, 4, 5],
   ![3, 5, 4],
   ![3, 6, 3],
   ![3, 7, 2],
   ![3, 8, 1],
   ![3, 9, 0],
   ![4, 0, 8],
   ![4, 1, 7],
   ![4, 2, 6],
   ![4, 3, 5],
   ![4, 4, 4],
   ![4, 5, 3],
   ![4, 6, 2],
   ![4, 7, 1],
   ![4, 8, 0],
   ![5, 0, 7],
   ![5, 1, 6],
   ![5, 2, 5],
   ![5, 3, 4],
   ![5, 4, 3],
   ![5, 5, 2],
   ![5, 6, 1],
   ![5, 7, 0],
   ![6, 0, 6],
   ![6, 1, 5],
   ![6, 2, 4],
   ![6, 3, 3],
   ![6, 4, 2],
   ![6, 5, 1],
   ![6, 6, 0],
   ![7, 0, 5],
   ![7, 1, 4],
   ![7, 2, 3],
   ![7, 3, 2],
   ![7, 4, 1],
   ![7, 5, 0],
   ![8, 0, 4],
   ![8, 1, 3],
   ![8, 2, 2],
   ![8, 3, 1],
   ![8, 4, 0],
   ![9, 0, 3],
   ![9, 1, 2],
   ![9, 2, 1],
   ![9, 3, 0],
   ![10, 0, 2],
   ![10, 1, 1],
   ![10, 2, 0],
   ![11, 0, 1],
   ![11, 1, 0],
   ![12, 0, 0]]

/-- Literal tuples cover exactly the original complete bounded enumeration. -/
theorem covers : classes.toFinset = SurfaceTarget.blowupTwo.bounded 12 := by
  -- Adjacent increasing keys prove distinctness without pairwise function comparison.
  let code (beta : SurfaceTarget.blowupTwo.Curve) : ℕ :=
    SurfaceTarget.blowupTwo.effective.energy beta * 2197
      + beta 0 * 169
      + beta 1 * 13
      + beta 2 * 1
  have hs : (classes.map code).IsChain (· < ·) := by decide +kernel
  have hn : classes.Nodup := List.Nodup.of_map code hs.pairwise.nodup
  have hi : ∀ beta ∈ classes, SurfaceTarget.blowupTwo.effective.energy beta ≤ 12 := by
    decide +kernel
  apply Finset.eq_of_subset_of_card_le
  · intro beta hb
    rw [SurfaceTarget.bounded_eq, SurfaceTarget.blowupTwo.effective.mem_bounded]
    exact hi beta (List.mem_toFinset.mp hb)
  · rw [List.toFinset_card_of_nodup hn]
    decide +kernel

private theorem row_0 : checkValue .blowupTwo values ![0, 0, 0] = true := by
  decide +kernel

private theorem row_1 : checkValue .blowupTwo values ![0, 0, 1] = true := by
  decide +kernel

private theorem row_2 : checkValue .blowupTwo values ![0, 1, 0] = true := by
  decide +kernel

private theorem row_3 : checkValue .blowupTwo values ![1, 0, 0] = true := by
  decide +kernel

private theorem row_4 : checkValue .blowupTwo values ![0, 0, 2] = true := by
  decide +kernel

private theorem row_5 : checkValue .blowupTwo values ![0, 1, 1] = true := by
  decide +kernel

private theorem row_6 : checkValue .blowupTwo values ![0, 2, 0] = true := by
  decide +kernel

private theorem row_7 : checkValue .blowupTwo values ![1, 0, 1] = true := by
  decide +kernel

private theorem row_8 : checkValue .blowupTwo values ![1, 1, 0] = true := by
  decide +kernel

private theorem row_9 : checkValue .blowupTwo values ![2, 0, 0] = true := by
  decide +kernel

private theorem row_10 : checkValue .blowupTwo values ![0, 0, 3] = true := by
  decide +kernel

private theorem row_11 : checkValue .blowupTwo values ![0, 1, 2] = true := by
  decide +kernel

private theorem row_12 : checkValue .blowupTwo values ![0, 2, 1] = true := by
  decide +kernel

private theorem row_13 : checkValue .blowupTwo values ![0, 3, 0] = true := by
  decide +kernel

private theorem row_14 : checkValue .blowupTwo values ![1, 0, 2] = true := by
  decide +kernel

private theorem row_15 : checkValue .blowupTwo values ![1, 1, 1] = true := by
  decide +kernel

private theorem row_16 : checkValue .blowupTwo values ![1, 2, 0] = true := by
  decide +kernel

private theorem row_17 : checkValue .blowupTwo values ![2, 0, 1] = true := by
  decide +kernel

private theorem row_18 : checkValue .blowupTwo values ![2, 1, 0] = true := by
  decide +kernel

private theorem row_19 : checkValue .blowupTwo values ![3, 0, 0] = true := by
  decide +kernel

private theorem row_20 : checkValue .blowupTwo values ![0, 0, 4] = true := by
  decide +kernel

private theorem row_21 : checkValue .blowupTwo values ![0, 1, 3] = true := by
  decide +kernel

private theorem row_22 : checkValue .blowupTwo values ![0, 2, 2] = true := by
  decide +kernel

private theorem row_23 : checkValue .blowupTwo values ![0, 3, 1] = true := by
  decide +kernel

private theorem row_24 : checkValue .blowupTwo values ![0, 4, 0] = true := by
  decide +kernel

private theorem row_25 : checkValue .blowupTwo values ![1, 0, 3] = true := by
  decide +kernel

private theorem row_26 : checkValue .blowupTwo values ![1, 1, 2] = true := by
  decide +kernel

private theorem row_27 : checkValue .blowupTwo values ![1, 2, 1] = true := by
  decide +kernel

private theorem row_28 : checkValue .blowupTwo values ![1, 3, 0] = true := by
  decide +kernel

private theorem row_29 : checkValue .blowupTwo values ![2, 0, 2] = true := by
  decide +kernel

private theorem row_30 : checkValue .blowupTwo values ![2, 1, 1] = true := by
  decide +kernel

private theorem row_31 : checkValue .blowupTwo values ![2, 2, 0] = true := by
  decide +kernel

private theorem row_32 : checkValue .blowupTwo values ![3, 0, 1] = true := by
  decide +kernel

private theorem row_33 : checkValue .blowupTwo values ![3, 1, 0] = true := by
  decide +kernel

private theorem row_34 : checkValue .blowupTwo values ![4, 0, 0] = true := by
  decide +kernel

private theorem row_35 : checkValue .blowupTwo values ![0, 0, 5] = true := by
  decide +kernel

private theorem row_36 : checkValue .blowupTwo values ![0, 1, 4] = true := by
  decide +kernel

private theorem row_37 : checkValue .blowupTwo values ![0, 2, 3] = true := by
  decide +kernel

private theorem row_38 : checkValue .blowupTwo values ![0, 3, 2] = true := by
  decide +kernel

private theorem row_39 : checkValue .blowupTwo values ![0, 4, 1] = true := by
  decide +kernel

private theorem row_40 : checkValue .blowupTwo values ![0, 5, 0] = true := by
  decide +kernel

private theorem row_41 : checkValue .blowupTwo values ![1, 0, 4] = true := by
  decide +kernel

private theorem row_42 : checkValue .blowupTwo values ![1, 1, 3] = true := by
  decide +kernel

private theorem row_43 : checkValue .blowupTwo values ![1, 2, 2] = true := by
  decide +kernel

private theorem row_44 : checkValue .blowupTwo values ![1, 3, 1] = true := by
  decide +kernel

private theorem row_45 : checkValue .blowupTwo values ![1, 4, 0] = true := by
  decide +kernel

private theorem row_46 : checkValue .blowupTwo values ![2, 0, 3] = true := by
  decide +kernel

private theorem row_47 : checkValue .blowupTwo values ![2, 1, 2] = true := by
  decide +kernel

private theorem row_48 : checkValue .blowupTwo values ![2, 2, 1] = true := by
  decide +kernel

private theorem row_49 : checkValue .blowupTwo values ![2, 3, 0] = true := by
  decide +kernel

private theorem row_50 : checkValue .blowupTwo values ![3, 0, 2] = true := by
  decide +kernel

private theorem row_51 : checkValue .blowupTwo values ![3, 1, 1] = true := by
  decide +kernel

private theorem row_52 : checkValue .blowupTwo values ![3, 2, 0] = true := by
  decide +kernel

private theorem row_53 : checkValue .blowupTwo values ![4, 0, 1] = true := by
  decide +kernel

private theorem row_54 : checkValue .blowupTwo values ![4, 1, 0] = true := by
  decide +kernel

private theorem row_55 : checkValue .blowupTwo values ![5, 0, 0] = true := by
  decide +kernel

private theorem row_56 : checkValue .blowupTwo values ![0, 0, 6] = true := by
  decide +kernel

private theorem row_57 : checkValue .blowupTwo values ![0, 1, 5] = true := by
  decide +kernel

private theorem row_58 : checkValue .blowupTwo values ![0, 2, 4] = true := by
  decide +kernel

private theorem row_59 : checkValue .blowupTwo values ![0, 3, 3] = true := by
  decide +kernel

private theorem row_60 : checkValue .blowupTwo values ![0, 4, 2] = true := by
  decide +kernel

private theorem row_61 : checkValue .blowupTwo values ![0, 5, 1] = true := by
  decide +kernel

private theorem row_62 : checkValue .blowupTwo values ![0, 6, 0] = true := by
  decide +kernel

private theorem row_63 : checkValue .blowupTwo values ![1, 0, 5] = true := by
  decide +kernel

private theorem row_64 : checkValue .blowupTwo values ![1, 1, 4] = true := by
  decide +kernel

private theorem row_65 : checkValue .blowupTwo values ![1, 2, 3] = true := by
  decide +kernel

private theorem row_66 : checkValue .blowupTwo values ![1, 3, 2] = true := by
  decide +kernel

private theorem row_67 : checkValue .blowupTwo values ![1, 4, 1] = true := by
  decide +kernel

private theorem row_68 : checkValue .blowupTwo values ![1, 5, 0] = true := by
  decide +kernel

private theorem row_69 : checkValue .blowupTwo values ![2, 0, 4] = true := by
  decide +kernel

private theorem row_70 : checkValue .blowupTwo values ![2, 1, 3] = true := by
  decide +kernel

private theorem row_71 : checkValue .blowupTwo values ![2, 2, 2] = true := by
  decide +kernel

private theorem row_72 : checkValue .blowupTwo values ![2, 3, 1] = true := by
  decide +kernel

private theorem row_73 : checkValue .blowupTwo values ![2, 4, 0] = true := by
  decide +kernel

private theorem row_74 : checkValue .blowupTwo values ![3, 0, 3] = true := by
  decide +kernel

private theorem row_75 : checkValue .blowupTwo values ![3, 1, 2] = true := by
  decide +kernel

private theorem row_76 : checkValue .blowupTwo values ![3, 2, 1] = true := by
  decide +kernel

private theorem row_77 : checkValue .blowupTwo values ![3, 3, 0] = true := by
  decide +kernel

private theorem row_78 : checkValue .blowupTwo values ![4, 0, 2] = true := by
  decide +kernel

private theorem row_79 : checkValue .blowupTwo values ![4, 1, 1] = true := by
  decide +kernel

private theorem row_80 : checkValue .blowupTwo values ![4, 2, 0] = true := by
  decide +kernel

private theorem row_81 : checkValue .blowupTwo values ![5, 0, 1] = true := by
  decide +kernel

private theorem row_82 : checkValue .blowupTwo values ![5, 1, 0] = true := by
  decide +kernel

private theorem row_83 : checkValue .blowupTwo values ![6, 0, 0] = true := by
  decide +kernel

private theorem row_84 : checkValue .blowupTwo values ![0, 0, 7] = true := by
  decide +kernel

private theorem row_85 : checkValue .blowupTwo values ![0, 1, 6] = true := by
  decide +kernel

private theorem row_86 : checkValue .blowupTwo values ![0, 2, 5] = true := by
  decide +kernel

private theorem row_87 : checkValue .blowupTwo values ![0, 3, 4] = true := by
  decide +kernel

private theorem row_88 : checkValue .blowupTwo values ![0, 4, 3] = true := by
  decide +kernel

private theorem row_89 : checkValue .blowupTwo values ![0, 5, 2] = true := by
  decide +kernel

private theorem row_90 : checkValue .blowupTwo values ![0, 6, 1] = true := by
  decide +kernel

private theorem row_91 : checkValue .blowupTwo values ![0, 7, 0] = true := by
  decide +kernel

private theorem row_92 : checkValue .blowupTwo values ![1, 0, 6] = true := by
  decide +kernel

private theorem row_93 : checkValue .blowupTwo values ![1, 1, 5] = true := by
  decide +kernel

private theorem row_94 : checkValue .blowupTwo values ![1, 2, 4] = true := by
  decide +kernel

private theorem row_95 : checkValue .blowupTwo values ![1, 3, 3] = true := by
  decide +kernel

private theorem row_96 : checkValue .blowupTwo values ![1, 4, 2] = true := by
  decide +kernel

private theorem row_97 : checkValue .blowupTwo values ![1, 5, 1] = true := by
  decide +kernel

private theorem row_98 : checkValue .blowupTwo values ![1, 6, 0] = true := by
  decide +kernel

private theorem row_99 : checkValue .blowupTwo values ![2, 0, 5] = true := by
  decide +kernel

private theorem row_100 : checkValue .blowupTwo values ![2, 1, 4] = true := by
  decide +kernel

private theorem row_101 : checkValue .blowupTwo values ![2, 2, 3] = true := by
  decide +kernel

private theorem row_102 : checkValue .blowupTwo values ![2, 3, 2] = true := by
  decide +kernel

private theorem row_103 : checkValue .blowupTwo values ![2, 4, 1] = true := by
  decide +kernel

private theorem row_104 : checkValue .blowupTwo values ![2, 5, 0] = true := by
  decide +kernel

private theorem row_105 : checkValue .blowupTwo values ![3, 0, 4] = true := by
  decide +kernel

private theorem row_106 : checkValue .blowupTwo values ![3, 1, 3] = true := by
  decide +kernel

private theorem row_107 : checkValue .blowupTwo values ![3, 2, 2] = true := by
  decide +kernel

private theorem row_108 : checkValue .blowupTwo values ![3, 3, 1] = true := by
  decide +kernel

private theorem row_109 : checkValue .blowupTwo values ![3, 4, 0] = true := by
  decide +kernel

private theorem row_110 : checkValue .blowupTwo values ![4, 0, 3] = true := by
  decide +kernel

private theorem row_111 : checkValue .blowupTwo values ![4, 1, 2] = true := by
  decide +kernel

private theorem row_112 : checkValue .blowupTwo values ![4, 2, 1] = true := by
  decide +kernel

private theorem row_113 : checkValue .blowupTwo values ![4, 3, 0] = true := by
  decide +kernel

private theorem row_114 : checkValue .blowupTwo values ![5, 0, 2] = true := by
  decide +kernel

private theorem row_115 : checkValue .blowupTwo values ![5, 1, 1] = true := by
  decide +kernel

private theorem row_116 : checkValue .blowupTwo values ![5, 2, 0] = true := by
  decide +kernel

private theorem row_117 : checkValue .blowupTwo values ![6, 0, 1] = true := by
  decide +kernel

private theorem row_118 : checkValue .blowupTwo values ![6, 1, 0] = true := by
  decide +kernel

private theorem row_119 : checkValue .blowupTwo values ![7, 0, 0] = true := by
  decide +kernel

private theorem row_120 : checkValue .blowupTwo values ![0, 0, 8] = true := by
  decide +kernel

private theorem row_121 : checkValue .blowupTwo values ![0, 1, 7] = true := by
  decide +kernel

private theorem row_122 : checkValue .blowupTwo values ![0, 2, 6] = true := by
  decide +kernel

private theorem row_123 : checkValue .blowupTwo values ![0, 3, 5] = true := by
  decide +kernel

private theorem row_124 : checkValue .blowupTwo values ![0, 4, 4] = true := by
  decide +kernel

private theorem row_125 : checkValue .blowupTwo values ![0, 5, 3] = true := by
  decide +kernel

private theorem row_126 : checkValue .blowupTwo values ![0, 6, 2] = true := by
  decide +kernel

private theorem row_127 : checkValue .blowupTwo values ![0, 7, 1] = true := by
  decide +kernel

private theorem row_128 : checkValue .blowupTwo values ![0, 8, 0] = true := by
  decide +kernel

private theorem row_129 : checkValue .blowupTwo values ![1, 0, 7] = true := by
  decide +kernel

private theorem row_130 : checkValue .blowupTwo values ![1, 1, 6] = true := by
  decide +kernel

private theorem row_131 : checkValue .blowupTwo values ![1, 2, 5] = true := by
  decide +kernel

private theorem row_132 : checkValue .blowupTwo values ![1, 3, 4] = true := by
  decide +kernel

private theorem row_133 : checkValue .blowupTwo values ![1, 4, 3] = true := by
  decide +kernel

private theorem row_134 : checkValue .blowupTwo values ![1, 5, 2] = true := by
  decide +kernel

private theorem row_135 : checkValue .blowupTwo values ![1, 6, 1] = true := by
  decide +kernel

private theorem row_136 : checkValue .blowupTwo values ![1, 7, 0] = true := by
  decide +kernel

private theorem row_137 : checkValue .blowupTwo values ![2, 0, 6] = true := by
  decide +kernel

private theorem row_138 : checkValue .blowupTwo values ![2, 1, 5] = true := by
  decide +kernel

private theorem row_139 : checkValue .blowupTwo values ![2, 2, 4] = true := by
  decide +kernel

private theorem row_140 : checkValue .blowupTwo values ![2, 3, 3] = true := by
  decide +kernel

private theorem row_141 : checkValue .blowupTwo values ![2, 4, 2] = true := by
  decide +kernel

private theorem row_142 : checkValue .blowupTwo values ![2, 5, 1] = true := by
  decide +kernel

private theorem row_143 : checkValue .blowupTwo values ![2, 6, 0] = true := by
  decide +kernel

private theorem row_144 : checkValue .blowupTwo values ![3, 0, 5] = true := by
  decide +kernel

private theorem row_145 : checkValue .blowupTwo values ![3, 1, 4] = true := by
  decide +kernel

private theorem row_146 : checkValue .blowupTwo values ![3, 2, 3] = true := by
  decide +kernel

private theorem row_147 : checkValue .blowupTwo values ![3, 3, 2] = true := by
  decide +kernel

private theorem row_148 : checkValue .blowupTwo values ![3, 4, 1] = true := by
  decide +kernel

private theorem row_149 : checkValue .blowupTwo values ![3, 5, 0] = true := by
  decide +kernel

private theorem row_150 : checkValue .blowupTwo values ![4, 0, 4] = true := by
  decide +kernel

private theorem row_151 : checkValue .blowupTwo values ![4, 1, 3] = true := by
  decide +kernel

private theorem row_152 : checkValue .blowupTwo values ![4, 2, 2] = true := by
  decide +kernel

private theorem row_153 : checkValue .blowupTwo values ![4, 3, 1] = true := by
  decide +kernel

private theorem row_154 : checkValue .blowupTwo values ![4, 4, 0] = true := by
  decide +kernel

private theorem row_155 : checkValue .blowupTwo values ![5, 0, 3] = true := by
  decide +kernel

private theorem row_156 : checkValue .blowupTwo values ![5, 1, 2] = true := by
  decide +kernel

private theorem row_157 : checkValue .blowupTwo values ![5, 2, 1] = true := by
  decide +kernel

private theorem row_158 : checkValue .blowupTwo values ![5, 3, 0] = true := by
  decide +kernel

private theorem row_159 : checkValue .blowupTwo values ![6, 0, 2] = true := by
  decide +kernel

private theorem row_160 : checkValue .blowupTwo values ![6, 1, 1] = true := by
  decide +kernel

private theorem row_161 : checkValue .blowupTwo values ![6, 2, 0] = true := by
  decide +kernel

private theorem row_162 : checkValue .blowupTwo values ![7, 0, 1] = true := by
  decide +kernel

private theorem row_163 : checkValue .blowupTwo values ![7, 1, 0] = true := by
  decide +kernel

private theorem row_164 : checkValue .blowupTwo values ![8, 0, 0] = true := by
  decide +kernel

private theorem row_165 : checkValue .blowupTwo values ![0, 0, 9] = true := by
  decide +kernel

private theorem row_166 : checkValue .blowupTwo values ![0, 1, 8] = true := by
  decide +kernel

private theorem row_167 : checkValue .blowupTwo values ![0, 2, 7] = true := by
  decide +kernel

private theorem row_168 : checkValue .blowupTwo values ![0, 3, 6] = true := by
  decide +kernel

private theorem row_169 : checkValue .blowupTwo values ![0, 4, 5] = true := by
  decide +kernel

private theorem row_170 : checkValue .blowupTwo values ![0, 5, 4] = true := by
  decide +kernel

private theorem row_171 : checkValue .blowupTwo values ![0, 6, 3] = true := by
  decide +kernel

private theorem row_172 : checkValue .blowupTwo values ![0, 7, 2] = true := by
  decide +kernel

private theorem row_173 : checkValue .blowupTwo values ![0, 8, 1] = true := by
  decide +kernel

private theorem row_174 : checkValue .blowupTwo values ![0, 9, 0] = true := by
  decide +kernel

private theorem row_175 : checkValue .blowupTwo values ![1, 0, 8] = true := by
  decide +kernel

private theorem row_176 : checkValue .blowupTwo values ![1, 1, 7] = true := by
  decide +kernel

private theorem row_177 : checkValue .blowupTwo values ![1, 2, 6] = true := by
  decide +kernel

private theorem row_178 : checkValue .blowupTwo values ![1, 3, 5] = true := by
  decide +kernel

private theorem row_179 : checkValue .blowupTwo values ![1, 4, 4] = true := by
  decide +kernel

private theorem row_180 : checkValue .blowupTwo values ![1, 5, 3] = true := by
  decide +kernel

private theorem row_181 : checkValue .blowupTwo values ![1, 6, 2] = true := by
  decide +kernel

private theorem row_182 : checkValue .blowupTwo values ![1, 7, 1] = true := by
  decide +kernel

private theorem row_183 : checkValue .blowupTwo values ![1, 8, 0] = true := by
  decide +kernel

private theorem row_184 : checkValue .blowupTwo values ![2, 0, 7] = true := by
  decide +kernel

private theorem row_185 : checkValue .blowupTwo values ![2, 1, 6] = true := by
  decide +kernel

private theorem row_186 : checkValue .blowupTwo values ![2, 2, 5] = true := by
  decide +kernel

private theorem row_187 : checkValue .blowupTwo values ![2, 3, 4] = true := by
  decide +kernel

private theorem row_188 : checkValue .blowupTwo values ![2, 4, 3] = true := by
  decide +kernel

private theorem row_189 : checkValue .blowupTwo values ![2, 5, 2] = true := by
  decide +kernel

private theorem row_190 : checkValue .blowupTwo values ![2, 6, 1] = true := by
  decide +kernel

private theorem row_191 : checkValue .blowupTwo values ![2, 7, 0] = true := by
  decide +kernel

private theorem row_192 : checkValue .blowupTwo values ![3, 0, 6] = true := by
  decide +kernel

private theorem row_193 : checkValue .blowupTwo values ![3, 1, 5] = true := by
  decide +kernel

private theorem row_194 : checkValue .blowupTwo values ![3, 2, 4] = true := by
  decide +kernel

private theorem row_195 : checkValue .blowupTwo values ![3, 3, 3] = true := by
  decide +kernel

private theorem row_196 : checkValue .blowupTwo values ![3, 4, 2] = true := by
  decide +kernel

private theorem row_197 : checkValue .blowupTwo values ![3, 5, 1] = true := by
  decide +kernel

private theorem row_198 : checkValue .blowupTwo values ![3, 6, 0] = true := by
  decide +kernel

private theorem row_199 : checkValue .blowupTwo values ![4, 0, 5] = true := by
  decide +kernel

private theorem row_200 : checkValue .blowupTwo values ![4, 1, 4] = true := by
  decide +kernel

private theorem row_201 : checkValue .blowupTwo values ![4, 2, 3] = true := by
  decide +kernel

private theorem row_202 : checkValue .blowupTwo values ![4, 3, 2] = true := by
  decide +kernel

private theorem row_203 : checkValue .blowupTwo values ![4, 4, 1] = true := by
  decide +kernel

private theorem row_204 : checkValue .blowupTwo values ![4, 5, 0] = true := by
  decide +kernel

private theorem row_205 : checkValue .blowupTwo values ![5, 0, 4] = true := by
  decide +kernel

private theorem row_206 : checkValue .blowupTwo values ![5, 1, 3] = true := by
  decide +kernel

private theorem row_207 : checkValue .blowupTwo values ![5, 2, 2] = true := by
  decide +kernel

private theorem row_208 : checkValue .blowupTwo values ![5, 3, 1] = true := by
  decide +kernel

private theorem row_209 : checkValue .blowupTwo values ![5, 4, 0] = true := by
  decide +kernel

private theorem row_210 : checkValue .blowupTwo values ![6, 0, 3] = true := by
  decide +kernel

private theorem row_211 : checkValue .blowupTwo values ![6, 1, 2] = true := by
  decide +kernel

private theorem row_212 : checkValue .blowupTwo values ![6, 2, 1] = true := by
  decide +kernel

private theorem row_213 : checkValue .blowupTwo values ![6, 3, 0] = true := by
  decide +kernel

private theorem row_214 : checkValue .blowupTwo values ![7, 0, 2] = true := by
  decide +kernel

private theorem row_215 : checkValue .blowupTwo values ![7, 1, 1] = true := by
  decide +kernel

private theorem row_216 : checkValue .blowupTwo values ![7, 2, 0] = true := by
  decide +kernel

private theorem row_217 : checkValue .blowupTwo values ![8, 0, 1] = true := by
  decide +kernel

private theorem row_218 : checkValue .blowupTwo values ![8, 1, 0] = true := by
  decide +kernel

private theorem row_219 : checkValue .blowupTwo values ![9, 0, 0] = true := by
  decide +kernel

private theorem row_220 : checkValue .blowupTwo values ![0, 0, 10] = true := by
  decide +kernel

private theorem row_221 : checkValue .blowupTwo values ![0, 1, 9] = true := by
  decide +kernel

private theorem row_222 : checkValue .blowupTwo values ![0, 2, 8] = true := by
  decide +kernel

private theorem row_223 : checkValue .blowupTwo values ![0, 3, 7] = true := by
  decide +kernel

private theorem row_224 : checkValue .blowupTwo values ![0, 4, 6] = true := by
  decide +kernel

private theorem row_225 : checkValue .blowupTwo values ![0, 5, 5] = true := by
  decide +kernel

private theorem row_226 : checkValue .blowupTwo values ![0, 6, 4] = true := by
  decide +kernel

private theorem row_227 : checkValue .blowupTwo values ![0, 7, 3] = true := by
  decide +kernel

private theorem row_228 : checkValue .blowupTwo values ![0, 8, 2] = true := by
  decide +kernel

private theorem row_229 : checkValue .blowupTwo values ![0, 9, 1] = true := by
  decide +kernel

private theorem row_230 : checkValue .blowupTwo values ![0, 10, 0] = true := by
  decide +kernel

private theorem row_231 : checkValue .blowupTwo values ![1, 0, 9] = true := by
  decide +kernel

private theorem row_232 : checkValue .blowupTwo values ![1, 1, 8] = true := by
  decide +kernel

private theorem row_233 : checkValue .blowupTwo values ![1, 2, 7] = true := by
  decide +kernel

private theorem row_234 : checkValue .blowupTwo values ![1, 3, 6] = true := by
  decide +kernel

private theorem row_235 : checkValue .blowupTwo values ![1, 4, 5] = true := by
  decide +kernel

private theorem row_236 : checkValue .blowupTwo values ![1, 5, 4] = true := by
  decide +kernel

private theorem row_237 : checkValue .blowupTwo values ![1, 6, 3] = true := by
  decide +kernel

private theorem row_238 : checkValue .blowupTwo values ![1, 7, 2] = true := by
  decide +kernel

private theorem row_239 : checkValue .blowupTwo values ![1, 8, 1] = true := by
  decide +kernel

private theorem row_240 : checkValue .blowupTwo values ![1, 9, 0] = true := by
  decide +kernel

private theorem row_241 : checkValue .blowupTwo values ![2, 0, 8] = true := by
  decide +kernel

private theorem row_242 : checkValue .blowupTwo values ![2, 1, 7] = true := by
  decide +kernel

private theorem row_243 : checkValue .blowupTwo values ![2, 2, 6] = true := by
  decide +kernel

private theorem row_244 : checkValue .blowupTwo values ![2, 3, 5] = true := by
  decide +kernel

private theorem row_245 : checkValue .blowupTwo values ![2, 4, 4] = true := by
  decide +kernel

private theorem row_246 : checkValue .blowupTwo values ![2, 5, 3] = true := by
  decide +kernel

private theorem row_247 : checkValue .blowupTwo values ![2, 6, 2] = true := by
  decide +kernel

private theorem row_248 : checkValue .blowupTwo values ![2, 7, 1] = true := by
  decide +kernel

private theorem row_249 : checkValue .blowupTwo values ![2, 8, 0] = true := by
  decide +kernel

private theorem row_250 : checkValue .blowupTwo values ![3, 0, 7] = true := by
  decide +kernel

private theorem row_251 : checkValue .blowupTwo values ![3, 1, 6] = true := by
  decide +kernel

private theorem row_252 : checkValue .blowupTwo values ![3, 2, 5] = true := by
  decide +kernel

private theorem row_253 : checkValue .blowupTwo values ![3, 3, 4] = true := by
  decide +kernel

private theorem row_254 : checkValue .blowupTwo values ![3, 4, 3] = true := by
  decide +kernel

private theorem row_255 : checkValue .blowupTwo values ![3, 5, 2] = true := by
  decide +kernel

private theorem row_256 : checkValue .blowupTwo values ![3, 6, 1] = true := by
  decide +kernel

private theorem row_257 : checkValue .blowupTwo values ![3, 7, 0] = true := by
  decide +kernel

private theorem row_258 : checkValue .blowupTwo values ![4, 0, 6] = true := by
  decide +kernel

private theorem row_259 : checkValue .blowupTwo values ![4, 1, 5] = true := by
  decide +kernel

private theorem row_260 : checkValue .blowupTwo values ![4, 2, 4] = true := by
  decide +kernel

private theorem row_261 : checkValue .blowupTwo values ![4, 3, 3] = true := by
  decide +kernel

private theorem row_262 : checkValue .blowupTwo values ![4, 4, 2] = true := by
  decide +kernel

private theorem row_263 : checkValue .blowupTwo values ![4, 5, 1] = true := by
  decide +kernel

private theorem row_264 : checkValue .blowupTwo values ![4, 6, 0] = true := by
  decide +kernel

private theorem row_265 : checkValue .blowupTwo values ![5, 0, 5] = true := by
  decide +kernel

private theorem row_266 : checkValue .blowupTwo values ![5, 1, 4] = true := by
  decide +kernel

private theorem row_267 : checkValue .blowupTwo values ![5, 2, 3] = true := by
  decide +kernel

private theorem row_268 : checkValue .blowupTwo values ![5, 3, 2] = true := by
  decide +kernel

private theorem row_269 : checkValue .blowupTwo values ![5, 4, 1] = true := by
  decide +kernel

private theorem row_270 : checkValue .blowupTwo values ![5, 5, 0] = true := by
  decide +kernel

private theorem row_271 : checkValue .blowupTwo values ![6, 0, 4] = true := by
  decide +kernel

private theorem row_272 : checkValue .blowupTwo values ![6, 1, 3] = true := by
  decide +kernel

private theorem row_273 : checkValue .blowupTwo values ![6, 2, 2] = true := by
  decide +kernel

private theorem row_274 : checkValue .blowupTwo values ![6, 3, 1] = true := by
  decide +kernel

private theorem row_275 : checkValue .blowupTwo values ![6, 4, 0] = true := by
  decide +kernel

private theorem row_276 : checkValue .blowupTwo values ![7, 0, 3] = true := by
  decide +kernel

private theorem row_277 : checkValue .blowupTwo values ![7, 1, 2] = true := by
  decide +kernel

private theorem row_278 : checkValue .blowupTwo values ![7, 2, 1] = true := by
  decide +kernel

private theorem row_279 : checkValue .blowupTwo values ![7, 3, 0] = true := by
  decide +kernel

private theorem row_280 : checkValue .blowupTwo values ![8, 0, 2] = true := by
  decide +kernel

private theorem row_281 : checkValue .blowupTwo values ![8, 1, 1] = true := by
  decide +kernel

private theorem row_282 : checkValue .blowupTwo values ![8, 2, 0] = true := by
  decide +kernel

private theorem row_283 : checkValue .blowupTwo values ![9, 0, 1] = true := by
  decide +kernel

private theorem row_284 : checkValue .blowupTwo values ![9, 1, 0] = true := by
  decide +kernel

private theorem row_285 : checkValue .blowupTwo values ![10, 0, 0] = true := by
  decide +kernel

private theorem row_286 : checkValue .blowupTwo values ![0, 0, 11] = true := by
  decide +kernel

private theorem row_287 : checkValue .blowupTwo values ![0, 1, 10] = true := by
  decide +kernel

private theorem row_288 : checkValue .blowupTwo values ![0, 2, 9] = true := by
  decide +kernel

private theorem row_289 : checkValue .blowupTwo values ![0, 3, 8] = true := by
  decide +kernel

private theorem row_290 : checkValue .blowupTwo values ![0, 4, 7] = true := by
  decide +kernel

private theorem row_291 : checkValue .blowupTwo values ![0, 5, 6] = true := by
  decide +kernel

private theorem row_292 : checkValue .blowupTwo values ![0, 6, 5] = true := by
  decide +kernel

private theorem row_293 : checkValue .blowupTwo values ![0, 7, 4] = true := by
  decide +kernel

private theorem row_294 : checkValue .blowupTwo values ![0, 8, 3] = true := by
  decide +kernel

private theorem row_295 : checkValue .blowupTwo values ![0, 9, 2] = true := by
  decide +kernel

private theorem row_296 : checkValue .blowupTwo values ![0, 10, 1] = true := by
  decide +kernel

private theorem row_297 : checkValue .blowupTwo values ![0, 11, 0] = true := by
  decide +kernel

private theorem row_298 : checkValue .blowupTwo values ![1, 0, 10] = true := by
  decide +kernel

private theorem row_299 : checkValue .blowupTwo values ![1, 1, 9] = true := by
  decide +kernel

private theorem row_300 : checkValue .blowupTwo values ![1, 2, 8] = true := by
  decide +kernel

private theorem row_301 : checkValue .blowupTwo values ![1, 3, 7] = true := by
  decide +kernel

private theorem row_302 : checkValue .blowupTwo values ![1, 4, 6] = true := by
  decide +kernel

private theorem row_303 : checkValue .blowupTwo values ![1, 5, 5] = true := by
  decide +kernel

private theorem row_304 : checkValue .blowupTwo values ![1, 6, 4] = true := by
  decide +kernel

private theorem row_305 : checkValue .blowupTwo values ![1, 7, 3] = true := by
  decide +kernel

private theorem row_306 : checkValue .blowupTwo values ![1, 8, 2] = true := by
  decide +kernel

private theorem row_307 : checkValue .blowupTwo values ![1, 9, 1] = true := by
  decide +kernel

private theorem row_308 : checkValue .blowupTwo values ![1, 10, 0] = true := by
  decide +kernel

private theorem row_309 : checkValue .blowupTwo values ![2, 0, 9] = true := by
  decide +kernel

private theorem row_310 : checkValue .blowupTwo values ![2, 1, 8] = true := by
  decide +kernel

private theorem row_311 : checkValue .blowupTwo values ![2, 2, 7] = true := by
  decide +kernel

private theorem row_312 : checkValue .blowupTwo values ![2, 3, 6] = true := by
  decide +kernel

private theorem row_313 : checkValue .blowupTwo values ![2, 4, 5] = true := by
  decide +kernel

private theorem row_314 : checkValue .blowupTwo values ![2, 5, 4] = true := by
  decide +kernel

private theorem row_315 : checkValue .blowupTwo values ![2, 6, 3] = true := by
  decide +kernel

private theorem row_316 : checkValue .blowupTwo values ![2, 7, 2] = true := by
  decide +kernel

private theorem row_317 : checkValue .blowupTwo values ![2, 8, 1] = true := by
  decide +kernel

private theorem row_318 : checkValue .blowupTwo values ![2, 9, 0] = true := by
  decide +kernel

private theorem row_319 : checkValue .blowupTwo values ![3, 0, 8] = true := by
  decide +kernel

private theorem row_320 : checkValue .blowupTwo values ![3, 1, 7] = true := by
  decide +kernel

private theorem row_321 : checkValue .blowupTwo values ![3, 2, 6] = true := by
  decide +kernel

private theorem row_322 : checkValue .blowupTwo values ![3, 3, 5] = true := by
  decide +kernel

private theorem row_323 : checkValue .blowupTwo values ![3, 4, 4] = true := by
  decide +kernel

private theorem row_324 : checkValue .blowupTwo values ![3, 5, 3] = true := by
  decide +kernel

private theorem row_325 : checkValue .blowupTwo values ![3, 6, 2] = true := by
  decide +kernel

private theorem row_326 : checkValue .blowupTwo values ![3, 7, 1] = true := by
  decide +kernel

private theorem row_327 : checkValue .blowupTwo values ![3, 8, 0] = true := by
  decide +kernel

private theorem row_328 : checkValue .blowupTwo values ![4, 0, 7] = true := by
  decide +kernel

private theorem row_329 : checkValue .blowupTwo values ![4, 1, 6] = true := by
  decide +kernel

private theorem row_330 : checkValue .blowupTwo values ![4, 2, 5] = true := by
  decide +kernel

private theorem row_331 : checkValue .blowupTwo values ![4, 3, 4] = true := by
  decide +kernel

private theorem row_332 : checkValue .blowupTwo values ![4, 4, 3] = true := by
  decide +kernel

private theorem row_333 : checkValue .blowupTwo values ![4, 5, 2] = true := by
  decide +kernel

private theorem row_334 : checkValue .blowupTwo values ![4, 6, 1] = true := by
  decide +kernel

private theorem row_335 : checkValue .blowupTwo values ![4, 7, 0] = true := by
  decide +kernel

private theorem row_336 : checkValue .blowupTwo values ![5, 0, 6] = true := by
  decide +kernel

private theorem row_337 : checkValue .blowupTwo values ![5, 1, 5] = true := by
  decide +kernel

private theorem row_338 : checkValue .blowupTwo values ![5, 2, 4] = true := by
  decide +kernel

private theorem row_339 : checkValue .blowupTwo values ![5, 3, 3] = true := by
  decide +kernel

private theorem row_340 : checkValue .blowupTwo values ![5, 4, 2] = true := by
  decide +kernel

private theorem row_341 : checkValue .blowupTwo values ![5, 5, 1] = true := by
  decide +kernel

private theorem row_342 : checkValue .blowupTwo values ![5, 6, 0] = true := by
  decide +kernel

private theorem row_343 : checkValue .blowupTwo values ![6, 0, 5] = true := by
  decide +kernel

private theorem row_344 : checkValue .blowupTwo values ![6, 1, 4] = true := by
  decide +kernel

private theorem row_345 : checkValue .blowupTwo values ![6, 2, 3] = true := by
  decide +kernel

private theorem row_346 : checkValue .blowupTwo values ![6, 3, 2] = true := by
  decide +kernel

private theorem row_347 : checkValue .blowupTwo values ![6, 4, 1] = true := by
  decide +kernel

private theorem row_348 : checkValue .blowupTwo values ![6, 5, 0] = true := by
  decide +kernel

private theorem row_349 : checkValue .blowupTwo values ![7, 0, 4] = true := by
  decide +kernel

private theorem row_350 : checkValue .blowupTwo values ![7, 1, 3] = true := by
  decide +kernel

private theorem row_351 : checkValue .blowupTwo values ![7, 2, 2] = true := by
  decide +kernel

private theorem row_352 : checkValue .blowupTwo values ![7, 3, 1] = true := by
  decide +kernel

private theorem row_353 : checkValue .blowupTwo values ![7, 4, 0] = true := by
  decide +kernel

private theorem row_354 : checkValue .blowupTwo values ![8, 0, 3] = true := by
  decide +kernel

private theorem row_355 : checkValue .blowupTwo values ![8, 1, 2] = true := by
  decide +kernel

private theorem row_356 : checkValue .blowupTwo values ![8, 2, 1] = true := by
  decide +kernel

private theorem row_357 : checkValue .blowupTwo values ![8, 3, 0] = true := by
  decide +kernel

private theorem row_358 : checkValue .blowupTwo values ![9, 0, 2] = true := by
  decide +kernel

private theorem row_359 : checkValue .blowupTwo values ![9, 1, 1] = true := by
  decide +kernel

private theorem row_360 : checkValue .blowupTwo values ![9, 2, 0] = true := by
  decide +kernel

private theorem row_361 : checkValue .blowupTwo values ![10, 0, 1] = true := by
  decide +kernel

private theorem row_362 : checkValue .blowupTwo values ![10, 1, 0] = true := by
  decide +kernel

private theorem row_363 : checkValue .blowupTwo values ![11, 0, 0] = true := by
  decide +kernel

private theorem row_364 : checkValue .blowupTwo values ![0, 0, 12] = true := by
  decide +kernel

private theorem row_365 : checkValue .blowupTwo values ![0, 1, 11] = true := by
  decide +kernel

private theorem row_366 : checkValue .blowupTwo values ![0, 2, 10] = true := by
  decide +kernel

private theorem row_367 : checkValue .blowupTwo values ![0, 3, 9] = true := by
  decide +kernel

private theorem row_368 : checkValue .blowupTwo values ![0, 4, 8] = true := by
  decide +kernel

private theorem row_369 : checkValue .blowupTwo values ![0, 5, 7] = true := by
  decide +kernel

private theorem row_370 : checkValue .blowupTwo values ![0, 6, 6] = true := by
  decide +kernel

private theorem row_371 : checkValue .blowupTwo values ![0, 7, 5] = true := by
  decide +kernel

private theorem row_372 : checkValue .blowupTwo values ![0, 8, 4] = true := by
  decide +kernel

private theorem row_373 : checkValue .blowupTwo values ![0, 9, 3] = true := by
  decide +kernel

private theorem row_374 : checkValue .blowupTwo values ![0, 10, 2] = true := by
  decide +kernel

private theorem row_375 : checkValue .blowupTwo values ![0, 11, 1] = true := by
  decide +kernel

private theorem row_376 : checkValue .blowupTwo values ![0, 12, 0] = true := by
  decide +kernel

private theorem row_377 : checkValue .blowupTwo values ![1, 0, 11] = true := by
  decide +kernel

private theorem row_378 : checkValue .blowupTwo values ![1, 1, 10] = true := by
  decide +kernel

private theorem row_379 : checkValue .blowupTwo values ![1, 2, 9] = true := by
  decide +kernel

private theorem row_380 : checkValue .blowupTwo values ![1, 3, 8] = true := by
  decide +kernel

private theorem row_381 : checkValue .blowupTwo values ![1, 4, 7] = true := by
  decide +kernel

private theorem row_382 : checkValue .blowupTwo values ![1, 5, 6] = true := by
  decide +kernel

private theorem row_383 : checkValue .blowupTwo values ![1, 6, 5] = true := by
  decide +kernel

private theorem row_384 : checkValue .blowupTwo values ![1, 7, 4] = true := by
  decide +kernel

private theorem row_385 : checkValue .blowupTwo values ![1, 8, 3] = true := by
  decide +kernel

private theorem row_386 : checkValue .blowupTwo values ![1, 9, 2] = true := by
  decide +kernel

private theorem row_387 : checkValue .blowupTwo values ![1, 10, 1] = true := by
  decide +kernel

private theorem row_388 : checkValue .blowupTwo values ![1, 11, 0] = true := by
  decide +kernel

private theorem row_389 : checkValue .blowupTwo values ![2, 0, 10] = true := by
  decide +kernel

private theorem row_390 : checkValue .blowupTwo values ![2, 1, 9] = true := by
  decide +kernel

private theorem row_391 : checkValue .blowupTwo values ![2, 2, 8] = true := by
  decide +kernel

private theorem row_392 : checkValue .blowupTwo values ![2, 3, 7] = true := by
  decide +kernel

private theorem row_393 : checkValue .blowupTwo values ![2, 4, 6] = true := by
  decide +kernel

private theorem row_394 : checkValue .blowupTwo values ![2, 5, 5] = true := by
  decide +kernel

private theorem row_395 : checkValue .blowupTwo values ![2, 6, 4] = true := by
  decide +kernel

private theorem row_396 : checkValue .blowupTwo values ![2, 7, 3] = true := by
  decide +kernel

private theorem row_397 : checkValue .blowupTwo values ![2, 8, 2] = true := by
  decide +kernel

private theorem row_398 : checkValue .blowupTwo values ![2, 9, 1] = true := by
  decide +kernel

private theorem row_399 : checkValue .blowupTwo values ![2, 10, 0] = true := by
  decide +kernel

private theorem row_400 : checkValue .blowupTwo values ![3, 0, 9] = true := by
  decide +kernel

private theorem row_401 : checkValue .blowupTwo values ![3, 1, 8] = true := by
  decide +kernel

private theorem row_402 : checkValue .blowupTwo values ![3, 2, 7] = true := by
  decide +kernel

private theorem row_403 : checkValue .blowupTwo values ![3, 3, 6] = true := by
  decide +kernel

private theorem row_404 : checkValue .blowupTwo values ![3, 4, 5] = true := by
  decide +kernel

private theorem row_405 : checkValue .blowupTwo values ![3, 5, 4] = true := by
  decide +kernel

private theorem row_406 : checkValue .blowupTwo values ![3, 6, 3] = true := by
  decide +kernel

private theorem row_407 : checkValue .blowupTwo values ![3, 7, 2] = true := by
  decide +kernel

private theorem row_408 : checkValue .blowupTwo values ![3, 8, 1] = true := by
  decide +kernel

private theorem row_409 : checkValue .blowupTwo values ![3, 9, 0] = true := by
  decide +kernel

private theorem row_410 : checkValue .blowupTwo values ![4, 0, 8] = true := by
  decide +kernel

private theorem row_411 : checkValue .blowupTwo values ![4, 1, 7] = true := by
  decide +kernel

private theorem row_412 : checkValue .blowupTwo values ![4, 2, 6] = true := by
  decide +kernel

private theorem row_413 : checkValue .blowupTwo values ![4, 3, 5] = true := by
  decide +kernel

private theorem row_414 : checkValue .blowupTwo values ![4, 4, 4] = true := by
  decide +kernel

private theorem row_415 : checkValue .blowupTwo values ![4, 5, 3] = true := by
  decide +kernel

private theorem row_416 : checkValue .blowupTwo values ![4, 6, 2] = true := by
  decide +kernel

private theorem row_417 : checkValue .blowupTwo values ![4, 7, 1] = true := by
  decide +kernel

private theorem row_418 : checkValue .blowupTwo values ![4, 8, 0] = true := by
  decide +kernel

private theorem row_419 : checkValue .blowupTwo values ![5, 0, 7] = true := by
  decide +kernel

private theorem row_420 : checkValue .blowupTwo values ![5, 1, 6] = true := by
  decide +kernel

private theorem row_421 : checkValue .blowupTwo values ![5, 2, 5] = true := by
  decide +kernel

private theorem row_422 : checkValue .blowupTwo values ![5, 3, 4] = true := by
  decide +kernel

private theorem row_423 : checkValue .blowupTwo values ![5, 4, 3] = true := by
  decide +kernel

private theorem row_424 : checkValue .blowupTwo values ![5, 5, 2] = true := by
  decide +kernel

private theorem row_425 : checkValue .blowupTwo values ![5, 6, 1] = true := by
  decide +kernel

private theorem row_426 : checkValue .blowupTwo values ![5, 7, 0] = true := by
  decide +kernel

private theorem row_427 : checkValue .blowupTwo values ![6, 0, 6] = true := by
  decide +kernel

private theorem row_428 : checkValue .blowupTwo values ![6, 1, 5] = true := by
  decide +kernel

private theorem row_429 : checkValue .blowupTwo values ![6, 2, 4] = true := by
  decide +kernel

private theorem row_430 : checkValue .blowupTwo values ![6, 3, 3] = true := by
  decide +kernel

private theorem row_431 : checkValue .blowupTwo values ![6, 4, 2] = true := by
  decide +kernel

private theorem row_432 : checkValue .blowupTwo values ![6, 5, 1] = true := by
  decide +kernel

private theorem row_433 : checkValue .blowupTwo values ![6, 6, 0] = true := by
  decide +kernel

private theorem row_434 : checkValue .blowupTwo values ![7, 0, 5] = true := by
  decide +kernel

private theorem row_435 : checkValue .blowupTwo values ![7, 1, 4] = true := by
  decide +kernel

private theorem row_436 : checkValue .blowupTwo values ![7, 2, 3] = true := by
  decide +kernel

private theorem row_437 : checkValue .blowupTwo values ![7, 3, 2] = true := by
  decide +kernel

private theorem row_438 : checkValue .blowupTwo values ![7, 4, 1] = true := by
  decide +kernel

private theorem row_439 : checkValue .blowupTwo values ![7, 5, 0] = true := by
  decide +kernel

private theorem row_440 : checkValue .blowupTwo values ![8, 0, 4] = true := by
  decide +kernel

private theorem row_441 : checkValue .blowupTwo values ![8, 1, 3] = true := by
  decide +kernel

private theorem row_442 : checkValue .blowupTwo values ![8, 2, 2] = true := by
  decide +kernel

private theorem row_443 : checkValue .blowupTwo values ![8, 3, 1] = true := by
  decide +kernel

private theorem row_444 : checkValue .blowupTwo values ![8, 4, 0] = true := by
  decide +kernel

private theorem row_445 : checkValue .blowupTwo values ![9, 0, 3] = true := by
  decide +kernel

private theorem row_446 : checkValue .blowupTwo values ![9, 1, 2] = true := by
  decide +kernel

private theorem row_447 : checkValue .blowupTwo values ![9, 2, 1] = true := by
  decide +kernel

private theorem row_448 : checkValue .blowupTwo values ![9, 3, 0] = true := by
  decide +kernel

private theorem row_449 : checkValue .blowupTwo values ![10, 0, 2] = true := by
  decide +kernel

private theorem row_450 : checkValue .blowupTwo values ![10, 1, 1] = true := by
  decide +kernel

private theorem row_451 : checkValue .blowupTwo values ![10, 2, 0] = true := by
  decide +kernel

private theorem row_452 : checkValue .blowupTwo values ![11, 0, 1] = true := by
  decide +kernel

private theorem row_453 : checkValue .blowupTwo values ![11, 1, 0] = true := by
  decide +kernel

private theorem row_454 : checkValue .blowupTwo values ![12, 0, 0] = true := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- Every candidate equation is checked on literal tuples, including all zeros. -/
theorem rows_checked : classes.all (checkValue .blowupTwo values) = true := by
  simp only [classes, List.all_cons, List.all_nil,
    row_0, row_1, row_2, row_3, row_4, row_5, row_6, row_7,
    row_8, row_9, row_10, row_11, row_12, row_13, row_14, row_15,
    row_16, row_17, row_18, row_19, row_20, row_21, row_22, row_23,
    row_24, row_25, row_26, row_27, row_28, row_29, row_30, row_31,
    row_32, row_33, row_34, row_35, row_36, row_37, row_38, row_39,
    row_40, row_41, row_42, row_43, row_44, row_45, row_46, row_47,
    row_48, row_49, row_50, row_51, row_52, row_53, row_54, row_55,
    row_56, row_57, row_58, row_59, row_60, row_61, row_62, row_63,
    row_64, row_65, row_66, row_67, row_68, row_69, row_70, row_71,
    row_72, row_73, row_74, row_75, row_76, row_77, row_78, row_79,
    row_80, row_81, row_82, row_83, row_84, row_85, row_86, row_87,
    row_88, row_89, row_90, row_91, row_92, row_93, row_94, row_95,
    row_96, row_97, row_98, row_99, row_100, row_101, row_102, row_103,
    row_104, row_105, row_106, row_107, row_108, row_109, row_110, row_111,
    row_112, row_113, row_114, row_115, row_116, row_117, row_118, row_119,
    row_120, row_121, row_122, row_123, row_124, row_125, row_126, row_127,
    row_128, row_129, row_130, row_131, row_132, row_133, row_134, row_135,
    row_136, row_137, row_138, row_139, row_140, row_141, row_142, row_143,
    row_144, row_145, row_146, row_147, row_148, row_149, row_150, row_151,
    row_152, row_153, row_154, row_155, row_156, row_157, row_158, row_159,
    row_160, row_161, row_162, row_163, row_164, row_165, row_166, row_167,
    row_168, row_169, row_170, row_171, row_172, row_173, row_174, row_175,
    row_176, row_177, row_178, row_179, row_180, row_181, row_182, row_183,
    row_184, row_185, row_186, row_187, row_188, row_189, row_190, row_191,
    row_192, row_193, row_194, row_195, row_196, row_197, row_198, row_199,
    row_200, row_201, row_202, row_203, row_204, row_205, row_206, row_207,
    row_208, row_209, row_210, row_211, row_212, row_213, row_214, row_215,
    row_216, row_217, row_218, row_219, row_220, row_221, row_222, row_223,
    row_224, row_225, row_226, row_227, row_228, row_229, row_230, row_231,
    row_232, row_233, row_234, row_235, row_236, row_237, row_238, row_239,
    row_240, row_241, row_242, row_243, row_244, row_245, row_246, row_247,
    row_248, row_249, row_250, row_251, row_252, row_253, row_254, row_255,
    row_256, row_257, row_258, row_259, row_260, row_261, row_262, row_263,
    row_264, row_265, row_266, row_267, row_268, row_269, row_270, row_271,
    row_272, row_273, row_274, row_275, row_276, row_277, row_278, row_279,
    row_280, row_281, row_282, row_283, row_284, row_285, row_286, row_287,
    row_288, row_289, row_290, row_291, row_292, row_293, row_294, row_295,
    row_296, row_297, row_298, row_299, row_300, row_301, row_302, row_303,
    row_304, row_305, row_306, row_307, row_308, row_309, row_310, row_311,
    row_312, row_313, row_314, row_315, row_316, row_317, row_318, row_319,
    row_320, row_321, row_322, row_323, row_324, row_325, row_326, row_327,
    row_328, row_329, row_330, row_331, row_332, row_333, row_334, row_335,
    row_336, row_337, row_338, row_339, row_340, row_341, row_342, row_343,
    row_344, row_345, row_346, row_347, row_348, row_349, row_350, row_351,
    row_352, row_353, row_354, row_355, row_356, row_357, row_358, row_359,
    row_360, row_361, row_362, row_363, row_364, row_365, row_366, row_367,
    row_368, row_369, row_370, row_371, row_372, row_373, row_374, row_375,
    row_376, row_377, row_378, row_379, row_380, row_381, row_382, row_383,
    row_384, row_385, row_386, row_387, row_388, row_389, row_390, row_391,
    row_392, row_393, row_394, row_395, row_396, row_397, row_398, row_399,
    row_400, row_401, row_402, row_403, row_404, row_405, row_406, row_407,
    row_408, row_409, row_410, row_411, row_412, row_413, row_414, row_415,
    row_416, row_417, row_418, row_419, row_420, row_421, row_422, row_423,
    row_424, row_425, row_426, row_427, row_428, row_429, row_430, row_431,
    row_432, row_433, row_434, row_435, row_436, row_437, row_438, row_439,
    row_440, row_441, row_442, row_443, row_444, row_445, row_446, row_447,
    row_448, row_449, row_450, row_451, row_452, row_453, row_454,
    Bool.and_true]

/-- Kernel replay checks every class in the held bound. -/
theorem accepted : checkBoundedValues .blowupTwo 12 values = true := by
  apply checkEnumeratedValues_sound .blowupTwo 12 classes values
  rw [checkEnumeratedValues, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨covers, rows_checked⟩

/-- Every covered candidate agrees with the original terminating evaluator. -/
theorem values_eq (beta : SurfaceTarget.blowupTwo.Curve)
    (hbound : SurfaceTarget.blowupTwo.effective.energy beta ≤ 12) :
    values beta = pointValue .blowupTwo beta :=
  checkBoundedValues_sound .blowupTwo 12 values accepted beta hbound

end AxiomaticGW.GenusZeroBl2Table

/-
Generated candidate values from the published Kontsevich--Manin formula (5.18).
The low-energy package is shared with the existing base cases.
Manifest SHA256: 8e3b8527a07b1da765890c1294e6b6f1e2a06c8e3a9b0454d2af51fb2862eacc
This digest records provenance; the finite Lean check proves acceptance.
-/
module

public import AxiomaticGW.Surfaces.GenusZeroCertificate

@[expose] public section

-- Check rows sequentially to bound kernel replay memory.
set_option Elab.async false

namespace AxiomaticGW.PlaneGenusZeroSupport

open SurfaceGenusZero

/-- Candidate point values, keyed by every effective curve coordinate. -/
def values (beta : SurfaceTarget.plane.Curve) : ℚ :=
  match beta 0 with
  | 1 => 1
  | 2 => 1
  | 3 => 12
  | 4 => 620
  | 5 => 87304
  | _ => 0

/-- Explicit full-coordinate requests, including every zero value. -/
def classes : List SurfaceTarget.plane.Curve :=
  [![0],
   ![1],
   ![2],
   ![3],
   ![4],
   ![5]]

/-- Literal tuples cover exactly the original complete bounded enumeration. -/
theorem covers : classes.toFinset = SurfaceTarget.plane.bounded 15 := by
  -- Adjacent increasing keys prove distinctness without pairwise function comparison.
  let code (beta : SurfaceTarget.plane.Curve) : ℕ :=
    SurfaceTarget.plane.effective.energy beta * 16
      + beta 0 * 1
  have hs : (classes.map code).IsChain (· < ·) := by decide +kernel
  have hn : classes.Nodup := List.Nodup.of_map code hs.pairwise.nodup
  have hi : ∀ beta ∈ classes, SurfaceTarget.plane.effective.energy beta ≤ 15 := by
    decide +kernel
  apply Finset.eq_of_subset_of_card_le
  · intro beta hb
    rw [SurfaceTarget.bounded_eq, SurfaceTarget.plane.effective.mem_bounded]
    exact hi beta (List.mem_toFinset.mp hb)
  · rw [List.toFinset_card_of_nodup hn]
    decide +kernel

private theorem row_0 : checkValue .plane values ![0] = true := by
  decide +kernel

private theorem row_1 : checkValue .plane values ![1] = true := by
  decide +kernel

private theorem row_2 : checkValue .plane values ![2] = true := by
  decide +kernel

private theorem row_3 : checkValue .plane values ![3] = true := by
  decide +kernel

private theorem row_4 : checkValue .plane values ![4] = true := by
  decide +kernel

private theorem row_5 : checkValue .plane values ![5] = true := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- Every candidate equation is checked on literal tuples, including all zeros. -/
theorem rows_checked : classes.all (checkValue .plane values) = true := by
  simp only [classes, List.all_cons, List.all_nil,
    row_0, row_1, row_2, row_3, row_4, row_5,
    Bool.and_true]

/-- Kernel replay checks every class in the held bound. -/
theorem accepted : checkBoundedValues .plane 15 values = true := by
  apply checkEnumeratedValues_sound .plane 15 classes values
  rw [checkEnumeratedValues, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨covers, rows_checked⟩

/-- Every covered candidate agrees with the original terminating evaluator. -/
theorem values_eq (beta : SurfaceTarget.plane.Curve)
    (hbound : SurfaceTarget.plane.effective.energy beta ≤ 15) :
    values beta = pointValue .plane beta :=
  checkBoundedValues_sound .plane 15 values accepted beta hbound

end AxiomaticGW.PlaneGenusZeroSupport

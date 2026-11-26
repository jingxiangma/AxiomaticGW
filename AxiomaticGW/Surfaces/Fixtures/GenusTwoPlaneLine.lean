/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneLineScalars

/-!
# Kernel certificates for the plane genus-two line queries

The three original source-degree-two equations have zero remainders after
the derived initial values are substituted. Their constants and the only
nonzero earlier contribution are checked separately, then assembled through
the finite-table checker. No positive-degree genus-two value is a seed.
-/

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 20000

namespace AxiomaticGW.GenusTwoPlaneLine
open BelorousskiPandharipande

/-- Candidates for the held degrees zero and one. Later entries are not certified. -/
def values (d : ℕ) : Fin 3 → ℚ :=
  match d with
  | 0 => ![0, -1 / 960, 0]
  | _ => ![0, 0, 0]

/-- Every full scalar remainder, including its lower-genus constant, is checked. -/
theorem remainder_one (i : Fin 3) : planeScalarRemainder values 1 i = 0 := by
  calc
    planeScalarRemainder values 1 i =
        planeShiftedConstantFast 1 i + planeEarlierCoefficient 1 i 0 1 * (-1 / 960) := by
      norm_num [planeScalarRemainder, Fin.sum_univ_one, Fin.sum_univ_three,
        values, Matrix.cons_val_two]
    _ = 0 := by
      rw [GenusTwoPlaneLineScalars.constants, GenusTwoPlaneLineScalars.coefficients]
      fin_cases i <;> norm_num [Matrix.cons_val_two]

private theorem row_zero : planeCheckCanonicalRow values 0 = true := by decide +kernel

private theorem row_one : planeCheckCanonicalRow values 1 = true := by
  have hr : (fun i ↦ -planeScalarRemainder values 1 i) = (0 : Fin 3 → ℚ) := by
    funext i
    rw [remainder_one, neg_zero]
    rfl
  rw [planeCheckCanonicalRow, if_neg (by decide), decide_eq_true_eq, hr]
  ext j
  fin_cases j <;> norm_num [values, planeShiftedSolve]

/-- The checker covers both degrees, all three families and all zero entries. -/
theorem accepted : planeCheckCanonicalTable 1 values = true := by
  rw [planeCheckCanonicalTable, decide_eq_true_eq]
  intro d
  fin_cases d
  · exact row_zero
  · exact row_one

/-- Every entry in the held range agrees with the original terminating algorithm. -/
theorem values_eq (d : ℕ) (hd : d ≤ 1) : values d = planeCanonicalValues d :=
  planeCheckCanonicalTable_sound 1 values accepted d hd

/-- The primary and both first-descendant line queries all have value zero. -/
theorem canonical_line : planeCanonicalValues 1 = ![0, 0, 0] :=
  (values_eq 1 le_rfl).symm

end AxiomaticGW.GenusTwoPlaneLine

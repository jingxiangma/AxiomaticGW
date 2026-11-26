/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.Fixtures.L24Claims
public import AxiomaticGW.Tautological.Fixtures.L24HighCorrectionsReplay
public import AxiomaticGW.Tautological.Fixtures.L24RationalCorrectionsReplay
public import AxiomaticGW.Tautological.Fixtures.L24WDVVCorrectionsReplay



/-!
# Exact incoming L24 correction coefficients

Input SHA256: 227cd365a71aa1377c2b6c79c5a15b3217edbaf348cab6bcc8f4ab2c543cebe7
All 71 contextual rows are compared to actual independently held Lean operations.
The initial BP coordinate claim is separate and requires its own graph replay.
-/

@[expose] public section

namespace AxiomaticGW.L24CorrectionsReplay
open RelationCertificate StrataOperation

set_option maxRecDepth 20000

/-- The unaveraged correction sum is checked before finite label averaging. -/
theorem beforeAverage_checked : initialClaim +
    (∑ i, highWeights i • highRows i) + (∑ i, rationalWeights i • rationalRows i) =
    beforeAverageClaim := by
  apply funext
  intro j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_succ, Fin.sum_univ_zero, highWeights, highRows,
    rationalWeights, rationalRows, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  revert j
  decide +kernel

/-- The exact complete correction sum, including its final marking average. -/
def assembled : Coordinates 815 :=
  L24Symmetry.averageCoordinates (initialClaim +
    (∑ i, highWeights i • highRows i) + (∑ i, rationalWeights i • rationalRows i)) +
    ∑ i, wdvvWeights i • wdvvRows i

/-- Kernel arithmetic checks the complete 721-term candidate. -/
theorem assembled_checked : assembled = fullClaim := by
  rw [assembled, beforeAverage_checked]
  apply funext
  intro j
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  revert j
  decide +kernel

end AxiomaticGW.L24CorrectionsReplay

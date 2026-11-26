/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineHReduction
public import AxiomaticGW.Surfaces.ZeroPointContraction

/-!
# The three class-zero divisor coefficients of the shifted Bl₂ line equation

The shift uses E₁, so K₁ and K₂ are separate calculations. The explicit
twenty-seven-term coefficient uses the original signed rational weights.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoLineH
open BlowupTwoLineBP SurfaceGenusTwo SurfaceGenusTwoBlowupHUniform

set_option Elab.async false
set_option maxRecDepth 65536

private theorem coefficient_sum (b : SurfaceBasisLabel .blowupTwo) :
    divisorCoefficient b = ∑ j ∈ genusTwoFrame, L24CorrectionsReplay.fullClaim j *
      zeroPointRemainder .blowupTwo (zeroColumn b)
        (remainderVertex .blowupTwo (zeroColumn b) (firstCoefficientVertex .blowupTwo 0 b 0) 0)
        (L24Gluing.term j).expression (L24Gluing.term j).decoration (L24Gluing.term j).labels
        shifted labels := by
  unfold divisorCoefficient
  apply Finset.sum_congr rfl
  intro j hj
  rw [remainderPointCoefficient, if_pos ((genusTwoFrame_checked j).mp hj).2,
    zeroPointRemainder_eq]

/-- The H₀ column contributes three before evaluation at its boundary seed. -/
theorem hyperplane_coefficient : divisorCoefficient .hyperplane = 3 := by
  rw [coefficient_sum]
  decide +kernel

/-- The K₁,₀ column uses the same exceptional divisor as the chosen shift. -/
theorem first_exceptional_coefficient : divisorCoefficient (.exceptional 0) = 1 := by
  rw [coefficient_sum]
  decide +kernel

/-- The K₂,₀ column uses the other exceptional divisor. -/
theorem second_exceptional_coefficient : divisorCoefficient (.exceptional 1) = -3 := by
  rw [coefficient_sum]
  decide +kernel

/-- Only the lower-genus constant remains to evaluate the absolute H value. -/
theorem value_eq_constant_sub :
    SurfaceGenusTwoBlowupRecursion.values 0 (line, .hyperplane) =
      SurfaceGenusTwoBlowupScalar.constant 0 (line, .hyperplane) - 7 / 2880 := by
  rw [value_eq, hyperplane_coefficient, first_exceptional_coefficient,
    second_exceptional_coefficient]
  ring

end AxiomaticGW.BlowupTwoLineH

import AxiomaticGW.GKM.Fixtures.BlowupPositivePlaneEnergyTwoBenchmark

/-! # Full-class marked reductions and distinct coverage on the two-point blowup -/

namespace AxiomaticGWTest.GKM.BlowupPositivePlaneEnergyTwoBenchmark
open AxiomaticGW AxiomaticGW.GKM SurfaceGenusTwoBlowupDescendants
open BlowupTwoPositivePlaneEnergyTwoPairs

/-- On E₁ + L, both the divisor intersection and lowering the unit descendant contribute. -/
theorem ruling_divisor_correction :
    CheckedDescendant 0 (⟨2, ![1,0,1], [⟨.unit,4⟩, ⟨.exceptional 1,0⟩]⟩ :
      SurfaceQuery .blowupTwo) (-127/5760) := by
  have h := marked_accepted (j := 220) (by decide +kernel)
  exact h

/-- The full-coordinate union counts each checked two-point-blowup request once. -/
example : BlowupPositivePlaneEnergyTwoBenchmark.twoBlowups.card = 1235 :=
  BlowupPositivePlaneEnergyTwoBenchmark.card_twoBlowups

end AxiomaticGWTest.GKM.BlowupPositivePlaneEnergyTwoBenchmark

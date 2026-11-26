module

import AxiomaticGW.GKM.Fixtures.GenusTwoUnitPairReplay
import AxiomaticGW.GKM.Fixtures.GenusTwoDivisorPairReplay

/-! # Ordered genus-two reconstruction checks for the offline test suite -/

namespace AxiomaticGWTest.GenusTwoPairComparisons
open AxiomaticGW AxiomaticGW.GKM

/-- A dilaton marking at the end multiplies the strict-line hyperplane value by three. -/
example : SurfaceGenusTwo.unitPairValue? 0
    (⟨2, ![0, 0, 1], [⟨.hyperplane, 2⟩, ⟨.unit, 1⟩]⟩ : SurfaceQuery .blowupTwo) =
    some (1 / 80 : ℚ) := by
  exact (GenusTwoUnitPairs.StrictLine.accepted 1 3).2.trans (by decide +kernel)

/-- Signed pairing with the exceptional curve for a divisor in the first position. -/
example : SurfaceGenusTwo.divisorPairValue? 0
    (⟨2, ![1, 0], [⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 2⟩]⟩ :
      SurfaceQuery .hirzebruchOne) = some (1 / 240 : ℚ) := by
  exact (GenusTwoDivisorPairs.OneBlowup.accepted 2 1 0).2.trans (by decide +kernel)

/-- The original plane evaluator includes the nonzero divisor-square correction. -/
example : BelorousskiPandharipande.planeQueryValue?
    ⟨2, ![1], [⟨.hyperplane, 0⟩, ⟨.hyperplane, 4⟩]⟩ = some (-1 / 192 : ℚ) := by
  exact (GenusTwoDivisorPairs.Plane.original 1 0 0).trans (by decide +kernel)

end AxiomaticGWTest.GenusTwoPairComparisons

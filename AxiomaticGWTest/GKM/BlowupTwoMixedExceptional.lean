module

import AxiomaticGW.GKM.Fixtures.BlowupDivisorBenchmarkCoverage
import AxiomaticGW.GKM.Fixtures.BlowupTwoMixedExceptionalGeometry

set_option linter.privateModule false
namespace AxiomaticGWTest.GKM.BlowupTwoMixedExceptional
open AxiomaticGW AxiomaticGW.GKM.BlowupTwoMixedExceptional

-- The unit pair needs a mixed ancestor calculation even though this class has no connected locus.
example : SurfaceGenusTwoBlowupDescendants.CheckedDescendant 0
    (⟨2, ![1, 1, 0], [⟨.unit, 2⟩, ⟨.unit, 3⟩]⟩ : SurfaceQuery .blowupTwo) 0 :=
  accepted 7

-- Equal numbers do not identify the two original ordered requests.
example : requests 7 ≠ requests 8 ∧ values 7 = values 8 := by decide +kernel

end AxiomaticGWTest.GKM.BlowupTwoMixedExceptional

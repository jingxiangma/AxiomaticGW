module

import AxiomaticGW.GKM.Fixtures.BlowupFewMarkingCoverage

set_option linter.privateModule false
namespace AxiomaticGWTest.GKM.F1EnergyTwo
open AxiomaticGW AxiomaticGW.GKM

-- The unit/exceptional pair uses two positive cotangent powers and a signed tail.
example : SurfaceGenusTwoBlowupDescendants.CheckedDescendant 0
    (⟨2, ![0, 1], [⟨.unit, 3⟩, ⟨.exceptional 0, 1⟩]⟩ : SurfaceQuery .hirzebruchOne)
    (-113 / 2880) := F1FiberPairs.accepted 14

-- Both cotangent powers are positive; the six surviving boundary terms occur in class 2E.
example : SurfaceGenusTwoBlowupDescendants.CheckedDescendant 0
    (⟨2, ![2, 0], [⟨.unit, 2⟩, ⟨.unit, 3⟩]⟩ : SurfaceQuery .hirzebruchOne)
    (27 / 1280) := F1DoubleExceptionalPairs.accepted 2

-- At the same energy the exceptional divisor sees different singleton values in F and 2E.
example : SurfaceGenusTwoBlowupDescendants.queryValue? 0
    (⟨2, ![2, 0], [⟨.exceptional 0, 3⟩]⟩ : SurfaceQuery .hirzebruchOne) = some (3 / 320) :=
  F1DoubleExceptionalOneMarking.accepted 2

example : SurfaceGenusTwoBlowupDescendants.queryValue? 0
    (⟨2, ![0, 1], [⟨.exceptional 0, 3⟩]⟩ : SurfaceQuery .hirzebruchOne) = some (-23 / 2880) :=
  F1FiberOneMarking.accepted 2

-- H pairs trivially with 2E and its cup product with E is zero.
example : SurfaceGenusTwo.markedPairValueWith? (fun _ ↦ none)
    (⟨2, ![2, 0], [⟨.hyperplane, 0⟩, ⟨.exceptional 0, 3⟩]⟩ : SurfaceQuery .hirzebruchOne) =
      some 0 := by decide +kernel

-- E pairs nontrivially with 2E, so the empty singleton table cannot certify this request.
example : SurfaceGenusTwo.markedPairValueWith? (fun _ ↦ none)
    (⟨2, ![2, 0], [⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 3⟩]⟩ : SurfaceQuery .hirzebruchOne) =
      none := by decide +kernel

end AxiomaticGWTest.GKM.F1EnergyTwo

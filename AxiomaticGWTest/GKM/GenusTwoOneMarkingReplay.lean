module

import AxiomaticGW.GKM.Fixtures.GenusTwoOneMarkingReplay
import AxiomaticGW.GKM.Fixtures.F1FiberOneMarkingReplay

set_option linter.privateModule false
namespace AxiomaticGWTest.GKM.GenusTwoOneMarkingReplay
open AxiomaticGW AxiomaticGW.GKM.GenusTwoOneMarking

-- The signed mixed descendant includes the exceptional tail on the F1 unit.
example : SurfaceGenusTwoBlowupDescendants.queryValue? 0
    (⟨2, ![1, 0], [⟨.unit, 3⟩]⟩ : SurfaceQuery .hirzebruchOne) = some (13 / 2880) :=
  OneBlowup.accepted 0

-- The point on the fiber retains the correction from the mixed cotangent comparison.
example : SurfaceGenusTwoBlowupDescendants.queryValue? 0
    (⟨2, ![0, 1], [⟨.point, 2⟩]⟩ : SurfaceQuery .hirzebruchOne) = some (1 / 240) :=
  AxiomaticGW.GKM.F1FiberOneMarking.accepted 3

-- At the same energy on Bl₂ the *same insertion* distinguishes E₁ from E₂.
example : SurfaceGenusTwoBlowupDescendants.queryValue? 0
    (⟨2, ![1, 0, 0], [⟨.exceptional 1, 2⟩]⟩ : SurfaceQuery .blowupTwo) = some 0 :=
  TwoBlowups.accepted 3

example : SurfaceGenusTwoBlowupDescendants.queryValue? 0
    (⟨2, ![0, 1, 0], [⟨.exceptional 1, 2⟩]⟩ : SurfaceQuery .blowupTwo) = some (-1 / 240) :=
  TwoBlowups.accepted 8

end AxiomaticGWTest.GKM.GenusTwoOneMarkingReplay

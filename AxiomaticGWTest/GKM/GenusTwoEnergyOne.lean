module

import AxiomaticGW.GKM.Fixtures.GenusTwoEnergyOneReplay
import AxiomaticGW.Surfaces.GenusTwoFewMarkingCounts

/-! # Full energy-one reconstruction and exceptional class sensitivity -/

namespace AxiomaticGWTest.GenusTwoEnergyOne
open AxiomaticGW AxiomaticGW.GKM.GenusTwoEnergyOne SurfaceGenusTwoBlowupDescendants

/-- The second descendant of the unit sees the self-intersection of the marked exceptional. -/
example : CheckedDescendant 0
    (⟨2, ![1, 0, 0], [⟨.unit, 2⟩, ⟨.exceptional 0, 1⟩]⟩ : SurfaceQuery .blowupTwo)
    (-5 / 288) := TwoBlowups.accepted 176

/-- The very same insertions on the disjoint exceptional give zero. -/
example : CheckedDescendant 0
    (⟨2, ![0, 1, 0], [⟨.unit, 2⟩, ⟨.exceptional 0, 1⟩]⟩ : SurfaceQuery .blowupTwo)
    0 := TwoBlowups.accepted 96

/-- The complete fixed domain uses four positive energy slices. -/
example : (SurfaceGenusTwo.fewMarkingQueries .blowupTwo).card = 4495 :=
  SurfaceGenusTwo.benchmark_sizes.2.2

end AxiomaticGWTest.GenusTwoEnergyOne

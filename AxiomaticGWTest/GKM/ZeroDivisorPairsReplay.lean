module

import AxiomaticGW.GKM.Fixtures.ZeroDivisorPairsReplay

set_option linter.privateModule false
namespace AxiomaticGWTest.GKM.ZeroDivisorPairsReplay
open AxiomaticGW AxiomaticGW.GKM F1ZeroDivisorPairs

-- A zero intersection and a zero cup correction remove all singleton inputs.
example : requests 4 =
    (⟨2, ![1, 1], [⟨.hyperplane, 4⟩, ⟨.exceptional 0, 0⟩]⟩ : SurfaceQuery .hirzebruchOne) ∧
    SurfaceGenusTwoBlowupDescendants.CheckedDescendant 0 (requests 4) 0 ∧
      equivariant 4 = 0 :=
  ⟨by decide +kernel, (values_zero 4) ▸ accepted 4, equivariant_zero 4⟩

end AxiomaticGWTest.GKM.ZeroDivisorPairsReplay

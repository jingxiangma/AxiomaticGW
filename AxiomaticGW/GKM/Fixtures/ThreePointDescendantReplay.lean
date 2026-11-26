/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.ThreePointDescendants

/-!
# Native three-point descendant replay

Input SHA256: 72b2dfb09ff86fd05a85111a88100e86b6d2316afbfc6e624fc54e2843f768f0
Each actual incoming value is compared with the proved descendant evaluator.
The digest is provenance, not a proof of localization geometry.
-/

@[expose] public section

namespace AxiomaticGW.GKM.ThreePointDescendantReplay

namespace Plane

def requests : Fin 10 → SurfaceThreePointDescendants.Request .plane :=
  ![(![0], ![0, 0, 0], ![.hyperplane, .hyperplane, .unit]),
    (![0], ![1, 0, 0], ![.hyperplane, .unit, .unit]),
    (![1], ![1, 0, 0], ![.point, .hyperplane, .hyperplane]),
    (![1], ![2, 0, 0], ![.point, .hyperplane, .unit]),
    (![1], ![3, 0, 0], ![.point, .unit, .unit]),
    (![1], ![3, 0, 0], ![.hyperplane, .hyperplane, .unit]),
    (![1], ![0, 0, 1], ![.hyperplane, .hyperplane, .point]),
    (![2], ![2, 2, 0], ![.point, .point, .unit]),
    (![2], ![2, 0, 2], ![.point, .unit, .point]),
    (![2], ![1, 1, 2], ![.point, .point, .unit])]

def values : Fin 10 → ℚ :=
  ![1, 0, 1, 1, 1, -2, 1, 1, 1, 0]

/-- Coverage is checked against the separately held requests. -/
theorem coverage : Finset.univ.image requests =
    (SurfaceThreePointDescendants.requests .plane).toFinset := by decide +kernel

/-- The value, full curve, both insertion data and their order are claim-bound. -/
theorem accepted : ∀ i, values i = SurfaceDescendant.threePointValue
    .plane (requests i).1 (requests i).2.1 (requests i).2.2 := by decide +kernel

end Plane

namespace OneBlowup

def requests : Fin 7 → SurfaceThreePointDescendants.Request .hirzebruchOne :=
  ![(![0, 0], ![0, 0, 0], ![.exceptional 0, .exceptional 0, .unit]),
    (![0, 0], ![1, 0, 0], ![.exceptional 0, .unit, .unit]),
    (![1, 0], ![1, 0, 0], ![.exceptional 0, .exceptional 0, .unit]),
    (![1, 0], ![2, 0, 0], ![.unit, .exceptional 0, .unit]),
    (![2, 0], ![1, 1, 0], ![.exceptional 0, .exceptional 0, .unit]),
    (![0, 1], ![1, 0, 0], ![.point, .exceptional 0, .unit]),
    (![1, 1], ![1, 0, 0], ![.point, .hyperplane, .hyperplane])]

def values : Fin 7 → ℚ :=
  ![-1, 0, 1, 1, -1, 1, 1]

/-- Coverage is checked against the separately held requests. -/
theorem coverage : Finset.univ.image requests =
    (SurfaceThreePointDescendants.requests .hirzebruchOne).toFinset := by decide +kernel

/-- The value, full curve, both insertion data and their order are claim-bound. -/
theorem accepted : ∀ i, values i = SurfaceDescendant.threePointValue
    .hirzebruchOne (requests i).1 (requests i).2.1 (requests i).2.2 := by decide +kernel

end OneBlowup

namespace TwoBlowups

def requests : Fin 10 → SurfaceThreePointDescendants.Request .blowupTwo :=
  ![(![0, 0, 0], ![0, 0, 0], ![.exceptional 0, .exceptional 1, .unit]),
    (![1, 0, 0], ![1, 0, 0], ![.exceptional 0, .exceptional 0, .unit]),
    (![0, 1, 0], ![1, 0, 0], ![.exceptional 0, .exceptional 0, .unit]),
    (![0, 1, 0], ![1, 0, 0], ![.exceptional 1, .exceptional 1, .unit]),
    (![1, 0, 0], ![2, 0, 0], ![.unit, .exceptional 0, .unit]),
    (![2, 0, 0], ![1, 1, 0], ![.exceptional 0, .exceptional 0, .unit]),
    (![1, 1, 0], ![1, 1, 0], ![.exceptional 0, .exceptional 1, .unit]),
    (![0, 0, 1], ![1, 0, 0], ![.hyperplane, .exceptional 0, .unit]),
    (![0, 1, 1], ![1, 0, 0], ![.point, .exceptional 1, .unit]),
    (![1, 0, 1], ![1, 0, 0], ![.point, .exceptional 0, .unit])]

def values : Fin 10 → ℚ :=
  ![0, 1, 0, 1, 1, -1, 0, 1, 0, 0]

/-- Coverage is checked against the separately held requests. -/
theorem coverage : Finset.univ.image requests =
    (SurfaceThreePointDescendants.requests .blowupTwo).toFinset := by decide +kernel

/-- The value, full curve, both insertion data and their order are claim-bound. -/
theorem accepted : ∀ i, values i = SurfaceDescendant.threePointValue
    .blowupTwo (requests i).1 (requests i).2.1 (requests i).2.2 := by decide +kernel

end TwoBlowups

end AxiomaticGW.GKM.ThreePointDescendantReplay

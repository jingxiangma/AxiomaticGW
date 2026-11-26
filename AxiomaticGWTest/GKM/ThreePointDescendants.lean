/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.GKM.Fixtures.ThreePointDescendantReplay

set_option linter.privateModule false

namespace AxiomaticGWTest.GKM.ThreePointDescendants
open AxiomaticGW

/-- Incoming values are checked at their own marking powers and full classes. -/
example (i) : GKM.ThreePointDescendantReplay.TwoBlowups.values i =
    SurfaceDescendant.threePointValue .blowupTwo
      (GKM.ThreePointDescendantReplay.TwoBlowups.requests i).1
      (GKM.ThreePointDescendantReplay.TwoBlowups.requests i).2.1
      (GKM.ThreePointDescendantReplay.TwoBlowups.requests i).2.2 :=
  GKM.ThreePointDescendantReplay.TwoBlowups.accepted i

end AxiomaticGWTest.GKM.ThreePointDescendants

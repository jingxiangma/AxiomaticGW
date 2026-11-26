/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.GKM.Fixtures.GenusOneDescendantReplay

set_option linter.privateModule false

namespace AxiomaticGWTest.GKM.GenusOneDescendants
open AxiomaticGW GKM.GenusOneDescendantReplay

/-- Every held arity on all three targets is replayed through the public evaluator. -/
example : (∀ i, SurfaceGenusOne.queryValue? (Plane.requests i) = some (Plane.values i)) ∧
    (∀ i, SurfaceGenusOne.queryValue? (OneBlowup.requests i) = some (OneBlowup.values i)) ∧
    (∀ i, SurfaceGenusOne.queryValue? (TwoBlowups.requests i) = some (TwoBlowups.values i)) :=
  ⟨Plane.accepted, OneBlowup.accepted, TwoBlowups.accepted⟩

end AxiomaticGWTest.GKM.GenusOneDescendants

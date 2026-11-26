/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.ThreePointDescendants

/-!
# Held three-point descendant localization requests

The 27 requests exercise degree zero, several powers at one marking,
descendants at multiple markings, simultaneous permutations, negative values,
exceptional multiple covers, and distinct full classes with equal energy.
These regression cases supplement, and do not replace, the research suites.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceThreePointDescendants

/-- Fixed three-marked input: full class, ordered powers and ordered labels. -/
abbrev Request (X : SurfaceTarget) := X.Curve × (Fin 3 → ℕ) × (Fin 3 → SurfaceBasisLabel X)

/-- Requests held independently of incoming producer claims. -/
def requests : (X : SurfaceTarget) → List (Request X)
  | .plane =>
      [(![0], ![0,0,0], ![.hyperplane,.hyperplane,.unit]),
       (![0], ![1,0,0], ![.hyperplane,.unit,.unit]),
       (![1], ![1,0,0], ![.point,.hyperplane,.hyperplane]),
       (![1], ![2,0,0], ![.point,.hyperplane,.unit]),
       (![1], ![3,0,0], ![.point,.unit,.unit]),
       (![1], ![3,0,0], ![.hyperplane,.hyperplane,.unit]),
       (![1], ![0,0,1], ![.hyperplane,.hyperplane,.point]),
       (![2], ![2,2,0], ![.point,.point,.unit]),
       (![2], ![2,0,2], ![.point,.unit,.point]),
       (![2], ![1,1,2], ![.point,.point,.unit])]
  | .hirzebruchOne =>
      [(![0,0], ![0,0,0], ![.exceptional 0,.exceptional 0,.unit]),
       (![0,0], ![1,0,0], ![.exceptional 0,.unit,.unit]),
       (![1,0], ![1,0,0], ![.exceptional 0,.exceptional 0,.unit]),
       (![1,0], ![2,0,0], ![.unit,.exceptional 0,.unit]),
       (![2,0], ![1,1,0], ![.exceptional 0,.exceptional 0,.unit]),
       (![0,1], ![1,0,0], ![.point,.exceptional 0,.unit]),
       (![1,1], ![1,0,0], ![.point,.hyperplane,.hyperplane])]
  | .blowupTwo =>
      [(![0,0,0], ![0,0,0], ![.exceptional 0,.exceptional 1,.unit]),
       (![1,0,0], ![1,0,0], ![.exceptional 0,.exceptional 0,.unit]),
       (![0,1,0], ![1,0,0], ![.exceptional 0,.exceptional 0,.unit]),
       (![0,1,0], ![1,0,0], ![.exceptional 1,.exceptional 1,.unit]),
       (![1,0,0], ![2,0,0], ![.unit,.exceptional 0,.unit]),
       (![2,0,0], ![1,1,0], ![.exceptional 0,.exceptional 0,.unit]),
       (![1,1,0], ![1,1,0], ![.exceptional 0,.exceptional 1,.unit]),
       (![0,0,1], ![1,0,0], ![.hyperplane,.exceptional 0,.unit]),
       (![0,1,1], ![1,0,0], ![.point,.exceptional 1,.unit]),
       (![1,0,1], ![1,0,0], ![.point,.exceptional 0,.unit])]

end AxiomaticGW.SurfaceThreePointDescendants

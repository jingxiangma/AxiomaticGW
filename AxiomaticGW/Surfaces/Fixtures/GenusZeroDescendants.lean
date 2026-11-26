/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroFullDescendants

/-!
# Held all-arity genus-zero descendant requests

These 34 fixed requests cover all three surfaces, four to six stable markings,
degree-zero psi intersections, and positive-degree zero-, one- and two-marked
invariants. They retain both exceptional labels and full classes. They are
regressions supplementing the fixed research suites, not a smaller benchmark goal.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusZeroDescendants

/-- The incoming numerical values cannot change this held request family. -/
def requests : (X : SurfaceTarget) → List (SurfaceQuery X)
  | .plane =>
      [⟨0, ![0], [⟨.unit, 1⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.point, 0⟩]⟩,
       ⟨0, ![0], [⟨.unit, 1⟩, ⟨.unit, 1⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.point, 0⟩]⟩,
       ⟨0, ![0], [⟨.unit, 1⟩, ⟨.unit, 1⟩, ⟨.unit, 1⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.point, 0⟩]⟩,
       ⟨0, ![0], [⟨.unit, 2⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.point, 0⟩]⟩,
       ⟨0, ![1], [⟨.point, 3⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.hyperplane, 0⟩]⟩,
       ⟨0, ![1], [⟨.hyperplane, 4⟩, ⟨.hyperplane, 0⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩]⟩,
       ⟨0, ![1], [⟨.point, 1⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩]⟩,
       ⟨0, ![1], [⟨.point, 4⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.hyperplane, 0⟩]⟩,
       ⟨0, ![1], [⟨.point, 1⟩]⟩,
       ⟨0, ![1], [⟨.hyperplane, 2⟩]⟩,
       ⟨0, ![1], [⟨.point, 2⟩, ⟨.unit, 0⟩]⟩,
       ⟨0, ![1], [⟨.hyperplane, 2⟩, ⟨.hyperplane, 0⟩]⟩]
  | .hirzebruchOne =>
      [⟨0, ![0, 0], [⟨.unit, 1⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 0⟩]⟩,
       ⟨0, ![0, 0], [⟨.unit, 1⟩, ⟨.unit, 1⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 0⟩]⟩,
       ⟨0, ![1, 0], [⟨.exceptional 0, 2⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩]⟩,
       ⟨0, ![2, 0], [⟨.exceptional 0, 2⟩, ⟨.exceptional 0, 1⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩]⟩,
       ⟨0, ![1, 0], []⟩,
       ⟨0, ![1, 0], [⟨.exceptional 0, 0⟩]⟩,
       ⟨0, ![1, 0], [⟨.unit, 1⟩]⟩,
       ⟨0, ![1, 0], [⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩]⟩,
       ⟨0, ![0, 1], [⟨.point, 0⟩]⟩,
       ⟨0, ![1, 1], [⟨.point, 3⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.hyperplane, 0⟩]⟩]
  | .blowupTwo =>
      [⟨0, ![0, 0, 0], [⟨.unit, 1⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.unit, 0⟩]⟩,
       ⟨0, ![0, 0, 0], [⟨.unit, 1⟩, ⟨.unit, 1⟩,
         ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.unit, 0⟩]⟩,
       ⟨0, ![1, 0, 0], [⟨.exceptional 0, 2⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩]⟩,
       ⟨0, ![0, 1, 0], [⟨.exceptional 0, 2⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩]⟩,
       ⟨0, ![0, 1, 0], [⟨.exceptional 1, 2⟩, ⟨.exceptional 1, 0⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩]⟩,
       ⟨0, ![0, 0, 1], [⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.unit, 1⟩]⟩,
       ⟨0, ![0, 0, 1], []⟩,
       ⟨0, ![1, 0, 0], []⟩,
       ⟨0, ![0, 1, 0], []⟩,
       ⟨0, ![1, 0, 0], [⟨.unit, 1⟩]⟩,
       ⟨0, ![0, 1, 1], [⟨.point, 0⟩]⟩,
       ⟨0, ![1, 0, 1], [⟨.point, 0⟩]⟩]

end AxiomaticGW.SurfaceGenusZeroDescendants

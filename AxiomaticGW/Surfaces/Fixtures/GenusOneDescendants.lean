/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusOneDescendants

/-!
# Held genus-one descendant requests

Coverage includes the raw elliptic loop, rational tails, signed exceptional
pairings, distinct full classes, multiple covers and the zero-marking sector.
Incoming GKM values cannot change this independently held request set.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusOneDescendants

/-- Fixed full requests; no incoming numerical values occur here. -/
def requests : (X : SurfaceTarget) → List (SurfaceQuery X)
  | .plane => [⟨1, ![0], [⟨.unit, 1⟩]⟩,
      ⟨1, ![0], [⟨.unit, 2⟩, ⟨.unit, 0⟩]⟩,
      ⟨1, ![0], [⟨.unit, 1⟩, ⟨.unit, 1⟩]⟩,
      ⟨1, ![0], [⟨.unit, 1⟩, ⟨.unit, 1⟩, ⟨.unit, 1⟩]⟩,
      ⟨1, ![0], [⟨.unit, 1⟩, ⟨.hyperplane, 0⟩]⟩,
      ⟨1, ![0], [⟨.hyperplane, 0⟩, ⟨.unit, 1⟩]⟩,
      ⟨1, ![0], [⟨.unit, 1⟩, ⟨.unit, 1⟩, ⟨.unit, 1⟩, ⟨.unit, 1⟩]⟩,
      ⟨1, ![1], [⟨.point, 2⟩]⟩,
      ⟨1, ![1], [⟨.hyperplane, 3⟩]⟩,
      ⟨1, ![1], [⟨.unit, 4⟩]⟩,
      ⟨1, ![1], [⟨.point, 3⟩, ⟨.unit, 0⟩]⟩,
      ⟨1, ![1], [⟨.hyperplane, 3⟩, ⟨.hyperplane, 0⟩]⟩,
      ⟨1, ![1], []⟩,
      ⟨1, ![2], [⟨.point, 5⟩]⟩]
  | .hirzebruchOne => [⟨1, ![0, 0], [⟨.unit, 1⟩]⟩,
      ⟨1, ![0, 0], [⟨.unit, 2⟩, ⟨.unit, 0⟩]⟩,
      ⟨1, ![0, 0], [⟨.unit, 1⟩, ⟨.unit, 1⟩, ⟨.unit, 1⟩]⟩,
      ⟨1, ![0, 0], [⟨.unit, 1⟩, ⟨.exceptional 0, 0⟩]⟩,
      ⟨1, ![0, 0], [⟨.exceptional 0, 0⟩, ⟨.unit, 1⟩]⟩,
      ⟨1, ![1, 0], [⟨.exceptional 0, 1⟩]⟩,
      ⟨1, ![1, 0], [⟨.unit, 2⟩]⟩,
      ⟨1, ![1, 0], [⟨.exceptional 0, 1⟩, ⟨.exceptional 0, 0⟩]⟩,
      ⟨1, ![1, 0], []⟩,
      ⟨1, ![2, 0], [⟨.exceptional 0, 2⟩]⟩,
      ⟨1, ![0, 1], [⟨.point, 1⟩]⟩,
      ⟨1, ![1, 1], [⟨.hyperplane, 3⟩]⟩]
  | .blowupTwo => [⟨1, ![0, 0, 0], [⟨.unit, 1⟩]⟩,
      ⟨1, ![0, 0, 0], [⟨.unit, 1⟩, ⟨.unit, 1⟩, ⟨.unit, 1⟩]⟩,
      ⟨1, ![0, 0, 0], [⟨.unit, 1⟩, ⟨.exceptional 1, 0⟩]⟩,
      ⟨1, ![1, 0, 0], [⟨.exceptional 0, 1⟩]⟩,
      ⟨1, ![0, 1, 0], [⟨.exceptional 0, 1⟩]⟩,
      ⟨1, ![0, 1, 0], [⟨.exceptional 1, 1⟩]⟩,
      ⟨1, ![1, 0, 0], [⟨.unit, 2⟩]⟩,
      ⟨1, ![0, 1, 0], [⟨.exceptional 1, 1⟩, ⟨.exceptional 1, 0⟩]⟩,
      ⟨1, ![0, 0, 1], [⟨.hyperplane, 1⟩]⟩,
      ⟨1, ![0, 0, 1], [⟨.exceptional 0, 1⟩]⟩,
      ⟨1, ![0, 0, 1], []⟩,
      ⟨1, ![1, 0, 0], []⟩,
      ⟨1, ![2, 0, 0], [⟨.exceptional 0, 2⟩]⟩,
      ⟨1, ![1, 0, 1], [⟨.point, 1⟩]⟩,
      ⟨1, ![1, 1, 1], [⟨.hyperplane, 3⟩]⟩]

end AxiomaticGW.SurfaceGenusOneDescendants

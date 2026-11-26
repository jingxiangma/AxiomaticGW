/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneGenusTwoFewMarkings

/-!
# Held ordered plane genus-two few-marking requests

Manifest SHA256: b7074be9bafc684fc1aacf31adabac18064ce16eba66330699a8cc4c6a9f3248
The requests depend only on the fixed bounds and dimension equation.
Coverage is checked against the separately proved complete mathematical frame.
No numerical values occur in this artifact.
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 20000

namespace AxiomaticGW.GenusTwoPlaneFewMarkingRequests

open BelorousskiPandharipande

/-- The held 48 ordered queries, retaining every state and descendant power. -/
def requests (i : Fin 48) : SurfaceQuery .plane :=
  (#[⟨2, ![1], [⟨.unit, 5⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 4⟩]⟩,
    ⟨2, ![1], [⟨.point, 3⟩]⟩,
    ⟨2, ![1], [⟨.unit, 0⟩, ⟨.unit, 6⟩]⟩,
    ⟨2, ![1], [⟨.unit, 1⟩, ⟨.unit, 5⟩]⟩,
    ⟨2, ![1], [⟨.unit, 2⟩, ⟨.unit, 4⟩]⟩,
    ⟨2, ![1], [⟨.unit, 3⟩, ⟨.unit, 3⟩]⟩,
    ⟨2, ![1], [⟨.unit, 4⟩, ⟨.unit, 2⟩]⟩,
    ⟨2, ![1], [⟨.unit, 5⟩, ⟨.unit, 1⟩]⟩,
    ⟨2, ![1], [⟨.unit, 6⟩, ⟨.unit, 0⟩]⟩,
    ⟨2, ![1], [⟨.unit, 0⟩, ⟨.hyperplane, 5⟩]⟩,
    ⟨2, ![1], [⟨.unit, 1⟩, ⟨.hyperplane, 4⟩]⟩,
    ⟨2, ![1], [⟨.unit, 2⟩, ⟨.hyperplane, 3⟩]⟩,
    ⟨2, ![1], [⟨.unit, 3⟩, ⟨.hyperplane, 2⟩]⟩,
    ⟨2, ![1], [⟨.unit, 4⟩, ⟨.hyperplane, 1⟩]⟩,
    ⟨2, ![1], [⟨.unit, 5⟩, ⟨.hyperplane, 0⟩]⟩,
    ⟨2, ![1], [⟨.unit, 0⟩, ⟨.point, 4⟩]⟩,
    ⟨2, ![1], [⟨.unit, 1⟩, ⟨.point, 3⟩]⟩,
    ⟨2, ![1], [⟨.unit, 2⟩, ⟨.point, 2⟩]⟩,
    ⟨2, ![1], [⟨.unit, 3⟩, ⟨.point, 1⟩]⟩,
    ⟨2, ![1], [⟨.unit, 4⟩, ⟨.point, 0⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 0⟩, ⟨.unit, 5⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 1⟩, ⟨.unit, 4⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 2⟩, ⟨.unit, 3⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 3⟩, ⟨.unit, 2⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 4⟩, ⟨.unit, 1⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 5⟩, ⟨.unit, 0⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 0⟩, ⟨.hyperplane, 4⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 1⟩, ⟨.hyperplane, 3⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 2⟩, ⟨.hyperplane, 2⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 3⟩, ⟨.hyperplane, 1⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 4⟩, ⟨.hyperplane, 0⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 0⟩, ⟨.point, 3⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 1⟩, ⟨.point, 2⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 2⟩, ⟨.point, 1⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 3⟩, ⟨.point, 0⟩]⟩,
    ⟨2, ![1], [⟨.point, 0⟩, ⟨.unit, 4⟩]⟩,
    ⟨2, ![1], [⟨.point, 1⟩, ⟨.unit, 3⟩]⟩,
    ⟨2, ![1], [⟨.point, 2⟩, ⟨.unit, 2⟩]⟩,
    ⟨2, ![1], [⟨.point, 3⟩, ⟨.unit, 1⟩]⟩,
    ⟨2, ![1], [⟨.point, 4⟩, ⟨.unit, 0⟩]⟩,
    ⟨2, ![1], [⟨.point, 0⟩, ⟨.hyperplane, 3⟩]⟩,
    ⟨2, ![1], [⟨.point, 1⟩, ⟨.hyperplane, 2⟩]⟩,
    ⟨2, ![1], [⟨.point, 2⟩, ⟨.hyperplane, 1⟩]⟩,
    ⟨2, ![1], [⟨.point, 3⟩, ⟨.hyperplane, 0⟩]⟩,
    ⟨2, ![1], [⟨.point, 0⟩, ⟨.point, 2⟩]⟩,
    ⟨2, ![1], [⟨.point, 1⟩, ⟨.point, 1⟩]⟩,
    ⟨2, ![1], [⟨.point, 2⟩, ⟨.point, 0⟩]⟩] : Array (SurfaceQuery .plane))[i.val]

/-- Every required ordered request occurs; no extra request is included. -/
theorem coverage : Finset.univ.image requests = planeFewMarkingQueries := by
  decide +kernel

/-- The explicit request list has no repeated complete query. -/
theorem requests_injective : Function.Injective requests := by
  decide +kernel

end AxiomaticGW.GenusTwoPlaneFewMarkingRequests

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneLine

/-!
# Native genus-two plane line replay

Input SHA256: 0ab54af0c2410bb3794086f150b9b447119a711fa6e2d5cb127a65ffbc1a24ba
Incoming ordinary values are checked against the full held queries.
This certificate does not prove equivariant localization or CohFT applicability.
-/

@[expose] public section

namespace AxiomaticGW.GKM.PlaneGenusTwoLineReplay

open BelorousskiPandharipande

/-- The three incoming full line queries, in N/H/P order. -/
def requests : Fin 3 → SurfaceQuery .plane :=
  ![⟨2, ![1], [⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩]⟩,
    ⟨2, ![1], [⟨.point, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩]⟩]

/-- Incoming ordinary rational values, bound to the requests by `accepted`. -/
def values : Fin 3 → ℚ := ![0, 0, 0]

/-- Exact full-class, genus and ordered insertion coverage. -/
theorem coverage : ∀ i, requests i = planeCanonicalQueries 1 i := by
  decide +kernel

/-- Each incoming value is bound to its actual requested invariant. -/
theorem accepted : ∀ i, planeCheckCanonicalClaim 1 GenusTwoPlaneLine.values
    (requests i) (values i) = true := by
  intro i
  rw [planeCheckCanonicalClaim, GenusTwoPlaneLine.accepted, Bool.and_true]
  fin_cases i <;> decide +kernel

end AxiomaticGW.GKM.PlaneGenusTwoLineReplay

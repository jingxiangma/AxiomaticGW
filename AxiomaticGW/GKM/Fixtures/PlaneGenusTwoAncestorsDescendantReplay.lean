/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsReplay
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsDescendants

/-!
# Full plane few-marking claims from the certified ancestor cache

Input SHA256: 640e00ec2d4b2055c49465d80a3590da42dec51772d34ea00bad356dad0950a8
Candidate values become certificates only after their full equations are checked.
The original canonical seeds and geometric hypotheses are unchanged.
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoAncestors

open BelorousskiPandharipande SurfaceGenusTwo

/-- All 48 original queries follow from both accepted tables and the original algorithm. -/
theorem descendants_accepted (i : Fin 48) :
    planeQueryValue? (PlaneGenusTwoFewMarkingsReplay.requests i) =
      some (PlaneGenusTwoFewMarkingsReplay.values i) := by
  rw [← planeQueryValueCached?_eq 1 GenusTwoPlaneLine.values GenusTwoPlaneLine.accepted
    queries values accepted (PlaneGenusTwoFewMarkingsReplay.requests i)
    (by revert i; decide +kernel)]
  exact cached_computation i

end AxiomaticGW.GKM.PlaneGenusTwoAncestors

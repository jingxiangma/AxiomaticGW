/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsData

/-!
# Plane ancestor arithmetic: LowPsi

Input SHA256: 640e00ec2d4b2055c49465d80a3590da42dec51772d34ea00bad356dad0950a8
Candidate values become certificates only after their full equations are checked.
The original canonical seeds and geometric hypotheses are unchanged.
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoAncestors

open BelorousskiPandharipande SurfaceGenusTwo

namespace LowPsi

attribute [local cbv_eval] PlaneGenusTwoFewMarkingsReplay.vectorLookup
attribute [local cbv_eval] PlaneGenusTwoFewMarkingsReplay.rationalCached
attribute [local cbv_eval] PlaneGenusTwoFewMarkingsReplay.ellipticCached

theorem terminal_0 : value 0 =
    planeLowPsiValueWith GenusTwoPlaneLine.values (key 0) := by
  cbv

theorem terminal_1 : value 1 =
    planeLowPsiValueWith GenusTwoPlaneLine.values (key 1) := by
  cbv

theorem terminal_2 : value 2 =
    planeLowPsiValueWith GenusTwoPlaneLine.values (key 2) := by
  cbv

theorem terminal_3 : value 3 =
    planeLowPsiValueWith GenusTwoPlaneLine.values (key 3) := by
  cbv

theorem terminal_4 : value 4 =
    planeLowPsiValueWith GenusTwoPlaneLine.values (key 4) := by
  cbv

theorem terminal_5 : value 5 =
    planeLowPsiValueWith GenusTwoPlaneLine.values (key 5) := by
  cbv

end LowPsi
end AxiomaticGW.GKM.PlaneGenusTwoAncestors

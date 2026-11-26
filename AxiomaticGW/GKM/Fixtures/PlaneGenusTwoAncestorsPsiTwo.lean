/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsData

/-!
# Plane ancestor arithmetic: PsiTwo

Input SHA256: 640e00ec2d4b2055c49465d80a3590da42dec51772d34ea00bad356dad0950a8
Candidate values become certificates only after their full equations are checked.
The original canonical seeds and geometric hypotheses are unchanged.
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoAncestors

open BelorousskiPandharipande SurfaceGenusTwo

namespace PsiTwo

attribute [local cbv_eval] PlaneGenusTwoFewMarkingsReplay.vectorLookup
attribute [local cbv_eval] PlaneGenusTwoFewMarkingsReplay.rationalCached
attribute [local cbv_eval] PlaneGenusTwoFewMarkingsReplay.ellipticCached

set_option maxHeartbeats 4000000 in
-- Replay the complete boundary contraction, including all lower-genus factors.
set_option cbv.maxSteps 4000000 in
theorem reduction_6 :
    ancestorReductionTerms (key 6) (by decide +kernel) = terms 6 := by
  apply of_decide_eq_true
  cbv

set_option maxHeartbeats 4000000 in
-- Replay the complete boundary contraction, including all lower-genus factors.
set_option cbv.maxSteps 4000000 in
theorem reduction_7 :
    ancestorReductionTerms (key 7) (by decide +kernel) = terms 7 := by
  apply of_decide_eq_true
  cbv

set_option maxHeartbeats 4000000 in
-- Replay the complete boundary contraction, including all lower-genus factors.
set_option cbv.maxSteps 4000000 in
theorem reduction_8 :
    ancestorReductionTerms (key 8) (by decide +kernel) = terms 8 := by
  apply of_decide_eq_true
  cbv

set_option maxHeartbeats 4000000 in
-- Replay the complete boundary contraction, including all lower-genus factors.
set_option cbv.maxSteps 4000000 in
theorem reduction_9 :
    ancestorReductionTerms (key 9) (by decide +kernel) = terms 9 := by
  apply of_decide_eq_true
  cbv

set_option maxHeartbeats 4000000 in
-- Replay the complete boundary contraction, including all lower-genus factors.
set_option cbv.maxSteps 4000000 in
theorem reduction_10 :
    ancestorReductionTerms (key 10) (by decide +kernel) = terms 10 := by
  apply of_decide_eq_true
  cbv

set_option maxHeartbeats 4000000 in
-- Replay the complete boundary contraction, including all lower-genus factors.
set_option cbv.maxSteps 4000000 in
theorem reduction_11 :
    ancestorReductionTerms (key 11) (by decide +kernel) = terms 11 := by
  apply of_decide_eq_true
  cbv

end PsiTwo
end AxiomaticGW.GKM.PlaneGenusTwoAncestors

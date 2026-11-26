/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsData
public import AxiomaticGW.Surfaces.LowGenusAncestorDimension

/-!
# Plane ancestor arithmetic: PsiSix

Input SHA256: 640e00ec2d4b2055c49465d80a3590da42dec51772d34ea00bad356dad0950a8
Candidate values become certificates only after their full equations are checked.
The original canonical seeds and geometric hypotheses are unchanged.
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoAncestors

open BelorousskiPandharipande SurfaceGenusTwo

namespace PsiSix

attribute [local cbv_eval] PlaneGenusTwoFewMarkingsReplay.vectorLookup
attribute [local cbv_eval] PlaneGenusTwoFewMarkingsReplay.rationalCached
attribute [local cbv_eval] PlaneGenusTwoFewMarkingsReplay.ellipticCached

-- Proved dimension vanishing avoids expanding impossible lower-genus ancestors.
attribute [local cbv_eval] SurfaceGenusZero.ancestorValue_pruned
attribute [local cbv_eval] SurfaceGenusOne.ancestorValue_pruned

set_option maxHeartbeats 4000000 in
-- Replay the complete boundary contraction, including all lower-genus factors.
set_option cbv.maxSteps 4000000 in
theorem reduction_35 :
    ancestorReductionTerms (key 35) (by decide +kernel) = terms 35 := by
  apply of_decide_eq_true
  cbv

set_option maxHeartbeats 4000000 in
-- Replay the complete boundary contraction, including all lower-genus factors.
set_option cbv.maxSteps 4000000 in
theorem reduction_36 :
    ancestorReductionTerms (key 36) (by decide +kernel) = terms 36 := by
  apply of_decide_eq_true
  cbv

set_option maxHeartbeats 4000000 in
-- Replay the complete boundary contraction, including all lower-genus factors.
set_option cbv.maxSteps 4000000 in
theorem reduction_37 :
    ancestorReductionTerms (key 37) (by decide +kernel) = terms 37 := by
  apply of_decide_eq_true
  cbv

set_option maxHeartbeats 4000000 in
-- Replay the complete boundary contraction, including all lower-genus factors.
set_option cbv.maxSteps 4000000 in
theorem reduction_38 :
    ancestorReductionTerms (key 38) (by decide +kernel) = terms 38 := by
  apply of_decide_eq_true
  cbv

end PsiSix
end AxiomaticGW.GKM.PlaneGenusTwoAncestors

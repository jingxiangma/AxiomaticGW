/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsData
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsCaches
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoPointAncestor

/-!
# Plane ancestor arithmetic: PsiThree

Input SHA256: 640e00ec2d4b2055c49465d80a3590da42dec51772d34ea00bad356dad0950a8
Candidate values become certificates only after their full equations are checked.
The original canonical seeds and geometric hypotheses are unchanged.
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoAncestors

open BelorousskiPandharipande SurfaceGenusTwo

namespace PsiThree

theorem reduction_12 :
    ancestorReductionTerms (key 12) (by decide +kernel) = terms 12 := by
  exact PlaneGenusTwoPointAncestor.reduction

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_13 :
    ancestorReductionTerms (key 13) (by decide +kernel) = terms 13 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_13]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_14 :
    ancestorReductionTerms (key 14) (by decide +kernel) = terms 14 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_14]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_15 :
    ancestorReductionTerms (key 15) (by decide +kernel) = terms 15 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_15]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_16 :
    ancestorReductionTerms (key 16) (by decide +kernel) = terms 16 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_16]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_17 :
    ancestorReductionTerms (key 17) (by decide +kernel) = terms 17 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_17]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_18 :
    ancestorReductionTerms (key 18) (by decide +kernel) = terms 18 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_18]
  decide +kernel

end PsiThree
end AxiomaticGW.GKM.PlaneGenusTwoAncestors

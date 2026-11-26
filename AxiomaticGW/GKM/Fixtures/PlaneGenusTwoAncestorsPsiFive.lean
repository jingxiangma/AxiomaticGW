/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsData
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsCaches

/-!
# Plane ancestor arithmetic: PsiFive

Input SHA256: 640e00ec2d4b2055c49465d80a3590da42dec51772d34ea00bad356dad0950a8
Candidate values become certificates only after their full equations are checked.
The original canonical seeds and geometric hypotheses are unchanged.
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoAncestors

open BelorousskiPandharipande SurfaceGenusTwo

namespace PsiFive

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_28 :
    ancestorReductionTerms (key 28) (by decide +kernel) = terms 28 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_28]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_29 :
    ancestorReductionTerms (key 29) (by decide +kernel) = terms 29 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_29]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_30 :
    ancestorReductionTerms (key 30) (by decide +kernel) = terms 30 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_30]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_31 :
    ancestorReductionTerms (key 31) (by decide +kernel) = terms 31 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_31]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_32 :
    ancestorReductionTerms (key 32) (by decide +kernel) = terms 32 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_32]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_33 :
    ancestorReductionTerms (key 33) (by decide +kernel) = terms 33 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_33]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_34 :
    ancestorReductionTerms (key 34) (by decide +kernel) = terms 34 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_34]
  decide +kernel

end PsiFive
end AxiomaticGW.GKM.PlaneGenusTwoAncestors

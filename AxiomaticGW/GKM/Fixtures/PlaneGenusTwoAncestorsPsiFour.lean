/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsData
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsCaches

/-!
# Plane ancestor arithmetic: PsiFour

Input SHA256: 640e00ec2d4b2055c49465d80a3590da42dec51772d34ea00bad356dad0950a8
Candidate values become certificates only after their full equations are checked.
The original canonical seeds and geometric hypotheses are unchanged.
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoAncestors

open BelorousskiPandharipande SurfaceGenusTwo

namespace PsiFour

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_19 :
    ancestorReductionTerms (key 19) (by decide +kernel) = terms 19 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_19]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_20 :
    ancestorReductionTerms (key 20) (by decide +kernel) = terms 20 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_20]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_21 :
    ancestorReductionTerms (key 21) (by decide +kernel) = terms 21 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_21]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_22 :
    ancestorReductionTerms (key 22) (by decide +kernel) = terms 22 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_22]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_23 :
    ancestorReductionTerms (key 23) (by decide +kernel) = terms 23 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_23]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_24 :
    ancestorReductionTerms (key 24) (by decide +kernel) = terms 24 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_24]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_25 :
    ancestorReductionTerms (key 25) (by decide +kernel) = terms 25 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_25]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_26 :
    ancestorReductionTerms (key 26) (by decide +kernel) = terms 26 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_26]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the full contraction using separately certified components.
theorem reduction_27 :
    ancestorReductionTerms (key 27) (by decide +kernel) = terms 27 := by
  rw [← ancestorReductionTermsCached_eq
    PlaneGenusTwoComponents.cache_27]
  decide +kernel

end PsiFour
end AxiomaticGW.GKM.PlaneGenusTwoAncestors

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsData

/-!
# Certified plane components: Genus0Psi0

Each candidate value is separately checked against the original residual algorithm.
The symbolic rows only select cache entries; final equations require their own replay.

Candidate input SHA256: 2001e7124121cf35e55daa7984cd86b3ac230a9d711f68b225941c4e7e3dbfc9
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoComponents
open SurfaceGenusTwo

namespace Genus0Psi0

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_1 : residualTerms (key 1) = entries 1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_2 : residualTerms (key 2) = entries 2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_7 : residualTerms (key 7) = entries 7 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_8 : residualTerms (key 8) = entries 8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_9 : residualTerms (key 9) = entries 9 := by
  decide +kernel

theorem value_11 : residualTerms (key 11) = entries 11 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 0) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

theorem value_16 : residualTerms (key 16) = entries 16 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 1) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_17 : residualTerms (key 17) = entries 17 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_18 : residualTerms (key 18) = entries 18 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_19 : residualTerms (key 19) = entries 19 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_43 : residualTerms (key 43) = entries 43 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_75 : residualTerms (key 75) = entries 75 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_84 : residualTerms (key 84) = entries 84 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_92 : residualTerms (key 92) = entries 92 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_121 : residualTerms (key 121) = entries 121 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_127 : residualTerms (key 127) = entries 127 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_133 : residualTerms (key 133) = entries 133 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_138 : residualTerms (key 138) = entries 138 := by
  decide +kernel

end Genus0Psi0
end AxiomaticGW.GKM.PlaneGenusTwoComponents

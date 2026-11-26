/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsData

/-!
# Certified plane components: Genus1Psi1

Each candidate value is separately checked against the original residual algorithm.
The symbolic rows only select cache entries; final equations require their own replay.

Candidate input SHA256: 2001e7124121cf35e55daa7984cd86b3ac230a9d711f68b225941c4e7e3dbfc9
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoComponents
open SurfaceGenusTwo

namespace Genus1Psi1

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_142 : residualTerms (key 142) = entries 142 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_143 : residualTerms (key 143) = entries 143 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_145 : residualTerms (key 145) = entries 145 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_148 : residualTerms (key 148) = entries 148 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_150 : residualTerms (key 150) = entries 150 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_154 : residualTerms (key 154) = entries 154 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_155 : residualTerms (key 155) = entries 155 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_157 : residualTerms (key 157) = entries 157 := by
  decide +kernel

theorem value_159 : residualTerms (key 159) = entries 159 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 10) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_163 : residualTerms (key 163) = entries 163 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_164 : residualTerms (key 164) = entries 164 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_165 : residualTerms (key 165) = entries 165 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_213 : residualTerms (key 213) = entries 213 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_244 : residualTerms (key 244) = entries 244 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_264 : residualTerms (key 264) = entries 264 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_272 : residualTerms (key 272) = entries 272 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_277 : residualTerms (key 277) = entries 277 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_285 : residualTerms (key 285) = entries 285 := by
  decide +kernel

theorem value_290 : residualTerms (key 290) = entries 290 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 20) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

end Genus1Psi1
end AxiomaticGW.GKM.PlaneGenusTwoComponents

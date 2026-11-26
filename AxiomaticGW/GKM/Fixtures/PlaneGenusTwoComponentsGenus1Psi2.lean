/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsData

/-!
# Certified plane components: Genus1Psi2

Each candidate value is separately checked against the original residual algorithm.
The symbolic rows only select cache entries; final equations require their own replay.

Candidate input SHA256: 2001e7124121cf35e55daa7984cd86b3ac230a9d711f68b225941c4e7e3dbfc9
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoComponents
open SurfaceGenusTwo

namespace Genus1Psi2

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_139 : residualTerms (key 139) = entries 139 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_140 : residualTerms (key 140) = entries 140 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_144 : residualTerms (key 144) = entries 144 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_146 : residualTerms (key 146) = entries 146 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_147 : residualTerms (key 147) = entries 147 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_149 : residualTerms (key 149) = entries 149 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_151 : residualTerms (key 151) = entries 151 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_152 : residualTerms (key 152) = entries 152 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_153 : residualTerms (key 153) = entries 153 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_160 : residualTerms (key 160) = entries 160 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_161 : residualTerms (key 161) = entries 161 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_162 : residualTerms (key 162) = entries 162 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_195 : residualTerms (key 195) = entries 195 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_197 : residualTerms (key 197) = entries 197 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_205 : residualTerms (key 205) = entries 205 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_207 : residualTerms (key 207) = entries 207 := by
  decide +kernel

theorem value_214 : residualTerms (key 214) = entries 214 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 13) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

theorem value_216 : residualTerms (key 216) = entries 216 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 14) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_233 : residualTerms (key 233) = entries 233 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_239 : residualTerms (key 239) = entries 239 := by
  decide +kernel

theorem value_245 : residualTerms (key 245) = entries 245 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 15) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_247 : residualTerms (key 247) = entries 247 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_257 : residualTerms (key 257) = entries 257 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_260 : residualTerms (key 260) = entries 260 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_261 : residualTerms (key 261) = entries 261 := by
  decide +kernel

theorem value_265 : residualTerms (key 265) = entries 265 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 16) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_270 : residualTerms (key 270) = entries 270 := by
  decide +kernel

theorem value_273 : residualTerms (key 273) = entries 273 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 17) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_274 : residualTerms (key 274) = entries 274 := by
  decide +kernel

theorem value_278 : residualTerms (key 278) = entries 278 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 18) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_283 : residualTerms (key 283) = entries 283 := by
  decide +kernel

theorem value_286 : residualTerms (key 286) = entries 286 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 19) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_287 : residualTerms (key 287) = entries 287 := by
  decide +kernel

end Genus1Psi2
end AxiomaticGW.GKM.PlaneGenusTwoComponents

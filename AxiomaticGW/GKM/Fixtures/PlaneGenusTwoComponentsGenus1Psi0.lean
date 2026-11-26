/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsData

/-!
# Certified plane components: Genus1Psi0

Each candidate value is separately checked against the original residual algorithm.
The symbolic rows only select cache entries; final equations require their own replay.

Candidate input SHA256: 2001e7124121cf35e55daa7984cd86b3ac230a9d711f68b225941c4e7e3dbfc9
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoComponents
open SurfaceGenusTwo

namespace Genus1Psi0

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_156 : residualTerms (key 156) = entries 156 := by
  decide +kernel

theorem value_158 : residualTerms (key 158) = entries 158 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 9) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

theorem value_166 : residualTerms (key 166) = entries 166 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 11) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

theorem value_167 : residualTerms (key 167) = entries 167 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 12) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_168 : residualTerms (key 168) = entries 168 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_289 : residualTerms (key 289) = entries 289 := by
  decide +kernel

end Genus1Psi0
end AxiomaticGW.GKM.PlaneGenusTwoComponents

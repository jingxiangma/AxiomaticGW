/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsData

/-!
# Certified plane components: Genus0Psi1

Each candidate value is separately checked against the original residual algorithm.
The symbolic rows only select cache entries; final equations require their own replay.

Candidate input SHA256: 2001e7124121cf35e55daa7984cd86b3ac230a9d711f68b225941c4e7e3dbfc9
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoComponents
open SurfaceGenusTwo

namespace Genus0Psi1

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_0 : residualTerms (key 0) = entries 0 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_3 : residualTerms (key 3) = entries 3 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_4 : residualTerms (key 4) = entries 4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_5 : residualTerms (key 5) = entries 5 := by
  decide +kernel

theorem value_10 : residualTerms (key 10) = entries 10 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 10) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_12 : residualTerms (key 12) = entries 12 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 12) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_13 : residualTerms (key 13) = entries 13 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_14 : residualTerms (key 14) = entries 14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_15 : residualTerms (key 15) = entries 15 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_34 : residualTerms (key 34) = entries 34 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_38 : residualTerms (key 38) = entries 38 := by
  decide +kernel

theorem value_44 : residualTerms (key 44) = entries 44 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 2) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_67 : residualTerms (key 67) = entries 67 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_71 : residualTerms (key 71) = entries 71 := by
  decide +kernel

theorem value_76 : residualTerms (key 76) = entries 76 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 3) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_80 : residualTerms (key 80) = entries 80 := by
  decide +kernel

theorem value_85 : residualTerms (key 85) = entries 85 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 4) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_89 : residualTerms (key 89) = entries 89 := by
  decide +kernel

theorem value_93 : residualTerms (key 93) = entries 93 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 5) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

theorem value_106 : residualTerms (key 106) = entries 106 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 106) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_116 : residualTerms (key 116) = entries 116 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_119 : residualTerms (key 119) = entries 119 := by
  decide +kernel

theorem value_122 : residualTerms (key 122) = entries 122 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 6) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_125 : residualTerms (key 125) = entries 125 := by
  decide +kernel

theorem value_128 : residualTerms (key 128) = entries 128 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 7) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_131 : residualTerms (key 131) = entries 131 := by
  decide +kernel

theorem value_134 : residualTerms (key 134) = entries 134 := by
  change residualTerms (PlaneGenusTwoPointComponents.key 8) = _
  rw [PlaneGenusTwoPointComponents.computed]
  decide +kernel

theorem value_137 : residualTerms (key 137) = entries 137 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 137) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

end Genus0Psi1
end AxiomaticGW.GKM.PlaneGenusTwoComponents

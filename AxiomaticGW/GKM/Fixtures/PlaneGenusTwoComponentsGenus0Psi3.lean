/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsData

/-!
# Certified plane components: Genus0Psi3

Each candidate value is separately checked against the original residual algorithm.
The symbolic rows only select cache entries; final equations require their own replay.

Candidate input SHA256: 2001e7124121cf35e55daa7984cd86b3ac230a9d711f68b225941c4e7e3dbfc9
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoComponents
open SurfaceGenusTwo

namespace Genus0Psi3

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_21 : residualTerms (key 21) = entries 21 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_23 : residualTerms (key 23) = entries 23 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_28 : residualTerms (key 28) = entries 28 := by
  decide +kernel

theorem value_32 : residualTerms (key 32) = entries 32 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 32) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_33 : residualTerms (key 33) = entries 33 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_36 : residualTerms (key 36) = entries 36 := by
  decide +kernel

theorem value_41 : residualTerms (key 41) = entries 41 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 41) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_42 : residualTerms (key 42) = entries 42 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 42) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_46 : residualTerms (key 46) = entries 46 := by
  decide +kernel

theorem value_49 : residualTerms (key 49) = entries 49 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 49) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_52 : residualTerms (key 52) = entries 52 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 52) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_62 : residualTerms (key 62) = entries 62 := by
  decide +kernel

theorem value_65 : residualTerms (key 65) = entries 65 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 65) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_66 : residualTerms (key 66) = entries 66 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_69 : residualTerms (key 69) = entries 69 := by
  decide +kernel

theorem value_73 : residualTerms (key 73) = entries 73 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 73) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_74 : residualTerms (key 74) = entries 74 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 74) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_78 : residualTerms (key 78) = entries 78 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 78) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_82 : residualTerms (key 82) = entries 82 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 82) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_83 : residualTerms (key 83) = entries 83 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 83) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_87 : residualTerms (key 87) = entries 87 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 87) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_91 : residualTerms (key 91) = entries 91 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 91) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_98 : residualTerms (key 98) = entries 98 := by
  decide +kernel

theorem value_100 : residualTerms (key 100) = entries 100 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 100) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_102 : residualTerms (key 102) = entries 102 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 102) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_104 : residualTerms (key 104) = entries 104 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 104) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_109 : residualTerms (key 109) = entries 109 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 109) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_111 : residualTerms (key 111) = entries 111 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 111) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_113 : residualTerms (key 113) = entries 113 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 113) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_114 : residualTerms (key 114) = entries 114 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_117 : residualTerms (key 117) = entries 117 := by
  decide +kernel

theorem value_123 : residualTerms (key 123) = entries 123 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 123) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_129 : residualTerms (key 129) = entries 129 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 129) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_135 : residualTerms (key 135) = entries 135 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 135) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

end Genus0Psi3
end AxiomaticGW.GKM.PlaneGenusTwoComponents

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsData

/-!
# Certified plane components: Genus0Psi2

Each candidate value is separately checked against the original residual algorithm.
The symbolic rows only select cache entries; final equations require their own replay.

Candidate input SHA256: 2001e7124121cf35e55daa7984cd86b3ac230a9d711f68b225941c4e7e3dbfc9
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoComponents
open SurfaceGenusTwo

namespace Genus0Psi2

theorem value_6 : residualTerms (key 6) = entries 6 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 6) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_22 : residualTerms (key 22) = entries 22 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_25 : residualTerms (key 25) = entries 25 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_26 : residualTerms (key 26) = entries 26 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_29 : residualTerms (key 29) = entries 29 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_30 : residualTerms (key 30) = entries 30 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_35 : residualTerms (key 35) = entries 35 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_37 : residualTerms (key 37) = entries 37 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_39 : residualTerms (key 39) = entries 39 := by
  decide +kernel

theorem value_45 : residualTerms (key 45) = entries 45 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 45) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_48 : residualTerms (key 48) = entries 48 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_51 : residualTerms (key 51) = entries 51 := by
  decide +kernel

theorem value_54 : residualTerms (key 54) = entries 54 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 54) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_55 : residualTerms (key 55) = entries 55 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 55) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_56 : residualTerms (key 56) = entries 56 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_58 : residualTerms (key 58) = entries 58 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_63 : residualTerms (key 63) = entries 63 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_64 : residualTerms (key 64) = entries 64 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_68 : residualTerms (key 68) = entries 68 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_70 : residualTerms (key 70) = entries 70 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_72 : residualTerms (key 72) = entries 72 := by
  decide +kernel

theorem value_77 : residualTerms (key 77) = entries 77 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 77) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_79 : residualTerms (key 79) = entries 79 := by
  decide +kernel

theorem value_81 : residualTerms (key 81) = entries 81 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 81) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_86 : residualTerms (key 86) = entries 86 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 86) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_88 : residualTerms (key 88) = entries 88 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 88) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_90 : residualTerms (key 90) = entries 90 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 90) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_99 : residualTerms (key 99) = entries 99 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_101 : residualTerms (key 101) = entries 101 := by
  decide +kernel

theorem value_103 : residualTerms (key 103) = entries 103 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 103) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_105 : residualTerms (key 105) = entries 105 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 105) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_107 : residualTerms (key 107) = entries 107 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 107) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_108 : residualTerms (key 108) = entries 108 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 108) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_110 : residualTerms (key 110) = entries 110 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_112 : residualTerms (key 112) = entries 112 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_115 : residualTerms (key 115) = entries 115 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_118 : residualTerms (key 118) = entries 118 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_120 : residualTerms (key 120) = entries 120 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor recursion at this full component.
theorem value_124 : residualTerms (key 124) = entries 124 := by
  decide +kernel

theorem value_126 : residualTerms (key 126) = entries 126 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 126) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_130 : residualTerms (key 130) = entries 130 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 130) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_132 : residualTerms (key 132) = entries 132 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 132) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_136 : residualTerms (key 136) = entries 136 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 136) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

end Genus0Psi2
end AxiomaticGW.GKM.PlaneGenusTwoComponents

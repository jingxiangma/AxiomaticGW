/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsData

/-!
# Certified plane components: Genus0Psi4

Each candidate value is separately checked against the original residual algorithm.
The symbolic rows only select cache entries; final equations require their own replay.

Candidate input SHA256: 2001e7124121cf35e55daa7984cd86b3ac230a9d711f68b225941c4e7e3dbfc9
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoComponents
open SurfaceGenusTwo

namespace Genus0Psi4

theorem value_20 : residualTerms (key 20) = entries 20 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 20) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_24 : residualTerms (key 24) = entries 24 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 24) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_27 : residualTerms (key 27) = entries 27 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 27) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_31 : residualTerms (key 31) = entries 31 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 31) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_40 : residualTerms (key 40) = entries 40 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 40) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_47 : residualTerms (key 47) = entries 47 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 47) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_50 : residualTerms (key 50) = entries 50 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 50) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_53 : residualTerms (key 53) = entries 53 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 53) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_57 : residualTerms (key 57) = entries 57 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 57) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_59 : residualTerms (key 59) = entries 59 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 59) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_60 : residualTerms (key 60) = entries 60 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 60) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_61 : residualTerms (key 61) = entries 61 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 61) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_94 : residualTerms (key 94) = entries 94 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 94) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_95 : residualTerms (key 95) = entries 95 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 95) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_96 : residualTerms (key 96) = entries 96 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 96) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

theorem value_97 : residualTerms (key 97) = entries 97 := by
  have hz := SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound
    (key 97) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_pos (by decide +kernel), hz]
  decide +kernel

end Genus0Psi4
end AxiomaticGW.GKM.PlaneGenusTwoComponents

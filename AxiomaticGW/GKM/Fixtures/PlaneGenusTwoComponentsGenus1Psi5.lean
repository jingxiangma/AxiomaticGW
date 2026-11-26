/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsData

/-!
# Certified plane components: Genus1Psi5

Each candidate value is separately checked against the original residual algorithm.
The symbolic rows only select cache entries; final equations require their own replay.

Candidate input SHA256: 2001e7124121cf35e55daa7984cd86b3ac230a9d711f68b225941c4e7e3dbfc9
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoComponents
open SurfaceGenusTwo

namespace Genus1Psi5

theorem value_169 : residualTerms (key 169) = entries 169 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 169) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_172 : residualTerms (key 172) = entries 172 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 172) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_176 : residualTerms (key 176) = entries 176 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 176) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_179 : residualTerms (key 179) = entries 179 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 179) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_181 : residualTerms (key 181) = entries 181 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 181) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_183 : residualTerms (key 183) = entries 183 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 183) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_184 : residualTerms (key 184) = entries 184 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 184) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_185 : residualTerms (key 185) = entries 185 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 185) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_188 : residualTerms (key 188) = entries 188 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 188) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_200 : residualTerms (key 200) = entries 200 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 200) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_219 : residualTerms (key 219) = entries 219 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 219) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_222 : residualTerms (key 222) = entries 222 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 222) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_223 : residualTerms (key 223) = entries 223 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 223) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_224 : residualTerms (key 224) = entries 224 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 224) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_227 : residualTerms (key 227) = entries 227 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 227) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_236 : residualTerms (key 236) = entries 236 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 236) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_249 : residualTerms (key 249) = entries 249 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 249) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_252 : residualTerms (key 252) = entries 252 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 252) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

end Genus1Psi5
end AxiomaticGW.GKM.PlaneGenusTwoComponents

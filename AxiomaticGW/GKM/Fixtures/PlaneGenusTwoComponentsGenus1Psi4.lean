/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsData
public import AxiomaticGW.Surfaces.GenusTwoCachedComponents
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsGenus0Psi0
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsGenus0Psi1
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsGenus0Psi2
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsGenus0Psi3
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsGenus1Psi0
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsGenus1Psi1
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsGenus1Psi2
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsGenus1Psi3

/-!
# Certified plane components: Genus1Psi4

Each candidate value is separately checked against the original residual algorithm.
The symbolic rows only select cache entries; final equations require their own replay.

Candidate input SHA256: 2001e7124121cf35e55daa7984cd86b3ac230a9d711f68b225941c4e7e3dbfc9
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoComponents
open SurfaceGenusTwo

namespace Genus1Psi4

-- Cache-selection SHA256: 6817bcfed4c1c432148fe5f9da51ac8a293fac0152910f2a2ed289f3a9b0d45f

private def indices_170 (j : Fin 8) : Fin 291 :=
  (#[
    21, 28, 32, 41, 82, 156, 158, 166
  ] : Array (Fin 291))[j.val]

private theorem components_170 (j : Fin 8) :
    residualTerms (key (indices_170 j)) = entries (indices_170 j) := by
  fin_cases j
  · exact Genus0Psi3.value_21
  · exact Genus0Psi3.value_28
  · exact Genus0Psi3.value_32
  · exact Genus0Psi3.value_41
  · exact Genus0Psi3.value_82
  · exact Genus1Psi0.value_156
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166

private def cache_170 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_170) (entries ∘ indices_170) (by decide +kernel)
    (fun j ↦ (components_170 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_170 : residualTerms (key 170) = entries 170 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_170 (key 170)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_173 (j : Fin 10) : Fin 291 :=
  (#[
    9, 11, 21, 28, 32, 41, 158, 166,
    211, 275
  ] : Array (Fin 291))[j.val]

private theorem components_173 (j : Fin 10) :
    residualTerms (key (indices_173 j)) = entries (indices_173 j) := by
  fin_cases j
  · exact Genus0Psi0.value_9
  · exact Genus0Psi0.value_11
  · exact Genus0Psi3.value_21
  · exact Genus0Psi3.value_28
  · exact Genus0Psi3.value_32
  · exact Genus0Psi3.value_41
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi3.value_211
  · exact Genus1Psi3.value_275

private def cache_173 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_173) (entries ∘ indices_173) (by decide +kernel)
    (fun j ↦ (components_173 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_173 : residualTerms (key 173) = entries 173 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_173 (key 173)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_175 (j : Fin 10) : Fin 291 :=
  (#[
    11, 90, 93, 144, 145, 158, 166, 208,
    287, 290
  ] : Array (Fin 291))[j.val]

private theorem components_175 (j : Fin 10) :
    residualTerms (key (indices_175 j)) = entries (indices_175 j) := by
  fin_cases j
  · exact Genus0Psi0.value_11
  · exact Genus0Psi2.value_90
  · exact Genus0Psi1.value_93
  · exact Genus1Psi2.value_144
  · exact Genus1Psi1.value_145
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi3.value_208
  · exact Genus1Psi2.value_287
  · exact Genus1Psi1.value_290

private def cache_175 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_175) (entries ∘ indices_175) (by decide +kernel)
    (fun j ↦ (components_175 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_175 : residualTerms (key 175) = entries 175 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_175 (key 175)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_177 (j : Fin 12) : Fin 291 :=
  (#[
    9, 11, 21, 28, 32, 41, 82, 156,
    158, 166, 211, 275
  ] : Array (Fin 291))[j.val]

private theorem components_177 (j : Fin 12) :
    residualTerms (key (indices_177 j)) = entries (indices_177 j) := by
  fin_cases j
  · exact Genus0Psi0.value_9
  · exact Genus0Psi0.value_11
  · exact Genus0Psi3.value_21
  · exact Genus0Psi3.value_28
  · exact Genus0Psi3.value_32
  · exact Genus0Psi3.value_41
  · exact Genus0Psi3.value_82
  · exact Genus1Psi0.value_156
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi3.value_211
  · exact Genus1Psi3.value_275

private def cache_177 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_177) (entries ∘ indices_177) (by decide +kernel)
    (fun j ↦ (components_177 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_177 : residualTerms (key 177) = entries 177 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_177 (key 177)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_186 (j : Fin 10) : Fin 291 :=
  (#[
    28, 62, 65, 73, 82, 156, 158, 166,
    167, 168
  ] : Array (Fin 291))[j.val]

private theorem components_186 (j : Fin 10) :
    residualTerms (key (indices_186 j)) = entries (indices_186 j) := by
  fin_cases j
  · exact Genus0Psi3.value_28
  · exact Genus0Psi3.value_62
  · exact Genus0Psi3.value_65
  · exact Genus0Psi3.value_73
  · exact Genus0Psi3.value_82
  · exact Genus1Psi0.value_156
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi0.value_168

private def cache_186 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_186) (entries ∘ indices_186) (by decide +kernel)
    (fun j ↦ (components_186 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_186 : residualTerms (key 186) = entries 186 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_186 (key 186)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_189 (j : Fin 14) : Fin 291 :=
  (#[
    16, 17, 28, 62, 65, 73, 82, 156,
    158, 166, 167, 211, 262, 275
  ] : Array (Fin 291))[j.val]

private theorem components_189 (j : Fin 14) :
    residualTerms (key (indices_189 j)) = entries (indices_189 j) := by
  fin_cases j
  · exact Genus0Psi0.value_16
  · exact Genus0Psi0.value_17
  · exact Genus0Psi3.value_28
  · exact Genus0Psi3.value_62
  · exact Genus0Psi3.value_65
  · exact Genus0Psi3.value_73
  · exact Genus0Psi3.value_82
  · exact Genus1Psi0.value_156
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi3.value_211
  · exact Genus1Psi3.value_262
  · exact Genus1Psi3.value_275

private def cache_189 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_189) (entries ∘ indices_189) (by decide +kernel)
    (fun j ↦ (components_189 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_189 : residualTerms (key 189) = entries 189 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_189 (key 189)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem value_192 : residualTerms (key 192) = entries 192 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 192) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

private def indices_193 (j : Fin 10) : Fin 291 :=
  (#[
    33, 66, 74, 83, 91, 109, 156, 158,
    166, 167
  ] : Array (Fin 291))[j.val]

private theorem components_193 (j : Fin 10) :
    residualTerms (key (indices_193 j)) = entries (indices_193 j) := by
  fin_cases j
  · exact Genus0Psi3.value_33
  · exact Genus0Psi3.value_66
  · exact Genus0Psi3.value_74
  · exact Genus0Psi3.value_83
  · exact Genus0Psi3.value_91
  · exact Genus0Psi3.value_109
  · exact Genus1Psi0.value_156
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167

private def cache_193 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_193) (entries ∘ indices_193) (by decide +kernel)
    (fun j ↦ (components_193 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_193 : residualTerms (key 193) = entries 193 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_193 (key 193)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_196 (j : Fin 15) : Fin 291 :=
  (#[
    9, 11, 33, 66, 74, 83, 91, 138,
    141, 156, 158, 166, 167, 276, 288
  ] : Array (Fin 291))[j.val]

private theorem components_196 (j : Fin 15) :
    residualTerms (key (indices_196 j)) = entries (indices_196 j) := by
  fin_cases j
  · exact Genus0Psi0.value_9
  · exact Genus0Psi0.value_11
  · exact Genus0Psi3.value_33
  · exact Genus0Psi3.value_66
  · exact Genus0Psi3.value_74
  · exact Genus0Psi3.value_83
  · exact Genus0Psi3.value_91
  · exact Genus0Psi0.value_138
  · exact Genus1Psi3.value_141
  · exact Genus1Psi0.value_156
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi3.value_276
  · exact Genus1Psi3.value_288

private def cache_196 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_196) (entries ∘ indices_196) (by decide +kernel)
    (fun j ↦ (components_196 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_196 : residualTerms (key 196) = entries 196 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_196 (key 196)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_199 (j : Fin 11) : Fin 291 :=
  (#[
    16, 85, 107, 134, 145, 151, 152, 158,
    166, 250, 290
  ] : Array (Fin 291))[j.val]

private theorem components_199 (j : Fin 11) :
    residualTerms (key (indices_199 j)) = entries (indices_199 j) := by
  fin_cases j
  · exact Genus0Psi0.value_16
  · exact Genus0Psi1.value_85
  · exact Genus0Psi2.value_107
  · exact Genus0Psi1.value_134
  · exact Genus1Psi1.value_145
  · exact Genus1Psi2.value_151
  · exact Genus1Psi2.value_152
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi3.value_250
  · exact Genus1Psi1.value_290

private def cache_199 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_199) (entries ∘ indices_199) (by decide +kernel)
    (fun j ↦ (components_199 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_199 : residualTerms (key 199) = entries 199 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_199 (key 199)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem value_203 : residualTerms (key 203) = entries 203 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 203) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

private def indices_204 (j : Fin 14) : Fin 291 :=
  (#[
    9, 16, 33, 66, 74, 83, 109, 138,
    141, 156, 158, 166, 276, 288
  ] : Array (Fin 291))[j.val]

private theorem components_204 (j : Fin 14) :
    residualTerms (key (indices_204 j)) = entries (indices_204 j) := by
  fin_cases j
  · exact Genus0Psi0.value_9
  · exact Genus0Psi0.value_16
  · exact Genus0Psi3.value_33
  · exact Genus0Psi3.value_66
  · exact Genus0Psi3.value_74
  · exact Genus0Psi3.value_83
  · exact Genus0Psi3.value_109
  · exact Genus0Psi0.value_138
  · exact Genus1Psi3.value_141
  · exact Genus1Psi0.value_156
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi3.value_276
  · exact Genus1Psi3.value_288

private def cache_204 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_204) (entries ∘ indices_204) (by decide +kernel)
    (fun j ↦ (components_204 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_204 : residualTerms (key 204) = entries 204 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_204 (key 204)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem value_209 : residualTerms (key 209) = entries 209 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 209) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_210 : residualTerms (key 210) = entries 210 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 210) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_215 : residualTerms (key 215) = entries 215 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 215) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

private def indices_218 (j : Fin 16) : Fin 291 :=
  (#[
    5, 11, 12, 23, 46, 49, 52, 81,
    90, 150, 158, 163, 166, 241, 274, 287
  ] : Array (Fin 291))[j.val]

private theorem components_218 (j : Fin 16) :
    residualTerms (key (indices_218 j)) = entries (indices_218 j) := by
  fin_cases j
  · exact Genus0Psi1.value_5
  · exact Genus0Psi0.value_11
  · exact Genus0Psi1.value_12
  · exact Genus0Psi3.value_23
  · exact Genus0Psi3.value_46
  · exact Genus0Psi3.value_49
  · exact Genus0Psi3.value_52
  · exact Genus0Psi2.value_81
  · exact Genus0Psi2.value_90
  · exact Genus1Psi1.value_150
  · exact Genus1Psi0.value_158
  · exact Genus1Psi1.value_163
  · exact Genus1Psi0.value_166
  · exact Genus1Psi3.value_241
  · exact Genus1Psi2.value_274
  · exact Genus1Psi2.value_287

private def cache_218 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_218) (entries ∘ indices_218) (by decide +kernel)
    (fun j ↦ (components_218 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_218 : residualTerms (key 218) = entries 218 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_218 (key 218)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_225 (j : Fin 12) : Fin 291 :=
  (#[
    16, 17, 28, 62, 65, 73, 82, 166,
    167, 168, 262, 275
  ] : Array (Fin 291))[j.val]

private theorem components_225 (j : Fin 12) :
    residualTerms (key (indices_225 j)) = entries (indices_225 j) := by
  fin_cases j
  · exact Genus0Psi0.value_16
  · exact Genus0Psi0.value_17
  · exact Genus0Psi3.value_28
  · exact Genus0Psi3.value_62
  · exact Genus0Psi3.value_65
  · exact Genus0Psi3.value_73
  · exact Genus0Psi3.value_82
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi0.value_168
  · exact Genus1Psi3.value_262
  · exact Genus1Psi3.value_275

private def cache_225 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_225) (entries ∘ indices_225) (by decide +kernel)
    (fun j ↦ (components_225 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_225 : residualTerms (key 225) = entries 225 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_225 (key 225)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_228 (j : Fin 11) : Fin 291 :=
  (#[
    10, 16, 81, 90, 155, 157, 166, 167,
    271, 274, 287
  ] : Array (Fin 291))[j.val]

private theorem components_228 (j : Fin 11) :
    residualTerms (key (indices_228 j)) = entries (indices_228 j) := by
  fin_cases j
  · exact Genus0Psi1.value_10
  · exact Genus0Psi0.value_16
  · exact Genus0Psi2.value_81
  · exact Genus0Psi2.value_90
  · exact Genus1Psi1.value_155
  · exact Genus1Psi1.value_157
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi3.value_271
  · exact Genus1Psi2.value_274
  · exact Genus1Psi2.value_287

private def cache_228 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_228) (entries ∘ indices_228) (by decide +kernel)
    (fun j ↦ (components_228 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_228 : residualTerms (key 228) = entries 228 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_228 (key 228)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem value_231 : residualTerms (key 231) = entries 231 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 231) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

private def indices_232 (j : Fin 14) : Fin 291 :=
  (#[
    9, 11, 16, 33, 66, 74, 83, 91,
    156, 158, 166, 167, 276, 288
  ] : Array (Fin 291))[j.val]

private theorem components_232 (j : Fin 14) :
    residualTerms (key (indices_232 j)) = entries (indices_232 j) := by
  fin_cases j
  · exact Genus0Psi0.value_9
  · exact Genus0Psi0.value_11
  · exact Genus0Psi0.value_16
  · exact Genus0Psi3.value_33
  · exact Genus0Psi3.value_66
  · exact Genus0Psi3.value_74
  · exact Genus0Psi3.value_83
  · exact Genus0Psi3.value_91
  · exact Genus1Psi0.value_156
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi3.value_276
  · exact Genus1Psi3.value_288

private def cache_232 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_232) (entries ∘ indices_232) (by decide +kernel)
    (fun j ↦ (components_232 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_232 : residualTerms (key 232) = entries 232 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_232 (key 232)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_235 (j : Fin 16) : Fin 291 :=
  (#[
    6, 10, 11, 36, 55, 69, 78, 87,
    89, 151, 157, 158, 166, 247, 279, 285
  ] : Array (Fin 291))[j.val]

private theorem components_235 (j : Fin 16) :
    residualTerms (key (indices_235 j)) = entries (indices_235 j) := by
  fin_cases j
  · exact Genus0Psi2.value_6
  · exact Genus0Psi1.value_10
  · exact Genus0Psi0.value_11
  · exact Genus0Psi3.value_36
  · exact Genus0Psi2.value_55
  · exact Genus0Psi3.value_69
  · exact Genus0Psi3.value_78
  · exact Genus0Psi3.value_87
  · exact Genus0Psi1.value_89
  · exact Genus1Psi2.value_151
  · exact Genus1Psi1.value_157
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi2.value_247
  · exact Genus1Psi3.value_279
  · exact Genus1Psi1.value_285

private def cache_235 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_235) (entries ∘ indices_235) (by decide +kernel)
    (fun j ↦ (components_235 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_235 : residualTerms (key 235) = entries 235 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_235 (key 235)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem value_238 : residualTerms (key 238) = entries 238 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 238) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_242 : residualTerms (key 242) = entries 242 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 242) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_243 : residualTerms (key 243) = entries 243 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 243) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_251 : residualTerms (key 251) = entries 251 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 251) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_254 : residualTerms (key 254) = entries 254 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 254) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

private def indices_255 (j : Fin 8) : Fin 291 :=
  (#[
    66, 109, 111, 113, 114, 166, 167, 168
  ] : Array (Fin 291))[j.val]

private theorem components_255 (j : Fin 8) :
    residualTerms (key (indices_255 j)) = entries (indices_255 j) := by
  fin_cases j
  · exact Genus0Psi3.value_66
  · exact Genus0Psi3.value_109
  · exact Genus0Psi3.value_111
  · exact Genus0Psi3.value_113
  · exact Genus0Psi3.value_114
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi0.value_168

private def cache_255 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_255) (entries ∘ indices_255) (by decide +kernel)
    (fun j ↦ (components_255 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_255 : residualTerms (key 255) = entries 255 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_255 (key 255)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_258 (j : Fin 12) : Fin 291 :=
  (#[
    16, 17, 66, 109, 111, 113, 114, 166,
    167, 168, 276, 288
  ] : Array (Fin 291))[j.val]

private theorem components_258 (j : Fin 12) :
    residualTerms (key (indices_258 j)) = entries (indices_258 j) := by
  fin_cases j
  · exact Genus0Psi0.value_16
  · exact Genus0Psi0.value_17
  · exact Genus0Psi3.value_66
  · exact Genus0Psi3.value_109
  · exact Genus0Psi3.value_111
  · exact Genus0Psi3.value_113
  · exact Genus0Psi3.value_114
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi0.value_168
  · exact Genus1Psi3.value_276
  · exact Genus1Psi3.value_288

private def cache_258 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_258) (entries ∘ indices_258) (by decide +kernel)
    (fun j ↦ (components_258 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_258 : residualTerms (key 258) = entries 258 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_258 (key 258)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem value_267 : residualTerms (key 267) = entries 267 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 267) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

private def indices_268 (j : Fin 16) : Fin 291 :=
  (#[
    16, 69, 107, 108, 117, 123, 129, 131,
    137, 151, 152, 155, 157, 166, 167, 279
  ] : Array (Fin 291))[j.val]

private theorem components_268 (j : Fin 16) :
    residualTerms (key (indices_268 j)) = entries (indices_268 j) := by
  fin_cases j
  · exact Genus0Psi0.value_16
  · exact Genus0Psi3.value_69
  · exact Genus0Psi2.value_107
  · exact Genus0Psi2.value_108
  · exact Genus0Psi3.value_117
  · exact Genus0Psi3.value_123
  · exact Genus0Psi3.value_129
  · exact Genus0Psi1.value_131
  · exact Genus0Psi1.value_137
  · exact Genus1Psi2.value_151
  · exact Genus1Psi2.value_152
  · exact Genus1Psi1.value_155
  · exact Genus1Psi1.value_157
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi3.value_279

private def cache_268 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_268) (entries ∘ indices_268) (by decide +kernel)
    (fun j ↦ (components_268 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_268 : residualTerms (key 268) = entries 268 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_268 (key 268)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem value_280 : residualTerms (key 280) = entries 280 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 280) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_281 : residualTerms (key 281) = entries 281 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 281) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

end Genus1Psi4
end AxiomaticGW.GKM.PlaneGenusTwoComponents

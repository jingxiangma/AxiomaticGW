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
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsGenus1Psi0
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsGenus1Psi1
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsGenus1Psi2

/-!
# Certified plane components: Genus1Psi3

Each candidate value is separately checked against the original residual algorithm.
The symbolic rows only select cache entries; final equations require their own replay.

Candidate input SHA256: 2001e7124121cf35e55daa7984cd86b3ac230a9d711f68b225941c4e7e3dbfc9
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoComponents
open SurfaceGenusTwo

namespace Genus1Psi3

-- Cache-selection SHA256: 6817bcfed4c1c432148fe5f9da51ac8a293fac0152910f2a2ed289f3a9b0d45f

private def indices_141 (j : Fin 3) : Fin 291 :=
  (#[
    6, 158, 166
  ] : Array (Fin 291))[j.val]

private theorem components_141 (j : Fin 3) :
    residualTerms (key (indices_141 j)) = entries (indices_141 j) := by
  fin_cases j
  · exact Genus0Psi2.value_6
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166

private def cache_141 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_141) (entries ∘ indices_141) (by decide +kernel)
    (fun j ↦ (components_141 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_141 : residualTerms (key 141) = entries 141 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_141 (key 141)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_171 (j : Fin 8) : Fin 291 :=
  (#[
    22, 29, 35, 45, 86, 156, 158, 166
  ] : Array (Fin 291))[j.val]

private theorem components_171 (j : Fin 8) :
    residualTerms (key (indices_171 j)) = entries (indices_171 j) := by
  fin_cases j
  · exact Genus0Psi2.value_22
  · exact Genus0Psi2.value_29
  · exact Genus0Psi2.value_35
  · exact Genus0Psi2.value_45
  · exact Genus0Psi2.value_86
  · exact Genus1Psi0.value_156
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166

private def cache_171 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_171) (entries ∘ indices_171) (by decide +kernel)
    (fun j ↦ (components_171 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_171 : residualTerms (key 171) = entries 171 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_171 (key 171)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_174 (j : Fin 10) : Fin 291 :=
  (#[
    9, 11, 22, 29, 35, 45, 158, 166,
    214, 278
  ] : Array (Fin 291))[j.val]

private theorem components_174 (j : Fin 10) :
    residualTerms (key (indices_174 j)) = entries (indices_174 j) := by
  fin_cases j
  · exact Genus0Psi0.value_9
  · exact Genus0Psi0.value_11
  · exact Genus0Psi2.value_22
  · exact Genus0Psi2.value_29
  · exact Genus0Psi2.value_35
  · exact Genus0Psi2.value_45
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi2.value_214
  · exact Genus1Psi2.value_278

private def cache_174 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_174) (entries ∘ indices_174) (by decide +kernel)
    (fun j ↦ (components_174 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_174 : residualTerms (key 174) = entries 174 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_174 (key 174)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_178 (j : Fin 12) : Fin 291 :=
  (#[
    9, 11, 22, 29, 35, 45, 86, 156,
    158, 166, 214, 278
  ] : Array (Fin 291))[j.val]

private theorem components_178 (j : Fin 12) :
    residualTerms (key (indices_178 j)) = entries (indices_178 j) := by
  fin_cases j
  · exact Genus0Psi0.value_9
  · exact Genus0Psi0.value_11
  · exact Genus0Psi2.value_22
  · exact Genus0Psi2.value_29
  · exact Genus0Psi2.value_35
  · exact Genus0Psi2.value_45
  · exact Genus0Psi2.value_86
  · exact Genus1Psi0.value_156
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi2.value_214
  · exact Genus1Psi2.value_278

private def cache_178 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_178) (entries ∘ indices_178) (by decide +kernel)
    (fun j ↦ (components_178 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_178 : residualTerms (key 178) = entries 178 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_178 (key 178)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_180 (j : Fin 7) : Fin 291 :=
  (#[
    11, 93, 145, 158, 166, 216, 290
  ] : Array (Fin 291))[j.val]

private theorem components_180 (j : Fin 7) :
    residualTerms (key (indices_180 j)) = entries (indices_180 j) := by
  fin_cases j
  · exact Genus0Psi0.value_11
  · exact Genus0Psi1.value_93
  · exact Genus1Psi1.value_145
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi2.value_216
  · exact Genus1Psi1.value_290

private def cache_180 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_180) (entries ∘ indices_180) (by decide +kernel)
    (fun j ↦ (components_180 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_180 : residualTerms (key 180) = entries 180 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_180 (key 180)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_182 (j : Fin 14) : Fin 291 :=
  (#[
    5, 12, 25, 48, 51, 54, 105, 106,
    145, 156, 158, 166, 277, 290
  ] : Array (Fin 291))[j.val]

private theorem components_182 (j : Fin 14) :
    residualTerms (key (indices_182 j)) = entries (indices_182 j) := by
  fin_cases j
  · exact Genus0Psi1.value_5
  · exact Genus0Psi1.value_12
  · exact Genus0Psi2.value_25
  · exact Genus0Psi2.value_48
  · exact Genus0Psi2.value_51
  · exact Genus0Psi2.value_54
  · exact Genus0Psi2.value_105
  · exact Genus0Psi1.value_106
  · exact Genus1Psi1.value_145
  · exact Genus1Psi0.value_156
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi1.value_277
  · exact Genus1Psi1.value_290

private def cache_182 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_182) (entries ∘ indices_182) (by decide +kernel)
    (fun j ↦ (components_182 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_182 : residualTerms (key 182) = entries 182 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_182 (key 182)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_187 (j : Fin 10) : Fin 291 :=
  (#[
    29, 63, 68, 77, 86, 156, 158, 166,
    167, 168
  ] : Array (Fin 291))[j.val]

private theorem components_187 (j : Fin 10) :
    residualTerms (key (indices_187 j)) = entries (indices_187 j) := by
  fin_cases j
  · exact Genus0Psi2.value_29
  · exact Genus0Psi2.value_63
  · exact Genus0Psi2.value_68
  · exact Genus0Psi2.value_77
  · exact Genus0Psi2.value_86
  · exact Genus1Psi0.value_156
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi0.value_168

private def cache_187 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_187) (entries ∘ indices_187) (by decide +kernel)
    (fun j ↦ (components_187 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_187 : residualTerms (key 187) = entries 187 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_187 (key 187)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_190 (j : Fin 14) : Fin 291 :=
  (#[
    16, 17, 29, 63, 68, 77, 86, 156,
    158, 166, 167, 214, 265, 278
  ] : Array (Fin 291))[j.val]

private theorem components_190 (j : Fin 14) :
    residualTerms (key (indices_190 j)) = entries (indices_190 j) := by
  fin_cases j
  · exact Genus0Psi0.value_16
  · exact Genus0Psi0.value_17
  · exact Genus0Psi2.value_29
  · exact Genus0Psi2.value_63
  · exact Genus0Psi2.value_68
  · exact Genus0Psi2.value_77
  · exact Genus0Psi2.value_86
  · exact Genus1Psi0.value_156
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi2.value_214
  · exact Genus1Psi2.value_265
  · exact Genus1Psi2.value_278

private def cache_190 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_190) (entries ∘ indices_190) (by decide +kernel)
    (fun j ↦ (components_190 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_190 : residualTerms (key 190) = entries 190 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_190 (key 190)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_191 (j : Fin 9) : Fin 291 :=
  (#[
    10, 137, 145, 156, 158, 166, 167, 277,
    290
  ] : Array (Fin 291))[j.val]

private theorem components_191 (j : Fin 9) :
    residualTerms (key (indices_191 j)) = entries (indices_191 j) := by
  fin_cases j
  · exact Genus0Psi1.value_10
  · exact Genus0Psi1.value_137
  · exact Genus1Psi1.value_145
  · exact Genus1Psi0.value_156
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi1.value_277
  · exact Genus1Psi1.value_290

private def cache_191 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_191) (entries ∘ indices_191) (by decide +kernel)
    (fun j ↦ (components_191 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_191 : residualTerms (key 191) = entries 191 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_191 (key 191)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_194 (j : Fin 10) : Fin 291 :=
  (#[
    30, 64, 72, 81, 90, 132, 156, 158,
    166, 167
  ] : Array (Fin 291))[j.val]

private theorem components_194 (j : Fin 10) :
    residualTerms (key (indices_194 j)) = entries (indices_194 j) := by
  fin_cases j
  · exact Genus0Psi2.value_30
  · exact Genus0Psi2.value_64
  · exact Genus0Psi2.value_72
  · exact Genus0Psi2.value_81
  · exact Genus0Psi2.value_90
  · exact Genus0Psi2.value_132
  · exact Genus1Psi0.value_156
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167

private def cache_194 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_194) (entries ∘ indices_194) (by decide +kernel)
    (fun j ↦ (components_194 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_194 : residualTerms (key 194) = entries 194 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_194 (key 194)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_198 (j : Fin 7) : Fin 291 :=
  (#[
    35, 68, 77, 86, 158, 166, 167
  ] : Array (Fin 291))[j.val]

private theorem components_198 (j : Fin 7) :
    residualTerms (key (indices_198 j)) = entries (indices_198 j) := by
  fin_cases j
  · exact Genus0Psi2.value_35
  · exact Genus0Psi2.value_68
  · exact Genus0Psi2.value_77
  · exact Genus0Psi2.value_86
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167

private def cache_198 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_198) (entries ∘ indices_198) (by decide +kernel)
    (fun j ↦ (components_198 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_198 : residualTerms (key 198) = entries 198 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_198 (key 198)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_201 (j : Fin 11) : Fin 291 :=
  (#[
    16, 85, 134, 137, 145, 155, 157, 158,
    166, 273, 290
  ] : Array (Fin 291))[j.val]

private theorem components_201 (j : Fin 11) :
    residualTerms (key (indices_201 j)) = entries (indices_201 j) := by
  fin_cases j
  · exact Genus0Psi0.value_16
  · exact Genus0Psi1.value_85
  · exact Genus0Psi1.value_134
  · exact Genus0Psi1.value_137
  · exact Genus1Psi1.value_145
  · exact Genus1Psi1.value_155
  · exact Genus1Psi1.value_157
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi2.value_273
  · exact Genus1Psi1.value_290

private def cache_201 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_201) (entries ∘ indices_201) (by decide +kernel)
    (fun j ↦ (components_201 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_201 : residualTerms (key 201) = entries 201 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_201 (key 201)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_202 (j : Fin 14) : Fin 291 :=
  (#[
    9, 16, 30, 64, 72, 81, 132, 138,
    144, 156, 158, 166, 274, 287
  ] : Array (Fin 291))[j.val]

private theorem components_202 (j : Fin 14) :
    residualTerms (key (indices_202 j)) = entries (indices_202 j) := by
  fin_cases j
  · exact Genus0Psi0.value_9
  · exact Genus0Psi0.value_16
  · exact Genus0Psi2.value_30
  · exact Genus0Psi2.value_64
  · exact Genus0Psi2.value_72
  · exact Genus0Psi2.value_81
  · exact Genus0Psi2.value_132
  · exact Genus0Psi0.value_138
  · exact Genus1Psi2.value_144
  · exact Genus1Psi0.value_156
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi2.value_274
  · exact Genus1Psi2.value_287

private def cache_202 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_202) (entries ∘ indices_202) (by decide +kernel)
    (fun j ↦ (components_202 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_202 : residualTerms (key 202) = entries 202 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_202 (key 202)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_206 (j : Fin 8) : Fin 291 :=
  (#[
    16, 35, 68, 77, 86, 158, 166, 278
  ] : Array (Fin 291))[j.val]

private theorem components_206 (j : Fin 8) :
    residualTerms (key (indices_206 j)) = entries (indices_206 j) := by
  fin_cases j
  · exact Genus0Psi0.value_16
  · exact Genus0Psi2.value_35
  · exact Genus0Psi2.value_68
  · exact Genus0Psi2.value_77
  · exact Genus0Psi2.value_86
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi2.value_278

private def cache_206 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_206) (entries ∘ indices_206) (by decide +kernel)
    (fun j ↦ (components_206 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_206 : residualTerms (key 206) = entries 206 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_206 (key 206)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_208 (j : Fin 4) : Fin 291 :=
  (#[
    10, 158, 166, 290
  ] : Array (Fin 291))[j.val]

private theorem components_208 (j : Fin 4) :
    residualTerms (key (indices_208 j)) = entries (indices_208 j) := by
  fin_cases j
  · exact Genus0Psi1.value_10
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi1.value_290

private def cache_208 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_208) (entries ∘ indices_208) (by decide +kernel)
    (fun j ↦ (components_208 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_208 : residualTerms (key 208) = entries 208 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_208 (key 208)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_211 (j : Fin 6) : Fin 291 :=
  (#[
    39, 72, 81, 90, 158, 166
  ] : Array (Fin 291))[j.val]

private theorem components_211 (j : Fin 6) :
    residualTerms (key (indices_211 j)) = entries (indices_211 j) := by
  fin_cases j
  · exact Genus0Psi2.value_39
  · exact Genus0Psi2.value_72
  · exact Genus0Psi2.value_81
  · exact Genus0Psi2.value_90
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166

private def cache_211 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_211) (entries ∘ indices_211) (by decide +kernel)
    (fun j ↦ (components_211 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_211 : residualTerms (key 211) = entries 211 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_211 (key 211)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_212 (j : Fin 10) : Fin 291 :=
  (#[
    6, 26, 55, 56, 58, 107, 156, 158,
    166, 289
  ] : Array (Fin 291))[j.val]

private theorem components_212 (j : Fin 10) :
    residualTerms (key (indices_212 j)) = entries (indices_212 j) := by
  fin_cases j
  · exact Genus0Psi2.value_6
  · exact Genus0Psi2.value_26
  · exact Genus0Psi2.value_55
  · exact Genus0Psi2.value_56
  · exact Genus0Psi2.value_58
  · exact Genus0Psi2.value_107
  · exact Genus1Psi0.value_156
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_289

private def cache_212 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_212) (entries ∘ indices_212) (by decide +kernel)
    (fun j ↦ (components_212 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_212 : residualTerms (key 212) = entries 212 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_212 (key 212)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem value_217 : residualTerms (key 217) = entries 217 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 217) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

private def indices_220 (j : Fin 16) : Fin 291 :=
  (#[
    5, 11, 12, 25, 48, 51, 54, 85,
    93, 150, 158, 163, 166, 245, 277, 290
  ] : Array (Fin 291))[j.val]

private theorem components_220 (j : Fin 16) :
    residualTerms (key (indices_220 j)) = entries (indices_220 j) := by
  fin_cases j
  · exact Genus0Psi1.value_5
  · exact Genus0Psi0.value_11
  · exact Genus0Psi1.value_12
  · exact Genus0Psi2.value_25
  · exact Genus0Psi2.value_48
  · exact Genus0Psi2.value_51
  · exact Genus0Psi2.value_54
  · exact Genus0Psi1.value_85
  · exact Genus0Psi1.value_93
  · exact Genus1Psi1.value_150
  · exact Genus1Psi0.value_158
  · exact Genus1Psi1.value_163
  · exact Genus1Psi0.value_166
  · exact Genus1Psi2.value_245
  · exact Genus1Psi1.value_277
  · exact Genus1Psi1.value_290

private def cache_220 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_220) (entries ∘ indices_220) (by decide +kernel)
    (fun j ↦ (components_220 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_220 : residualTerms (key 220) = entries 220 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_220 (key 220)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_221 (j : Fin 12) : Fin 291 :=
  (#[
    6, 11, 26, 55, 56, 58, 92, 151,
    158, 166, 247, 289
  ] : Array (Fin 291))[j.val]

private theorem components_221 (j : Fin 12) :
    residualTerms (key (indices_221 j)) = entries (indices_221 j) := by
  fin_cases j
  · exact Genus0Psi2.value_6
  · exact Genus0Psi0.value_11
  · exact Genus0Psi2.value_26
  · exact Genus0Psi2.value_55
  · exact Genus0Psi2.value_56
  · exact Genus0Psi2.value_58
  · exact Genus0Psi0.value_92
  · exact Genus1Psi2.value_151
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi2.value_247
  · exact Genus1Psi0.value_289

private def cache_221 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_221) (entries ∘ indices_221) (by decide +kernel)
    (fun j ↦ (components_221 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_221 : residualTerms (key 221) = entries 221 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_221 (key 221)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_226 (j : Fin 12) : Fin 291 :=
  (#[
    16, 17, 29, 63, 68, 77, 86, 166,
    167, 168, 265, 278
  ] : Array (Fin 291))[j.val]

private theorem components_226 (j : Fin 12) :
    residualTerms (key (indices_226 j)) = entries (indices_226 j) := by
  fin_cases j
  · exact Genus0Psi0.value_16
  · exact Genus0Psi0.value_17
  · exact Genus0Psi2.value_29
  · exact Genus0Psi2.value_63
  · exact Genus0Psi2.value_68
  · exact Genus0Psi2.value_77
  · exact Genus0Psi2.value_86
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi0.value_168
  · exact Genus1Psi2.value_265
  · exact Genus1Psi2.value_278

private def cache_226 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_226) (entries ∘ indices_226) (by decide +kernel)
    (fun j ↦ (components_226 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_226 : residualTerms (key 226) = entries 226 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_226 (key 226)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_229 (j : Fin 11) : Fin 291 :=
  (#[
    10, 16, 85, 93, 155, 157, 166, 167,
    273, 277, 290
  ] : Array (Fin 291))[j.val]

private theorem components_229 (j : Fin 11) :
    residualTerms (key (indices_229 j)) = entries (indices_229 j) := by
  fin_cases j
  · exact Genus0Psi1.value_10
  · exact Genus0Psi0.value_16
  · exact Genus0Psi1.value_85
  · exact Genus0Psi1.value_93
  · exact Genus1Psi1.value_155
  · exact Genus1Psi1.value_157
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi2.value_273
  · exact Genus1Psi1.value_277
  · exact Genus1Psi1.value_290

private def cache_229 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_229) (entries ∘ indices_229) (by decide +kernel)
    (fun j ↦ (components_229 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_229 : residualTerms (key 229) = entries 229 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_229 (key 229)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_230 (j : Fin 14) : Fin 291 :=
  (#[
    9, 11, 16, 30, 64, 72, 81, 90,
    156, 158, 166, 167, 274, 287
  ] : Array (Fin 291))[j.val]

private theorem components_230 (j : Fin 14) :
    residualTerms (key (indices_230 j)) = entries (indices_230 j) := by
  fin_cases j
  · exact Genus0Psi0.value_9
  · exact Genus0Psi0.value_11
  · exact Genus0Psi0.value_16
  · exact Genus0Psi2.value_30
  · exact Genus0Psi2.value_64
  · exact Genus0Psi2.value_72
  · exact Genus0Psi2.value_81
  · exact Genus0Psi2.value_90
  · exact Genus1Psi0.value_156
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi2.value_274
  · exact Genus1Psi2.value_287

private def cache_230 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_230) (entries ∘ indices_230) (by decide +kernel)
    (fun j ↦ (components_230 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_230 : residualTerms (key 230) = entries 230 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_230 (key 230)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_234 (j : Fin 8) : Fin 291 :=
  (#[
    16, 35, 68, 77, 86, 166, 167, 278
  ] : Array (Fin 291))[j.val]

private theorem components_234 (j : Fin 8) :
    residualTerms (key (indices_234 j)) = entries (indices_234 j) := by
  fin_cases j
  · exact Genus0Psi0.value_16
  · exact Genus0Psi2.value_35
  · exact Genus0Psi2.value_68
  · exact Genus0Psi2.value_77
  · exact Genus0Psi2.value_86
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi2.value_278

private def cache_234 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_234) (entries ∘ indices_234) (by decide +kernel)
    (fun j ↦ (components_234 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_234 : residualTerms (key 234) = entries 234 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_234 (key 234)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_237 (j : Fin 12) : Fin 291 :=
  (#[
    10, 11, 37, 70, 79, 88, 89, 157,
    158, 166, 283, 285
  ] : Array (Fin 291))[j.val]

private theorem components_237 (j : Fin 12) :
    residualTerms (key (indices_237 j)) = entries (indices_237 j) := by
  fin_cases j
  · exact Genus0Psi1.value_10
  · exact Genus0Psi0.value_11
  · exact Genus0Psi2.value_37
  · exact Genus0Psi2.value_70
  · exact Genus0Psi2.value_79
  · exact Genus0Psi2.value_88
  · exact Genus0Psi1.value_89
  · exact Genus1Psi1.value_157
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi2.value_283
  · exact Genus1Psi1.value_285

private def cache_237 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_237) (entries ∘ indices_237) (by decide +kernel)
    (fun j ↦ (components_237 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_237 : residualTerms (key 237) = entries 237 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_237 (key 237)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_240 (j : Fin 5) : Fin 291 :=
  (#[
    10, 93, 157, 166, 290
  ] : Array (Fin 291))[j.val]

private theorem components_240 (j : Fin 5) :
    residualTerms (key (indices_240 j)) = entries (indices_240 j) := by
  fin_cases j
  · exact Genus0Psi1.value_10
  · exact Genus0Psi1.value_93
  · exact Genus1Psi1.value_157
  · exact Genus1Psi0.value_166
  · exact Genus1Psi1.value_290

private def cache_240 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_240) (entries ∘ indices_240) (by decide +kernel)
    (fun j ↦ (components_240 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_240 : residualTerms (key 240) = entries 240 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_240 (key 240)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_241 (j : Fin 8) : Fin 291 :=
  (#[
    11, 39, 72, 81, 90, 158, 166, 287
  ] : Array (Fin 291))[j.val]

private theorem components_241 (j : Fin 8) :
    residualTerms (key (indices_241 j)) = entries (indices_241 j) := by
  fin_cases j
  · exact Genus0Psi0.value_11
  · exact Genus0Psi2.value_39
  · exact Genus0Psi2.value_72
  · exact Genus0Psi2.value_81
  · exact Genus0Psi2.value_90
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi2.value_287

private def cache_241 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_241) (entries ∘ indices_241) (by decide +kernel)
    (fun j ↦ (components_241 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_241 : residualTerms (key 241) = entries 241 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_241 (key 241)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem value_246 : residualTerms (key 246) = entries 246 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 246) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_248 : residualTerms (key 248) = entries 248 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 248) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

private def indices_250 (j : Fin 8) : Fin 291 :=
  (#[
    12, 51, 101, 103, 105, 166, 167, 290
  ] : Array (Fin 291))[j.val]

private theorem components_250 (j : Fin 8) :
    residualTerms (key (indices_250 j)) = entries (indices_250 j) := by
  fin_cases j
  · exact Genus0Psi1.value_12
  · exact Genus0Psi2.value_51
  · exact Genus0Psi2.value_101
  · exact Genus0Psi2.value_103
  · exact Genus0Psi2.value_105
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi1.value_290

private def cache_250 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_250) (entries ∘ indices_250) (by decide +kernel)
    (fun j ↦ (components_250 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_250 : residualTerms (key 250) = entries 250 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_250 (key 250)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_253 (j : Fin 12) : Fin 291 :=
  (#[
    12, 13, 48, 99, 101, 103, 105, 166,
    167, 168, 277, 290
  ] : Array (Fin 291))[j.val]

private theorem components_253 (j : Fin 12) :
    residualTerms (key (indices_253 j)) = entries (indices_253 j) := by
  fin_cases j
  · exact Genus0Psi1.value_12
  · exact Genus0Psi1.value_13
  · exact Genus0Psi2.value_48
  · exact Genus0Psi2.value_99
  · exact Genus0Psi2.value_101
  · exact Genus0Psi2.value_103
  · exact Genus0Psi2.value_105
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi0.value_168
  · exact Genus1Psi1.value_277
  · exact Genus1Psi1.value_290

private def cache_253 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_253) (entries ∘ indices_253) (by decide +kernel)
    (fun j ↦ (components_253 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_253 : residualTerms (key 253) = entries 253 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_253 (key 253)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_256 (j : Fin 8) : Fin 291 :=
  (#[
    64, 115, 120, 126, 132, 166, 167, 168
  ] : Array (Fin 291))[j.val]

private theorem components_256 (j : Fin 8) :
    residualTerms (key (indices_256 j)) = entries (indices_256 j) := by
  fin_cases j
  · exact Genus0Psi2.value_64
  · exact Genus0Psi2.value_115
  · exact Genus0Psi2.value_120
  · exact Genus0Psi2.value_126
  · exact Genus0Psi2.value_132
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi0.value_168

private def cache_256 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_256) (entries ∘ indices_256) (by decide +kernel)
    (fun j ↦ (components_256 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_256 : residualTerms (key 256) = entries 256 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_256 (key 256)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_259 (j : Fin 12) : Fin 291 :=
  (#[
    16, 17, 64, 115, 120, 126, 132, 166,
    167, 168, 274, 287
  ] : Array (Fin 291))[j.val]

private theorem components_259 (j : Fin 12) :
    residualTerms (key (indices_259 j)) = entries (indices_259 j) := by
  fin_cases j
  · exact Genus0Psi0.value_16
  · exact Genus0Psi0.value_17
  · exact Genus0Psi2.value_64
  · exact Genus0Psi2.value_115
  · exact Genus0Psi2.value_120
  · exact Genus0Psi2.value_126
  · exact Genus0Psi2.value_132
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi0.value_168
  · exact Genus1Psi2.value_274
  · exact Genus1Psi2.value_287

private def cache_259 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_259) (entries ∘ indices_259) (by decide +kernel)
    (fun j ↦ (components_259 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_259 : residualTerms (key 259) = entries 259 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_259 (key 259)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_262 (j : Fin 6) : Fin 291 :=
  (#[
    72, 120, 126, 132, 166, 167
  ] : Array (Fin 291))[j.val]

private theorem components_262 (j : Fin 6) :
    residualTerms (key (indices_262 j)) = entries (indices_262 j) := by
  fin_cases j
  · exact Genus0Psi2.value_72
  · exact Genus0Psi2.value_120
  · exact Genus0Psi2.value_126
  · exact Genus0Psi2.value_132
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167

private def cache_262 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_262) (entries ∘ indices_262) (by decide +kernel)
    (fun j ↦ (components_262 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_262 : residualTerms (key 262) = entries 262 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_262 (key 262)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_263 (j : Fin 10) : Fin 291 :=
  (#[
    58, 107, 108, 110, 112, 156, 158, 166,
    167, 168
  ] : Array (Fin 291))[j.val]

private theorem components_263 (j : Fin 10) :
    residualTerms (key (indices_263 j)) = entries (indices_263 j) := by
  fin_cases j
  · exact Genus0Psi2.value_58
  · exact Genus0Psi2.value_107
  · exact Genus0Psi2.value_108
  · exact Genus0Psi2.value_110
  · exact Genus0Psi2.value_112
  · exact Genus1Psi0.value_156
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi0.value_168

private def cache_263 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_263) (entries ∘ indices_263) (by decide +kernel)
    (fun j ↦ (components_263 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_263 : residualTerms (key 263) = entries 263 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_263 (key 263)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_266 (j : Fin 15) : Fin 291 :=
  (#[
    16, 58, 107, 108, 110, 112, 133, 138,
    151, 152, 156, 158, 166, 167, 247
  ] : Array (Fin 291))[j.val]

private theorem components_266 (j : Fin 15) :
    residualTerms (key (indices_266 j)) = entries (indices_266 j) := by
  fin_cases j
  · exact Genus0Psi0.value_16
  · exact Genus0Psi2.value_58
  · exact Genus0Psi2.value_107
  · exact Genus0Psi2.value_108
  · exact Genus0Psi2.value_110
  · exact Genus0Psi2.value_112
  · exact Genus0Psi0.value_133
  · exact Genus0Psi0.value_138
  · exact Genus1Psi2.value_151
  · exact Genus1Psi2.value_152
  · exact Genus1Psi0.value_156
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi2.value_247

private def cache_266 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_266) (entries ∘ indices_266) (by decide +kernel)
    (fun j ↦ (components_266 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_266 : residualTerms (key 266) = entries 266 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_266 (key 266)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_269 (j : Fin 12) : Fin 291 :=
  (#[
    16, 70, 118, 124, 130, 131, 137, 155,
    157, 166, 167, 283
  ] : Array (Fin 291))[j.val]

private theorem components_269 (j : Fin 12) :
    residualTerms (key (indices_269 j)) = entries (indices_269 j) := by
  fin_cases j
  · exact Genus0Psi0.value_16
  · exact Genus0Psi2.value_70
  · exact Genus0Psi2.value_118
  · exact Genus0Psi2.value_124
  · exact Genus0Psi2.value_130
  · exact Genus0Psi1.value_131
  · exact Genus0Psi1.value_137
  · exact Genus1Psi1.value_155
  · exact Genus1Psi1.value_157
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi2.value_283

private def cache_269 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_269) (entries ∘ indices_269) (by decide +kernel)
    (fun j ↦ (components_269 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_269 : residualTerms (key 269) = entries 269 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_269 (key 269)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_271 (j : Fin 8) : Fin 291 :=
  (#[
    16, 72, 120, 126, 132, 166, 167, 287
  ] : Array (Fin 291))[j.val]

private theorem components_271 (j : Fin 8) :
    residualTerms (key (indices_271 j)) = entries (indices_271 j) := by
  fin_cases j
  · exact Genus0Psi0.value_16
  · exact Genus0Psi2.value_72
  · exact Genus0Psi2.value_120
  · exact Genus0Psi2.value_126
  · exact Genus0Psi2.value_132
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167
  · exact Genus1Psi2.value_287

private def cache_271 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_271) (entries ∘ indices_271) (by decide +kernel)
    (fun j ↦ (components_271 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_271 : residualTerms (key 271) = entries 271 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_271 (key 271)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem value_275 : residualTerms (key 275) = entries 275 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 275) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

private def indices_276 (j : Fin 7) : Fin 291 :=
  (#[
    56, 107, 108, 110, 158, 166, 167
  ] : Array (Fin 291))[j.val]

private theorem components_276 (j : Fin 7) :
    residualTerms (key (indices_276 j)) = entries (indices_276 j) := by
  fin_cases j
  · exact Genus0Psi2.value_56
  · exact Genus0Psi2.value_107
  · exact Genus0Psi2.value_108
  · exact Genus0Psi2.value_110
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166
  · exact Genus1Psi0.value_167

private def cache_276 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_276) (entries ∘ indices_276) (by decide +kernel)
    (fun j ↦ (components_276 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_276 : residualTerms (key 276) = entries 276 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_276 (key 276)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_279 (j : Fin 8) : Fin 291 :=
  (#[
    56, 107, 108, 110, 138, 151, 158, 166
  ] : Array (Fin 291))[j.val]

private theorem components_279 (j : Fin 8) :
    residualTerms (key (indices_279 j)) = entries (indices_279 j) := by
  fin_cases j
  · exact Genus0Psi2.value_56
  · exact Genus0Psi2.value_107
  · exact Genus0Psi2.value_108
  · exact Genus0Psi2.value_110
  · exact Genus0Psi0.value_138
  · exact Genus1Psi2.value_151
  · exact Genus1Psi0.value_158
  · exact Genus1Psi0.value_166

private def cache_279 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_279) (entries ∘ indices_279) (by decide +kernel)
    (fun j ↦ (components_279 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_279 : residualTerms (key 279) = entries 279 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_279 (key 279)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def indices_282 (j : Fin 6) : Fin 291 :=
  (#[
    79, 124, 130, 137, 157, 166
  ] : Array (Fin 291))[j.val]

private theorem components_282 (j : Fin 6) :
    residualTerms (key (indices_282 j)) = entries (indices_282 j) := by
  fin_cases j
  · exact Genus0Psi2.value_79
  · exact Genus0Psi2.value_124
  · exact Genus0Psi2.value_130
  · exact Genus0Psi1.value_137
  · exact Genus1Psi1.value_157
  · exact Genus1Psi0.value_166

private def cache_282 : ResidualCache .plane :=
  .ofEntries (key ∘ indices_282) (entries ∘ indices_282) (by decide +kernel)
    (fun j ↦ (components_282 j).symm)

set_option maxHeartbeats 4000000 in
-- Check the original finite ancestor equation at this full component.
theorem value_282 : residualTerms (key 282) = entries 282 := by
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),
    ← ellipticStepCached_eq cache_282 (key 282)
      (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem value_284 : residualTerms (key 284) = entries 284 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 284) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

theorem value_288 : residualTerms (key 288) = entries 288 := by
  have hz := SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound
    (key 288) (by decide +kernel) (by decide +kernel)
  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),
    SurfaceGenusOne.componentValue, if_neg (by decide +kernel), hz]
  decide +kernel

end Genus1Psi3
end AxiomaticGW.GKM.PlaneGenusTwoComponents

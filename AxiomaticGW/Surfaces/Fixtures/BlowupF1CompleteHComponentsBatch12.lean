/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 12: indices 192–207

Complete request: F1 source [1,1], one added point, H/E0/E0/E0; 721 L24 terms.
These component certificates do not certify the final 721-term contraction.
Full-key labels use sortCode: unit=0, H=1, E0=2, point=3.
Selector observation-log SHA256:
  a5c4c41abad31443bffce2ffd25e3033c4746a82c1ef4ba144644d1e583a82f1
Selector Lean source SHA256:
  9dd879b24ac01f7d32f29e994b43ac9aba2add243b1104879f5dbab9947e7369
Untrusted candidate input SHA256:
  292366499879e648aeb9deaa66c1f33a693d2eadde188eb7639801e33fe9ec1b
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.BlowupF1CompleteHComponents
open SurfaceGenusTwo
open BlowupF1CertifiedPoints (rational elliptic rational_eq elliptic_eq)

set_option maxHeartbeats 0 in
theorem component_192_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 192) = value 192 := by
  decide +kernel

theorem entry_192_eq : entries 192 = residualTerms (key 192) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_192_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_192 : keyIndex (key 192) = 192 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_193_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 193) = value 193 := by
  decide +kernel

theorem entry_193_eq : entries 193 = residualTerms (key 193) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_193_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_193 : keyIndex (key 193) = 193 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_194_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 194) = value 194 := by
  decide +kernel

theorem entry_194_eq : entries 194 = residualTerms (key 194) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_194_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_194 : keyIndex (key 194) = 194 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_195_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 195) = value 195 := by
  decide +kernel

theorem entry_195_eq : entries 195 = residualTerms (key 195) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_195_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_195 : keyIndex (key 195) = 195 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_196_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 196) = value 196 := by
  decide +kernel

theorem entry_196_eq : entries 196 = residualTerms (key 196) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_196_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_196 : keyIndex (key 196) = 196 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_197_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 197) = value 197 := by
  decide +kernel

theorem entry_197_eq : entries 197 = residualTerms (key 197) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_197_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_197 : keyIndex (key 197) = 197 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_198_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 198) = value 198 := by
  decide +kernel

theorem entry_198_eq : entries 198 = residualTerms (key 198) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_198_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_198 : keyIndex (key 198) = 198 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_199_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 199) = value 199 := by
  decide +kernel

theorem entry_199_eq : entries 199 = residualTerms (key 199) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_199_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_199 : keyIndex (key 199) = 199 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_200_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 200) = value 200 := by
  decide +kernel

theorem entry_200_eq : entries 200 = residualTerms (key 200) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_200_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_200 : keyIndex (key 200) = 200 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_201_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 201) = value 201 := by
  decide +kernel

theorem entry_201_eq : entries 201 = residualTerms (key 201) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_201_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_201 : keyIndex (key 201) = 201 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_202_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 202) = value 202 := by
  decide +kernel

theorem entry_202_eq : entries 202 = residualTerms (key 202) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_202_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_202 : keyIndex (key 202) = 202 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_203_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 203) = value 203 := by
  decide +kernel

theorem entry_203_eq : entries 203 = residualTerms (key 203) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_203_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_203 : keyIndex (key 203) = 203 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_204_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 204) = value 204 := by
  decide +kernel

theorem entry_204_eq : entries 204 = residualTerms (key 204) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_204_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_204 : keyIndex (key 204) = 204 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_205_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 205) = value 205 := by
  decide +kernel

theorem entry_205_eq : entries 205 = residualTerms (key 205) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_205_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_205 : keyIndex (key 205) = 205 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_206_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 206) = value 206 := by
  decide +kernel

theorem entry_206_eq : entries 206 = residualTerms (key 206) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_206_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_206 : keyIndex (key 206) = 206 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_207_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 207) = value 207 := by
  decide +kernel

theorem entry_207_eq : entries 207 = residualTerms (key 207) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_207_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_207 : keyIndex (key 207) = 207 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

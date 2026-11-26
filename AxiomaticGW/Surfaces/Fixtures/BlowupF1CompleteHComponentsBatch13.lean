/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 13: indices 208–223

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
theorem component_208_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 208) = value 208 := by
  decide +kernel

theorem entry_208_eq : entries 208 = residualTerms (key 208) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_208_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_208 : keyIndex (key 208) = 208 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_209_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 209) = value 209 := by
  decide +kernel

theorem entry_209_eq : entries 209 = residualTerms (key 209) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_209_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_209 : keyIndex (key 209) = 209 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_210_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 210) = value 210 := by
  decide +kernel

theorem entry_210_eq : entries 210 = residualTerms (key 210) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_210_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_210 : keyIndex (key 210) = 210 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_211_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 211) = value 211 := by
  decide +kernel

theorem entry_211_eq : entries 211 = residualTerms (key 211) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_211_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_211 : keyIndex (key 211) = 211 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_212_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 212) = value 212 := by
  decide +kernel

theorem entry_212_eq : entries 212 = residualTerms (key 212) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_212_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_212 : keyIndex (key 212) = 212 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_213_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 213) = value 213 := by
  decide +kernel

theorem entry_213_eq : entries 213 = residualTerms (key 213) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_213_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_213 : keyIndex (key 213) = 213 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_214_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 214) = value 214 := by
  decide +kernel

theorem entry_214_eq : entries 214 = residualTerms (key 214) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_214_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_214 : keyIndex (key 214) = 214 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_215_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 215) = value 215 := by
  decide +kernel

theorem entry_215_eq : entries 215 = residualTerms (key 215) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_215_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_215 : keyIndex (key 215) = 215 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_216_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 216) = value 216 := by
  decide +kernel

theorem entry_216_eq : entries 216 = residualTerms (key 216) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_216_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_216 : keyIndex (key 216) = 216 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_217_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 217) = value 217 := by
  decide +kernel

theorem entry_217_eq : entries 217 = residualTerms (key 217) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_217_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_217 : keyIndex (key 217) = 217 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_218_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 218) = value 218 := by
  decide +kernel

theorem entry_218_eq : entries 218 = residualTerms (key 218) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_218_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_218 : keyIndex (key 218) = 218 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_219_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 219) = value 219 := by
  decide +kernel

theorem entry_219_eq : entries 219 = residualTerms (key 219) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_219_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_219 : keyIndex (key 219) = 219 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_220_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 220) = value 220 := by
  decide +kernel

theorem entry_220_eq : entries 220 = residualTerms (key 220) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_220_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_220 : keyIndex (key 220) = 220 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_221_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 221) = value 221 := by
  decide +kernel

theorem entry_221_eq : entries 221 = residualTerms (key 221) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_221_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_221 : keyIndex (key 221) = 221 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_222_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 222) = value 222 := by
  decide +kernel

theorem entry_222_eq : entries 222 = residualTerms (key 222) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_222_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_222 : keyIndex (key 222) = 222 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_223_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 223) = value 223 := by
  decide +kernel

theorem entry_223_eq : entries 223 = residualTerms (key 223) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_223_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_223 : keyIndex (key 223) = 223 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

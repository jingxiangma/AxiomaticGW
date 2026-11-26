/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue06

/-!
# Complete F1 H-row component batch 15: indices 240–255

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
theorem component_240_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 240) = value 240 := by
  decide +kernel

theorem entry_240_eq : entries 240 = residualTerms (key 240) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_240_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_240 : keyIndex (key 240) = 240 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_241_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 241) = value 241 := by
  decide +kernel

theorem entry_241_eq : entries 241 = residualTerms (key 241) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_241_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_241 : keyIndex (key 241) = 241 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_242_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 242) = value 242 := by
  decide +kernel

theorem entry_242_eq : entries 242 = residualTerms (key 242) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_242_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_242 : keyIndex (key 242) = 242 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_243_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 243) = value 243 := by
  decide +kernel

theorem entry_243_eq : entries 243 = residualTerms (key 243) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_243_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_243 : keyIndex (key 243) = 243 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_244_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 244) = value 244 := by
  decide +kernel

theorem entry_244_eq : entries 244 = residualTerms (key 244) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_244_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_244 : keyIndex (key 244) = 244 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_245_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 245) = value 245 := by
  decide +kernel

theorem entry_245_eq : entries 245 = residualTerms (key 245) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_245_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_245 : keyIndex (key 245) = 245 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_246_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 246) = value 246 := by
  decide +kernel

theorem entry_246_eq : entries 246 = residualTerms (key 246) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_246_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_246 : keyIndex (key 246) = 246 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_247_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 247) = value 247 := by
  decide +kernel

theorem entry_247_eq : entries 247 = residualTerms (key 247) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_247_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_247 : keyIndex (key 247) = 247 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_248_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 248) = value 248 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 6) = AxiomaticGW.BlowupF1H121Components.value 6
  exact AxiomaticGW.BlowupF1H121Components.component_6_computed

theorem entry_248_eq : entries 248 = residualTerms (key 248) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_248_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_248 : keyIndex (key 248) = 248 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_249_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 249) = value 249 := by
  decide +kernel

theorem entry_249_eq : entries 249 = residualTerms (key 249) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_249_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_249 : keyIndex (key 249) = 249 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_250_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 250) = value 250 := by
  decide +kernel

theorem entry_250_eq : entries 250 = residualTerms (key 250) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_250_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_250 : keyIndex (key 250) = 250 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_251_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 251) = value 251 := by
  decide +kernel

theorem entry_251_eq : entries 251 = residualTerms (key 251) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_251_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_251 : keyIndex (key 251) = 251 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_252_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 252) = value 252 := by
  decide +kernel

theorem entry_252_eq : entries 252 = residualTerms (key 252) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_252_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_252 : keyIndex (key 252) = 252 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_253_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 253) = value 253 := by
  decide +kernel

theorem entry_253_eq : entries 253 = residualTerms (key 253) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_253_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_253 : keyIndex (key 253) = 253 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_254_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 254) = value 254 := by
  decide +kernel

theorem entry_254_eq : entries 254 = residualTerms (key 254) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_254_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_254 : keyIndex (key 254) = 254 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_255_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 255) = value 255 := by
  decide +kernel

theorem entry_255_eq : entries 255 = residualTerms (key 255) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_255_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_255 : keyIndex (key 255) = 255 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

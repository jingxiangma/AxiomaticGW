/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue08
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue09

/-!
# Complete F1 H-row component batch 17: indices 272–287

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
theorem component_272_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 272) = value 272 := by
  decide +kernel

theorem entry_272_eq : entries 272 = residualTerms (key 272) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_272_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_272 : keyIndex (key 272) = 272 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_273_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 273) = value 273 := by
  decide +kernel

theorem entry_273_eq : entries 273 = residualTerms (key 273) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_273_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_273 : keyIndex (key 273) = 273 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_274_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 274) = value 274 := by
  decide +kernel

theorem entry_274_eq : entries 274 = residualTerms (key 274) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_274_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_274 : keyIndex (key 274) = 274 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_275_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 275) = value 275 := by
  decide +kernel

theorem entry_275_eq : entries 275 = residualTerms (key 275) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_275_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_275 : keyIndex (key 275) = 275 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_276_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 276) = value 276 := by
  decide +kernel

theorem entry_276_eq : entries 276 = residualTerms (key 276) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_276_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_276 : keyIndex (key 276) = 276 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_277_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 277) = value 277 := by
  decide +kernel

theorem entry_277_eq : entries 277 = residualTerms (key 277) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_277_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_277 : keyIndex (key 277) = 277 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_278_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 278) = value 278 := by
  decide +kernel

theorem entry_278_eq : entries 278 = residualTerms (key 278) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_278_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_278 : keyIndex (key 278) = 278 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_279_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 279) = value 279 := by
  decide +kernel

theorem entry_279_eq : entries 279 = residualTerms (key 279) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_279_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_279 : keyIndex (key 279) = 279 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_280_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 280) = value 280 := by
  decide +kernel

theorem entry_280_eq : entries 280 = residualTerms (key 280) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_280_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_280 : keyIndex (key 280) = 280 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_281_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 281) = value 281 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 8) = AxiomaticGW.BlowupF1H121Components.value 8
  exact AxiomaticGW.BlowupF1H121Components.component_8_computed

theorem entry_281_eq : entries 281 = residualTerms (key 281) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_281_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_281 : keyIndex (key 281) = 281 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_282_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 282) = value 282 := by
  decide +kernel

theorem entry_282_eq : entries 282 = residualTerms (key 282) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_282_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_282 : keyIndex (key 282) = 282 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_283_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 283) = value 283 := by
  decide +kernel

theorem entry_283_eq : entries 283 = residualTerms (key 283) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_283_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_283 : keyIndex (key 283) = 283 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_284_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 284) = value 284 := by
  decide +kernel

theorem entry_284_eq : entries 284 = residualTerms (key 284) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_284_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_284 : keyIndex (key 284) = 284 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_285_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 285) = value 285 := by
  decide +kernel

theorem entry_285_eq : entries 285 = residualTerms (key 285) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_285_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_285 : keyIndex (key 285) = 285 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_286_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 286) = value 286 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 9) = AxiomaticGW.BlowupF1H121Components.value 9
  exact AxiomaticGW.BlowupF1H121Components.component_9_computed

theorem entry_286_eq : entries 286 = residualTerms (key 286) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_286_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_286 : keyIndex (key 286) = 286 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_287_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 287) = value 287 := by
  decide +kernel

theorem entry_287_eq : entries 287 = residualTerms (key 287) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_287_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_287 : keyIndex (key 287) = 287 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

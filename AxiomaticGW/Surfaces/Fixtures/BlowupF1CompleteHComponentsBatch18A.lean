/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 18: indices 288–303

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
theorem component_288_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 288) = value 288 := by
  decide +kernel

theorem entry_288_eq : entries 288 = residualTerms (key 288) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_288_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_288 : keyIndex (key 288) = 288 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_289_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 289) = value 289 := by
  decide +kernel

theorem entry_289_eq : entries 289 = residualTerms (key 289) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_289_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_289 : keyIndex (key 289) = 289 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_290_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 290) = value 290 := by
  decide +kernel

theorem entry_290_eq : entries 290 = residualTerms (key 290) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_290_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_290 : keyIndex (key 290) = 290 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_291_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 291) = value 291 := by
  decide +kernel

theorem entry_291_eq : entries 291 = residualTerms (key 291) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_291_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_291 : keyIndex (key 291) = 291 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_292_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 292) = value 292 := by
  decide +kernel

theorem entry_292_eq : entries 292 = residualTerms (key 292) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_292_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_292 : keyIndex (key 292) = 292 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_293_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 293) = value 293 := by
  decide +kernel

theorem entry_293_eq : entries 293 = residualTerms (key 293) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_293_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_293 : keyIndex (key 293) = 293 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_294_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 294) = value 294 := by
  decide +kernel

theorem entry_294_eq : entries 294 = residualTerms (key 294) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_294_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_294 : keyIndex (key 294) = 294 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_295_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 295) = value 295 := by
  decide +kernel

theorem entry_295_eq : entries 295 = residualTerms (key 295) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_295_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_295 : keyIndex (key 295) = 295 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

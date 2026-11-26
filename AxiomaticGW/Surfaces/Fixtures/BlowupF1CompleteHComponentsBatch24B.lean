/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue11

/-!
# Complete F1 H-row component batch 24: indices 384–399

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
theorem component_392_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 392) = value 392 := by
  decide +kernel

theorem entry_392_eq : entries 392 = residualTerms (key 392) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_392_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_392 : keyIndex (key 392) = 392 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_393_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 393) = value 393 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 11) = AxiomaticGW.BlowupF1H121Components.value 11
  exact AxiomaticGW.BlowupF1H121Components.component_11_computed

theorem entry_393_eq : entries 393 = residualTerms (key 393) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_393_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_393 : keyIndex (key 393) = 393 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_394_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 394) = value 394 := by
  decide +kernel

theorem entry_394_eq : entries 394 = residualTerms (key 394) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_394_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_394 : keyIndex (key 394) = 394 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_395_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 395) = value 395 := by
  decide +kernel

theorem entry_395_eq : entries 395 = residualTerms (key 395) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_395_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_395 : keyIndex (key 395) = 395 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_396_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 396) = value 396 := by
  decide +kernel

theorem entry_396_eq : entries 396 = residualTerms (key 396) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_396_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_396 : keyIndex (key 396) = 396 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_397_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 397) = value 397 := by
  decide +kernel

theorem entry_397_eq : entries 397 = residualTerms (key 397) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_397_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_397 : keyIndex (key 397) = 397 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_398_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 398) = value 398 := by
  decide +kernel

theorem entry_398_eq : entries 398 = residualTerms (key 398) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_398_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_398 : keyIndex (key 398) = 398 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_399_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 399) = value 399 := by
  decide +kernel

theorem entry_399_eq : entries 399 = residualTerms (key 399) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_399_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_399 : keyIndex (key 399) = 399 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue32

/-!
# Complete F1 H-row component batch 35: indices 560–575

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
theorem component_560_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 560) = value 560 := by
  decide +kernel

theorem entry_560_eq : entries 560 = residualTerms (key 560) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_560_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_560 : keyIndex (key 560) = 560 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_561_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 561) = value 561 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 32) = AxiomaticGW.BlowupF1H121Components.value 32
  exact AxiomaticGW.BlowupF1H121Components.component_32_computed

theorem entry_561_eq : entries 561 = residualTerms (key 561) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_561_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_561 : keyIndex (key 561) = 561 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_562_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 562) = value 562 := by
  decide +kernel

theorem entry_562_eq : entries 562 = residualTerms (key 562) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_562_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_562 : keyIndex (key 562) = 562 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_563_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 563) = value 563 := by
  decide +kernel

theorem entry_563_eq : entries 563 = residualTerms (key 563) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_563_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_563 : keyIndex (key 563) = 563 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_564_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 564) = value 564 := by
  decide +kernel

theorem entry_564_eq : entries 564 = residualTerms (key 564) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_564_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_564 : keyIndex (key 564) = 564 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_565_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 565) = value 565 := by
  decide +kernel

theorem entry_565_eq : entries 565 = residualTerms (key 565) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_565_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_565 : keyIndex (key 565) = 565 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_566_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 566) = value 566 := by
  decide +kernel

theorem entry_566_eq : entries 566 = residualTerms (key 566) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_566_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_566 : keyIndex (key 566) = 566 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_567_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 567) = value 567 := by
  decide +kernel

theorem entry_567_eq : entries 567 = residualTerms (key 567) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_567_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_567 : keyIndex (key 567) = 567 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

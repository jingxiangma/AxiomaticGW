/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue26
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue27
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue28

/-!
# Complete F1 H-row component batch 33: indices 528–543

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
theorem component_536_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 536) = value 536 := by
  decide +kernel

theorem entry_536_eq : entries 536 = residualTerms (key 536) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_536_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_536 : keyIndex (key 536) = 536 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_537_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 537) = value 537 := by
  decide +kernel

theorem entry_537_eq : entries 537 = residualTerms (key 537) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_537_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_537 : keyIndex (key 537) = 537 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_538_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 538) = value 538 := by
  decide +kernel

theorem entry_538_eq : entries 538 = residualTerms (key 538) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_538_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_538 : keyIndex (key 538) = 538 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_539_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 539) = value 539 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 28) = AxiomaticGW.BlowupF1H121Components.value 28
  exact AxiomaticGW.BlowupF1H121Components.component_28_computed

theorem entry_539_eq : entries 539 = residualTerms (key 539) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_539_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_539 : keyIndex (key 539) = 539 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_540_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 540) = value 540 := by
  decide +kernel

theorem entry_540_eq : entries 540 = residualTerms (key 540) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_540_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_540 : keyIndex (key 540) = 540 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_541_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 541) = value 541 := by
  decide +kernel

theorem entry_541_eq : entries 541 = residualTerms (key 541) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_541_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_541 : keyIndex (key 541) = 541 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_542_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 542) = value 542 := by
  decide +kernel

theorem entry_542_eq : entries 542 = residualTerms (key 542) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_542_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_542 : keyIndex (key 542) = 542 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_543_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 543) = value 543 := by
  decide +kernel

theorem entry_543_eq : entries 543 = residualTerms (key 543) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_543_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_543 : keyIndex (key 543) = 543 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

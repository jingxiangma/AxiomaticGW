/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue45

/-!
# Complete F1 H-row component batch 43: indices 688–703

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
theorem component_688_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 688) = value 688 := by
  decide +kernel

theorem entry_688_eq : entries 688 = residualTerms (key 688) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_688_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_688 : keyIndex (key 688) = 688 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_689_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 689) = value 689 := by
  decide +kernel

theorem entry_689_eq : entries 689 = residualTerms (key 689) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_689_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_689 : keyIndex (key 689) = 689 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_690_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 690) = value 690 := by
  decide +kernel

theorem entry_690_eq : entries 690 = residualTerms (key 690) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_690_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_690 : keyIndex (key 690) = 690 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_691_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 691) = value 691 := by
  decide +kernel

theorem entry_691_eq : entries 691 = residualTerms (key 691) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_691_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_691 : keyIndex (key 691) = 691 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_692_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 692) = value 692 := by
  decide +kernel

theorem entry_692_eq : entries 692 = residualTerms (key 692) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_692_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_692 : keyIndex (key 692) = 692 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_693_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 693) = value 693 := by
  decide +kernel

theorem entry_693_eq : entries 693 = residualTerms (key 693) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_693_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_693 : keyIndex (key 693) = 693 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_694_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 694) = value 694 := by
  decide +kernel

theorem entry_694_eq : entries 694 = residualTerms (key 694) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_694_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_694 : keyIndex (key 694) = 694 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_695_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 695) = value 695 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 45) = AxiomaticGW.BlowupF1H121Components.value 45
  exact AxiomaticGW.BlowupF1H121Components.component_45_computed

theorem entry_695_eq : entries 695 = residualTerms (key 695) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_695_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_695 : keyIndex (key 695) = 695 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

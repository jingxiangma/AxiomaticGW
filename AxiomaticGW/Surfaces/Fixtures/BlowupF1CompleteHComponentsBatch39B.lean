/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue36
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue37

/-!
# Complete F1 H-row component batch 39: indices 624–639

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
theorem component_632_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 632) = value 632 := by
  decide +kernel

theorem entry_632_eq : entries 632 = residualTerms (key 632) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_632_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_632 : keyIndex (key 632) = 632 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_633_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 633) = value 633 := by
  decide +kernel

theorem entry_633_eq : entries 633 = residualTerms (key 633) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_633_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_633 : keyIndex (key 633) = 633 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_634_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 634) = value 634 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 36) = AxiomaticGW.BlowupF1H121Components.value 36
  exact AxiomaticGW.BlowupF1H121Components.component_36_computed

theorem entry_634_eq : entries 634 = residualTerms (key 634) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_634_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_634 : keyIndex (key 634) = 634 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_635_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 635) = value 635 := by
  decide +kernel

theorem entry_635_eq : entries 635 = residualTerms (key 635) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_635_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_635 : keyIndex (key 635) = 635 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_636_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 636) = value 636 := by
  decide +kernel

theorem entry_636_eq : entries 636 = residualTerms (key 636) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_636_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_636 : keyIndex (key 636) = 636 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_637_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 637) = value 637 := by
  decide +kernel

theorem entry_637_eq : entries 637 = residualTerms (key 637) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_637_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_637 : keyIndex (key 637) = 637 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_638_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 638) = value 638 := by
  decide +kernel

theorem entry_638_eq : entries 638 = residualTerms (key 638) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_638_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_638 : keyIndex (key 638) = 638 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_639_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 639) = value 639 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 37) = AxiomaticGW.BlowupF1H121Components.value 37
  exact AxiomaticGW.BlowupF1H121Components.component_37_computed

theorem entry_639_eq : entries 639 = residualTerms (key 639) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_639_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_639 : keyIndex (key 639) = 639 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

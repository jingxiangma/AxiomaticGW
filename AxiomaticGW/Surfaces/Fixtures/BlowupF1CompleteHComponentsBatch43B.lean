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
theorem component_696_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 696) = value 696 := by
  decide +kernel

theorem entry_696_eq : entries 696 = residualTerms (key 696) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_696_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_696 : keyIndex (key 696) = 696 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_697_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 697) = value 697 := by
  decide +kernel

theorem entry_697_eq : entries 697 = residualTerms (key 697) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_697_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_697 : keyIndex (key 697) = 697 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_698_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 698) = value 698 := by
  decide +kernel

theorem entry_698_eq : entries 698 = residualTerms (key 698) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_698_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_698 : keyIndex (key 698) = 698 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_699_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 699) = value 699 := by
  decide +kernel

theorem entry_699_eq : entries 699 = residualTerms (key 699) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_699_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_699 : keyIndex (key 699) = 699 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_700_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 700) = value 700 := by
  decide +kernel

theorem entry_700_eq : entries 700 = residualTerms (key 700) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_700_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_700 : keyIndex (key 700) = 700 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_701_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 701) = value 701 := by
  decide +kernel

theorem entry_701_eq : entries 701 = residualTerms (key 701) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_701_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_701 : keyIndex (key 701) = 701 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_702_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 702) = value 702 := by
  decide +kernel

theorem entry_702_eq : entries 702 = residualTerms (key 702) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_702_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_702 : keyIndex (key 702) = 702 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_703_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 703) = value 703 := by
  decide +kernel

theorem entry_703_eq : entries 703 = residualTerms (key 703) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_703_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_703 : keyIndex (key 703) = 703 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

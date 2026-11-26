/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue46
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue47

/-!
# Complete F1 H-row component batch 44: indices 704–719

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
theorem component_712_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 712) = value 712 := by
  decide +kernel

theorem entry_712_eq : entries 712 = residualTerms (key 712) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_712_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_712 : keyIndex (key 712) = 712 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_713_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 713) = value 713 := by
  decide +kernel

theorem entry_713_eq : entries 713 = residualTerms (key 713) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_713_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_713 : keyIndex (key 713) = 713 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_714_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 714) = value 714 := by
  decide +kernel

theorem entry_714_eq : entries 714 = residualTerms (key 714) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_714_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_714 : keyIndex (key 714) = 714 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_715_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 715) = value 715 := by
  decide +kernel

theorem entry_715_eq : entries 715 = residualTerms (key 715) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_715_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_715 : keyIndex (key 715) = 715 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_716_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 716) = value 716 := by
  decide +kernel

theorem entry_716_eq : entries 716 = residualTerms (key 716) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_716_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_716 : keyIndex (key 716) = 716 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_717_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 717) = value 717 := by
  decide +kernel

theorem entry_717_eq : entries 717 = residualTerms (key 717) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_717_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_717 : keyIndex (key 717) = 717 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_718_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 718) = value 718 := by
  decide +kernel

theorem entry_718_eq : entries 718 = residualTerms (key 718) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_718_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_718 : keyIndex (key 718) = 718 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_719_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 719) = value 719 := by
  decide +kernel

theorem entry_719_eq : entries 719 = residualTerms (key 719) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_719_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_719 : keyIndex (key 719) = 719 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

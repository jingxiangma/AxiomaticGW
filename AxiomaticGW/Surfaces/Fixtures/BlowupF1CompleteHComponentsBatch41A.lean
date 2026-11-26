/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue41
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue42
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue43
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue44

/-!
# Complete F1 H-row component batch 41: indices 656–671

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
theorem component_656_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 656) = value 656 := by
  decide +kernel

theorem entry_656_eq : entries 656 = residualTerms (key 656) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_656_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_656 : keyIndex (key 656) = 656 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_657_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 657) = value 657 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 41) = AxiomaticGW.BlowupF1H121Components.value 41
  exact AxiomaticGW.BlowupF1H121Components.component_41_computed

theorem entry_657_eq : entries 657 = residualTerms (key 657) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_657_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_657 : keyIndex (key 657) = 657 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_658_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 658) = value 658 := by
  decide +kernel

theorem entry_658_eq : entries 658 = residualTerms (key 658) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_658_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_658 : keyIndex (key 658) = 658 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_659_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 659) = value 659 := by
  decide +kernel

theorem entry_659_eq : entries 659 = residualTerms (key 659) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_659_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_659 : keyIndex (key 659) = 659 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_660_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 660) = value 660 := by
  decide +kernel

theorem entry_660_eq : entries 660 = residualTerms (key 660) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_660_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_660 : keyIndex (key 660) = 660 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_661_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 661) = value 661 := by
  decide +kernel

theorem entry_661_eq : entries 661 = residualTerms (key 661) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_661_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_661 : keyIndex (key 661) = 661 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_662_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 662) = value 662 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 42) = AxiomaticGW.BlowupF1H121Components.value 42
  exact AxiomaticGW.BlowupF1H121Components.component_42_computed

theorem entry_662_eq : entries 662 = residualTerms (key 662) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_662_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_662 : keyIndex (key 662) = 662 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_663_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 663) = value 663 := by
  decide +kernel

theorem entry_663_eq : entries 663 = residualTerms (key 663) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_663_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_663 : keyIndex (key 663) = 663 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

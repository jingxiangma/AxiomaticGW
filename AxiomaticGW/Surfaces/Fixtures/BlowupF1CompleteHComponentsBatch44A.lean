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
theorem component_704_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 704) = value 704 := by
  decide +kernel

theorem entry_704_eq : entries 704 = residualTerms (key 704) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_704_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_704 : keyIndex (key 704) = 704 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_705_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 705) = value 705 := by
  decide +kernel

theorem entry_705_eq : entries 705 = residualTerms (key 705) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_705_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_705 : keyIndex (key 705) = 705 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_706_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 706) = value 706 := by
  decide +kernel

theorem entry_706_eq : entries 706 = residualTerms (key 706) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_706_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_706 : keyIndex (key 706) = 706 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_707_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 707) = value 707 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 46) = AxiomaticGW.BlowupF1H121Components.value 46
  exact AxiomaticGW.BlowupF1H121Components.component_46_computed

theorem entry_707_eq : entries 707 = residualTerms (key 707) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_707_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_707 : keyIndex (key 707) = 707 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_708_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 708) = value 708 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 47) = AxiomaticGW.BlowupF1H121Components.value 47
  exact AxiomaticGW.BlowupF1H121Components.component_47_computed

theorem entry_708_eq : entries 708 = residualTerms (key 708) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_708_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_708 : keyIndex (key 708) = 708 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_709_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 709) = value 709 := by
  decide +kernel

theorem entry_709_eq : entries 709 = residualTerms (key 709) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_709_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_709 : keyIndex (key 709) = 709 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_710_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 710) = value 710 := by
  decide +kernel

theorem entry_710_eq : entries 710 = residualTerms (key 710) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_710_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_710 : keyIndex (key 710) = 710 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_711_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 711) = value 711 := by
  decide +kernel

theorem entry_711_eq : entries 711 = residualTerms (key 711) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_711_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_711 : keyIndex (key 711) = 711 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

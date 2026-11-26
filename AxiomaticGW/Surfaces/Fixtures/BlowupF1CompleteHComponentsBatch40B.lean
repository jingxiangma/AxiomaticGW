/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue38
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue39
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue40

/-!
# Complete F1 H-row component batch 40: indices 640–655

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
theorem component_648_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 648) = value 648 := by
  decide +kernel

theorem entry_648_eq : entries 648 = residualTerms (key 648) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_648_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_648 : keyIndex (key 648) = 648 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_649_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 649) = value 649 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 39) = AxiomaticGW.BlowupF1H121Components.value 39
  exact AxiomaticGW.BlowupF1H121Components.component_39_computed

theorem entry_649_eq : entries 649 = residualTerms (key 649) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_649_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_649 : keyIndex (key 649) = 649 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_650_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 650) = value 650 := by
  decide +kernel

theorem entry_650_eq : entries 650 = residualTerms (key 650) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_650_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_650 : keyIndex (key 650) = 650 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_651_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 651) = value 651 := by
  decide +kernel

theorem entry_651_eq : entries 651 = residualTerms (key 651) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_651_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_651 : keyIndex (key 651) = 651 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_652_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 652) = value 652 := by
  decide +kernel

theorem entry_652_eq : entries 652 = residualTerms (key 652) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_652_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_652 : keyIndex (key 652) = 652 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_653_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 653) = value 653 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 40) = AxiomaticGW.BlowupF1H121Components.value 40
  exact AxiomaticGW.BlowupF1H121Components.component_40_computed

theorem entry_653_eq : entries 653 = residualTerms (key 653) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_653_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_653 : keyIndex (key 653) = 653 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_654_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 654) = value 654 := by
  decide +kernel

theorem entry_654_eq : entries 654 = residualTerms (key 654) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_654_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_654 : keyIndex (key 654) = 654 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_655_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 655) = value 655 := by
  decide +kernel

theorem entry_655_eq : entries 655 = residualTerms (key 655) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_655_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_655 : keyIndex (key 655) = 655 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

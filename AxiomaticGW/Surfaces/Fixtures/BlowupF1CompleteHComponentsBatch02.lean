/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue00

/-!
# Complete F1 H-row component batch 2: indices 32–47

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
theorem component_32_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 32) = value 32 := by
  decide +kernel

theorem entry_32_eq : entries 32 = residualTerms (key 32) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_32_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_32 : keyIndex (key 32) = 32 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_33_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 33) = value 33 := by
  decide +kernel

theorem entry_33_eq : entries 33 = residualTerms (key 33) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_33_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_33 : keyIndex (key 33) = 33 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_34_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 34) = value 34 := by
  decide +kernel

theorem entry_34_eq : entries 34 = residualTerms (key 34) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_34_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_34 : keyIndex (key 34) = 34 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_35_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 35) = value 35 := by
  decide +kernel

theorem entry_35_eq : entries 35 = residualTerms (key 35) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_35_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_35 : keyIndex (key 35) = 35 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_36_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 36) = value 36 := by
  decide +kernel

theorem entry_36_eq : entries 36 = residualTerms (key 36) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_36_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_36 : keyIndex (key 36) = 36 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_37_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 37) = value 37 := by
  decide +kernel

theorem entry_37_eq : entries 37 = residualTerms (key 37) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_37_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_37 : keyIndex (key 37) = 37 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_38_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 38) = value 38 := by
  decide +kernel

theorem entry_38_eq : entries 38 = residualTerms (key 38) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_38_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_38 : keyIndex (key 38) = 38 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_39_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 39) = value 39 := by
  decide +kernel

theorem entry_39_eq : entries 39 = residualTerms (key 39) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_39_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_39 : keyIndex (key 39) = 39 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_40_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 40) = value 40 := by
  decide +kernel

theorem entry_40_eq : entries 40 = residualTerms (key 40) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_40_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_40 : keyIndex (key 40) = 40 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_41_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 41) = value 41 := by
  decide +kernel

theorem entry_41_eq : entries 41 = residualTerms (key 41) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_41_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_41 : keyIndex (key 41) = 41 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_42_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 42) = value 42 := by
  decide +kernel

theorem entry_42_eq : entries 42 = residualTerms (key 42) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_42_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_42 : keyIndex (key 42) = 42 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_43_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 43) = value 43 := by
  decide +kernel

theorem entry_43_eq : entries 43 = residualTerms (key 43) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_43_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_43 : keyIndex (key 43) = 43 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_44_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 44) = value 44 := by
  decide +kernel

theorem entry_44_eq : entries 44 = residualTerms (key 44) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_44_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_44 : keyIndex (key 44) = 44 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_45_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 45) = value 45 := by
  decide +kernel

theorem entry_45_eq : entries 45 = residualTerms (key 45) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_45_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_45 : keyIndex (key 45) = 45 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_46_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 46) = value 46 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 0) = AxiomaticGW.BlowupF1H121Components.value 0
  exact AxiomaticGW.BlowupF1H121Components.component_0_computed

theorem entry_46_eq : entries 46 = residualTerms (key 46) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_46_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_46 : keyIndex (key 46) = 46 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_47_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 47) = value 47 := by
  decide +kernel

theorem entry_47_eq : entries 47 = residualTerms (key 47) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_47_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_47 : keyIndex (key 47) = 47 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

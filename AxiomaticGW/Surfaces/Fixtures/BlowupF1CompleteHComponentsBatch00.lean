/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 0: indices 0–15

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
theorem component_0_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 0) = value 0 := by
  decide +kernel

theorem entry_0_eq : entries 0 = residualTerms (key 0) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_0_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_0 : keyIndex (key 0) = 0 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_1_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 1) = value 1 := by
  decide +kernel

theorem entry_1_eq : entries 1 = residualTerms (key 1) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_1_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_1 : keyIndex (key 1) = 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_2_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 2) = value 2 := by
  decide +kernel

theorem entry_2_eq : entries 2 = residualTerms (key 2) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_2_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_2 : keyIndex (key 2) = 2 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_3_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 3) = value 3 := by
  decide +kernel

theorem entry_3_eq : entries 3 = residualTerms (key 3) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_3_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_3 : keyIndex (key 3) = 3 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_4_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 4) = value 4 := by
  decide +kernel

theorem entry_4_eq : entries 4 = residualTerms (key 4) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_4_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_4 : keyIndex (key 4) = 4 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_5_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 5) = value 5 := by
  decide +kernel

theorem entry_5_eq : entries 5 = residualTerms (key 5) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_5_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_5 : keyIndex (key 5) = 5 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_6_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 6) = value 6 := by
  decide +kernel

theorem entry_6_eq : entries 6 = residualTerms (key 6) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_6_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_6 : keyIndex (key 6) = 6 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_7_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 7) = value 7 := by
  decide +kernel

theorem entry_7_eq : entries 7 = residualTerms (key 7) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_7_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_7 : keyIndex (key 7) = 7 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_8_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 8) = value 8 := by
  decide +kernel

theorem entry_8_eq : entries 8 = residualTerms (key 8) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_8_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_8 : keyIndex (key 8) = 8 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_9_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 9) = value 9 := by
  decide +kernel

theorem entry_9_eq : entries 9 = residualTerms (key 9) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_9_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_9 : keyIndex (key 9) = 9 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_10_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 10) = value 10 := by
  decide +kernel

theorem entry_10_eq : entries 10 = residualTerms (key 10) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_10_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_10 : keyIndex (key 10) = 10 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_11_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 11) = value 11 := by
  decide +kernel

theorem entry_11_eq : entries 11 = residualTerms (key 11) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_11_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_11 : keyIndex (key 11) = 11 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_12_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 12) = value 12 := by
  decide +kernel

theorem entry_12_eq : entries 12 = residualTerms (key 12) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_12_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_12 : keyIndex (key 12) = 12 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_13_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 13) = value 13 := by
  decide +kernel

theorem entry_13_eq : entries 13 = residualTerms (key 13) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_13_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_13 : keyIndex (key 13) = 13 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_14_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 14) = value 14 := by
  decide +kernel

theorem entry_14_eq : entries 14 = residualTerms (key 14) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_14_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_14 : keyIndex (key 14) = 14 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_15_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 15) = value 15 := by
  decide +kernel

theorem entry_15_eq : entries 15 = residualTerms (key 15) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_15_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_15 : keyIndex (key 15) = 15 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

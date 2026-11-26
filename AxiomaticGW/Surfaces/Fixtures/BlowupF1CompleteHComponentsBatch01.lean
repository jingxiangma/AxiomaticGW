/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 1: indices 16–31

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
theorem component_16_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 16) = value 16 := by
  decide +kernel

theorem entry_16_eq : entries 16 = residualTerms (key 16) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_16_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_16 : keyIndex (key 16) = 16 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_17_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 17) = value 17 := by
  decide +kernel

theorem entry_17_eq : entries 17 = residualTerms (key 17) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_17_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_17 : keyIndex (key 17) = 17 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_18_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 18) = value 18 := by
  decide +kernel

theorem entry_18_eq : entries 18 = residualTerms (key 18) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_18_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_18 : keyIndex (key 18) = 18 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_19_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 19) = value 19 := by
  decide +kernel

theorem entry_19_eq : entries 19 = residualTerms (key 19) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_19_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_19 : keyIndex (key 19) = 19 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_20_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 20) = value 20 := by
  decide +kernel

theorem entry_20_eq : entries 20 = residualTerms (key 20) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_20_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_20 : keyIndex (key 20) = 20 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_21_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 21) = value 21 := by
  decide +kernel

theorem entry_21_eq : entries 21 = residualTerms (key 21) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_21_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_21 : keyIndex (key 21) = 21 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_22_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 22) = value 22 := by
  decide +kernel

theorem entry_22_eq : entries 22 = residualTerms (key 22) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_22_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_22 : keyIndex (key 22) = 22 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_23_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 23) = value 23 := by
  decide +kernel

theorem entry_23_eq : entries 23 = residualTerms (key 23) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_23_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_23 : keyIndex (key 23) = 23 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_24_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 24) = value 24 := by
  decide +kernel

theorem entry_24_eq : entries 24 = residualTerms (key 24) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_24_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_24 : keyIndex (key 24) = 24 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_25_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 25) = value 25 := by
  decide +kernel

theorem entry_25_eq : entries 25 = residualTerms (key 25) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_25_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_25 : keyIndex (key 25) = 25 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_26_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 26) = value 26 := by
  decide +kernel

theorem entry_26_eq : entries 26 = residualTerms (key 26) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_26_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_26 : keyIndex (key 26) = 26 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_27_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 27) = value 27 := by
  decide +kernel

theorem entry_27_eq : entries 27 = residualTerms (key 27) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_27_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_27 : keyIndex (key 27) = 27 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_28_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 28) = value 28 := by
  decide +kernel

theorem entry_28_eq : entries 28 = residualTerms (key 28) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_28_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_28 : keyIndex (key 28) = 28 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_29_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 29) = value 29 := by
  decide +kernel

theorem entry_29_eq : entries 29 = residualTerms (key 29) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_29_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_29 : keyIndex (key 29) = 29 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_30_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 30) = value 30 := by
  decide +kernel

theorem entry_30_eq : entries 30 = residualTerms (key 30) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_30_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_30 : keyIndex (key 30) = 30 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_31_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 31) = value 31 := by
  decide +kernel

theorem entry_31_eq : entries 31 = residualTerms (key 31) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_31_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_31 : keyIndex (key 31) = 31 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 3: indices 48–63

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
theorem component_48_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 48) = value 48 := by
  decide +kernel

theorem entry_48_eq : entries 48 = residualTerms (key 48) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_48_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_48 : keyIndex (key 48) = 48 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_49_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 49) = value 49 := by
  decide +kernel

theorem entry_49_eq : entries 49 = residualTerms (key 49) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_49_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_49 : keyIndex (key 49) = 49 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_50_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 50) = value 50 := by
  decide +kernel

theorem entry_50_eq : entries 50 = residualTerms (key 50) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_50_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_50 : keyIndex (key 50) = 50 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_51_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 51) = value 51 := by
  decide +kernel

theorem entry_51_eq : entries 51 = residualTerms (key 51) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_51_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_51 : keyIndex (key 51) = 51 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_52_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 52) = value 52 := by
  decide +kernel

theorem entry_52_eq : entries 52 = residualTerms (key 52) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_52_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_52 : keyIndex (key 52) = 52 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_53_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 53) = value 53 := by
  decide +kernel

theorem entry_53_eq : entries 53 = residualTerms (key 53) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_53_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_53 : keyIndex (key 53) = 53 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_54_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 54) = value 54 := by
  decide +kernel

theorem entry_54_eq : entries 54 = residualTerms (key 54) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_54_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_54 : keyIndex (key 54) = 54 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_55_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 55) = value 55 := by
  decide +kernel

theorem entry_55_eq : entries 55 = residualTerms (key 55) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_55_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_55 : keyIndex (key 55) = 55 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_56_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 56) = value 56 := by
  decide +kernel

theorem entry_56_eq : entries 56 = residualTerms (key 56) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_56_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_56 : keyIndex (key 56) = 56 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_57_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 57) = value 57 := by
  decide +kernel

theorem entry_57_eq : entries 57 = residualTerms (key 57) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_57_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_57 : keyIndex (key 57) = 57 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_58_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 58) = value 58 := by
  decide +kernel

theorem entry_58_eq : entries 58 = residualTerms (key 58) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_58_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_58 : keyIndex (key 58) = 58 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_59_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 59) = value 59 := by
  decide +kernel

theorem entry_59_eq : entries 59 = residualTerms (key 59) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_59_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_59 : keyIndex (key 59) = 59 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_60_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 60) = value 60 := by
  decide +kernel

theorem entry_60_eq : entries 60 = residualTerms (key 60) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_60_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_60 : keyIndex (key 60) = 60 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_61_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 61) = value 61 := by
  decide +kernel

theorem entry_61_eq : entries 61 = residualTerms (key 61) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_61_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_61 : keyIndex (key 61) = 61 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_62_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 62) = value 62 := by
  decide +kernel

theorem entry_62_eq : entries 62 = residualTerms (key 62) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_62_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_62 : keyIndex (key 62) = 62 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_63_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 63) = value 63 := by
  decide +kernel

theorem entry_63_eq : entries 63 = residualTerms (key 63) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_63_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_63 : keyIndex (key 63) = 63 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 4: indices 64–79

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
theorem component_64_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 64) = value 64 := by
  decide +kernel

theorem entry_64_eq : entries 64 = residualTerms (key 64) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_64_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_64 : keyIndex (key 64) = 64 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_65_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 65) = value 65 := by
  decide +kernel

theorem entry_65_eq : entries 65 = residualTerms (key 65) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_65_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_65 : keyIndex (key 65) = 65 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_66_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 66) = value 66 := by
  decide +kernel

theorem entry_66_eq : entries 66 = residualTerms (key 66) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_66_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_66 : keyIndex (key 66) = 66 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_67_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 67) = value 67 := by
  decide +kernel

theorem entry_67_eq : entries 67 = residualTerms (key 67) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_67_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_67 : keyIndex (key 67) = 67 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_68_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 68) = value 68 := by
  decide +kernel

theorem entry_68_eq : entries 68 = residualTerms (key 68) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_68_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_68 : keyIndex (key 68) = 68 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_69_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 69) = value 69 := by
  decide +kernel

theorem entry_69_eq : entries 69 = residualTerms (key 69) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_69_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_69 : keyIndex (key 69) = 69 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_70_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 70) = value 70 := by
  decide +kernel

theorem entry_70_eq : entries 70 = residualTerms (key 70) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_70_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_70 : keyIndex (key 70) = 70 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_71_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 71) = value 71 := by
  decide +kernel

theorem entry_71_eq : entries 71 = residualTerms (key 71) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_71_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_71 : keyIndex (key 71) = 71 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_72_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 72) = value 72 := by
  decide +kernel

theorem entry_72_eq : entries 72 = residualTerms (key 72) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_72_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_72 : keyIndex (key 72) = 72 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_73_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 73) = value 73 := by
  decide +kernel

theorem entry_73_eq : entries 73 = residualTerms (key 73) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_73_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_73 : keyIndex (key 73) = 73 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_74_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 74) = value 74 := by
  decide +kernel

theorem entry_74_eq : entries 74 = residualTerms (key 74) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_74_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_74 : keyIndex (key 74) = 74 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_75_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 75) = value 75 := by
  decide +kernel

theorem entry_75_eq : entries 75 = residualTerms (key 75) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_75_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_75 : keyIndex (key 75) = 75 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_76_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 76) = value 76 := by
  decide +kernel

theorem entry_76_eq : entries 76 = residualTerms (key 76) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_76_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_76 : keyIndex (key 76) = 76 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_77_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 77) = value 77 := by
  decide +kernel

theorem entry_77_eq : entries 77 = residualTerms (key 77) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_77_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_77 : keyIndex (key 77) = 77 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_78_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 78) = value 78 := by
  decide +kernel

theorem entry_78_eq : entries 78 = residualTerms (key 78) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_78_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_78 : keyIndex (key 78) = 78 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_79_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 79) = value 79 := by
  decide +kernel

theorem entry_79_eq : entries 79 = residualTerms (key 79) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_79_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_79 : keyIndex (key 79) = 79 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

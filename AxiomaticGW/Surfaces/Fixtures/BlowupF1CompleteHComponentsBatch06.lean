/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 6: indices 96–111

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
theorem component_96_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 96) = value 96 := by
  decide +kernel

theorem entry_96_eq : entries 96 = residualTerms (key 96) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_96_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_96 : keyIndex (key 96) = 96 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_97_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 97) = value 97 := by
  decide +kernel

theorem entry_97_eq : entries 97 = residualTerms (key 97) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_97_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_97 : keyIndex (key 97) = 97 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_98_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 98) = value 98 := by
  decide +kernel

theorem entry_98_eq : entries 98 = residualTerms (key 98) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_98_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_98 : keyIndex (key 98) = 98 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_99_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 99) = value 99 := by
  decide +kernel

theorem entry_99_eq : entries 99 = residualTerms (key 99) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_99_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_99 : keyIndex (key 99) = 99 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_100_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 100) = value 100 := by
  decide +kernel

theorem entry_100_eq : entries 100 = residualTerms (key 100) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_100_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_100 : keyIndex (key 100) = 100 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_101_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 101) = value 101 := by
  decide +kernel

theorem entry_101_eq : entries 101 = residualTerms (key 101) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_101_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_101 : keyIndex (key 101) = 101 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_102_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 102) = value 102 := by
  decide +kernel

theorem entry_102_eq : entries 102 = residualTerms (key 102) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_102_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_102 : keyIndex (key 102) = 102 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_103_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 103) = value 103 := by
  decide +kernel

theorem entry_103_eq : entries 103 = residualTerms (key 103) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_103_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_103 : keyIndex (key 103) = 103 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_104_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 104) = value 104 := by
  decide +kernel

theorem entry_104_eq : entries 104 = residualTerms (key 104) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_104_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_104 : keyIndex (key 104) = 104 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_105_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 105) = value 105 := by
  decide +kernel

theorem entry_105_eq : entries 105 = residualTerms (key 105) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_105_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_105 : keyIndex (key 105) = 105 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_106_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 106) = value 106 := by
  decide +kernel

theorem entry_106_eq : entries 106 = residualTerms (key 106) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_106_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_106 : keyIndex (key 106) = 106 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_107_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 107) = value 107 := by
  decide +kernel

theorem entry_107_eq : entries 107 = residualTerms (key 107) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_107_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_107 : keyIndex (key 107) = 107 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_108_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 108) = value 108 := by
  decide +kernel

theorem entry_108_eq : entries 108 = residualTerms (key 108) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_108_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_108 : keyIndex (key 108) = 108 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_109_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 109) = value 109 := by
  decide +kernel

theorem entry_109_eq : entries 109 = residualTerms (key 109) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_109_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_109 : keyIndex (key 109) = 109 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_110_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 110) = value 110 := by
  decide +kernel

theorem entry_110_eq : entries 110 = residualTerms (key 110) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_110_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_110 : keyIndex (key 110) = 110 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_111_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 111) = value 111 := by
  decide +kernel

theorem entry_111_eq : entries 111 = residualTerms (key 111) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_111_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_111 : keyIndex (key 111) = 111 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

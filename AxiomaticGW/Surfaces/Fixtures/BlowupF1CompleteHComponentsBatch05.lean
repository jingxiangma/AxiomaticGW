/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 5: indices 80–95

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
theorem component_80_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 80) = value 80 := by
  decide +kernel

theorem entry_80_eq : entries 80 = residualTerms (key 80) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_80_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_80 : keyIndex (key 80) = 80 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_81_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 81) = value 81 := by
  decide +kernel

theorem entry_81_eq : entries 81 = residualTerms (key 81) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_81_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_81 : keyIndex (key 81) = 81 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_82_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 82) = value 82 := by
  decide +kernel

theorem entry_82_eq : entries 82 = residualTerms (key 82) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_82_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_82 : keyIndex (key 82) = 82 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_83_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 83) = value 83 := by
  decide +kernel

theorem entry_83_eq : entries 83 = residualTerms (key 83) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_83_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_83 : keyIndex (key 83) = 83 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_84_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 84) = value 84 := by
  decide +kernel

theorem entry_84_eq : entries 84 = residualTerms (key 84) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_84_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_84 : keyIndex (key 84) = 84 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_85_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 85) = value 85 := by
  decide +kernel

theorem entry_85_eq : entries 85 = residualTerms (key 85) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_85_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_85 : keyIndex (key 85) = 85 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_86_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 86) = value 86 := by
  decide +kernel

theorem entry_86_eq : entries 86 = residualTerms (key 86) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_86_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_86 : keyIndex (key 86) = 86 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_87_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 87) = value 87 := by
  decide +kernel

theorem entry_87_eq : entries 87 = residualTerms (key 87) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_87_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_87 : keyIndex (key 87) = 87 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_88_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 88) = value 88 := by
  decide +kernel

theorem entry_88_eq : entries 88 = residualTerms (key 88) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_88_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_88 : keyIndex (key 88) = 88 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_89_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 89) = value 89 := by
  decide +kernel

theorem entry_89_eq : entries 89 = residualTerms (key 89) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_89_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_89 : keyIndex (key 89) = 89 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_90_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 90) = value 90 := by
  decide +kernel

theorem entry_90_eq : entries 90 = residualTerms (key 90) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_90_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_90 : keyIndex (key 90) = 90 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_91_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 91) = value 91 := by
  decide +kernel

theorem entry_91_eq : entries 91 = residualTerms (key 91) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_91_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_91 : keyIndex (key 91) = 91 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_92_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 92) = value 92 := by
  decide +kernel

theorem entry_92_eq : entries 92 = residualTerms (key 92) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_92_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_92 : keyIndex (key 92) = 92 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_93_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 93) = value 93 := by
  decide +kernel

theorem entry_93_eq : entries 93 = residualTerms (key 93) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_93_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_93 : keyIndex (key 93) = 93 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_94_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 94) = value 94 := by
  decide +kernel

theorem entry_94_eq : entries 94 = residualTerms (key 94) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_94_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_94 : keyIndex (key 94) = 94 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_95_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 95) = value 95 := by
  decide +kernel

theorem entry_95_eq : entries 95 = residualTerms (key 95) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_95_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_95 : keyIndex (key 95) = 95 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

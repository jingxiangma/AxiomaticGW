/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 8: indices 128–143

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
theorem component_128_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 128) = value 128 := by
  decide +kernel

theorem entry_128_eq : entries 128 = residualTerms (key 128) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_128_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_128 : keyIndex (key 128) = 128 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_129_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 129) = value 129 := by
  decide +kernel

theorem entry_129_eq : entries 129 = residualTerms (key 129) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_129_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_129 : keyIndex (key 129) = 129 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_130_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 130) = value 130 := by
  decide +kernel

theorem entry_130_eq : entries 130 = residualTerms (key 130) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_130_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_130 : keyIndex (key 130) = 130 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_131_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 131) = value 131 := by
  decide +kernel

theorem entry_131_eq : entries 131 = residualTerms (key 131) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_131_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_131 : keyIndex (key 131) = 131 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_132_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 132) = value 132 := by
  decide +kernel

theorem entry_132_eq : entries 132 = residualTerms (key 132) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_132_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_132 : keyIndex (key 132) = 132 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_133_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 133) = value 133 := by
  decide +kernel

theorem entry_133_eq : entries 133 = residualTerms (key 133) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_133_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_133 : keyIndex (key 133) = 133 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_134_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 134) = value 134 := by
  decide +kernel

theorem entry_134_eq : entries 134 = residualTerms (key 134) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_134_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_134 : keyIndex (key 134) = 134 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_135_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 135) = value 135 := by
  decide +kernel

theorem entry_135_eq : entries 135 = residualTerms (key 135) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_135_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_135 : keyIndex (key 135) = 135 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_136_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 136) = value 136 := by
  decide +kernel

theorem entry_136_eq : entries 136 = residualTerms (key 136) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_136_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_136 : keyIndex (key 136) = 136 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_137_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 137) = value 137 := by
  decide +kernel

theorem entry_137_eq : entries 137 = residualTerms (key 137) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_137_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_137 : keyIndex (key 137) = 137 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_138_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 138) = value 138 := by
  decide +kernel

theorem entry_138_eq : entries 138 = residualTerms (key 138) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_138_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_138 : keyIndex (key 138) = 138 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_139_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 139) = value 139 := by
  decide +kernel

theorem entry_139_eq : entries 139 = residualTerms (key 139) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_139_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_139 : keyIndex (key 139) = 139 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_140_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 140) = value 140 := by
  decide +kernel

theorem entry_140_eq : entries 140 = residualTerms (key 140) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_140_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_140 : keyIndex (key 140) = 140 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_141_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 141) = value 141 := by
  decide +kernel

theorem entry_141_eq : entries 141 = residualTerms (key 141) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_141_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_141 : keyIndex (key 141) = 141 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_142_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 142) = value 142 := by
  decide +kernel

theorem entry_142_eq : entries 142 = residualTerms (key 142) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_142_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_142 : keyIndex (key 142) = 142 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_143_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 143) = value 143 := by
  decide +kernel

theorem entry_143_eq : entries 143 = residualTerms (key 143) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_143_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_143 : keyIndex (key 143) = 143 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

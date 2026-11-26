/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue01

/-!
# Complete F1 H-row component batch 9: indices 144–159

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
theorem component_144_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 144) = value 144 := by
  decide +kernel

theorem entry_144_eq : entries 144 = residualTerms (key 144) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_144_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_144 : keyIndex (key 144) = 144 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_145_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 145) = value 145 := by
  decide +kernel

theorem entry_145_eq : entries 145 = residualTerms (key 145) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_145_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_145 : keyIndex (key 145) = 145 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_146_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 146) = value 146 := by
  decide +kernel

theorem entry_146_eq : entries 146 = residualTerms (key 146) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_146_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_146 : keyIndex (key 146) = 146 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_147_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 147) = value 147 := by
  decide +kernel

theorem entry_147_eq : entries 147 = residualTerms (key 147) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_147_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_147 : keyIndex (key 147) = 147 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_148_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 148) = value 148 := by
  decide +kernel

theorem entry_148_eq : entries 148 = residualTerms (key 148) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_148_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_148 : keyIndex (key 148) = 148 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_149_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 149) = value 149 := by
  decide +kernel

theorem entry_149_eq : entries 149 = residualTerms (key 149) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_149_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_149 : keyIndex (key 149) = 149 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_150_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 150) = value 150 := by
  decide +kernel

theorem entry_150_eq : entries 150 = residualTerms (key 150) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_150_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_150 : keyIndex (key 150) = 150 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_151_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 151) = value 151 := by
  decide +kernel

theorem entry_151_eq : entries 151 = residualTerms (key 151) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_151_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_151 : keyIndex (key 151) = 151 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_152_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 152) = value 152 := by
  decide +kernel

theorem entry_152_eq : entries 152 = residualTerms (key 152) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_152_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_152 : keyIndex (key 152) = 152 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_153_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 153) = value 153 := by
  decide +kernel

theorem entry_153_eq : entries 153 = residualTerms (key 153) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_153_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_153 : keyIndex (key 153) = 153 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_154_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 154) = value 154 := by
  decide +kernel

theorem entry_154_eq : entries 154 = residualTerms (key 154) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_154_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_154 : keyIndex (key 154) = 154 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_155_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 155) = value 155 := by
  decide +kernel

theorem entry_155_eq : entries 155 = residualTerms (key 155) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_155_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_155 : keyIndex (key 155) = 155 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_156_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 156) = value 156 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 1) = AxiomaticGW.BlowupF1H121Components.value 1
  exact AxiomaticGW.BlowupF1H121Components.component_1_computed

theorem entry_156_eq : entries 156 = residualTerms (key 156) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_156_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_156 : keyIndex (key 156) = 156 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_157_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 157) = value 157 := by
  decide +kernel

theorem entry_157_eq : entries 157 = residualTerms (key 157) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_157_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_157 : keyIndex (key 157) = 157 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_158_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 158) = value 158 := by
  decide +kernel

theorem entry_158_eq : entries 158 = residualTerms (key 158) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_158_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_158 : keyIndex (key 158) = 158 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_159_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 159) = value 159 := by
  decide +kernel

theorem entry_159_eq : entries 159 = residualTerms (key 159) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_159_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_159 : keyIndex (key 159) = 159 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

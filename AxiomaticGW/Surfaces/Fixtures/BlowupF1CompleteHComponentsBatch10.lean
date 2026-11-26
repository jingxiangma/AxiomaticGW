/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue02
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue03

/-!
# Complete F1 H-row component batch 10: indices 160–175

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
theorem component_160_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 160) = value 160 := by
  decide +kernel

theorem entry_160_eq : entries 160 = residualTerms (key 160) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_160_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_160 : keyIndex (key 160) = 160 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_161_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 161) = value 161 := by
  decide +kernel

theorem entry_161_eq : entries 161 = residualTerms (key 161) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_161_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_161 : keyIndex (key 161) = 161 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_162_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 162) = value 162 := by
  decide +kernel

theorem entry_162_eq : entries 162 = residualTerms (key 162) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_162_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_162 : keyIndex (key 162) = 162 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_163_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 163) = value 163 := by
  decide +kernel

theorem entry_163_eq : entries 163 = residualTerms (key 163) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_163_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_163 : keyIndex (key 163) = 163 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_164_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 164) = value 164 := by
  decide +kernel

theorem entry_164_eq : entries 164 = residualTerms (key 164) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_164_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_164 : keyIndex (key 164) = 164 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_165_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 165) = value 165 := by
  decide +kernel

theorem entry_165_eq : entries 165 = residualTerms (key 165) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_165_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_165 : keyIndex (key 165) = 165 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_166_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 166) = value 166 := by
  decide +kernel

theorem entry_166_eq : entries 166 = residualTerms (key 166) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_166_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_166 : keyIndex (key 166) = 166 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_167_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 167) = value 167 := by
  decide +kernel

theorem entry_167_eq : entries 167 = residualTerms (key 167) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_167_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_167 : keyIndex (key 167) = 167 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_168_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 168) = value 168 := by
  decide +kernel

theorem entry_168_eq : entries 168 = residualTerms (key 168) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_168_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_168 : keyIndex (key 168) = 168 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_169_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 169) = value 169 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 2) = AxiomaticGW.BlowupF1H121Components.value 2
  exact AxiomaticGW.BlowupF1H121Components.component_2_computed

theorem entry_169_eq : entries 169 = residualTerms (key 169) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_169_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_169 : keyIndex (key 169) = 169 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_170_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 170) = value 170 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 3) = AxiomaticGW.BlowupF1H121Components.value 3
  exact AxiomaticGW.BlowupF1H121Components.component_3_computed

theorem entry_170_eq : entries 170 = residualTerms (key 170) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_170_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_170 : keyIndex (key 170) = 170 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_171_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 171) = value 171 := by
  decide +kernel

theorem entry_171_eq : entries 171 = residualTerms (key 171) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_171_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_171 : keyIndex (key 171) = 171 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_172_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 172) = value 172 := by
  decide +kernel

theorem entry_172_eq : entries 172 = residualTerms (key 172) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_172_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_172 : keyIndex (key 172) = 172 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_173_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 173) = value 173 := by
  decide +kernel

theorem entry_173_eq : entries 173 = residualTerms (key 173) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_173_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_173 : keyIndex (key 173) = 173 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_174_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 174) = value 174 := by
  decide +kernel

theorem entry_174_eq : entries 174 = residualTerms (key 174) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_174_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_174 : keyIndex (key 174) = 174 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_175_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 175) = value 175 := by
  decide +kernel

theorem entry_175_eq : entries 175 = residualTerms (key 175) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_175_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_175 : keyIndex (key 175) = 175 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue04
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue05

/-!
# Complete F1 H-row component batch 11: indices 176–191

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
theorem component_176_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 176) = value 176 := by
  decide +kernel

theorem entry_176_eq : entries 176 = residualTerms (key 176) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_176_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_176 : keyIndex (key 176) = 176 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_177_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 177) = value 177 := by
  decide +kernel

theorem entry_177_eq : entries 177 = residualTerms (key 177) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_177_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_177 : keyIndex (key 177) = 177 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_178_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 178) = value 178 := by
  decide +kernel

theorem entry_178_eq : entries 178 = residualTerms (key 178) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_178_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_178 : keyIndex (key 178) = 178 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_179_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 179) = value 179 := by
  decide +kernel

theorem entry_179_eq : entries 179 = residualTerms (key 179) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_179_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_179 : keyIndex (key 179) = 179 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_180_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 180) = value 180 := by
  decide +kernel

theorem entry_180_eq : entries 180 = residualTerms (key 180) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_180_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_180 : keyIndex (key 180) = 180 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_181_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 181) = value 181 := by
  decide +kernel

theorem entry_181_eq : entries 181 = residualTerms (key 181) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_181_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_181 : keyIndex (key 181) = 181 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_182_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 182) = value 182 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 4) = AxiomaticGW.BlowupF1H121Components.value 4
  exact AxiomaticGW.BlowupF1H121Components.component_4_computed

theorem entry_182_eq : entries 182 = residualTerms (key 182) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_182_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_182 : keyIndex (key 182) = 182 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_183_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 183) = value 183 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 5) = AxiomaticGW.BlowupF1H121Components.value 5
  exact AxiomaticGW.BlowupF1H121Components.component_5_computed

theorem entry_183_eq : entries 183 = residualTerms (key 183) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_183_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_183 : keyIndex (key 183) = 183 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_184_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 184) = value 184 := by
  decide +kernel

theorem entry_184_eq : entries 184 = residualTerms (key 184) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_184_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_184 : keyIndex (key 184) = 184 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_185_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 185) = value 185 := by
  decide +kernel

theorem entry_185_eq : entries 185 = residualTerms (key 185) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_185_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_185 : keyIndex (key 185) = 185 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_186_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 186) = value 186 := by
  decide +kernel

theorem entry_186_eq : entries 186 = residualTerms (key 186) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_186_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_186 : keyIndex (key 186) = 186 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_187_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 187) = value 187 := by
  decide +kernel

theorem entry_187_eq : entries 187 = residualTerms (key 187) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_187_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_187 : keyIndex (key 187) = 187 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_188_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 188) = value 188 := by
  decide +kernel

theorem entry_188_eq : entries 188 = residualTerms (key 188) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_188_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_188 : keyIndex (key 188) = 188 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_189_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 189) = value 189 := by
  decide +kernel

theorem entry_189_eq : entries 189 = residualTerms (key 189) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_189_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_189 : keyIndex (key 189) = 189 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_190_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 190) = value 190 := by
  decide +kernel

theorem entry_190_eq : entries 190 = residualTerms (key 190) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_190_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_190 : keyIndex (key 190) = 190 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_191_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 191) = value 191 := by
  decide +kernel

theorem entry_191_eq : entries 191 = residualTerms (key 191) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_191_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_191 : keyIndex (key 191) = 191 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

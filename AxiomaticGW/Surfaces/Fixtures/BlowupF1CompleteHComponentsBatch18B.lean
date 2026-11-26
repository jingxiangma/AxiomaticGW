/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 18: indices 288–303

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
theorem component_296_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 296) = value 296 := by
  decide +kernel

theorem entry_296_eq : entries 296 = residualTerms (key 296) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_296_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_296 : keyIndex (key 296) = 296 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_297_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 297) = value 297 := by
  decide +kernel

theorem entry_297_eq : entries 297 = residualTerms (key 297) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_297_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_297 : keyIndex (key 297) = 297 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_298_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 298) = value 298 := by
  decide +kernel

theorem entry_298_eq : entries 298 = residualTerms (key 298) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_298_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_298 : keyIndex (key 298) = 298 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_299_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 299) = value 299 := by
  decide +kernel

theorem entry_299_eq : entries 299 = residualTerms (key 299) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_299_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_299 : keyIndex (key 299) = 299 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_300_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 300) = value 300 := by
  decide +kernel

theorem entry_300_eq : entries 300 = residualTerms (key 300) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_300_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_300 : keyIndex (key 300) = 300 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_301_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 301) = value 301 := by
  decide +kernel

theorem entry_301_eq : entries 301 = residualTerms (key 301) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_301_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_301 : keyIndex (key 301) = 301 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_302_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 302) = value 302 := by
  decide +kernel

theorem entry_302_eq : entries 302 = residualTerms (key 302) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_302_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_302 : keyIndex (key 302) = 302 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_303_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 303) = value 303 := by
  decide +kernel

theorem entry_303_eq : entries 303 = residualTerms (key 303) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_303_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_303 : keyIndex (key 303) = 303 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

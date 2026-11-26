/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 22: indices 352–367

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
theorem component_360_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 360) = value 360 := by
  decide +kernel

theorem entry_360_eq : entries 360 = residualTerms (key 360) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_360_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_360 : keyIndex (key 360) = 360 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_361_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 361) = value 361 := by
  decide +kernel

theorem entry_361_eq : entries 361 = residualTerms (key 361) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_361_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_361 : keyIndex (key 361) = 361 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_362_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 362) = value 362 := by
  decide +kernel

theorem entry_362_eq : entries 362 = residualTerms (key 362) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_362_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_362 : keyIndex (key 362) = 362 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_363_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 363) = value 363 := by
  decide +kernel

theorem entry_363_eq : entries 363 = residualTerms (key 363) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_363_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_363 : keyIndex (key 363) = 363 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

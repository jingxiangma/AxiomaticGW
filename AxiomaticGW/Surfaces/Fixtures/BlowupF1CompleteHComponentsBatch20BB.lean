/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 20: indices 320–335

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
theorem component_332_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 332) = value 332 := by
  decide +kernel

theorem entry_332_eq : entries 332 = residualTerms (key 332) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_332_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_332 : keyIndex (key 332) = 332 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_333_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 333) = value 333 := by
  decide +kernel

theorem entry_333_eq : entries 333 = residualTerms (key 333) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_333_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_333 : keyIndex (key 333) = 333 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_334_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 334) = value 334 := by
  decide +kernel

theorem entry_334_eq : entries 334 = residualTerms (key 334) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_334_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_334 : keyIndex (key 334) = 334 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_335_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 335) = value 335 := by
  decide +kernel

theorem entry_335_eq : entries 335 = residualTerms (key 335) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_335_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_335 : keyIndex (key 335) = 335 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

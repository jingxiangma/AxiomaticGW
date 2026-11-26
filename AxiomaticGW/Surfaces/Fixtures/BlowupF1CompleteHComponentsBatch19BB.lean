/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 19: indices 304–319

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
theorem component_316_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 316) = value 316 := by
  decide +kernel

theorem entry_316_eq : entries 316 = residualTerms (key 316) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_316_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_316 : keyIndex (key 316) = 316 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_317_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 317) = value 317 := by
  decide +kernel

theorem entry_317_eq : entries 317 = residualTerms (key 317) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_317_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_317 : keyIndex (key 317) = 317 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_318_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 318) = value 318 := by
  decide +kernel

theorem entry_318_eq : entries 318 = residualTerms (key 318) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_318_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_318 : keyIndex (key 318) = 318 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_319_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 319) = value 319 := by
  decide +kernel

theorem entry_319_eq : entries 319 = residualTerms (key 319) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_319_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_319 : keyIndex (key 319) = 319 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

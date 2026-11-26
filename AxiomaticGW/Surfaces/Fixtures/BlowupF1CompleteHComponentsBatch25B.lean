/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue12

/-!
# Complete F1 H-row component batch 25: indices 400–415

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
theorem component_408_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 408) = value 408 := by
  decide +kernel

theorem entry_408_eq : entries 408 = residualTerms (key 408) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_408_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_408 : keyIndex (key 408) = 408 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_409_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 409) = value 409 := by
  decide +kernel

theorem entry_409_eq : entries 409 = residualTerms (key 409) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_409_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_409 : keyIndex (key 409) = 409 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_410_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 410) = value 410 := by
  decide +kernel

theorem entry_410_eq : entries 410 = residualTerms (key 410) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_410_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_410 : keyIndex (key 410) = 410 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_411_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 411) = value 411 := by
  decide +kernel

theorem entry_411_eq : entries 411 = residualTerms (key 411) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_411_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_411 : keyIndex (key 411) = 411 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_412_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 412) = value 412 := by
  decide +kernel

theorem entry_412_eq : entries 412 = residualTerms (key 412) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_412_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_412 : keyIndex (key 412) = 412 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_413_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 413) = value 413 := by
  decide +kernel

theorem entry_413_eq : entries 413 = residualTerms (key 413) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_413_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_413 : keyIndex (key 413) = 413 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_414_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 414) = value 414 := by
  decide +kernel

theorem entry_414_eq : entries 414 = residualTerms (key 414) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_414_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_414 : keyIndex (key 414) = 414 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_415_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 415) = value 415 := by
  decide +kernel

theorem entry_415_eq : entries 415 = residualTerms (key 415) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_415_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_415 : keyIndex (key 415) = 415 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

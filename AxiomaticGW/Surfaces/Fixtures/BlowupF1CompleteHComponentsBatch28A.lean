/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue18

/-!
# Complete F1 H-row component batch 28: indices 448–463

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
theorem component_448_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 448) = value 448 := by
  decide +kernel

theorem entry_448_eq : entries 448 = residualTerms (key 448) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_448_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_448 : keyIndex (key 448) = 448 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_449_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 449) = value 449 := by
  decide +kernel

theorem entry_449_eq : entries 449 = residualTerms (key 449) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_449_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_449 : keyIndex (key 449) = 449 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_450_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 450) = value 450 := by
  decide +kernel

theorem entry_450_eq : entries 450 = residualTerms (key 450) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_450_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_450 : keyIndex (key 450) = 450 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_451_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 451) = value 451 := by
  decide +kernel

theorem entry_451_eq : entries 451 = residualTerms (key 451) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_451_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_451 : keyIndex (key 451) = 451 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_452_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 452) = value 452 := by
  decide +kernel

theorem entry_452_eq : entries 452 = residualTerms (key 452) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_452_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_452 : keyIndex (key 452) = 452 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_453_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 453) = value 453 := by
  decide +kernel

theorem entry_453_eq : entries 453 = residualTerms (key 453) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_453_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_453 : keyIndex (key 453) = 453 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_454_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 454) = value 454 := by
  decide +kernel

theorem entry_454_eq : entries 454 = residualTerms (key 454) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_454_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_454 : keyIndex (key 454) = 454 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_455_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 455) = value 455 := by
  decide +kernel

theorem entry_455_eq : entries 455 = residualTerms (key 455) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_455_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_455 : keyIndex (key 455) = 455 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

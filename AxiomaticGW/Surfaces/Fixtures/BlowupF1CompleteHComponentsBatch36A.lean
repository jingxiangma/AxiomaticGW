/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue33

/-!
# Complete F1 H-row component batch 36: indices 576–591

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
theorem component_576_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 576) = value 576 := by
  decide +kernel

theorem entry_576_eq : entries 576 = residualTerms (key 576) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_576_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_576 : keyIndex (key 576) = 576 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_577_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 577) = value 577 := by
  decide +kernel

theorem entry_577_eq : entries 577 = residualTerms (key 577) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_577_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_577 : keyIndex (key 577) = 577 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_578_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 578) = value 578 := by
  decide +kernel

theorem entry_578_eq : entries 578 = residualTerms (key 578) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_578_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_578 : keyIndex (key 578) = 578 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_579_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 579) = value 579 := by
  decide +kernel

theorem entry_579_eq : entries 579 = residualTerms (key 579) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_579_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_579 : keyIndex (key 579) = 579 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_580_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 580) = value 580 := by
  decide +kernel

theorem entry_580_eq : entries 580 = residualTerms (key 580) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_580_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_580 : keyIndex (key 580) = 580 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_581_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 581) = value 581 := by
  decide +kernel

theorem entry_581_eq : entries 581 = residualTerms (key 581) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_581_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_581 : keyIndex (key 581) = 581 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_582_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 582) = value 582 := by
  decide +kernel

theorem entry_582_eq : entries 582 = residualTerms (key 582) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_582_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_582 : keyIndex (key 582) = 582 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_583_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 583) = value 583 := by
  decide +kernel

theorem entry_583_eq : entries 583 = residualTerms (key 583) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_583_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_583 : keyIndex (key 583) = 583 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

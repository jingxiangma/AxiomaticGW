/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue25

/-!
# Complete F1 H-row component batch 32: indices 512–527

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
theorem component_512_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 512) = value 512 := by
  decide +kernel

theorem entry_512_eq : entries 512 = residualTerms (key 512) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_512_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_512 : keyIndex (key 512) = 512 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_513_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 513) = value 513 := by
  decide +kernel

theorem entry_513_eq : entries 513 = residualTerms (key 513) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_513_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_513 : keyIndex (key 513) = 513 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_514_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 514) = value 514 := by
  decide +kernel

theorem entry_514_eq : entries 514 = residualTerms (key 514) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_514_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_514 : keyIndex (key 514) = 514 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_515_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 515) = value 515 := by
  decide +kernel

theorem entry_515_eq : entries 515 = residualTerms (key 515) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_515_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_515 : keyIndex (key 515) = 515 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_516_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 516) = value 516 := by
  decide +kernel

theorem entry_516_eq : entries 516 = residualTerms (key 516) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_516_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_516 : keyIndex (key 516) = 516 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_517_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 517) = value 517 := by
  decide +kernel

theorem entry_517_eq : entries 517 = residualTerms (key 517) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_517_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_517 : keyIndex (key 517) = 517 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_518_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 518) = value 518 := by
  decide +kernel

theorem entry_518_eq : entries 518 = residualTerms (key 518) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_518_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_518 : keyIndex (key 518) = 518 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_519_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 519) = value 519 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 25) = AxiomaticGW.BlowupF1H121Components.value 25
  exact AxiomaticGW.BlowupF1H121Components.component_25_computed

theorem entry_519_eq : entries 519 = residualTerms (key 519) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_519_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_519 : keyIndex (key 519) = 519 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

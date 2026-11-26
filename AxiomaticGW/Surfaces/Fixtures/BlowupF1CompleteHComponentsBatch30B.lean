/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue24

/-!
# Complete F1 H-row component batch 30: indices 480–495

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
theorem component_488_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 488) = value 488 := by
  decide +kernel

theorem entry_488_eq : entries 488 = residualTerms (key 488) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_488_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_488 : keyIndex (key 488) = 488 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_489_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 489) = value 489 := by
  decide +kernel

theorem entry_489_eq : entries 489 = residualTerms (key 489) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_489_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_489 : keyIndex (key 489) = 489 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_490_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 490) = value 490 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 24) = AxiomaticGW.BlowupF1H121Components.value 24
  exact AxiomaticGW.BlowupF1H121Components.component_24_computed

theorem entry_490_eq : entries 490 = residualTerms (key 490) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_490_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_490 : keyIndex (key 490) = 490 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_491_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 491) = value 491 := by
  decide +kernel

theorem entry_491_eq : entries 491 = residualTerms (key 491) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_491_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_491 : keyIndex (key 491) = 491 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_492_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 492) = value 492 := by
  decide +kernel

theorem entry_492_eq : entries 492 = residualTerms (key 492) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_492_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_492 : keyIndex (key 492) = 492 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_493_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 493) = value 493 := by
  decide +kernel

theorem entry_493_eq : entries 493 = residualTerms (key 493) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_493_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_493 : keyIndex (key 493) = 493 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_494_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 494) = value 494 := by
  decide +kernel

theorem entry_494_eq : entries 494 = residualTerms (key 494) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_494_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_494 : keyIndex (key 494) = 494 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_495_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 495) = value 495 := by
  decide +kernel

theorem entry_495_eq : entries 495 = residualTerms (key 495) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_495_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_495 : keyIndex (key 495) = 495 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

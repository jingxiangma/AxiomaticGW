/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue29
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue30
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue31

/-!
# Complete F1 H-row component batch 34: indices 544–559

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
theorem component_544_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 544) = value 544 := by
  decide +kernel

theorem entry_544_eq : entries 544 = residualTerms (key 544) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_544_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_544 : keyIndex (key 544) = 544 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_545_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 545) = value 545 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 29) = AxiomaticGW.BlowupF1H121Components.value 29
  exact AxiomaticGW.BlowupF1H121Components.component_29_computed

theorem entry_545_eq : entries 545 = residualTerms (key 545) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_545_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_545 : keyIndex (key 545) = 545 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_546_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 546) = value 546 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 30) = AxiomaticGW.BlowupF1H121Components.value 30
  exact AxiomaticGW.BlowupF1H121Components.component_30_computed

theorem entry_546_eq : entries 546 = residualTerms (key 546) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_546_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_546 : keyIndex (key 546) = 546 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_547_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 547) = value 547 := by
  decide +kernel

theorem entry_547_eq : entries 547 = residualTerms (key 547) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_547_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_547 : keyIndex (key 547) = 547 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_548_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 548) = value 548 := by
  decide +kernel

theorem entry_548_eq : entries 548 = residualTerms (key 548) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_548_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_548 : keyIndex (key 548) = 548 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_549_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 549) = value 549 := by
  decide +kernel

theorem entry_549_eq : entries 549 = residualTerms (key 549) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_549_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_549 : keyIndex (key 549) = 549 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_550_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 550) = value 550 := by
  decide +kernel

theorem entry_550_eq : entries 550 = residualTerms (key 550) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_550_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_550 : keyIndex (key 550) = 550 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_551_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 551) = value 551 := by
  decide +kernel

theorem entry_551_eq : entries 551 = residualTerms (key 551) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_551_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_551 : keyIndex (key 551) = 551 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue34
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue35

/-!
# Complete F1 H-row component batch 37: indices 592–607

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
theorem component_600_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 600) = value 600 := by
  decide +kernel

theorem entry_600_eq : entries 600 = residualTerms (key 600) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_600_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_600 : keyIndex (key 600) = 600 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_601_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 601) = value 601 := by
  decide +kernel

theorem entry_601_eq : entries 601 = residualTerms (key 601) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_601_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_601 : keyIndex (key 601) = 601 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_602_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 602) = value 602 := by
  decide +kernel

theorem entry_602_eq : entries 602 = residualTerms (key 602) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_602_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_602 : keyIndex (key 602) = 602 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_603_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 603) = value 603 := by
  decide +kernel

theorem entry_603_eq : entries 603 = residualTerms (key 603) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_603_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_603 : keyIndex (key 603) = 603 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_604_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 604) = value 604 := by
  decide +kernel

theorem entry_604_eq : entries 604 = residualTerms (key 604) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_604_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_604 : keyIndex (key 604) = 604 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_605_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 605) = value 605 := by
  decide +kernel

theorem entry_605_eq : entries 605 = residualTerms (key 605) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_605_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_605 : keyIndex (key 605) = 605 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_606_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 606) = value 606 := by
  decide +kernel

theorem entry_606_eq : entries 606 = residualTerms (key 606) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_606_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_606 : keyIndex (key 606) = 606 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_607_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 607) = value 607 := by
  decide +kernel

theorem entry_607_eq : entries 607 = residualTerms (key 607) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_607_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_607 : keyIndex (key 607) = 607 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

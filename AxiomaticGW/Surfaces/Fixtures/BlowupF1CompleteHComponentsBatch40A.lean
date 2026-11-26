/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue38
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue39
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue40

/-!
# Complete F1 H-row component batch 40: indices 640–655

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
theorem component_640_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 640) = value 640 := by
  decide +kernel

theorem entry_640_eq : entries 640 = residualTerms (key 640) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_640_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_640 : keyIndex (key 640) = 640 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_641_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 641) = value 641 := by
  decide +kernel

theorem entry_641_eq : entries 641 = residualTerms (key 641) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_641_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_641 : keyIndex (key 641) = 641 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_642_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 642) = value 642 := by
  decide +kernel

theorem entry_642_eq : entries 642 = residualTerms (key 642) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_642_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_642 : keyIndex (key 642) = 642 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_643_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 643) = value 643 := by
  decide +kernel

theorem entry_643_eq : entries 643 = residualTerms (key 643) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_643_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_643 : keyIndex (key 643) = 643 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_644_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 644) = value 644 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 38) = AxiomaticGW.BlowupF1H121Components.value 38
  exact AxiomaticGW.BlowupF1H121Components.component_38_computed

theorem entry_644_eq : entries 644 = residualTerms (key 644) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_644_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_644 : keyIndex (key 644) = 644 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_645_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 645) = value 645 := by
  decide +kernel

theorem entry_645_eq : entries 645 = residualTerms (key 645) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_645_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_645 : keyIndex (key 645) = 645 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_646_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 646) = value 646 := by
  decide +kernel

theorem entry_646_eq : entries 646 = residualTerms (key 646) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_646_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_646 : keyIndex (key 646) = 646 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_647_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 647) = value 647 := by
  decide +kernel

theorem entry_647_eq : entries 647 = residualTerms (key 647) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_647_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_647 : keyIndex (key 647) = 647 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

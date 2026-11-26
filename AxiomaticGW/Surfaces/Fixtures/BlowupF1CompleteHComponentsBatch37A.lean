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
theorem component_592_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 592) = value 592 := by
  decide +kernel

theorem entry_592_eq : entries 592 = residualTerms (key 592) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_592_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_592 : keyIndex (key 592) = 592 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_593_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 593) = value 593 := by
  decide +kernel

theorem entry_593_eq : entries 593 = residualTerms (key 593) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_593_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_593 : keyIndex (key 593) = 593 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_594_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 594) = value 594 := by
  decide +kernel

theorem entry_594_eq : entries 594 = residualTerms (key 594) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_594_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_594 : keyIndex (key 594) = 594 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_595_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 595) = value 595 := by
  decide +kernel

theorem entry_595_eq : entries 595 = residualTerms (key 595) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_595_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_595 : keyIndex (key 595) = 595 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_596_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 596) = value 596 := by
  decide +kernel

theorem entry_596_eq : entries 596 = residualTerms (key 596) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_596_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_596 : keyIndex (key 596) = 596 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_597_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 597) = value 597 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 34) = AxiomaticGW.BlowupF1H121Components.value 34
  exact AxiomaticGW.BlowupF1H121Components.component_34_computed

theorem entry_597_eq : entries 597 = residualTerms (key 597) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_597_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_597 : keyIndex (key 597) = 597 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_598_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 598) = value 598 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 35) = AxiomaticGW.BlowupF1H121Components.value 35
  exact AxiomaticGW.BlowupF1H121Components.component_35_computed

theorem entry_598_eq : entries 598 = residualTerms (key 598) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_598_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_598 : keyIndex (key 598) = 598 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_599_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 599) = value 599 := by
  decide +kernel

theorem entry_599_eq : entries 599 = residualTerms (key 599) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_599_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_599 : keyIndex (key 599) = 599 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

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
theorem component_552_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 552) = value 552 := by
  decide +kernel

theorem entry_552_eq : entries 552 = residualTerms (key 552) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_552_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_552 : keyIndex (key 552) = 552 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_553_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 553) = value 553 := by
  decide +kernel

theorem entry_553_eq : entries 553 = residualTerms (key 553) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_553_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_553 : keyIndex (key 553) = 553 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_554_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 554) = value 554 := by
  decide +kernel

theorem entry_554_eq : entries 554 = residualTerms (key 554) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_554_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_554 : keyIndex (key 554) = 554 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_555_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 555) = value 555 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 31) = AxiomaticGW.BlowupF1H121Components.value 31
  exact AxiomaticGW.BlowupF1H121Components.component_31_computed

theorem entry_555_eq : entries 555 = residualTerms (key 555) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_555_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_555 : keyIndex (key 555) = 555 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_556_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 556) = value 556 := by
  decide +kernel

theorem entry_556_eq : entries 556 = residualTerms (key 556) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_556_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_556 : keyIndex (key 556) = 556 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_557_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 557) = value 557 := by
  decide +kernel

theorem entry_557_eq : entries 557 = residualTerms (key 557) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_557_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_557 : keyIndex (key 557) = 557 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_558_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 558) = value 558 := by
  decide +kernel

theorem entry_558_eq : entries 558 = residualTerms (key 558) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_558_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_558 : keyIndex (key 558) = 558 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_559_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 559) = value 559 := by
  decide +kernel

theorem entry_559_eq : entries 559 = residualTerms (key 559) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_559_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_559 : keyIndex (key 559) = 559 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

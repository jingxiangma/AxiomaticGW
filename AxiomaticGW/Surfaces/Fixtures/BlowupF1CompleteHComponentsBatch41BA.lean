/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue41
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue42
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue43
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue44

/-!
# Complete F1 H-row component batch 41: indices 656–671

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
theorem component_664_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 664) = value 664 := by
  decide +kernel

theorem entry_664_eq : entries 664 = residualTerms (key 664) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_664_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_664 : keyIndex (key 664) = 664 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_665_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 665) = value 665 := by
  decide +kernel

theorem entry_665_eq : entries 665 = residualTerms (key 665) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_665_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_665 : keyIndex (key 665) = 665 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_666_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 666) = value 666 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 43) = AxiomaticGW.BlowupF1H121Components.value 43
  exact AxiomaticGW.BlowupF1H121Components.component_43_computed

theorem entry_666_eq : entries 666 = residualTerms (key 666) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_666_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_666 : keyIndex (key 666) = 666 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_667_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 667) = value 667 := by
  decide +kernel

theorem entry_667_eq : entries 667 = residualTerms (key 667) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_667_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_667 : keyIndex (key 667) = 667 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

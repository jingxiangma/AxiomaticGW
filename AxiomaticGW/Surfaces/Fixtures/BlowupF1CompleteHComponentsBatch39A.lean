/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue36
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue37

/-!
# Complete F1 H-row component batch 39: indices 624–639

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
theorem component_624_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 624) = value 624 := by
  decide +kernel

theorem entry_624_eq : entries 624 = residualTerms (key 624) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_624_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_624 : keyIndex (key 624) = 624 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_625_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 625) = value 625 := by
  decide +kernel

theorem entry_625_eq : entries 625 = residualTerms (key 625) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_625_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_625 : keyIndex (key 625) = 625 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_626_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 626) = value 626 := by
  decide +kernel

theorem entry_626_eq : entries 626 = residualTerms (key 626) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_626_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_626 : keyIndex (key 626) = 626 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_627_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 627) = value 627 := by
  decide +kernel

theorem entry_627_eq : entries 627 = residualTerms (key 627) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_627_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_627 : keyIndex (key 627) = 627 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_628_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 628) = value 628 := by
  decide +kernel

theorem entry_628_eq : entries 628 = residualTerms (key 628) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_628_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_628 : keyIndex (key 628) = 628 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_629_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 629) = value 629 := by
  decide +kernel

theorem entry_629_eq : entries 629 = residualTerms (key 629) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_629_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_629 : keyIndex (key 629) = 629 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_630_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 630) = value 630 := by
  decide +kernel

theorem entry_630_eq : entries 630 = residualTerms (key 630) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_630_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_630 : keyIndex (key 630) = 630 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_631_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 631) = value 631 := by
  decide +kernel

theorem entry_631_eq : entries 631 = residualTerms (key 631) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_631_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_631 : keyIndex (key 631) = 631 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

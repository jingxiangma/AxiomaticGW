/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue32

/-!
# Complete F1 H-row component batch 35: indices 560–575

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
theorem component_568_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 568) = value 568 := by
  decide +kernel

theorem entry_568_eq : entries 568 = residualTerms (key 568) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_568_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_568 : keyIndex (key 568) = 568 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_569_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 569) = value 569 := by
  decide +kernel

theorem entry_569_eq : entries 569 = residualTerms (key 569) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_569_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_569 : keyIndex (key 569) = 569 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_570_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 570) = value 570 := by
  decide +kernel

theorem entry_570_eq : entries 570 = residualTerms (key 570) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_570_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_570 : keyIndex (key 570) = 570 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_571_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 571) = value 571 := by
  decide +kernel

theorem entry_571_eq : entries 571 = residualTerms (key 571) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_571_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_571 : keyIndex (key 571) = 571 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_572_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 572) = value 572 := by
  decide +kernel

theorem entry_572_eq : entries 572 = residualTerms (key 572) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_572_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_572 : keyIndex (key 572) = 572 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_573_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 573) = value 573 := by
  decide +kernel

theorem entry_573_eq : entries 573 = residualTerms (key 573) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_573_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_573 : keyIndex (key 573) = 573 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_574_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 574) = value 574 := by
  decide +kernel

theorem entry_574_eq : entries 574 = residualTerms (key 574) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_574_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_574 : keyIndex (key 574) = 574 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_575_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 575) = value 575 := by
  decide +kernel

theorem entry_575_eq : entries 575 = residualTerms (key 575) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_575_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_575 : keyIndex (key 575) = 575 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue33

/-!
# Complete F1 H-row component batch 36: indices 576–591

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
theorem component_584_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 584) = value 584 := by
  decide +kernel

theorem entry_584_eq : entries 584 = residualTerms (key 584) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_584_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_584 : keyIndex (key 584) = 584 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_585_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 585) = value 585 := by
  decide +kernel

theorem entry_585_eq : entries 585 = residualTerms (key 585) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_585_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_585 : keyIndex (key 585) = 585 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_586_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 586) = value 586 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 33) = AxiomaticGW.BlowupF1H121Components.value 33
  exact AxiomaticGW.BlowupF1H121Components.component_33_computed

theorem entry_586_eq : entries 586 = residualTerms (key 586) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_586_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_586 : keyIndex (key 586) = 586 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_587_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 587) = value 587 := by
  decide +kernel

theorem entry_587_eq : entries 587 = residualTerms (key 587) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_587_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_587 : keyIndex (key 587) = 587 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_588_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 588) = value 588 := by
  decide +kernel

theorem entry_588_eq : entries 588 = residualTerms (key 588) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_588_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_588 : keyIndex (key 588) = 588 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_589_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 589) = value 589 := by
  decide +kernel

theorem entry_589_eq : entries 589 = residualTerms (key 589) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_589_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_589 : keyIndex (key 589) = 589 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_590_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 590) = value 590 := by
  decide +kernel

theorem entry_590_eq : entries 590 = residualTerms (key 590) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_590_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_590 : keyIndex (key 590) = 590 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_591_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 591) = value 591 := by
  decide +kernel

theorem entry_591_eq : entries 591 = residualTerms (key 591) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_591_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_591 : keyIndex (key 591) = 591 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

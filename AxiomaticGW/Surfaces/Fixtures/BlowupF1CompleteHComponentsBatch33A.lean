/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue26
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue27
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue28

/-!
# Complete F1 H-row component batch 33: indices 528–543

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
theorem component_528_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 528) = value 528 := by
  decide +kernel

theorem entry_528_eq : entries 528 = residualTerms (key 528) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_528_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_528 : keyIndex (key 528) = 528 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_529_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 529) = value 529 := by
  decide +kernel

theorem entry_529_eq : entries 529 = residualTerms (key 529) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_529_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_529 : keyIndex (key 529) = 529 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_530_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 530) = value 530 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 26) = AxiomaticGW.BlowupF1H121Components.value 26
  exact AxiomaticGW.BlowupF1H121Components.component_26_computed

theorem entry_530_eq : entries 530 = residualTerms (key 530) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_530_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_530 : keyIndex (key 530) = 530 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_531_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 531) = value 531 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 27) = AxiomaticGW.BlowupF1H121Components.value 27
  exact AxiomaticGW.BlowupF1H121Components.component_27_computed

theorem entry_531_eq : entries 531 = residualTerms (key 531) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_531_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_531 : keyIndex (key 531) = 531 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_532_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 532) = value 532 := by
  decide +kernel

theorem entry_532_eq : entries 532 = residualTerms (key 532) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_532_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_532 : keyIndex (key 532) = 532 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_533_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 533) = value 533 := by
  decide +kernel

theorem entry_533_eq : entries 533 = residualTerms (key 533) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_533_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_533 : keyIndex (key 533) = 533 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_534_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 534) = value 534 := by
  decide +kernel

theorem entry_534_eq : entries 534 = residualTerms (key 534) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_534_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_534 : keyIndex (key 534) = 534 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_535_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 535) = value 535 := by
  decide +kernel

theorem entry_535_eq : entries 535 = residualTerms (key 535) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_535_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_535 : keyIndex (key 535) = 535 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

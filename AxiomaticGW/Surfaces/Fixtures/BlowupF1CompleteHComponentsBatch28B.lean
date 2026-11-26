/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue18

/-!
# Complete F1 H-row component batch 28: indices 448–463

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
theorem component_456_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 456) = value 456 := by
  decide +kernel

theorem entry_456_eq : entries 456 = residualTerms (key 456) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_456_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_456 : keyIndex (key 456) = 456 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_457_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 457) = value 457 := by
  decide +kernel

theorem entry_457_eq : entries 457 = residualTerms (key 457) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_457_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_457 : keyIndex (key 457) = 457 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_458_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 458) = value 458 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 18) = AxiomaticGW.BlowupF1H121Components.value 18
  exact AxiomaticGW.BlowupF1H121Components.component_18_computed

theorem entry_458_eq : entries 458 = residualTerms (key 458) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_458_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_458 : keyIndex (key 458) = 458 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_459_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 459) = value 459 := by
  decide +kernel

theorem entry_459_eq : entries 459 = residualTerms (key 459) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_459_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_459 : keyIndex (key 459) = 459 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_460_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 460) = value 460 := by
  decide +kernel

theorem entry_460_eq : entries 460 = residualTerms (key 460) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_460_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_460 : keyIndex (key 460) = 460 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_461_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 461) = value 461 := by
  decide +kernel

theorem entry_461_eq : entries 461 = residualTerms (key 461) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_461_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_461 : keyIndex (key 461) = 461 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_462_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 462) = value 462 := by
  decide +kernel

theorem entry_462_eq : entries 462 = residualTerms (key 462) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_462_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_462 : keyIndex (key 462) = 462 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_463_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 463) = value 463 := by
  decide +kernel

theorem entry_463_eq : entries 463 = residualTerms (key 463) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_463_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_463 : keyIndex (key 463) = 463 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

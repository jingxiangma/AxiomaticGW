/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue15
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue16
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue17

/-!
# Complete F1 H-row component batch 27: indices 432–447

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
theorem component_440_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 440) = value 440 := by
  decide +kernel

theorem entry_440_eq : entries 440 = residualTerms (key 440) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_440_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_440 : keyIndex (key 440) = 440 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_441_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 441) = value 441 := by
  decide +kernel

theorem entry_441_eq : entries 441 = residualTerms (key 441) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_441_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_441 : keyIndex (key 441) = 441 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_442_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 442) = value 442 := by
  decide +kernel

theorem entry_442_eq : entries 442 = residualTerms (key 442) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_442_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_442 : keyIndex (key 442) = 442 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_443_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 443) = value 443 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 17) = AxiomaticGW.BlowupF1H121Components.value 17
  exact AxiomaticGW.BlowupF1H121Components.component_17_computed

theorem entry_443_eq : entries 443 = residualTerms (key 443) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_443_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_443 : keyIndex (key 443) = 443 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_444_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 444) = value 444 := by
  decide +kernel

theorem entry_444_eq : entries 444 = residualTerms (key 444) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_444_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_444 : keyIndex (key 444) = 444 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_445_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 445) = value 445 := by
  decide +kernel

theorem entry_445_eq : entries 445 = residualTerms (key 445) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_445_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_445 : keyIndex (key 445) = 445 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_446_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 446) = value 446 := by
  decide +kernel

theorem entry_446_eq : entries 446 = residualTerms (key 446) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_446_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_446 : keyIndex (key 446) = 446 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_447_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 447) = value 447 := by
  decide +kernel

theorem entry_447_eq : entries 447 = residualTerms (key 447) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_447_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_447 : keyIndex (key 447) = 447 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

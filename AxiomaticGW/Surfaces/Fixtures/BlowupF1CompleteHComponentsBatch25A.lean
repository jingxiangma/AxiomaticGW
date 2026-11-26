/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue12

/-!
# Complete F1 H-row component batch 25: indices 400–415

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
theorem component_400_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 400) = value 400 := by
  decide +kernel

theorem entry_400_eq : entries 400 = residualTerms (key 400) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_400_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_400 : keyIndex (key 400) = 400 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_401_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 401) = value 401 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 12) = AxiomaticGW.BlowupF1H121Components.value 12
  exact AxiomaticGW.BlowupF1H121Components.component_12_computed

theorem entry_401_eq : entries 401 = residualTerms (key 401) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_401_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_401 : keyIndex (key 401) = 401 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_402_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 402) = value 402 := by
  decide +kernel

theorem entry_402_eq : entries 402 = residualTerms (key 402) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_402_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_402 : keyIndex (key 402) = 402 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_403_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 403) = value 403 := by
  decide +kernel

theorem entry_403_eq : entries 403 = residualTerms (key 403) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_403_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_403 : keyIndex (key 403) = 403 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_404_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 404) = value 404 := by
  decide +kernel

theorem entry_404_eq : entries 404 = residualTerms (key 404) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_404_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_404 : keyIndex (key 404) = 404 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_405_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 405) = value 405 := by
  decide +kernel

theorem entry_405_eq : entries 405 = residualTerms (key 405) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_405_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_405 : keyIndex (key 405) = 405 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_406_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 406) = value 406 := by
  decide +kernel

theorem entry_406_eq : entries 406 = residualTerms (key 406) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_406_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_406 : keyIndex (key 406) = 406 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_407_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 407) = value 407 := by
  decide +kernel

theorem entry_407_eq : entries 407 = residualTerms (key 407) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_407_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_407 : keyIndex (key 407) = 407 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

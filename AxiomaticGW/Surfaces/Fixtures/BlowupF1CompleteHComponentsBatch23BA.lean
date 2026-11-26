/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue10

/-!
# Complete F1 H-row component batch 23: indices 368–383

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
theorem component_376_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 376) = value 376 := by
  decide +kernel

theorem entry_376_eq : entries 376 = residualTerms (key 376) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_376_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_376 : keyIndex (key 376) = 376 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_377_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 377) = value 377 := by
  decide +kernel

theorem entry_377_eq : entries 377 = residualTerms (key 377) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_377_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_377 : keyIndex (key 377) = 377 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_378_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 378) = value 378 := by
  decide +kernel

theorem entry_378_eq : entries 378 = residualTerms (key 378) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_378_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_378 : keyIndex (key 378) = 378 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_379_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 379) = value 379 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 10) = AxiomaticGW.BlowupF1H121Components.value 10
  exact AxiomaticGW.BlowupF1H121Components.component_10_computed

theorem entry_379_eq : entries 379 = residualTerms (key 379) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_379_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_379 : keyIndex (key 379) = 379 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

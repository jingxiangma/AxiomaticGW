/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue13
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue14

/-!
# Complete F1 H-row component batch 26: indices 416–431

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
theorem component_424_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 424) = value 424 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 13) = AxiomaticGW.BlowupF1H121Components.value 13
  exact AxiomaticGW.BlowupF1H121Components.component_13_computed

theorem entry_424_eq : entries 424 = residualTerms (key 424) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_424_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_424 : keyIndex (key 424) = 424 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_425_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 425) = value 425 := by
  decide +kernel

theorem entry_425_eq : entries 425 = residualTerms (key 425) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_425_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_425 : keyIndex (key 425) = 425 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_426_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 426) = value 426 := by
  decide +kernel

theorem entry_426_eq : entries 426 = residualTerms (key 426) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_426_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_426 : keyIndex (key 426) = 426 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_427_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 427) = value 427 := by
  decide +kernel

theorem entry_427_eq : entries 427 = residualTerms (key 427) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_427_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_427 : keyIndex (key 427) = 427 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_428_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 428) = value 428 := by
  decide +kernel

theorem entry_428_eq : entries 428 = residualTerms (key 428) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_428_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_428 : keyIndex (key 428) = 428 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_429_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 429) = value 429 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 14) = AxiomaticGW.BlowupF1H121Components.value 14
  exact AxiomaticGW.BlowupF1H121Components.component_14_computed

theorem entry_429_eq : entries 429 = residualTerms (key 429) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_429_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_429 : keyIndex (key 429) = 429 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_430_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 430) = value 430 := by
  decide +kernel

theorem entry_430_eq : entries 430 = residualTerms (key 430) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_430_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_430 : keyIndex (key 430) = 430 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_431_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 431) = value 431 := by
  decide +kernel

theorem entry_431_eq : entries 431 = residualTerms (key 431) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_431_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_431 : keyIndex (key 431) = 431 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

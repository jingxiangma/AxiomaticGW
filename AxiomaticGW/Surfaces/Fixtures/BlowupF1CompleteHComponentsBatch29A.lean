/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue19
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue20
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue21
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue22
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue23

/-!
# Complete F1 H-row component batch 29: indices 464–479

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
theorem component_464_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 464) = value 464 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 19) = AxiomaticGW.BlowupF1H121Components.value 19
  exact AxiomaticGW.BlowupF1H121Components.component_19_computed

theorem entry_464_eq : entries 464 = residualTerms (key 464) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_464_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_464 : keyIndex (key 464) = 464 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_465_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 465) = value 465 := by
  decide +kernel

theorem entry_465_eq : entries 465 = residualTerms (key 465) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_465_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_465 : keyIndex (key 465) = 465 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_466_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 466) = value 466 := by
  decide +kernel

theorem entry_466_eq : entries 466 = residualTerms (key 466) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_466_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_466 : keyIndex (key 466) = 466 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_467_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 467) = value 467 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 20) = AxiomaticGW.BlowupF1H121Components.value 20
  exact AxiomaticGW.BlowupF1H121Components.component_20_computed

theorem entry_467_eq : entries 467 = residualTerms (key 467) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_467_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_467 : keyIndex (key 467) = 467 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_468_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 468) = value 468 := by
  decide +kernel

theorem entry_468_eq : entries 468 = residualTerms (key 468) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_468_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_468 : keyIndex (key 468) = 468 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_469_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 469) = value 469 := by
  decide +kernel

theorem entry_469_eq : entries 469 = residualTerms (key 469) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_469_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_469 : keyIndex (key 469) = 469 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_470_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 470) = value 470 := by
  decide +kernel

theorem entry_470_eq : entries 470 = residualTerms (key 470) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_470_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_470 : keyIndex (key 470) = 470 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_471_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 471) = value 471 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 21) = AxiomaticGW.BlowupF1H121Components.value 21
  exact AxiomaticGW.BlowupF1H121Components.component_21_computed

theorem entry_471_eq : entries 471 = residualTerms (key 471) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_471_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_471 : keyIndex (key 471) = 471 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

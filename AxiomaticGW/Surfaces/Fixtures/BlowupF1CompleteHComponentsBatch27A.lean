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
theorem component_432_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 432) = value 432 := by
  decide +kernel

theorem entry_432_eq : entries 432 = residualTerms (key 432) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_432_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_432 : keyIndex (key 432) = 432 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_433_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 433) = value 433 := by
  decide +kernel

theorem entry_433_eq : entries 433 = residualTerms (key 433) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_433_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_433 : keyIndex (key 433) = 433 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_434_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 434) = value 434 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 15) = AxiomaticGW.BlowupF1H121Components.value 15
  exact AxiomaticGW.BlowupF1H121Components.component_15_computed

theorem entry_434_eq : entries 434 = residualTerms (key 434) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_434_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_434 : keyIndex (key 434) = 434 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_435_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 435) = value 435 := by
  decide +kernel

theorem entry_435_eq : entries 435 = residualTerms (key 435) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_435_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_435 : keyIndex (key 435) = 435 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_436_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 436) = value 436 := by
  decide +kernel

theorem entry_436_eq : entries 436 = residualTerms (key 436) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_436_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_436 : keyIndex (key 436) = 436 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_437_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 437) = value 437 := by
  decide +kernel

theorem entry_437_eq : entries 437 = residualTerms (key 437) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_437_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_437 : keyIndex (key 437) = 437 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_438_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 438) = value 438 := by
  decide +kernel

theorem entry_438_eq : entries 438 = residualTerms (key 438) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_438_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_438 : keyIndex (key 438) = 438 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_439_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 439) = value 439 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 16) = AxiomaticGW.BlowupF1H121Components.value 16
  exact AxiomaticGW.BlowupF1H121Components.component_16_computed

theorem entry_439_eq : entries 439 = residualTerms (key 439) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_439_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_439 : keyIndex (key 439) = 439 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

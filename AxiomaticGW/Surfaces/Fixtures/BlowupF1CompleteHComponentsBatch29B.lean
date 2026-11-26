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
theorem component_472_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 472) = value 472 := by
  decide +kernel

theorem entry_472_eq : entries 472 = residualTerms (key 472) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_472_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_472 : keyIndex (key 472) = 472 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_473_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 473) = value 473 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 22) = AxiomaticGW.BlowupF1H121Components.value 22
  exact AxiomaticGW.BlowupF1H121Components.component_22_computed

theorem entry_473_eq : entries 473 = residualTerms (key 473) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_473_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_473 : keyIndex (key 473) = 473 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_474_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 474) = value 474 := by
  decide +kernel

theorem entry_474_eq : entries 474 = residualTerms (key 474) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_474_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_474 : keyIndex (key 474) = 474 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_475_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 475) = value 475 := by
  decide +kernel

theorem entry_475_eq : entries 475 = residualTerms (key 475) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_475_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_475 : keyIndex (key 475) = 475 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_476_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 476) = value 476 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 23) = AxiomaticGW.BlowupF1H121Components.value 23
  exact AxiomaticGW.BlowupF1H121Components.component_23_computed

theorem entry_476_eq : entries 476 = residualTerms (key 476) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_476_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_476 : keyIndex (key 476) = 476 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_477_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 477) = value 477 := by
  decide +kernel

theorem entry_477_eq : entries 477 = residualTerms (key 477) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_477_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_477 : keyIndex (key 477) = 477 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_478_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 478) = value 478 := by
  decide +kernel

theorem entry_478_eq : entries 478 = residualTerms (key 478) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_478_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_478 : keyIndex (key 478) = 478 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_479_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 479) = value 479 := by
  decide +kernel

theorem entry_479_eq : entries 479 = residualTerms (key 479) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_479_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_479 : keyIndex (key 479) = 479 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

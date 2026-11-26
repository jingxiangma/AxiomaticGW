/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 22: indices 352–367

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
theorem component_356_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 356) = value 356 := by
  decide +kernel

theorem entry_356_eq : entries 356 = residualTerms (key 356) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_356_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_356 : keyIndex (key 356) = 356 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_357_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 357) = value 357 := by
  decide +kernel

theorem entry_357_eq : entries 357 = residualTerms (key 357) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_357_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_357 : keyIndex (key 357) = 357 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_358_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 358) = value 358 := by
  decide +kernel

theorem entry_358_eq : entries 358 = residualTerms (key 358) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_358_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_358 : keyIndex (key 358) = 358 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_359_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 359) = value 359 := by
  decide +kernel

theorem entry_359_eq : entries 359 = residualTerms (key 359) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_359_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_359 : keyIndex (key 359) = 359 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

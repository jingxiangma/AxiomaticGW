/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 31: indices 496–511

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
theorem component_496_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 496) = value 496 := by
  decide +kernel

theorem entry_496_eq : entries 496 = residualTerms (key 496) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_496_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_496 : keyIndex (key 496) = 496 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_497_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 497) = value 497 := by
  decide +kernel

theorem entry_497_eq : entries 497 = residualTerms (key 497) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_497_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_497 : keyIndex (key 497) = 497 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_498_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 498) = value 498 := by
  decide +kernel

theorem entry_498_eq : entries 498 = residualTerms (key 498) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_498_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_498 : keyIndex (key 498) = 498 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_499_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 499) = value 499 := by
  decide +kernel

theorem entry_499_eq : entries 499 = residualTerms (key 499) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_499_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_499 : keyIndex (key 499) = 499 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_500_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 500) = value 500 := by
  decide +kernel

theorem entry_500_eq : entries 500 = residualTerms (key 500) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_500_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_500 : keyIndex (key 500) = 500 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_501_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 501) = value 501 := by
  decide +kernel

theorem entry_501_eq : entries 501 = residualTerms (key 501) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_501_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_501 : keyIndex (key 501) = 501 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_502_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 502) = value 502 := by
  decide +kernel

theorem entry_502_eq : entries 502 = residualTerms (key 502) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_502_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_502 : keyIndex (key 502) = 502 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_503_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 503) = value 503 := by
  decide +kernel

theorem entry_503_eq : entries 503 = residualTerms (key 503) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_503_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_503 : keyIndex (key 503) = 503 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

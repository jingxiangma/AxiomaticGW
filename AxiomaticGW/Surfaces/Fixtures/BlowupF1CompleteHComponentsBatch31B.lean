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
theorem component_504_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 504) = value 504 := by
  decide +kernel

theorem entry_504_eq : entries 504 = residualTerms (key 504) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_504_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_504 : keyIndex (key 504) = 504 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_505_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 505) = value 505 := by
  decide +kernel

theorem entry_505_eq : entries 505 = residualTerms (key 505) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_505_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_505 : keyIndex (key 505) = 505 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_506_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 506) = value 506 := by
  decide +kernel

theorem entry_506_eq : entries 506 = residualTerms (key 506) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_506_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_506 : keyIndex (key 506) = 506 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_507_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 507) = value 507 := by
  decide +kernel

theorem entry_507_eq : entries 507 = residualTerms (key 507) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_507_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_507 : keyIndex (key 507) = 507 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_508_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 508) = value 508 := by
  decide +kernel

theorem entry_508_eq : entries 508 = residualTerms (key 508) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_508_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_508 : keyIndex (key 508) = 508 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_509_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 509) = value 509 := by
  decide +kernel

theorem entry_509_eq : entries 509 = residualTerms (key 509) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_509_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_509 : keyIndex (key 509) = 509 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_510_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 510) = value 510 := by
  decide +kernel

theorem entry_510_eq : entries 510 = residualTerms (key 510) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_510_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_510 : keyIndex (key 510) = 510 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_511_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 511) = value 511 := by
  decide +kernel

theorem entry_511_eq : entries 511 = residualTerms (key 511) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_511_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_511 : keyIndex (key 511) = 511 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

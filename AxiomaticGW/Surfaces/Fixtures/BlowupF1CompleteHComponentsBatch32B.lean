/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue25

/-!
# Complete F1 H-row component batch 32: indices 512–527

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
theorem component_520_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 520) = value 520 := by
  decide +kernel

theorem entry_520_eq : entries 520 = residualTerms (key 520) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_520_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_520 : keyIndex (key 520) = 520 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_521_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 521) = value 521 := by
  decide +kernel

theorem entry_521_eq : entries 521 = residualTerms (key 521) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_521_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_521 : keyIndex (key 521) = 521 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_522_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 522) = value 522 := by
  decide +kernel

theorem entry_522_eq : entries 522 = residualTerms (key 522) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_522_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_522 : keyIndex (key 522) = 522 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_523_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 523) = value 523 := by
  decide +kernel

theorem entry_523_eq : entries 523 = residualTerms (key 523) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_523_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_523 : keyIndex (key 523) = 523 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_524_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 524) = value 524 := by
  decide +kernel

theorem entry_524_eq : entries 524 = residualTerms (key 524) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_524_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_524 : keyIndex (key 524) = 524 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_525_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 525) = value 525 := by
  decide +kernel

theorem entry_525_eq : entries 525 = residualTerms (key 525) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_525_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_525 : keyIndex (key 525) = 525 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_526_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 526) = value 526 := by
  decide +kernel

theorem entry_526_eq : entries 526 = residualTerms (key 526) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_526_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_526 : keyIndex (key 526) = 526 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_527_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 527) = value 527 := by
  decide +kernel

theorem entry_527_eq : entries 527 = residualTerms (key 527) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_527_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_527 : keyIndex (key 527) = 527 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

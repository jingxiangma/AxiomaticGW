/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 38: indices 608–623

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
theorem component_608_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 608) = value 608 := by
  decide +kernel

theorem entry_608_eq : entries 608 = residualTerms (key 608) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_608_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_608 : keyIndex (key 608) = 608 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_609_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 609) = value 609 := by
  decide +kernel

theorem entry_609_eq : entries 609 = residualTerms (key 609) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_609_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_609 : keyIndex (key 609) = 609 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_610_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 610) = value 610 := by
  decide +kernel

theorem entry_610_eq : entries 610 = residualTerms (key 610) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_610_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_610 : keyIndex (key 610) = 610 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_611_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 611) = value 611 := by
  decide +kernel

theorem entry_611_eq : entries 611 = residualTerms (key 611) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_611_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_611 : keyIndex (key 611) = 611 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_612_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 612) = value 612 := by
  decide +kernel

theorem entry_612_eq : entries 612 = residualTerms (key 612) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_612_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_612 : keyIndex (key 612) = 612 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_613_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 613) = value 613 := by
  decide +kernel

theorem entry_613_eq : entries 613 = residualTerms (key 613) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_613_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_613 : keyIndex (key 613) = 613 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_614_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 614) = value 614 := by
  decide +kernel

theorem entry_614_eq : entries 614 = residualTerms (key 614) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_614_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_614 : keyIndex (key 614) = 614 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_615_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 615) = value 615 := by
  decide +kernel

theorem entry_615_eq : entries 615 = residualTerms (key 615) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_615_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_615 : keyIndex (key 615) = 615 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

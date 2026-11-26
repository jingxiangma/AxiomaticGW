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
theorem component_616_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 616) = value 616 := by
  decide +kernel

theorem entry_616_eq : entries 616 = residualTerms (key 616) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_616_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_616 : keyIndex (key 616) = 616 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_617_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 617) = value 617 := by
  decide +kernel

theorem entry_617_eq : entries 617 = residualTerms (key 617) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_617_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_617 : keyIndex (key 617) = 617 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_618_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 618) = value 618 := by
  decide +kernel

theorem entry_618_eq : entries 618 = residualTerms (key 618) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_618_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_618 : keyIndex (key 618) = 618 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_619_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 619) = value 619 := by
  decide +kernel

theorem entry_619_eq : entries 619 = residualTerms (key 619) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_619_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_619 : keyIndex (key 619) = 619 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_620_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 620) = value 620 := by
  decide +kernel

theorem entry_620_eq : entries 620 = residualTerms (key 620) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_620_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_620 : keyIndex (key 620) = 620 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_621_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 621) = value 621 := by
  decide +kernel

theorem entry_621_eq : entries 621 = residualTerms (key 621) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_621_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_621 : keyIndex (key 621) = 621 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_622_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 622) = value 622 := by
  decide +kernel

theorem entry_622_eq : entries 622 = residualTerms (key 622) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_622_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_622 : keyIndex (key 622) = 622 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_623_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 623) = value 623 := by
  decide +kernel

theorem entry_623_eq : entries 623 = residualTerms (key 623) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_623_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_623 : keyIndex (key 623) = 623 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

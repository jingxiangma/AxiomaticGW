/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 42: indices 672–687

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
theorem component_680_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 680) = value 680 := by
  decide +kernel

theorem entry_680_eq : entries 680 = residualTerms (key 680) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_680_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_680 : keyIndex (key 680) = 680 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_681_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 681) = value 681 := by
  decide +kernel

theorem entry_681_eq : entries 681 = residualTerms (key 681) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_681_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_681 : keyIndex (key 681) = 681 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_682_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 682) = value 682 := by
  decide +kernel

theorem entry_682_eq : entries 682 = residualTerms (key 682) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_682_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_682 : keyIndex (key 682) = 682 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_683_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 683) = value 683 := by
  decide +kernel

theorem entry_683_eq : entries 683 = residualTerms (key 683) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_683_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_683 : keyIndex (key 683) = 683 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_684_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 684) = value 684 := by
  decide +kernel

theorem entry_684_eq : entries 684 = residualTerms (key 684) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_684_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_684 : keyIndex (key 684) = 684 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_685_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 685) = value 685 := by
  decide +kernel

theorem entry_685_eq : entries 685 = residualTerms (key 685) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_685_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_685 : keyIndex (key 685) = 685 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_686_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 686) = value 686 := by
  decide +kernel

theorem entry_686_eq : entries 686 = residualTerms (key 686) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_686_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_686 : keyIndex (key 686) = 686 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_687_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 687) = value 687 := by
  decide +kernel

theorem entry_687_eq : entries 687 = residualTerms (key 687) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_687_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_687 : keyIndex (key 687) = 687 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

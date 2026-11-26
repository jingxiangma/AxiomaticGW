/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue24

/-!
# Complete F1 H-row component batch 30: indices 480–495

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
theorem component_480_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 480) = value 480 := by
  decide +kernel

theorem entry_480_eq : entries 480 = residualTerms (key 480) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_480_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_480 : keyIndex (key 480) = 480 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_481_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 481) = value 481 := by
  decide +kernel

theorem entry_481_eq : entries 481 = residualTerms (key 481) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_481_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_481 : keyIndex (key 481) = 481 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_482_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 482) = value 482 := by
  decide +kernel

theorem entry_482_eq : entries 482 = residualTerms (key 482) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_482_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_482 : keyIndex (key 482) = 482 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_483_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 483) = value 483 := by
  decide +kernel

theorem entry_483_eq : entries 483 = residualTerms (key 483) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_483_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_483 : keyIndex (key 483) = 483 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_484_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 484) = value 484 := by
  decide +kernel

theorem entry_484_eq : entries 484 = residualTerms (key 484) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_484_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_484 : keyIndex (key 484) = 484 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_485_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 485) = value 485 := by
  decide +kernel

theorem entry_485_eq : entries 485 = residualTerms (key 485) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_485_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_485 : keyIndex (key 485) = 485 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_486_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 486) = value 486 := by
  decide +kernel

theorem entry_486_eq : entries 486 = residualTerms (key 486) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_486_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_486 : keyIndex (key 486) = 486 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_487_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 487) = value 487 := by
  decide +kernel

theorem entry_487_eq : entries 487 = residualTerms (key 487) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_487_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_487 : keyIndex (key 487) = 487 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

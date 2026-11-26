/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue11

/-!
# Complete F1 H-row component batch 24: indices 384–399

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
theorem component_384_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 384) = value 384 := by
  decide +kernel

theorem entry_384_eq : entries 384 = residualTerms (key 384) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_384_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_384 : keyIndex (key 384) = 384 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_385_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 385) = value 385 := by
  decide +kernel

theorem entry_385_eq : entries 385 = residualTerms (key 385) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_385_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_385 : keyIndex (key 385) = 385 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_386_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 386) = value 386 := by
  decide +kernel

theorem entry_386_eq : entries 386 = residualTerms (key 386) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_386_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_386 : keyIndex (key 386) = 386 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_387_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 387) = value 387 := by
  decide +kernel

theorem entry_387_eq : entries 387 = residualTerms (key 387) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_387_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_387 : keyIndex (key 387) = 387 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_388_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 388) = value 388 := by
  decide +kernel

theorem entry_388_eq : entries 388 = residualTerms (key 388) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_388_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_388 : keyIndex (key 388) = 388 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_389_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 389) = value 389 := by
  decide +kernel

theorem entry_389_eq : entries 389 = residualTerms (key 389) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_389_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_389 : keyIndex (key 389) = 389 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_390_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 390) = value 390 := by
  decide +kernel

theorem entry_390_eq : entries 390 = residualTerms (key 390) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_390_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_390 : keyIndex (key 390) = 390 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_391_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 391) = value 391 := by
  decide +kernel

theorem entry_391_eq : entries 391 = residualTerms (key 391) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_391_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_391 : keyIndex (key 391) = 391 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

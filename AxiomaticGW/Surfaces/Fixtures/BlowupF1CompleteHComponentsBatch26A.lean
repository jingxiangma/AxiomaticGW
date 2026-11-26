/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue13
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue14

/-!
# Complete F1 H-row component batch 26: indices 416–431

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
theorem component_416_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 416) = value 416 := by
  decide +kernel

theorem entry_416_eq : entries 416 = residualTerms (key 416) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_416_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_416 : keyIndex (key 416) = 416 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_417_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 417) = value 417 := by
  decide +kernel

theorem entry_417_eq : entries 417 = residualTerms (key 417) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_417_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_417 : keyIndex (key 417) = 417 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_418_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 418) = value 418 := by
  decide +kernel

theorem entry_418_eq : entries 418 = residualTerms (key 418) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_418_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_418 : keyIndex (key 418) = 418 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_419_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 419) = value 419 := by
  decide +kernel

theorem entry_419_eq : entries 419 = residualTerms (key 419) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_419_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_419 : keyIndex (key 419) = 419 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_420_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 420) = value 420 := by
  decide +kernel

theorem entry_420_eq : entries 420 = residualTerms (key 420) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_420_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_420 : keyIndex (key 420) = 420 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_421_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 421) = value 421 := by
  decide +kernel

theorem entry_421_eq : entries 421 = residualTerms (key 421) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_421_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_421 : keyIndex (key 421) = 421 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_422_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 422) = value 422 := by
  decide +kernel

theorem entry_422_eq : entries 422 = residualTerms (key 422) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_422_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_422 : keyIndex (key 422) = 422 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_423_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 423) = value 423 := by
  decide +kernel

theorem entry_423_eq : entries 423 = residualTerms (key 423) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_423_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_423 : keyIndex (key 423) = 423 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

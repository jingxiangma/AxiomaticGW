/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 19: indices 304–319

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
theorem component_304_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 304) = value 304 := by
  decide +kernel

theorem entry_304_eq : entries 304 = residualTerms (key 304) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_304_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_304 : keyIndex (key 304) = 304 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_305_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 305) = value 305 := by
  decide +kernel

theorem entry_305_eq : entries 305 = residualTerms (key 305) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_305_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_305 : keyIndex (key 305) = 305 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_306_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 306) = value 306 := by
  decide +kernel

theorem entry_306_eq : entries 306 = residualTerms (key 306) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_306_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_306 : keyIndex (key 306) = 306 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_307_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 307) = value 307 := by
  decide +kernel

theorem entry_307_eq : entries 307 = residualTerms (key 307) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_307_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_307 : keyIndex (key 307) = 307 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_308_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 308) = value 308 := by
  decide +kernel

theorem entry_308_eq : entries 308 = residualTerms (key 308) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_308_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_308 : keyIndex (key 308) = 308 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_309_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 309) = value 309 := by
  decide +kernel

theorem entry_309_eq : entries 309 = residualTerms (key 309) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_309_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_309 : keyIndex (key 309) = 309 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_310_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 310) = value 310 := by
  decide +kernel

theorem entry_310_eq : entries 310 = residualTerms (key 310) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_310_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_310 : keyIndex (key 310) = 310 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_311_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 311) = value 311 := by
  decide +kernel

theorem entry_311_eq : entries 311 = residualTerms (key 311) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_311_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_311 : keyIndex (key 311) = 311 := by
  decide +kernel


end AxiomaticGW.BlowupF1CompleteHComponents

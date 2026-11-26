/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsValue07

/-!
# Complete F1 H-row component batch 16: indices 256–271

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
theorem component_256_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 256) = value 256 := by
  decide +kernel

theorem entry_256_eq : entries 256 = residualTerms (key 256) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_256_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_256 : keyIndex (key 256) = 256 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_257_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 257) = value 257 := by
  decide +kernel

theorem entry_257_eq : entries 257 = residualTerms (key 257) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_257_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_257 : keyIndex (key 257) = 257 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_258_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 258) = value 258 := by
  decide +kernel

theorem entry_258_eq : entries 258 = residualTerms (key 258) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_258_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_258 : keyIndex (key 258) = 258 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_259_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 259) = value 259 := by
  decide +kernel

theorem entry_259_eq : entries 259 = residualTerms (key 259) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_259_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_259 : keyIndex (key 259) = 259 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_260_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 260) = value 260 := by
  change SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
    (AxiomaticGW.BlowupF1H121Components.key 7) = AxiomaticGW.BlowupF1H121Components.value 7
  exact AxiomaticGW.BlowupF1H121Components.component_7_computed

theorem entry_260_eq : entries 260 = residualTerms (key 260) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_260_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_260 : keyIndex (key 260) = 260 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_261_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 261) = value 261 := by
  decide +kernel

theorem entry_261_eq : entries 261 = residualTerms (key 261) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_261_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_261 : keyIndex (key 261) = 261 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_262_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 262) = value 262 := by
  decide +kernel

theorem entry_262_eq : entries 262 = residualTerms (key 262) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_262_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_262 : keyIndex (key 262) = 262 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_263_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 263) = value 263 := by
  decide +kernel

theorem entry_263_eq : entries 263 = residualTerms (key 263) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_263_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_263 : keyIndex (key 263) = 263 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_264_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 264) = value 264 := by
  decide +kernel

theorem entry_264_eq : entries 264 = residualTerms (key 264) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_264_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_264 : keyIndex (key 264) = 264 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_265_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 265) = value 265 := by
  decide +kernel

theorem entry_265_eq : entries 265 = residualTerms (key 265) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_265_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_265 : keyIndex (key 265) = 265 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_266_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 266) = value 266 := by
  decide +kernel

theorem entry_266_eq : entries 266 = residualTerms (key 266) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_266_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_266 : keyIndex (key 266) = 266 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_267_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 267) = value 267 := by
  decide +kernel

theorem entry_267_eq : entries 267 = residualTerms (key 267) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_267_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_267 : keyIndex (key 267) = 267 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_268_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 268) = value 268 := by
  decide +kernel

theorem entry_268_eq : entries 268 = residualTerms (key 268) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_268_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_268 : keyIndex (key 268) = 268 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_269_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 269) = value 269 := by
  decide +kernel

theorem entry_269_eq : entries 269 = residualTerms (key 269) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_269_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_269 : keyIndex (key 269) = 269 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_270_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 270) = value 270 := by
  decide +kernel

theorem entry_270_eq : entries 270 = residualTerms (key 270) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_270_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_270 : keyIndex (key 270) = 270 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_271_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 271) = value 271 := by
  decide +kernel

theorem entry_271_eq : entries 271 = residualTerms (key 271) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_271_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_271 : keyIndex (key 271) = 271 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

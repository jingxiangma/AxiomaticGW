/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 14: indices 224–239

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
theorem component_224_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 224) = value 224 := by
  decide +kernel

theorem entry_224_eq : entries 224 = residualTerms (key 224) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_224_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_224 : keyIndex (key 224) = 224 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_225_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 225) = value 225 := by
  decide +kernel

theorem entry_225_eq : entries 225 = residualTerms (key 225) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_225_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_225 : keyIndex (key 225) = 225 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_226_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 226) = value 226 := by
  decide +kernel

theorem entry_226_eq : entries 226 = residualTerms (key 226) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_226_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_226 : keyIndex (key 226) = 226 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_227_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 227) = value 227 := by
  decide +kernel

theorem entry_227_eq : entries 227 = residualTerms (key 227) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_227_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_227 : keyIndex (key 227) = 227 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_228_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 228) = value 228 := by
  decide +kernel

theorem entry_228_eq : entries 228 = residualTerms (key 228) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_228_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_228 : keyIndex (key 228) = 228 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_229_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 229) = value 229 := by
  decide +kernel

theorem entry_229_eq : entries 229 = residualTerms (key 229) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_229_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_229 : keyIndex (key 229) = 229 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_230_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 230) = value 230 := by
  decide +kernel

theorem entry_230_eq : entries 230 = residualTerms (key 230) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_230_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_230 : keyIndex (key 230) = 230 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_231_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 231) = value 231 := by
  decide +kernel

theorem entry_231_eq : entries 231 = residualTerms (key 231) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_231_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_231 : keyIndex (key 231) = 231 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_232_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 232) = value 232 := by
  decide +kernel

theorem entry_232_eq : entries 232 = residualTerms (key 232) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_232_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_232 : keyIndex (key 232) = 232 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_233_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 233) = value 233 := by
  decide +kernel

theorem entry_233_eq : entries 233 = residualTerms (key 233) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_233_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_233 : keyIndex (key 233) = 233 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_234_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 234) = value 234 := by
  decide +kernel

theorem entry_234_eq : entries 234 = residualTerms (key 234) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_234_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_234 : keyIndex (key 234) = 234 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_235_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 235) = value 235 := by
  decide +kernel

theorem entry_235_eq : entries 235 = residualTerms (key 235) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_235_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_235 : keyIndex (key 235) = 235 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_236_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 236) = value 236 := by
  decide +kernel

theorem entry_236_eq : entries 236 = residualTerms (key 236) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_236_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_236 : keyIndex (key 236) = 236 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_237_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 237) = value 237 := by
  decide +kernel

theorem entry_237_eq : entries 237 = residualTerms (key 237) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_237_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_237 : keyIndex (key 237) = 237 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_238_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 238) = value 238 := by
  decide +kernel

theorem entry_238_eq : entries 238 = residualTerms (key 238) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_238_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_238 : keyIndex (key 238) = 238 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_239_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 239) = value 239 := by
  decide +kernel

theorem entry_239_eq : entries 239 = residualTerms (key 239) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_239_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_239 : keyIndex (key 239) = 239 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

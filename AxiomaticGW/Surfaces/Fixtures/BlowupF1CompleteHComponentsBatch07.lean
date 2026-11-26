/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsIndex

/-!
# Complete F1 H-row component batch 7: indices 112–127

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
theorem component_112_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 112) = value 112 := by
  decide +kernel

theorem entry_112_eq : entries 112 = residualTerms (key 112) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_112_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_112 : keyIndex (key 112) = 112 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_113_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 113) = value 113 := by
  decide +kernel

theorem entry_113_eq : entries 113 = residualTerms (key 113) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_113_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_113 : keyIndex (key 113) = 113 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_114_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 114) = value 114 := by
  decide +kernel

theorem entry_114_eq : entries 114 = residualTerms (key 114) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_114_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_114 : keyIndex (key 114) = 114 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_115_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 115) = value 115 := by
  decide +kernel

theorem entry_115_eq : entries 115 = residualTerms (key 115) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_115_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_115 : keyIndex (key 115) = 115 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_116_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 116) = value 116 := by
  decide +kernel

theorem entry_116_eq : entries 116 = residualTerms (key 116) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_116_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_116 : keyIndex (key 116) = 116 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_117_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 117) = value 117 := by
  decide +kernel

theorem entry_117_eq : entries 117 = residualTerms (key 117) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_117_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_117 : keyIndex (key 117) = 117 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_118_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 118) = value 118 := by
  decide +kernel

theorem entry_118_eq : entries 118 = residualTerms (key 118) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_118_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_118 : keyIndex (key 118) = 118 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_119_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 119) = value 119 := by
  decide +kernel

theorem entry_119_eq : entries 119 = residualTerms (key 119) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_119_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_119 : keyIndex (key 119) = 119 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_120_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 120) = value 120 := by
  decide +kernel

theorem entry_120_eq : entries 120 = residualTerms (key 120) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_120_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_120 : keyIndex (key 120) = 120 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_121_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 121) = value 121 := by
  decide +kernel

theorem entry_121_eq : entries 121 = residualTerms (key 121) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_121_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_121 : keyIndex (key 121) = 121 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_122_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 122) = value 122 := by
  decide +kernel

theorem entry_122_eq : entries 122 = residualTerms (key 122) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_122_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_122 : keyIndex (key 122) = 122 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_123_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 123) = value 123 := by
  decide +kernel

theorem entry_123_eq : entries 123 = residualTerms (key 123) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_123_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_123 : keyIndex (key 123) = 123 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_124_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 124) = value 124 := by
  decide +kernel

theorem entry_124_eq : entries 124 = residualTerms (key 124) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_124_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_124 : keyIndex (key 124) = 124 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_125_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 125) = value 125 := by
  decide +kernel

theorem entry_125_eq : entries 125 = residualTerms (key 125) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_125_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_125 : keyIndex (key 125) = 125 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_126_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 126) = value 126 := by
  decide +kernel

theorem entry_126_eq : entries 126 = residualTerms (key 126) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_126_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_126 : keyIndex (key 126) = 126 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem component_127_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 127) = value 127 := by
  decide +kernel

theorem entry_127_eq : entries 127 = residualTerms (key 127) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_127_computed]
  rfl

set_option maxHeartbeats 0 in
theorem key_index_127 : keyIndex (key 127) = 127 := by
  decide +kernel

end AxiomaticGW.BlowupF1CompleteHComponents

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineIncidence

/-! # Cotangent degree 1 in the two-marked squares of twice the strict line -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleLinePairComponents
open SurfaceGenusTwoPositiveSquare SurfaceLowGenusPointCache
open GenusTwoSecondUnitPairs.TwoBlowupComponents
open BlowupTwoDoubleLine (curve)

/-- Add checked entries ahead of a complete fallback, preserving previously checked
singleton vertices even when they have the same total cotangent degree. -/
def supplement (c : CertifiedComponents X) (d : ℕ) (rows : ℕ → List (Entry X)) :
    CertifiedComponents X where
  value q := if q.totalPsi = d then stageLookup c.value q (rows (slot q)) else c.value q
  sound q := by
    split
    · exact stageLookup_eq c.value c.sound q _
    · exact c.sound q

/-- Reuse the primitive and singleton components already certified on the strict line. -/
def initial : CertifiedComponents X := BlowupTwoDoubleLineIncidence.withPointSupport
  BlowupTwoDoubleLineComponents.Third.backend

namespace First

/-- Full marked vertices in class zero, L or 2L used by the original square equations. -/
def key (j : Fin 110) : SurfaceAncestorKey X :=
  (#[componentKey 0 z [u₀, u₀, h₀, h₀, h₁],
    componentKey 0 z [u₀, u₀, h₀, a₀, h₁],
    componentKey 0 z [u₀, u₀, h₀, a₀, b₁],
    componentKey 0 z [u₀, u₀, h₀, b₀, h₁],
    componentKey 0 z [u₀, u₀, h₀, b₀, a₁],
    componentKey 0 z [u₀, u₀, h₀, h₁],
    componentKey 0 z [u₀, u₀, a₀, a₀, h₁],
    componentKey 0 z [u₀, u₀, a₀, h₁],
    componentKey 0 z [u₀, u₀, b₀, b₀, h₁],
    componentKey 0 z [u₀, u₀, b₀, b₀, a₁],
    componentKey 0 z [u₀, u₀, b₀, h₁],
    componentKey 0 l [u₀, h₀, a₀, b₀, h₁],
    componentKey 0 l [u₀, h₀, a₀, h₁],
    componentKey 0 l [u₀, h₀, a₀, b₁],
    componentKey 0 l [u₀, h₀, b₀, h₁],
    componentKey 0 l [u₀, h₀, b₀, a₁],
    componentKey 0 l [u₀, a₀, a₀, a₀, h₁],
    componentKey 0 l [u₀, a₀, a₀, b₀, h₁],
    componentKey 0 l [u₀, a₀, b₀, b₀, h₁],
    componentKey 0 l [u₀, a₀, b₀, h₁],
    componentKey 0 l [u₀, b₀, b₀, b₀, h₁],
    componentKey 0 l [u₀, b₀, b₀, b₀, a₁],
    componentKey 0 curve [h₀, h₀, h₀, h₀, h₀, h₁],
    componentKey 0 curve [h₀, h₀, h₀, h₀, h₀, a₁],
    componentKey 0 curve [h₀, h₀, h₀, h₀, h₀, b₁],
    componentKey 0 curve [h₀, h₀, h₀, h₀, a₀, h₁],
    componentKey 0 curve [h₀, h₀, h₀, h₀, a₀, a₁],
    componentKey 0 curve [h₀, h₀, h₀, h₀, a₀, b₁],
    componentKey 0 curve [h₀, h₀, h₀, h₀, b₀, h₁],
    componentKey 0 curve [h₀, h₀, h₀, h₀, b₀, a₁],
    componentKey 0 curve [h₀, h₀, h₀, h₀, b₀, b₁],
    componentKey 0 curve [h₀, h₀, h₀, a₀, a₀, h₁],
    componentKey 0 curve [h₀, h₀, h₀, a₀, a₀, a₁],
    componentKey 0 curve [h₀, h₀, h₀, a₀, a₀, b₁],
    componentKey 0 curve [h₀, h₀, h₀, a₀, b₀, a₁],
    componentKey 0 curve [h₀, h₀, h₀, a₀, b₀, b₁],
    componentKey 0 curve [h₀, h₀, h₀, a₀, h₁],
    componentKey 0 curve [h₀, h₀, h₀, a₀, b₁],
    componentKey 0 curve [h₀, h₀, h₀, b₀, b₀, h₁],
    componentKey 0 curve [h₀, h₀, h₀, b₀, b₀, a₁],
    componentKey 0 curve [h₀, h₀, h₀, b₀, b₀, b₁],
    componentKey 0 curve [h₀, h₀, h₀, b₀, h₁],
    componentKey 0 curve [h₀, h₀, h₀, b₀, a₁],
    componentKey 0 curve [h₀, h₀, a₀, a₀, a₀, h₁],
    componentKey 0 curve [h₀, h₀, a₀, a₀, a₀, a₁],
    componentKey 0 curve [h₀, h₀, a₀, a₀, a₀, b₁],
    componentKey 0 curve [h₀, h₀, a₀, a₀, b₀, h₁],
    componentKey 0 curve [h₀, h₀, a₀, a₀, b₀, a₁],
    componentKey 0 curve [h₀, h₀, a₀, a₀, b₀, b₁],
    componentKey 0 curve [h₀, h₀, a₀, b₀, b₀, h₁],
    componentKey 0 curve [h₀, h₀, a₀, b₀, b₀, a₁],
    componentKey 0 curve [h₀, h₀, a₀, b₀, b₀, b₁],
    componentKey 0 curve [h₀, h₀, a₀, b₀, h₁],
    componentKey 0 curve [h₀, h₀, a₀, b₀, a₁],
    componentKey 0 curve [h₀, h₀, b₀, b₀, b₀, h₁],
    componentKey 0 curve [h₀, h₀, b₀, b₀, b₀, a₁],
    componentKey 0 curve [h₀, h₀, b₀, b₀, b₀, b₁],
    componentKey 0 curve [h₀, a₀, a₀, a₀, a₀, h₁],
    componentKey 0 curve [h₀, a₀, a₀, a₀, a₀, a₁],
    componentKey 0 curve [h₀, a₀, a₀, a₀, a₀, b₁],
    componentKey 0 curve [h₀, a₀, a₀, a₀, b₀, a₁],
    componentKey 0 curve [h₀, a₀, a₀, a₀, b₀, b₁],
    componentKey 0 curve [h₀, a₀, a₀, a₀, h₁],
    componentKey 0 curve [h₀, a₀, a₀, a₀, b₁],
    componentKey 0 curve [h₀, a₀, a₀, b₀, b₀, h₁],
    componentKey 0 curve [h₀, a₀, a₀, b₀, b₀, a₁],
    componentKey 0 curve [h₀, a₀, a₀, b₀, b₀, b₁],
    componentKey 0 curve [h₀, a₀, a₀, b₀, h₁],
    componentKey 0 curve [h₀, a₀, a₀, b₀, a₁],
    componentKey 0 curve [h₀, a₀, b₀, b₀, b₀, a₁],
    componentKey 0 curve [h₀, a₀, b₀, b₀, b₀, b₁],
    componentKey 0 curve [h₀, a₀, b₀, b₀, h₁],
    componentKey 0 curve [h₀, a₀, b₀, b₀, b₁],
    componentKey 0 curve [h₀, a₀, b₀, h₁],
    componentKey 0 curve [h₀, b₀, b₀, b₀, b₀, h₁],
    componentKey 0 curve [h₀, b₀, b₀, b₀, b₀, a₁],
    componentKey 0 curve [h₀, b₀, b₀, b₀, b₀, b₁],
    componentKey 0 curve [h₀, b₀, b₀, b₀, h₁],
    componentKey 0 curve [h₀, b₀, b₀, b₀, a₁],
    componentKey 0 curve [a₀, a₀, a₀, a₀, a₀, h₁],
    componentKey 0 curve [a₀, a₀, a₀, a₀, a₀, a₁],
    componentKey 0 curve [a₀, a₀, a₀, a₀, a₀, b₁],
    componentKey 0 curve [a₀, a₀, a₀, a₀, b₀, h₁],
    componentKey 0 curve [a₀, a₀, a₀, a₀, b₀, a₁],
    componentKey 0 curve [a₀, a₀, a₀, a₀, b₀, b₁],
    componentKey 0 curve [a₀, a₀, a₀, b₀, b₀, h₁],
    componentKey 0 curve [a₀, a₀, a₀, b₀, b₀, a₁],
    componentKey 0 curve [a₀, a₀, a₀, b₀, b₀, b₁],
    componentKey 0 curve [a₀, a₀, a₀, b₀, h₁],
    componentKey 0 curve [a₀, a₀, a₀, b₀, a₁],
    componentKey 0 curve [a₀, a₀, b₀, b₀, b₀, h₁],
    componentKey 0 curve [a₀, a₀, b₀, b₀, b₀, a₁],
    componentKey 0 curve [a₀, a₀, b₀, b₀, b₀, b₁],
    componentKey 0 curve [a₀, b₀, b₀, b₀, b₀, h₁],
    componentKey 0 curve [a₀, b₀, b₀, b₀, b₀, a₁],
    componentKey 0 curve [a₀, b₀, b₀, b₀, b₀, b₁],
    componentKey 0 curve [a₀, b₀, b₀, b₀, h₁],
    componentKey 0 curve [a₀, b₀, b₀, b₀, a₁],
    componentKey 0 curve [b₀, b₀, b₀, b₀, b₀, h₁],
    componentKey 0 curve [b₀, b₀, b₀, b₀, b₀, a₁],
    componentKey 0 curve [b₀, b₀, b₀, b₀, b₀, b₁],
    componentKey 1 z [h₀, h₀, u₁],
    componentKey 1 z [h₀, a₀, u₁],
    componentKey 1 z [h₀, b₀, u₁],
    componentKey 1 z [h₀, u₁],
    componentKey 1 z [a₀, a₀, u₁],
    componentKey 1 z [a₀, b₀, u₁],
    componentKey 1 z [a₀, u₁],
    componentKey 1 z [b₀, b₀, u₁],
    componentKey 1 z [b₀, u₁]] :
    Array (SurfaceAncestorKey X))[j.val]'j.isLt

/-- Source values for these rational and elliptic vertices, in the same order. -/
def values (j : Fin 110) : ℚ :=
  (#[0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -7, -7, -7, -7,
      -7, -7, -7, -7, -7, -7, -7, -7, -7, -7, -3, -3, -7, -7, -7, -3, -3, -7, -7, -7,
      -7, -7, -7, -7, -7, -7, -3, -3, -7, -7, -7, -7, -7, -7, -7, -7, -3, -3, -7, -7,
      -7, -3, -3, -7, -7, -3, -3, -1, -7, -7, -7, -3, -3, -7, -7, -7, -7, -7, -7, -7,
      -7, -7, -3, -3, -7, -7, -7, -7, -7, -7, -3, -3, -7, -7, -7, 0, 0, 0, -1/8, 0, 0,
      -1/24, 0, -1/24] : Array ℚ)[j.val]'j.isLt

set_option Elab.async false
set_option maxRecDepth 65536

set_option maxHeartbeats 4000000 in
-- Check the original boundary recursion on every full marked vertex at this degree.
/-- Check each complete key by its preceding cotangent equation. -/
theorem accepted (j : Fin 110) : values j = stagedValue initial.value (key j) := by
  fin_cases j <;> decide +kernel

/-- Hash buckets for these keys. Acceptance still requires full curve and marking equality. -/
def indices (s : ℕ) : List (Fin 110) :=
  let buckets : Array (List (Fin 110)) :=
    #[[59, 90, 101], [6, 73], [32, 94], [22, 35, 80, 100], [43, 77, 84, 103],
      [5, 16, 107], [47], [28, 51], [36, 108], [10, 12], [42, 65], [15, 38, 70, 89],
      [2, 52, 85], [19], [91], [33, 54, 95], [0, 20, 71, 81, 102], [23], [44, 78],
      [25, 48, 74], [3, 57, 63, 96, 106], [7, 29], [60], [66, 98], [8, 11, 82], [39],
      [53, 86], [49, 92], [18, 67], [55], [21, 24], [45], [1, 105], [26, 75],
      [4, 30, 58, 97], [31, 37, 61, 93], [13, 79, 104], [34, 99], [9, 40, 83],
      [46, 87], [17, 62, 109], [50], [56, 68], [41, 64, 72], [14, 88], [69], [27, 76]]
  (buckets[s]?).getD []

theorem index_complete (j : Fin 110) : j ∈ indices (slot (key j)) := by
  revert j
  decide +kernel

/-- Reuse checked values at this degree while retaining the original fallback everywhere. -/
def backend : CertifiedComponents X := supplement initial 1 fun s ↦
  ((indices s).map fun j ↦ initial.entry (key j) (values j) (accepted j)) ++
    BlowupTwoMixedExceptionalSingletonComponents.FirstPower.candidates s ++
    GenusTwoSecondUnitPairs.TwoBlowupFirstPower.candidates s

end First
end AxiomaticGW.BlowupTwoDoubleLinePairComponents

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineAncestors
public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalSingletons.ThirdPower

/-! # Cotangent-degree 1 lower-genus vertices for the pure double strict line -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleLineComponents.First
open SurfaceGenusTwoPositiveSquare SurfaceLowGenusPointCache
open GenusTwoSecondUnitPairs.TwoBlowupComponents
open BlowupTwoDoubleLine (curve)
open BlowupTwoMixedExceptionalSingletonComponents.ThirdPower (components)

/-- The full marked keys used by the original ten graphs or their lower-cotangent dependencies. -/
def key (j : Fin 177) : SurfaceAncestorKey X :=
  (#[componentKey 0 z [u₀, u₀, u₀, p₁],
    componentKey 0 z [u₀, u₀, a₀, a₁],
    componentKey 0 z [u₀, u₀, b₀, b₁],
    componentKey 0 z [u₀, u₀, p₀, u₁],
    componentKey 0 z [u₀, h₀, h₀, u₁],
    componentKey 0 z [u₀, a₀, a₀, u₁],
    componentKey 0 z [u₀, b₀, b₀, u₁],
    componentKey 0 l [u₀, u₀, h₀, p₁],
    componentKey 0 l [u₀, u₀, a₀, p₁],
    componentKey 0 l [u₀, u₀, b₀, p₁],
    componentKey 0 l [u₀, u₀, p₀, h₁],
    componentKey 0 l [u₀, u₀, p₀, a₁],
    componentKey 0 l [u₀, u₀, p₀, b₁],
    componentKey 0 l [u₀, h₀, h₀, h₁],
    componentKey 0 l [u₀, h₀, h₀, a₁],
    componentKey 0 l [u₀, h₀, h₀, b₁],
    componentKey 0 l [u₀, h₀, a₀, a₁],
    componentKey 0 l [u₀, h₀, b₀, b₁],
    componentKey 0 l [u₀, h₀, p₀, u₁],
    componentKey 0 l [u₀, a₀, a₀, h₁],
    componentKey 0 l [u₀, a₀, a₀, a₁],
    componentKey 0 l [u₀, a₀, a₀, b₁],
    componentKey 0 l [u₀, a₀, b₀, a₁],
    componentKey 0 l [u₀, a₀, b₀, b₁],
    componentKey 0 l [u₀, a₀, p₀, u₁],
    componentKey 0 l [u₀, b₀, b₀, h₁],
    componentKey 0 l [u₀, b₀, b₀, a₁],
    componentKey 0 l [u₀, b₀, b₀, b₁],
    componentKey 0 l [u₀, b₀, p₀, u₁],
    componentKey 0 l [h₀, h₀, h₀, u₁],
    componentKey 0 l [h₀, h₀, a₀, u₁],
    componentKey 0 l [h₀, h₀, b₀, u₁],
    componentKey 0 l [h₀, a₀, a₀, u₁],
    componentKey 0 l [h₀, b₀, b₀, u₁],
    componentKey 0 l [a₀, a₀, a₀, u₁],
    componentKey 0 l [a₀, a₀, b₀, u₁],
    componentKey 0 l [a₀, b₀, b₀, u₁],
    componentKey 0 l [b₀, b₀, b₀, u₁],
    componentKey 0 curve [u₀, u₀, h₀, p₀, p₁],
    componentKey 0 curve [u₀, u₀, a₀, p₀, p₁],
    componentKey 0 curve [u₀, u₀, b₀, p₀, p₁],
    componentKey 0 curve [u₀, u₀, p₀, p₀, h₁],
    componentKey 0 curve [u₀, u₀, p₀, p₀, a₁],
    componentKey 0 curve [u₀, u₀, p₀, p₀, b₁],
    componentKey 0 curve [u₀, u₀, p₀, p₁],
    componentKey 0 curve [u₀, h₀, h₀, h₀, p₁],
    componentKey 0 curve [u₀, h₀, h₀, a₀, p₁],
    componentKey 0 curve [u₀, h₀, h₀, b₀, p₁],
    componentKey 0 curve [u₀, h₀, h₀, p₀, h₁],
    componentKey 0 curve [u₀, h₀, h₀, p₀, a₁],
    componentKey 0 curve [u₀, h₀, h₀, p₀, b₁],
    componentKey 0 curve [u₀, h₀, h₀, p₁],
    componentKey 0 curve [u₀, h₀, a₀, a₀, p₁],
    componentKey 0 curve [u₀, h₀, a₀, p₀, a₁],
    componentKey 0 curve [u₀, h₀, a₀, p₁],
    componentKey 0 curve [u₀, h₀, b₀, b₀, p₁],
    componentKey 0 curve [u₀, h₀, b₀, p₀, b₁],
    componentKey 0 curve [u₀, h₀, b₀, p₁],
    componentKey 0 curve [u₀, h₀, p₀, h₁],
    componentKey 0 curve [u₀, h₀, p₀, a₁],
    componentKey 0 curve [u₀, h₀, p₀, b₁],
    componentKey 0 curve [u₀, a₀, a₀, a₀, p₁],
    componentKey 0 curve [u₀, a₀, a₀, b₀, p₁],
    componentKey 0 curve [u₀, a₀, a₀, p₀, h₁],
    componentKey 0 curve [u₀, a₀, a₀, p₀, a₁],
    componentKey 0 curve [u₀, a₀, a₀, p₀, b₁],
    componentKey 0 curve [u₀, a₀, a₀, p₁],
    componentKey 0 curve [u₀, a₀, b₀, b₀, p₁],
    componentKey 0 curve [u₀, a₀, b₀, p₀, b₁],
    componentKey 0 curve [u₀, a₀, b₀, p₁],
    componentKey 0 curve [u₀, a₀, p₀, h₁],
    componentKey 0 curve [u₀, a₀, p₀, a₁],
    componentKey 0 curve [u₀, a₀, p₀, b₁],
    componentKey 0 curve [u₀, b₀, b₀, b₀, p₁],
    componentKey 0 curve [u₀, b₀, b₀, p₀, h₁],
    componentKey 0 curve [u₀, b₀, b₀, p₀, a₁],
    componentKey 0 curve [u₀, b₀, b₀, p₀, b₁],
    componentKey 0 curve [u₀, b₀, b₀, p₁],
    componentKey 0 curve [u₀, b₀, p₀, h₁],
    componentKey 0 curve [u₀, b₀, p₀, a₁],
    componentKey 0 curve [u₀, b₀, p₀, b₁],
    componentKey 0 curve [u₀, p₀, p₀, u₁],
    componentKey 0 curve [h₀, h₀, h₀, h₀, h₁],
    componentKey 0 curve [h₀, h₀, h₀, h₀, a₁],
    componentKey 0 curve [h₀, h₀, h₀, h₀, b₁],
    componentKey 0 curve [h₀, h₀, h₀, a₀, a₁],
    componentKey 0 curve [h₀, h₀, h₀, b₀, b₁],
    componentKey 0 curve [h₀, h₀, h₀, h₁],
    componentKey 0 curve [h₀, h₀, h₀, a₁],
    componentKey 0 curve [h₀, h₀, h₀, b₁],
    componentKey 0 curve [h₀, h₀, a₀, a₀, h₁],
    componentKey 0 curve [h₀, h₀, a₀, a₀, a₁],
    componentKey 0 curve [h₀, h₀, a₀, a₀, b₁],
    componentKey 0 curve [h₀, h₀, a₀, b₀, b₁],
    componentKey 0 curve [h₀, h₀, a₀, h₁],
    componentKey 0 curve [h₀, h₀, a₀, a₁],
    componentKey 0 curve [h₀, h₀, a₀, b₁],
    componentKey 0 curve [h₀, h₀, b₀, b₀, h₁],
    componentKey 0 curve [h₀, h₀, b₀, b₀, a₁],
    componentKey 0 curve [h₀, h₀, b₀, b₀, b₁],
    componentKey 0 curve [h₀, h₀, b₀, h₁],
    componentKey 0 curve [h₀, h₀, b₀, a₁],
    componentKey 0 curve [h₀, h₀, b₀, b₁],
    componentKey 0 curve [h₀, h₀, p₀, u₁],
    componentKey 0 curve [h₀, a₀, a₀, a₀, a₁],
    componentKey 0 curve [h₀, a₀, a₀, b₀, b₁],
    componentKey 0 curve [h₀, a₀, a₀, h₁],
    componentKey 0 curve [h₀, a₀, a₀, a₁],
    componentKey 0 curve [h₀, a₀, a₀, b₁],
    componentKey 0 curve [h₀, a₀, b₀, b₀, a₁],
    componentKey 0 curve [h₀, a₀, b₀, a₁],
    componentKey 0 curve [h₀, a₀, b₀, b₁],
    componentKey 0 curve [h₀, a₀, p₀, u₁],
    componentKey 0 curve [h₀, b₀, b₀, b₀, b₁],
    componentKey 0 curve [h₀, b₀, b₀, h₁],
    componentKey 0 curve [h₀, b₀, b₀, a₁],
    componentKey 0 curve [h₀, b₀, b₀, b₁],
    componentKey 0 curve [h₀, b₀, p₀, u₁],
    componentKey 0 curve [a₀, a₀, a₀, a₀, h₁],
    componentKey 0 curve [a₀, a₀, a₀, a₀, a₁],
    componentKey 0 curve [a₀, a₀, a₀, a₀, b₁],
    componentKey 0 curve [a₀, a₀, a₀, b₀, b₁],
    componentKey 0 curve [a₀, a₀, a₀, h₁],
    componentKey 0 curve [a₀, a₀, a₀, a₁],
    componentKey 0 curve [a₀, a₀, a₀, b₁],
    componentKey 0 curve [a₀, a₀, b₀, b₀, h₁],
    componentKey 0 curve [a₀, a₀, b₀, b₀, a₁],
    componentKey 0 curve [a₀, a₀, b₀, b₀, b₁],
    componentKey 0 curve [a₀, a₀, b₀, h₁],
    componentKey 0 curve [a₀, a₀, b₀, a₁],
    componentKey 0 curve [a₀, a₀, b₀, b₁],
    componentKey 0 curve [a₀, a₀, p₀, u₁],
    componentKey 0 curve [a₀, b₀, b₀, b₀, b₁],
    componentKey 0 curve [a₀, b₀, b₀, h₁],
    componentKey 0 curve [a₀, b₀, b₀, a₁],
    componentKey 0 curve [a₀, b₀, b₀, b₁],
    componentKey 0 curve [a₀, b₀, p₀, u₁],
    componentKey 0 curve [b₀, b₀, b₀, b₀, h₁],
    componentKey 0 curve [b₀, b₀, b₀, b₀, a₁],
    componentKey 0 curve [b₀, b₀, b₀, b₀, b₁],
    componentKey 0 curve [b₀, b₀, b₀, h₁],
    componentKey 0 curve [b₀, b₀, b₀, a₁],
    componentKey 0 curve [b₀, b₀, b₀, b₁],
    componentKey 0 curve [b₀, b₀, p₀, u₁],
    componentKey 1 z [u₀, h₁],
    componentKey 1 z [u₀, a₁],
    componentKey 1 z [u₀, b₁],
    componentKey 1 z [u₁],
    componentKey 1 l [u₀, p₁],
    componentKey 1 l [h₀, h₁],
    componentKey 1 l [h₀, a₁],
    componentKey 1 l [h₀, b₁],
    componentKey 1 l [a₀, h₁],
    componentKey 1 l [a₀, a₁],
    componentKey 1 l [a₀, b₁],
    componentKey 1 l [b₀, h₁],
    componentKey 1 l [b₀, a₁],
    componentKey 1 l [b₀, b₁],
    componentKey 1 l [p₀, u₁],
    componentKey 1 l [h₁],
    componentKey 1 l [a₁],
    componentKey 1 l [b₁],
    componentKey 1 curve [u₀, p₀, p₁],
    componentKey 1 curve [h₀, h₀, p₁],
    componentKey 1 curve [h₀, p₀, h₁],
    componentKey 1 curve [h₀, p₁],
    componentKey 1 curve [a₀, a₀, p₁],
    componentKey 1 curve [a₀, p₀, a₁],
    componentKey 1 curve [a₀, p₁],
    componentKey 1 curve [b₀, b₀, p₁],
    componentKey 1 curve [b₀, p₀, b₁],
    componentKey 1 curve [b₀, p₁],
    componentKey 1 curve [p₀, p₀, u₁],
    componentKey 1 curve [p₀, h₁],
    componentKey 1 curve [p₀, a₁],
    componentKey 1 curve [p₀, b₁],
    componentKey 1 curve [p₁]] :
    Array (SurfaceAncestorKey X))[j.val]'j.isLt

/-- Reconstructed values in the order of the marked class and genus keys. -/
def values (j : Fin 177) : ℚ :=
  (#[1, -1, -1, 1, 1, -1, -1, 0, 0, 0,
    0, 0, 0, 1, 1, 1, 1, 1, 0, 1,
    1, 1, 1, 1, 0, 1, 1, 1, 0, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, -3, -3, -3, -3, -3, -1, -1, -1,
    -3, -3, -3, -3, -1, -1, -1, -3, -3, -3,
    -1, -1, -1, 0, -3, -3, -1, -1, -1, -3,
    -1, -1, 0, -3, -1, -1, -1, 0, -3, -3,
    -3, -3, -1, -1, -1, -3, -3, -3, -1, -1,
    -1, 0, -3, -1, -1, -1, 0, -3, -3, -3,
    -1, -1, -1, 0, -1/8, -1/24, -1/24, 5/24, 0, -1/12,
    -1/12, -1/12, -1/12, -1/12, -1/12, -1/12, -1/12, -1/12, 0, -1/24,
    -1/24, -1/24, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0] : Array ℚ)[j.val]'j.isLt

set_option Elab.async false
set_option maxRecDepth 65536

set_option maxHeartbeats 3000000 in
-- Each declared component is checked by the preceding lower-cotangent recursion.
/-- Every value satisfies its original genus-zero or genus-one decorated boundary equation. -/
theorem accepted (j : Fin 177) : values j = stagedValue components.value (key j) := by
  fin_cases j <;> decide +kernel

/-- The original component lookup slots, retaining each full key when two slots collide. -/
def indices (s : ℕ) : List (Fin 177) :=
  let buckets : Array (List (Fin 177)) :=
    #[[51, 62, 70, 81, 97, 132, 159], [25, 117], [79, 173], [5, 44, 74, 115, 146],
      [57, 92], [21, 133, 143], [29, 83], [14, 34, 65, 104, 141, 154, 176],
      [77, 89, 105, 137], [18, 49, 118, 124], [11, 31], [45, 60, 95, 149],
      [7, 42, 61, 102, 127], [28, 106, 112, 164], [33, 38, 71, 98, 160, 166],
      [26, 47, 80, 110, 155], [9, 54, 116, 174], [75, 128, 136], [4, 37, 40, 165],
      [55, 84, 134], [15, 69, 142], [3], [30, 50, 85, 138, 171],
      [12, 16, 73, 86, 119, 144], [0, 17, 90, 96, 121], [19, 24, 43, 53, 147, 150],
      [6, 56], [22, 46, 63, 72, 99, 107, 152, 158, 161], [8, 27, 87, 111],
      [122, 131, 156, 163, 172, 175], [36, 39, 76, 109, 148], [58, 113, 129],
      [66, 100, 125, 135, 162], [], [168], [1, 67, 78, 139], [2, 114, 120],
      [145, 169], [32, 91, 151], [20, 82, 93], [13, 23, 108, 140], [64, 153],
      [35, 48, 68, 88, 157], [10, 52, 123, 167], [94, 103, 130, 170], [41, 59],
      [101, 126]]
  (buckets[s]?).getD []

/-- None of the enumerated full keys is omitted by the original slot calculation. -/
theorem index_complete (j : Fin 177) : j ∈ indices (slot (key j)) := by
  revert j
  decide +kernel

/-- Complete lower-genus backend through cotangent degree 1, with original fallback. -/
def backend : CertifiedComponents X := components.layer 1 fun s ↦
  (indices s).map fun j ↦ components.entry (key j) (values j) (accepted j)

end AxiomaticGW.BlowupTwoDoubleLineComponents.First

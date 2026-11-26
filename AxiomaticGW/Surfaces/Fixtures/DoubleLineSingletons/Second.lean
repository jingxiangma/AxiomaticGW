/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.DoubleLineSingletons.First

/-! # Cotangent-degree 2 lower-genus vertices for the pure double strict line -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleLineComponents.Second
open SurfaceGenusTwoPositiveSquare SurfaceLowGenusPointCache
open GenusTwoSecondUnitPairs.TwoBlowupComponents
open BlowupTwoDoubleLine (curve)

/-- The full marked keys used by the original ten graphs or their lower-cotangent dependencies. -/
def key (j : Fin 75) : SurfaceAncestorKey X :=
  (#[componentKey 0 curve [u₀, u₀, p₀, p₀, u₂],
    componentKey 0 curve [u₀, u₀, p₀, u₁, p₁],
    componentKey 0 curve [u₀, h₀, h₀, p₀, u₂],
    componentKey 0 curve [u₀, h₀, h₀, u₁, p₁],
    componentKey 0 curve [u₀, a₀, a₀, p₀, u₂],
    componentKey 0 curve [u₀, a₀, a₀, u₁, p₁],
    componentKey 0 curve [u₀, a₀, p₀, u₁, a₁],
    componentKey 0 curve [u₀, b₀, b₀, p₀, u₂],
    componentKey 0 curve [u₀, b₀, b₀, u₁, p₁],
    componentKey 0 curve [u₀, b₀, p₀, u₁, b₁],
    componentKey 0 curve [h₀, h₀, h₀, h₀, u₂],
    componentKey 0 curve [h₀, h₀, a₀, a₀, u₂],
    componentKey 0 curve [h₀, h₀, a₀, u₁, a₁],
    componentKey 0 curve [h₀, h₀, b₀, b₀, u₂],
    componentKey 0 curve [h₀, h₀, b₀, u₁, b₁],
    componentKey 0 curve [a₀, a₀, a₀, a₀, u₂],
    componentKey 0 curve [a₀, a₀, a₀, u₁, a₁],
    componentKey 0 curve [a₀, a₀, b₀, b₀, u₂],
    componentKey 0 curve [a₀, a₀, b₀, u₁, b₁],
    componentKey 0 curve [a₀, b₀, b₀, u₁, a₁],
    componentKey 0 curve [b₀, b₀, b₀, b₀, u₂],
    componentKey 0 curve [b₀, b₀, b₀, u₁, b₁],
    componentKey 1 z [u₀, u₂],
    componentKey 1 l [u₀, ⟨.hyperplane, 2⟩],
    componentKey 1 l [u₀, ⟨.exceptional 0, 2⟩],
    componentKey 1 l [u₀, ⟨.exceptional 1, 2⟩],
    componentKey 1 l [h₀, u₂],
    componentKey 1 l [a₀, u₂],
    componentKey 1 l [b₀, u₂],
    componentKey 1 l [u₁, h₁],
    componentKey 1 l [u₁, a₁],
    componentKey 1 l [u₁, b₁],
    componentKey 1 curve [u₀, p₀, ⟨.hyperplane, 2⟩],
    componentKey 1 curve [u₀, p₀, ⟨.exceptional 0, 2⟩],
    componentKey 1 curve [u₀, p₀, ⟨.exceptional 1, 2⟩],
    componentKey 1 curve [u₀, h₁, p₁],
    componentKey 1 curve [u₀, a₁, p₁],
    componentKey 1 curve [u₀, b₁, p₁],
    componentKey 1 curve [h₀, h₀, ⟨.hyperplane, 2⟩],
    componentKey 1 curve [h₀, h₀, ⟨.exceptional 0, 2⟩],
    componentKey 1 curve [h₀, h₀, ⟨.exceptional 1, 2⟩],
    componentKey 1 curve [h₀, h₁, h₁],
    componentKey 1 curve [h₀, h₁, a₁],
    componentKey 1 curve [h₀, h₁, b₁],
    componentKey 1 curve [h₀, ⟨.hyperplane, 2⟩],
    componentKey 1 curve [h₀, ⟨.exceptional 0, 2⟩],
    componentKey 1 curve [h₀, ⟨.exceptional 1, 2⟩],
    componentKey 1 curve [a₀, a₀, ⟨.hyperplane, 2⟩],
    componentKey 1 curve [a₀, a₀, ⟨.exceptional 0, 2⟩],
    componentKey 1 curve [a₀, a₀, ⟨.exceptional 1, 2⟩],
    componentKey 1 curve [a₀, h₁, a₁],
    componentKey 1 curve [a₀, a₁, a₁],
    componentKey 1 curve [a₀, a₁, b₁],
    componentKey 1 curve [a₀, ⟨.hyperplane, 2⟩],
    componentKey 1 curve [a₀, ⟨.exceptional 0, 2⟩],
    componentKey 1 curve [a₀, ⟨.exceptional 1, 2⟩],
    componentKey 1 curve [b₀, b₀, ⟨.hyperplane, 2⟩],
    componentKey 1 curve [b₀, b₀, ⟨.exceptional 0, 2⟩],
    componentKey 1 curve [b₀, b₀, ⟨.exceptional 1, 2⟩],
    componentKey 1 curve [b₀, h₁, b₁],
    componentKey 1 curve [b₀, a₁, b₁],
    componentKey 1 curve [b₀, b₁, b₁],
    componentKey 1 curve [b₀, ⟨.hyperplane, 2⟩],
    componentKey 1 curve [b₀, ⟨.exceptional 0, 2⟩],
    componentKey 1 curve [b₀, ⟨.exceptional 1, 2⟩],
    componentKey 1 curve [p₀, u₁, h₁],
    componentKey 1 curve [p₀, u₁, a₁],
    componentKey 1 curve [p₀, u₁, b₁],
    componentKey 1 curve [p₀, u₂],
    componentKey 1 curve [h₁, h₁],
    componentKey 1 curve [h₁, a₁],
    componentKey 1 curve [h₁, b₁],
    componentKey 1 curve [a₁, a₁],
    componentKey 1 curve [a₁, b₁],
    componentKey 1 curve [b₁, b₁]] :
    Array (SurfaceAncestorKey X))[j.val]'j.isLt

/-- Reconstructed values in the order of the marked class and genus keys. -/
def values (j : Fin 75) : ℚ :=
  (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    -1, -1, -2, -1, -2, -1, -2, -1, -2, -2,
    -1, -2, 5/24, -1/24, -1/24, -1/24, -1/24, -1/24, -1/24, -1/24,
    -1/24, -1/24, 0, 0, 0, 0, 0, 0, 1/6, 1/6,
    1/6, 1/4, 1/4, 1/4, 1/24, 1/24, 1/24, 1/6, 1/6, 1/6,
    1/4, 1/4, 1/4, 1/24, 1/24, 1/24, 1/6, 1/6, 1/6, 1/4,
    1/4, 1/4, 1/24, 1/24, 1/24, 0, 0, 0, 0, 1/24,
    1/24, 1/24, 1/24, 1/24, 1/24] : Array ℚ)[j.val]'j.isLt

set_option Elab.async false
set_option maxRecDepth 65536

set_option maxHeartbeats 3000000 in
-- Each declared component is checked by the preceding lower-cotangent recursion.
/-- Every value satisfies its original genus-zero or genus-one decorated boundary equation. -/
theorem accepted (j : Fin 75) : values j = stagedValue First.backend.value (key j) := by
  fin_cases j <;> decide +kernel

/-- The original component lookup slots, retaining each full key when two slots collide. -/
def indices (s : ℕ) : List (Fin 75) :=
  let buckets : Array (List (Fin 75)) :=
    #[[35, 64], [28, 38], [23], [8], [32], [], [12, 53], [14, 40], [25, 43],
      [6, 22, 30, 56], [9, 11, 34, 48], [50, 66, 73], [55, 59], [4, 27], [19, 36, 45],
      [21, 58], [], [69], [17, 63], [], [], [], [31], [], [67, 74], [10, 39, 51],
      [24, 60], [5, 37], [2, 33, 41], [], [54], [0, 70], [], [13, 47, 57], [], [68],
      [7], [44], [16, 52], [18, 49, 61], [], [20, 62], [3, 15, 29, 42], [46],
      [26, 65, 71], [1, 72], []]
  (buckets[s]?).getD []

/-- None of the enumerated full keys is omitted by the original slot calculation. -/
theorem index_complete (j : Fin 75) : j ∈ indices (slot (key j)) := by
  revert j
  decide +kernel

/-- Complete lower-genus backend through cotangent degree 2, with original fallback. -/
def backend : CertifiedComponents X := First.backend.layer 2 fun s ↦
  (indices s).map fun j ↦ First.backend.entry (key j) (values j) (accepted j)

end AxiomaticGW.BlowupTwoDoubleLineComponents.Second

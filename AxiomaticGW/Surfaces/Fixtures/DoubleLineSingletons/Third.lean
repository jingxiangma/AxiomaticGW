/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.DoubleLineSingletons.Second

/-! # Cotangent-degree 3 lower-genus vertices for the pure double strict line -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleLineComponents.Third
open SurfaceGenusTwoPositiveSquare SurfaceLowGenusPointCache
open GenusTwoSecondUnitPairs.TwoBlowupComponents
open BlowupTwoDoubleLine (curve)

/-- The full marked keys used by the original ten graphs or their lower-cotangent dependencies. -/
def key (j : Fin 9) : SurfaceAncestorKey X :=
  (#[componentKey 1 curve [u₀, p₀, ⟨.unit, 3⟩],
    componentKey 1 curve [u₀, p₁, u₂],
    componentKey 1 curve [h₀, h₀, ⟨.unit, 3⟩],
    componentKey 1 curve [h₀, h₁, u₂],
    componentKey 1 curve [a₀, a₀, ⟨.unit, 3⟩],
    componentKey 1 curve [a₀, a₁, u₂],
    componentKey 1 curve [b₀, b₀, ⟨.unit, 3⟩],
    componentKey 1 curve [b₀, b₁, u₂],
    componentKey 1 curve [p₀, u₁, u₂]] :
    Array (SurfaceAncestorKey X))[j.val]'j.isLt

/-- Reconstructed values in the order of the marked class and genus keys. -/
def values (j : Fin 9) : ℚ :=
  (#[0, 0, 1/24, 1/12, 1/24, 1/12, 1/24, 1/12, 0] : Array ℚ)[j.val]'j.isLt

set_option Elab.async false
set_option maxRecDepth 65536

set_option maxHeartbeats 3000000 in
-- Each declared component is checked by the preceding lower-cotangent recursion.
/-- Every value satisfies its original genus-zero or genus-one decorated boundary equation. -/
theorem accepted (j : Fin 9) : values j = stagedValue Second.backend.value (key j) := by
  fin_cases j <;> decide +kernel

/-- The original component lookup slots, retaining each full key when two slots collide. -/
def indices (s : ℕ) : List (Fin 9) :=
  let buckets : Array (List (Fin 9)) :=
    #[[], [], [], [], [], [], [], [], [], [4], [], [], [], [], [3], [], [], [], [],
      [], [], [], [], [], [2], [], [], [0], [], [], [8], [], [6], [1], [], [], [], [],
      [], [], [], [], [], [], [5], [7], []]
  (buckets[s]?).getD []

/-- None of the enumerated full keys is omitted by the original slot calculation. -/
theorem index_complete (j : Fin 9) : j ∈ indices (slot (key j)) := by
  revert j
  decide +kernel

/-- Complete lower-genus backend through cotangent degree 3, with original fallback. -/
def backend : CertifiedComponents X := Second.backend.layer 3 fun s ↦
  (indices s).map fun j ↦ Second.backend.entry (key j) (values j) (accepted j)

end AxiomaticGW.BlowupTwoDoubleLineComponents.Third

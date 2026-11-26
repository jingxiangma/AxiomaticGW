/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHValue

/-!
# Incoming genus-two F1 fiber hyperplane descendant

Input SHA256: 7d705ea6e15c2490ff17c6b9e7cc2995f5dcd6b9d78b04ab884e0d3fa534b208
The incoming ordinary value is bound to the complete held descendant query.
Geometric interpretation retains the original equation and seed hypotheses.
This does not certify equivariant localization or import CohFT classes.
-/

@[expose] public section

namespace AxiomaticGW.GKM.BlowupF1FiberHReplay

open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder

/-- Incoming class, genus, ordered states and powers, including both point markings. -/
def request : SurfaceQuery .hirzebruchOne :=
  ⟨2, ![0, 1], [⟨.hyperplane, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩]⟩

/-- The actual incoming ordinary rational, independently checked by `accepted`. -/
def value : ℚ := 0

/-- Exact binding to the separately held full fiber descendant request. -/
theorem request_eq : request = BlowupF1FiberHValue.query := by
  decide +kernel

/-- The incoming value agrees with the proved reconstruction at that exact query. -/
theorem accepted :
    canonicalValuation (SurfaceGenusTwoBlowupRecursion.values 0) (.inr request) = value := by
  rw [request_eq, BlowupF1FiberHValue.reconstructed_query]
  norm_num only [value]

end AxiomaticGW.GKM.BlowupF1FiberHReplay

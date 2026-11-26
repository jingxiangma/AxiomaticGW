/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.LowGenusVirtualDimension
public import AxiomaticGW.Surfaces.Fixtures.CertifiedComponentLayers

/-! # Virtual-dimension pruning for certified component evaluators -/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwoPositiveSquare.CertifiedComponents
open SurfaceLowGenusPointCache SurfacePointBenchmarkCache

/-- Reject a lower-genus key of the wrong virtual dimension before inspecting a cache or
expanding another cotangent equation. All compatible keys retain the supplied evaluator. -/
def withVirtualDimension {X : SurfaceTarget} (c : CertifiedComponents X) :
    CertifiedComponents X where
  value q := if q.genus ≤ 1 ∧ ¬q.DimensionCompatible then 0 else c.value q
  sound q := by
    split
    next h =>
      rw [pointCoordinateComponent, coordinateComponent_eq]
      exact (component_zero_of_dimension (genusZero X) (genusOne X) q h.1 h.2).symm
    exact c.sound q

end AxiomaticGW.SurfaceGenusTwoPositiveSquare.CertifiedComponents

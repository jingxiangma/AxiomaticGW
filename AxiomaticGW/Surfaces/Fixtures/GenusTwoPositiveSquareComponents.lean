/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.ScalarAncestorStep
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPositiveDivisorPairs

/-! # Effective-coordinate component values for the positive two-marked square -/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwoPositiveSquare
open SurfaceGenusTwoPositiveDivisorPairs SurfaceLowGenusPointCache SurfacePointBenchmarkCache
variable {X : SurfaceTarget}

/-- The lower-genus recursion sums over full effective-coordinate boxes. The supplied
higher-genus terminal receives the original dimension-compatible ancestor key. -/
def component (next : SurfaceAncestorKey X → ℚ) : SurfaceVertexValues X ℚ :=
  fun g S _ h beta k a ↦
    let q := SurfaceAncestorKey.ofLabels g S h beta k a
    if q.DimensionCompatible then
      if g ≤ 1 then scalarComponentValue X (genusZero X) (genusOne X) q else next q
    else 0

theorem component_eq (next : SurfaceAncestorKey X → ℚ) :
    component next = vertex next := by
  funext g S inst h beta k a
  simp only [component, vertex, scalarComponentValue_eq]

end AxiomaticGW.SurfaceGenusTwoPositiveSquare

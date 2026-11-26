import AxiomaticGW.Surfaces.Fixtures.BlowupTwoShiftedPrimaries

/-! # Primary sewing on intersecting and orthogonal rational curves

Both primary factors are nonzero in each control. The internal diagonal distinguishes
the strict line's intersections with the exceptional curve and its neighboring ruling.
-/

namespace AxiomaticGWTest.BlowupTwoShiftedPrimaries
open AxiomaticGW SurfaceLowGenusPointCache SurfacePointBenchmarkCache
private abbrev X := SurfaceTarget.blowupTwo

private def line : X.Curve := ![0, 0, 1]
private def ruling : X.Curve := ![1, 0, 1]
private def exceptional : X.Curve := ![1, 0, 0]

private def sewn (d : X.Curve) (m : Multiset (SurfaceBasisLabel X)) : ℚ :=
  ∑ b : SurfaceBasisLabel X, b.inverseWeight *
    (rationalPrimary X (genusZero X) d (b ::ₘ m) *
      rationalPrimary X (genusZero X) line (b.dual ::ₘ {.hyperplane, .hyperplane}))

example : sewn ruling {.point, .hyperplane} = 0 ∧
    sewn exceptional {.exceptional 0, .exceptional 0} = 1 := by
  constructor <;> unfold sewn <;>
    rw [rationalPrimary_node_sewing _ _ _ (by decide +kernel) (by decide +kernel)] <;>
    decide +kernel

/-- An actual dimension-compatible elliptic vertex of the shifted L24 calculation at E₁+2L. -/
private def elliptic : SurfaceAncestorKey X :=
  SurfaceAncestorKey.ofLabels 1 (Fin 6) (by norm_num [StableArity]) ![1, 0, 2]
    ![0, 0, 0, 0, 0, 1] ![.hyperplane, .hyperplane, .hyperplane, .exceptional 0, .point, .point]

example : elliptic.DimensionCompatible ∧
    componentValue X (genusZero X) (genusOne X) elliptic = 0 := by
  refine ⟨by decide +kernel, AxiomaticGW.BlowupTwoShiftedPrimaries.component_zero 0 _ ?_ ?_ ?_⟩
  all_goals decide +kernel

end AxiomaticGWTest.BlowupTwoShiftedPrimaries

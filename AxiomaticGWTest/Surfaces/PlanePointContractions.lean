/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.PlanePointContractions

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.PlanePointContractions
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwo BelorousskiPandharipande

private def hyperplane (d : ℕ) : Variable .plane :=
  .inr (SurfaceFirstDescendant.query 2 ![d] .hyperplane (3 * d))

private def point (d : ℕ) : Variable .plane :=
  .inr (SurfaceFirstDescendant.query 2 ![d] .point (3 * d - 1))

-- The raw third and fourth diagrams distinguish an external psi from a
-- node psi, even when the three external labels are identical points.
example : remainderPointCoefficient .plane (point 1) (planeCoefficientVertex (point 1))
    (paperCotangentTerm 2) ![1] 2 ![.point, .point, .point] = 1 := by
  rw [plane_paper_two_two_points]
  have hk : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
  rw [hk, remainderVertex_plane_point_hyperplane]
  decide +kernel

example : remainderPointCoefficient .plane (hyperplane 1) (planeCoefficientVertex (hyperplane 1))
    (paperCotangentTerm 2) ![1] 2 ![.point, .point, .point] = 0 := by
  rw [plane_paper_two_two_points]
  have hk : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
  rw [hk, remainderVertex_plane_point_hyperplane]
  decide +kernel

example : remainderPointCoefficient .plane (point 1) (planeCoefficientVertex (point 1))
    (paperCotangentTerm 3) ![1] 2 ![.point, .point, .point] = 0 := by
  rw [plane_paper_three_two_points]
  have hk : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
  rw [hk, remainderVertex_plane_point_hyperplane]
  decide +kernel

example : remainderPointCoefficient .plane (hyperplane 1) (planeCoefficientVertex (hyperplane 1))
    (paperCotangentTerm 3) ![1] 2 ![.point, .point, .point] = 1 := by
  rw [plane_paper_three_two_points]
  have hk : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
  rw [hk, remainderVertex_plane_point_hyperplane]
  decide +kernel

-- The degree-zero boundary cannot satisfy n + 1 = 3d for any count.
example (v : Variable .plane) (n : ℕ) (hv : SurfaceGenusZero.variableCurve v 0 = 0) :
    planeRemainderPointCoefficient n ![1] ![.point, .point, .point] v = 0 := by
  rw [planeRemainderPointCoefficient_three_points_canonical]
  simp only [hv, Nat.mul_zero, if_neg (by omega : n + 1 ≠ 0)]

-- A wrong primary-point multiplicity is a different requested invariant.
example : planeRemainderPointCoefficient 8 ![1] ![.point, .point, .point]
    (.inr (SurfaceFirstDescendant.query 2 ![3] .hyperplane 8)) = 0 := by
  rw [planeRemainderPointCoefficient_three_points_canonical]
  decide +kernel

-- A higher-power ancestor cannot reuse a first-descendant coefficient.
example : planeRemainderPointCoefficient 8 ![1] ![.point, .point, .point]
    (.inl (SurfaceAncestorKey.ofLabels 2 (Fin 1) (by norm_num [StableArity])
      ![3] ![2] ![.hyperplane])) = 0 := by
  rw [planeRemainderPointCoefficient_three_points_canonical]
  decide +kernel

-- The uniform row reaches the fixed quartic benchmark degree; these remain
-- equation coefficients, not a claim that the invariant suite is completed.
example :
    let f := fun q : SurfaceQuery .plane ↦
      planeRemainderPointCoefficient 11 ![1] ![.point, .point, .point] (.inr q)
    (f (SurfaceQuery.points .plane 2 ![4] 13),
      f (SurfaceFirstDescendant.query 2 ![4] .hyperplane 12),
      f (SurfaceFirstDescendant.query 2 ![4] .point 11)) = (0, -18, 72) := by
  convert planeRemainderPointCoefficient_three_points_row 4 (by decide) using 1
  norm_num

-- This consumer uses the full original equation, not the remainder shortcut.
example : RationalTerms.coefficient (normalizedGenusTwoTerms .plane 8 ![4] 0
      (SurfaceGenusZero.pointLabels ![.point, .point, .point] 8)) {point 3} = 54 := by
  have h := congrArg (fun t : ℚ × ℚ × ℚ ↦ t.2.2) (normalized_plane_three_points_row 3 (by decide))
  convert h using 1 <;> norm_num [point]

end AxiomaticGWTest.Surfaces.PlanePointContractions

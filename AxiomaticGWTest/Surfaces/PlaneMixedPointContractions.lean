/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.PlaneSourceDegree

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.PlaneMixedPointContractions
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwo BelorousskiPandharipande
open GluingExpression

-- An arbitrary main functional makes lost classical branches visible. It is
-- only a contraction probe, not a claimed geometric invariant model.
private def probe : ℕ → SurfaceCotangentVertexValues .plane ℚ :=
  fun m _ _ _ _ _ _ delta _ ↦ if delta = ![1] then 7 else (m : ℚ) + 1

private def pair (v : Variable .plane) (n : ℕ) (a : Fin 3 → SurfaceBasisLabel .plane) : ℚ :=
  remainderContraction .plane v probe
    (GetzlerGraphs.join (m := 1) (n := 2) 1 2
      (fundamental 2 (Fin 2) (by norm_num [StableArity]))
      (fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (by exact ((0 : Fin 2 → ℕ), (0 : Fin 3 → ℕ)))
    (by exact ((inferInstance : DecidableEq (Fin 2)),
      (inferInstance : DecidableEq (Fin 3)))) ![1] n a

-- The classical HH component survives with no added points, where both
-- binomial line terms vanish. Dropping it would incorrectly return zero.
example (v : Variable .plane) : pair v 0 ![.point, .hyperplane, .hyperplane] = 7 := by
  rw [pair, remainderContraction_plane_two_hyperplanes_join]
  norm_num [remainderContraction, probe]

-- Natural subtraction at counts zero and one causes no spurious line term.
example (v : Variable .plane) : pair v 1 ![.point, .hyperplane, .hyperplane] = 8 := by
  have hz : (0 : SurfaceTarget.plane.Curve) ≠ ![1] := by decide +kernel
  rw [pair, remainderContraction_plane_two_hyperplanes_join]
  norm_num [remainderContraction, probe, hz]

-- The two independent placements have weights n and choose(n,2), and the
-- classical term still contributes seven.
example (v : Variable .plane) : pair v 4 ![.point, .hyperplane, .hyperplane] = 41 := by
  have hz : (0 : SurfaceTarget.plane.Curve) ≠ ![1] := by decide +kernel
  rw [pair, remainderContraction_plane_two_hyperplanes_join]
  norm_num [remainderContraction, probe, hz, Nat.choose]

example (v : Variable .plane) : pair v 4 ![.hyperplane, .hyperplane, .point] = 21 := by
  have hz : (0 : SurfaceTarget.plane.Curve) ≠ ![1] := by decide +kernel
  rw [pair, remainderContraction_plane_hyperplane_point_join]
  norm_num [remainderContraction, probe, hz]

-- Swapping the two rational external slots preserves their incidence, while
-- the main marking stays in slot zero.
example (v : Variable .plane) (n : ℕ) :
    pair v n ![.hyperplane, .point, .hyperplane] =
      pair v n ![.hyperplane, .hyperplane, .point] := by
  exact remainderContraction_plane_pair_swap v probe n _ _ _ ![1] _ _ _

private def point (d : ℕ) : Variable .plane :=
  .inr (SurfaceFirstDescendant.query 2 ![d] .point (3 * d - 1))

-- Both single-psi source-degree HHP diagrams are nonzero. Their opposite
-- raw coefficients must cancel, rather than either diagram being discarded.
example : remainderPointCoefficient .plane (point 2) (planeCoefficientVertex (point 2))
    (paperCotangentTerm 2) 0 4 ![.point, .hyperplane, .hyperplane] = 1 := by
  change remainderPointCoefficient .plane (point 2) (planeCoefficientVertex (point 2))
    (paperCotangentTerm (if (0 : Fin 2) = 0 then 2 else 3)) 0 4
      ![.point, .hyperplane, .hyperplane] = 1
  rw [plane_paper_onePsi_two_hyperplanes_zero, remainderVertex_onePsi_plane_zero_normalized]
  decide +kernel

example : remainderPointCoefficient .plane (point 2) (planeCoefficientVertex (point 2))
    (paperCotangentTerm 3) 0 4 ![.point, .hyperplane, .hyperplane] = 1 := by
  change remainderPointCoefficient .plane (point 2) (planeCoefficientVertex (point 2))
    (paperCotangentTerm (if (1 : Fin 2) = 0 then 2 else 3)) 0 4
      ![.point, .hyperplane, .hyperplane] = 1
  rw [plane_paper_onePsi_two_hyperplanes_zero, remainderVertex_onePsi_plane_zero_normalized]
  decide +kernel

-- The complete equation vanishes at the source degree, despite those two
-- nonzero individual contributions.
example : RationalTerms.coefficient (normalizedGenusTwoTerms .plane 4 ![2] 0
    (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .point] 4)) {point 2} = 0 := by
  simpa only [point, SurfaceGenusZero.variableCurve, SurfaceFirstDescendant.query] using
    normalized_plane_two_hyperplanes_source_degree (point 2) 4

-- Source cancellation covers higher-ancestor tags as well as the three
-- canonical columns in the explored numerical matrix.
example (n : ℕ) :
    let v : Variable .plane := .inl (SurfaceAncestorKey.ofLabels 2 (Fin 1)
      (by norm_num [StableArity]) ![4] ![2] ![.hyperplane])
    RationalTerms.coefficient (normalizedGenusTwoTerms .plane n ![4] 0
      (SurfaceGenusZero.pointLabels ![.hyperplane, .point, .point] n)) {v} = 0 := by
  dsimp only
  simpa only [SurfaceGenusZero.variableCurve, SurfaceAncestorKey.ofLabels] using
    normalized_plane_two_points_source_degree
      (.inl (SurfaceAncestorKey.ofLabels 2 (Fin 1) (by norm_num [StableArity])
        ![4] ![2] ![.hyperplane])) n .hyperplane (Or.inl rfl)

-- The degree-zero source boundary and arbitrary extra point counts are included.
example (n : ℕ) : planeRemainderPointCoefficient n 0 ![.point, .point, .point]
    (.inr (SurfaceQuery.points .plane 2 0 1)) = 0 :=
  planeRemainderPointCoefficient_two_points_zero _ n .point (Or.inr rfl)

-- A nonzero coefficient in source degree d+1 can have degree d, but cannot
-- remain at d+1. This support statement alone is not a reconstruction pivot.
example (v : Variable .plane) (n d : ℕ)
    (hc : RationalTerms.coefficient (normalizedGenusTwoTerms .plane n ![d + 1] 0
      (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .point] n)) {v} ≠ 0) :
    SurfaceGenusZero.variableCurve v 0 ≤ d := by
  have h := normalized_plane_two_hyperplanes_degree_lt v n (d + 1) hc
  omega

example (v : Variable .plane) (n d : ℕ)
    (hc : RationalTerms.coefficient (normalizedGenusTwoTerms .plane n ![d + 1] 0
      (SurfaceGenusZero.pointLabels ![.hyperplane, .point, .point] n)) {v} ≠ 0) :
    SurfaceGenusZero.variableCurve v 0 ≤ d := by
  have h := normalized_plane_two_points_degree_lt v n (d + 1) .hyperplane (Or.inl rfl) hc
  omega

end AxiomaticGWTest.Surfaces.PlaneMixedPointContractions

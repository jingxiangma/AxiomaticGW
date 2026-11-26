/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.PlaneShiftedSystem

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.PlaneShiftedSystem
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwo BelorousskiPandharipande

private def primary (d : ℕ) : Variable .plane :=
  .inr (SurfaceQuery.points .plane 2 ![d] (3 * d + 1))

private def hyperplane (d : ℕ) : Variable .plane :=
  .inr (SurfaceFirstDescendant.query 2 ![d] .hyperplane (3 * d))

-- The middle node, rather than an external slot, carries the hyperplane.
example : (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal 4, ((4 : ℕ).choose ij.1 : ℚ) *
    ((ij.1 + 1 : ℚ) * SurfaceGenusZero.primaryScalar .plane
      (SurfaceGenusZero.pointValue .plane) ![1] ij.2
        (![.point, .hyperplane, .point] : Fin 3 → _))) = 5 := by
  rw [SurfaceGenusZero.sum_binomial_primary_plane_point_node_point
    (fun m ↦ (m : ℚ) + 1) 4 .hyperplane]
  decide +kernel

-- Retaining the inner line gives five, not just the four outer-line placements.
example : remainderPointCoefficient .plane (primary 1) (planeCoefficientVertex (primary 1))
    (paperCotangentTerm 0) ![1] 4 ![.point, .hyperplane, .hyperplane] = 5 := by
  have huH : SurfaceBasisLabel.unit ∉
      Finset.univ.val.map (![.hyperplane] : Fin 1 → SurfaceBasisLabel .plane) := by decide
  have huP : SurfaceBasisLabel.unit ∉
      Finset.univ.val.map (![.point] : Fin 1 → SurfaceBasisLabel .plane) := by decide
  rw [plane_paper_zero_point_two_hyperplanes]
  rw [remainderVertex_plane_primary_canonical _ _ _ _ _ _ huH,
    remainderVertex_plane_primary_canonical _ _ _ _ _ _ huP]
  decide +kernel

-- The equal-point cancellation includes a nonzero negative line tail.
example : remainderVertex .plane (primary 1) (planeCoefficientVertex (primary 1)) 4
    2 (Fin 2) (by norm_num [StableArity]) (Pi.single 0 1) inferInstance ![1]
      ![.point, .point] = -4 := by
  have hu : SurfaceBasisLabel.unit ∉ Finset.univ.val.map
      (Function.update (![.point, .point] : Fin 2 → SurfaceBasisLabel .plane)
        0 .hyperplane) := by decide
  rw [remainderVertex_onePsi_plane_line]
  simp only [Matrix.cons_val_zero]
  rw [remainderVertex_plane_primary_canonical _ _ _ _ _ _ hu]
  decide +kernel

-- Both psi locations carry the same tail before their opposite raw signs cancel.
example (v : Variable .plane) (n : ℕ) :
    remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single 0 1) inferInstance ![1] ![.point, .point] -
    remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single 1 1) inferInstance ![1] ![.point, .point] = 0 := by
  rw [remainderVertex_plane_two_points_onePsi_line_swap, sub_self]

-- Zero points cannot meet the HHP dimension guard, regardless of the requested variable.
example (v : Variable .plane) :
    planeRemainderPointCoefficient 0 ![1] ![.hyperplane, .hyperplane, .point] v = 0 := by
  rw [planeRemainderPointCoefficient_two_hyperplanes_point_canonical,
    if_neg (by omega)]

-- At degree zero the single-point HHP hyperplane-descendant coefficient survives.
example : planeRemainderPointCoefficient 1 ![1] ![.hyperplane, .hyperplane, .point]
    (hyperplane 0) = 12 := by
  rw [planeRemainderPointCoefficient_two_hyperplanes_point_canonical]
  decide +kernel

-- PPP's positive-degree formula must not be extrapolated across d=0.
example : planeRemainderPointCoefficient 0 ![1] ![.point, .point, .point]
    (hyperplane 0) = 0 := by
  rw [planeRemainderPointCoefficient_three_points_canonical]
  decide +kernel

-- Full degree-five equation, with quartic canonical columns and thirteen added points.
example :
    let p := normalizedGenusTwoTerms .plane 13 ![5] 0
      (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .point] 13)
    let f := fun q : SurfaceQuery .plane ↦ RationalTerms.coefficient p {Sum.inr q}
    (f (SurfaceQuery.points .plane 2 ![4] 13),
      f (SurfaceFirstDescendant.query 2 ![4] .hyperplane 12),
      f (SurfaceFirstDescendant.query 2 ![4] .point 11)) = (-432, -312, 1872) := by
  have h := normalized_plane_two_hyperplanes_point_row 4
  norm_num only at h
  exact h

-- A different requested point multiplicity has zero coefficient even at the same degree.
example : RationalTerms.coefficient (normalizedGenusTwoTerms .plane 7 ![3] 0
    (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .point] 7))
    {Sum.inr (SurfaceFirstDescendant.query 2 ![2] .hyperplane 7)} = 0 := by
  rw [normalized_plane_two_hyperplanes_point_canonical 2 _ rfl]
  decide +kernel

-- A dimension-compatible higher ancestor is absent from the whole HHP degree-d block.
example (d : ℕ) :
    let v : Variable .plane := .inl (SurfaceAncestorKey.ofLabels 2 (Fin 1)
      (by norm_num [StableArity]) ![d] ![3 * d + 1] ![.hyperplane])
    RationalTerms.coefficient (normalizedGenusTwoTerms .plane (3 * d + 1) ![d + 1] 0
      (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .point] (3 * d + 1))) {v} = 0 := by
  dsimp only
  rw [normalized_plane_two_hyperplanes_point_canonical d _ rfl]
  simp only [reduceCtorEq, ite_false, mul_zero, add_zero]

-- The extracted matrix has the independently held degree-two coefficient rows.
example : planeShiftedMatrix 2 = !![-216, -42, 252; -36, -60, 144; 0, -18, 36] := by
  have h := planeShiftedMatrix_eq 2 (by decide)
  norm_num only at h
  exact h

-- This determinant belongs to the full coefficient matrix, not an unattached symbolic table.
example : (planeShiftedMatrix 4).det = 31104 := by
  rw [planeShiftedMatrix_det 4 (by decide)]
  norm_num

-- Exact executable block solve; these are arbitrary linear data, not invariant values.
example : planeShiftedSolve 2 ![456, 276, 72] = ![1, 2, 3] := by decide +kernel

-- The reusable solver certifies any supplied right-hand side at positive degree.
example (b : Fin 3 → ℚ) :
    (planeShiftedMatrix 4).mulVec (planeShiftedSolve 4 b) = b :=
  planeShiftedSolve_spec 4 (by decide) b

-- An ancestor variable surviving in any row must have strictly smaller degree.
example (d : ℕ) (hd : 0 < d) (i : Fin 3) (q : SurfaceAncestorKey .plane)
    (hc : RationalTerms.coefficient (planeShiftedTerms d i) {Sum.inl q} ≠ 0) :
    q.beta 0 < d := by
  exact planeShiftedTerms_lower d hd i (.inl q)
    (fun _ ↦ by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hc

end AxiomaticGWTest.Surfaces.PlaneShiftedSystem

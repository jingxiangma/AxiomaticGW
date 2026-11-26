/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.GenusTwoPointTails

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.PrimaryPointPullback
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwo

-- A dimension-selected placement is zero when fewer than k points are supplied,
-- even when f at the truncated index is nonzero.
example (f : ℕ → ℚ) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal 1, (Nat.choose 1 ij.1 : ℚ) *
      (f ij.1 * if ij.2 = 2 then 1 else 0)) = 0 := by
  rw [SurfacePointPullback.sum_binomial_of_right_support f (fun j ↦ if j = 2 then 1 else 0)
    1 2 (fun j hj ↦ if_neg hj)]
  norm_num

-- The closed line formula covers arbitrary point counts, not an interpolated table.
example (f : ℕ → ℚ) (n : ℕ) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane)
        ![1] ij.2 (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → _))) =
      (n.choose 2 : ℚ) * f (n - 2) := by
  rw [SurfaceGenusZero.sum_binomial_primary_plane_one]
  rfl

example (f : ℕ → ℚ) (n : ℕ) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane)
        ![1] ij.2 (![.hyperplane, .point, .point] : Fin 3 → _))) = f n := by
  rw [SurfaceGenusZero.sum_binomial_primary_plane_one]
  change (n.choose 0 : ℚ) * f (n - 0) = _
  rw [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]

-- Zero, one and two additional points supply the required two-point total.
example : SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane)
    ![1] 0 (![.hyperplane, .point, .point] : Fin 3 → _) = 1 := by
  rw [SurfaceGenusZero.primaryScalar_plane_one]
  decide +kernel

example : SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane)
    ![1] 1 (![.hyperplane, .hyperplane, .point] : Fin 3 → _) = 1 := by
  rw [SurfaceGenusZero.primaryScalar_plane_one]
  decide +kernel

example : SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane)
    ![1] 2 (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → _) = 1 := by
  rw [SurfaceGenusZero.primaryScalar_plane_one]
  decide +kernel

-- A unit still kills a dimension-compatible positive-class primary component.
example : SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane)
    ![1] 2 (![.unit, .hyperplane, .point] : Fin 3 → _) = 0 := by
  rw [SurfaceGenusZero.primaryScalar_plane_one]
  decide +kernel

example (f : ℕ → ℚ) (n : ℕ) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane)
        ![1] ij.2 (![.point, .point, .point] : Fin 3 → _))) = 0 := by
  rw [SurfaceGenusZero.sum_binomial_primary_plane_one]
  rfl

-- The actual coefficient consumer retains the negative exceptional divisor product.
example (v : Variable .blowupTwo) : primaryPointVertex .blowupTwo v 0 0 (Fin 3)
    (by norm_num [StableArity]) 0 inferInstance ![1,0,0]
      ![.exceptional 0, .exceptional 0, .exceptional 0] = -1 := by
  change SurfaceGenusZero.primaryScalar .blowupTwo (SurfaceGenusZero.pointValue .blowupTwo)
    ![1,0,0] 0 (![.exceptional 0, .exceptional 0, .exceptional 0] : Fin 3 → _) = -1
  decide +kernel

-- The other exceptional generator has the same energy but a different intersection.
example (v : Variable .blowupTwo) : primaryPointVertex .blowupTwo v 0 0 (Fin 3)
    (by norm_num [StableArity]) 0 inferInstance ![0,1,0]
      ![.exceptional 0, .exceptional 0, .exceptional 0] = 0 := by
  change SurfaceGenusZero.primaryScalar .blowupTwo (SurfaceGenusZero.pointValue .blowupTwo)
    ![0,1,0] 0 (![.exceptional 0, .exceptional 0, .exceptional 0] : Fin 3 → _) = 0
  decide +kernel

example (v : Variable .plane) : primaryPointVertex .plane v 0 0 (Fin 3)
    (by norm_num [StableArity]) 0 inferInstance 0 ![.unit, .unit, .point] = 1 := by
  change SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane)
    0 0 (![.unit, .unit, .point] : Fin 3 → _) = 1
  decide +kernel

example (X : SurfaceTarget) (v : Variable X) (n : ℕ) :
    SurfacePointPullback.vertex X (coefficientVertex X v) (n + 1) 0 (Fin 3)
      (by norm_num [StableArity]) 0 inferInstance 0 (fun _ ↦ .point) = 0 :=
  vertex_primary_genusZero_zero_of_pos v (n + 1) (Nat.succ_pos _) _ _ _ _

-- Primary main components consume no positive plane remainder for any n.
example (v : Variable .plane) (n : ℕ) (a : Fin 2 → SurfaceBasisLabel .plane) :
    remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 2)
      (by norm_num [StableArity]) 0 inferInstance ![1] a = 0 := by
  rw [remainderVertex_plane_primary, if_neg (by decide)]

-- A primary unit vanishes at every class, not just a sampled plane degree.
example (X : SurfaceTarget) (v : Variable X) (n : ℕ) (beta : X.Curve)
    (a : Fin 2 → SurfaceBasisLabel X) :
    SurfacePointPullback.vertex X (coefficientVertex X v) n 2 (Fin 2)
      (by norm_num [StableArity]) 0 inferInstance beta (Function.update a 0 .unit) = 0 :=
  vertex_primary_genusTwo_unit_zero v n _ _ beta a 0

private def cubicPrimary : Variable .plane := .inr (SurfaceQuery.points .plane 2 ![3] 10)

-- Nine points give -choose(9,2) times the degree-three primary divisor factor.
example : remainderVertex .plane cubicPrimary (planeCoefficientVertex cubicPrimary)
    9 2 (Fin 4) (by norm_num [StableArity]) (Pi.single 0 1) inferInstance ![1]
      ![.hyperplane, .point, .point, .point] = -108 := by
  rw [remainderVertex_onePsi_plane_line]
  change -(Nat.choose 9 2 : ℚ) * remainderVertex .plane cubicPrimary
    (planeCoefficientVertex cubicPrimary) 7 2 (Fin 4) _ 0 inferInstance 0
      (Function.update ![.hyperplane, .point, .point, .point] 0 .hyperplane) = -108
  rw [remainderVertex_plane_primary]
  decide +kernel

-- A point psi insertion has the distinct linear coefficient -n.
example : remainderVertex .plane cubicPrimary (planeCoefficientVertex cubicPrimary)
    8 2 (Fin 4) (by norm_num [StableArity]) (Pi.single 0 1) inferInstance ![1]
      ![.point, .point, .point, .point] = -24 := by
  rw [remainderVertex_onePsi_plane_line]
  change -(8 : ℚ) * remainderVertex .plane cubicPrimary
    (planeCoefficientVertex cubicPrimary) 7 2 (Fin 4) _ 0 inferInstance 0
      (Function.update ![.point, .point, .point, .point] 0 .hyperplane) = -24
  rw [remainderVertex_plane_primary]
  decide +kernel

example (v : Variable .plane) (n : ℕ) :
    remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single 0 1) inferInstance ![1] ![.unit, .point] = 0 := by
  rw [remainderVertex_onePsi_plane_line]
  rfl

-- The HH tail cannot contribute without a second point, even with arbitrary main values.
example (f : ℕ → ℚ) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal 0, (Nat.choose 0 ij.1 : ℚ) *
      (f ij.1 * SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane)
        ![1] ij.2 (Option.elim · .hyperplane
          (fun t : Bool ↦ if t then .point else .hyperplane)))) = 0 := by
  rw [SurfaceGenusZero.sum_binomial_primary_plane_tail]
  exact zero_mul _

end AxiomaticGWTest.Surfaces.PrimaryPointPullback

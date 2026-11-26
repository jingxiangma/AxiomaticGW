/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.PlaneGenusTwoFirstCoefficients

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.PlaneGenusTwoFirstCoefficients
open AxiomaticGW SurfaceGenusTwo BelorousskiPandharipande SurfacePolynomialReduction

-- The guard sees the cotangent power, including at zero curve class.
example (d : ℕ) : requestsPositivePsi (Sum.inr (planeCanonicalQueries d 1)) = true := rfl
example (d : ℕ) : requestsPositivePsi (Sum.inr (planeCanonicalQueries d 2)) = true := rfl
example (d : ℕ) : requestsPositivePsi (Sum.inr (planeCanonicalQueries d 0)) = false :=
  requestsPositivePsi_points _ _

-- Primary requests retain the original evaluator, including its signed corrections.
example (beta : SurfaceTarget.plane.Curve) (r n g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (d : S → ℕ) (l : DecidableEq S)
    (delta : SurfaceTarget.plane.Curve) (a : S → SurfaceBasisLabel .plane) :
    planeLowPsiCoefficientVertex (Sum.inr (SurfaceQuery.points .plane 2 beta r))
      n g S h d l delta a =
      planeCachedRemainderVertex (Sum.inr (SurfaceQuery.points .plane 2 beta r))
        n g S h d l delta a := by
  simp only [planeLowPsiCoefficientVertex, requestsPositivePsi_points, Bool.false_eq_true,
    and_false, ite_false]

-- Higher psi degrees fall back as well; the shortcut asserts no unsupported formula.
example (v : Variable .plane) (n : ℕ) (S : Type) [Fintype S] (h : StableArity 2 S)
    (d : S → ℕ) (hd : 1 < ∑ s, d s) (l : DecidableEq S)
    (delta : SurfaceTarget.plane.Curve) (a : S → SurfaceBasisLabel .plane) :
    planeLowPsiCoefficientVertex v n 2 S h d l delta a =
      planeCachedRemainderVertex v n 2 S h d l delta a := by
  rw [planeLowPsiCoefficientVertex, if_neg (fun hc ↦ (not_le_of_gt hd) hc.2.1)]

-- The vanishing is uniform in all original labels, point counts and positive remainders.
example (b n : ℕ) (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S)
    (d : S → ℕ) (hd : ∑ s, d s ≤ 1) (delta : SurfaceTarget.plane.Curve)
    (he : delta ≠ 0) (a : S → SurfaceBasisLabel .plane) :
    remainderVertex .plane (Sum.inr (planeCanonicalQueries b 1))
      (planeCoefficientVertex (Sum.inr (planeCanonicalQueries b 1)))
        n 2 S h d inferInstance delta a = 0 := by
  rw [remainderVertex_plane_lowPsi_of_not_points _
    (not_points_of_requestsPositivePsi _ rfl) n S h d hd delta a, if_neg he]

attribute [local cbv_eval] Matrix.cons_val_zero Matrix.cons_val_succ
attribute [local cbv_eval] Matrix.cons_val_zero' Matrix.cons_val_succ'

-- This original nonzero quartic coefficient exceeded the earlier CBV budget.
set_option maxHeartbeats 1000000 in
-- Kernel replay of the complete contribution using the proved low-psi identity.
set_option cbv.maxSteps 1000000 in
example : planeEarlierCoefficientPart 4 0 0 1 1 0 = 21826000 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  cbv

-- A requested class beyond the source is rejected before natural subtraction.
example : planeEarlierCoefficientPart 1 0 3 1 1 0 = 0 := by
  rw [← planeEarlierCoefficientPartFast_eq]
  cbv

-- A primary request still has its actual nonzero terminal coefficient.
example : planeLowPsiCoefficientVertex (Sum.inr (planeCanonicalQueries 0 0)) 0
    2 (Fin 1) (by norm_num [StableArity]) 0 inferInstance 0 ![.point] = 1 := by
  cbv

end AxiomaticGWTest.Surfaces.PlaneGenusTwoFirstCoefficients

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneCanonicalComponents
public import AxiomaticGW.Surfaces.PlaneSourceDegree

/-!
# Mixed-insertion rows in the shifted plane equations

The first BP diagram has a rational node at its middle marking. The
contractions below preserve that incidence before applying classical
products and the canonical genus-two component formulas.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction GluingExpression

/-- The inner edge of the first BP diagram retains its actual middle node. -/
theorem remainderContraction_plane_inner_join (v : Variable .plane)
    (main : ℕ → SurfaceCotangentVertexValues .plane ℚ) (n : ℕ) (k : Fin 1 → ℕ)
    (delta : SurfaceTarget.plane.Curve) (a b : SurfaceBasisLabel .plane) :
    remainderContraction .plane v main
      (GetzlerGraphs.join (m := 0) (n := 2) 0 1
        (fundamental 2 (Fin 1) (by norm_num [StableArity]))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (by exact (k, (0 : Fin 3 → ℕ)))
      (by exact ((inferInstance : DecidableEq (Fin 1)),
        (inferInstance : DecidableEq (Fin 3)))) delta n ![a, b] =
      ∑ split ∈ SurfaceTarget.plane.splittings delta, ∑ t : SurfaceBasisLabel .plane,
        t.inverseWeight * ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          (n.choose ij.1 : ℚ) *
            (main ij.1 2 (Fin 1) (by norm_num [StableArity]) k inferInstance split.1 ![t] *
              SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane)
                split.2 ij.2 (![a, t.dual, b] : Fin 3 → _)) := by
  simp only [GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction]
  have hl (t : SurfaceBasisLabel .plane) :
      (Option.elim · t (((![a, b] : Fin 2 → _) ∘
        (finSumFinEquiv : Fin 0 ⊕ Fin 2 ≃ Fin 2)) ∘ Sum.inl)) ∘
        finSuccEquiv' 0 = ![t] := by
    funext i
    fin_cases i
    rfl
  have hr (t : SurfaceBasisLabel .plane) :
      (Option.elim · t (((![a, b] : Fin 2 → _) ∘
        (finSumFinEquiv : Fin 0 ⊕ Fin 2 ≃ Fin 2)) ∘ Sum.inr)) ∘
        finSuccEquiv' 1 = ![a, t, b] := by
    funext i
    fin_cases i <;> rfl
  simp only [hl, hr, primaryPointVertex, and_self, ite_true]

private theorem sum_classical (f : ℕ → ℚ) (n : ℕ)
    (a : Fin 3 → SurfaceBasisLabel .plane) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * SurfaceGenusZero.primaryScalar .plane
        (SurfaceGenusZero.pointValue .plane) 0 ij.2 a)) =
      f n * SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane) 0 0 a := by
  rw [SurfacePointPullback.sum_binomial_of_right_support f
    (fun j ↦ SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane) 0 j a)
    n 0 (by
    intro j hj
    have hcard : j + Fintype.card (Fin 3) ≠ 3 := by
      simp only [Fintype.card_fin]
      omega
    simp only [SurfaceGenusZero.primaryScalar, ne_eq, not_true_eq_false, false_and,
      ite_true, if_neg hcard, ite_self])]
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul]

/-- All added points lie off the classical inner rational component. -/
theorem remainderContraction_plane_inner_zero (v : Variable .plane)
    (main : ℕ → SurfaceCotangentVertexValues .plane ℚ) (n : ℕ) (k : Fin 1 → ℕ)
    (a b : SurfaceBasisLabel .plane) :
    remainderContraction .plane v main
      (GetzlerGraphs.join (m := 0) (n := 2) 0 1
        (fundamental 2 (Fin 1) (by norm_num [StableArity]))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (by exact (k, (0 : Fin 3 → ℕ)))
      (by exact ((inferInstance : DecidableEq (Fin 1)),
        (inferInstance : DecidableEq (Fin 3)))) 0 n ![a, b] =
      ∑ t : SurfaceBasisLabel .plane, t.inverseWeight *
        (main n 2 (Fin 1) (by norm_num [StableArity]) k inferInstance 0 ![t] *
          SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane)
            0 0 (![a, t.dual, b] : Fin 3 → _)) := by
  rw [remainderContraction_plane_inner_join,
    (SurfaceTarget.plane.splittings_eq 0).trans SurfaceTarget.plane.effective.splittings_zero]
  simp only [Finset.sum_singleton]
  have hs (t : SurfaceBasisLabel .plane) := sum_classical
    (fun m ↦ main m 2 (Fin 1) (by norm_num [StableArity]) k inferInstance 0 ![t])
      n ![a, t.dual, b]
  simp only [hs]

/-- The classical unit at the inner rational component preserves its other
state on the main component, with the inverse metric included. -/
theorem remainderContraction_plane_inner_unit_zero (v : Variable .plane)
    (main : ℕ → SurfaceCotangentVertexValues .plane ℚ) (n : ℕ) (k : Fin 1 → ℕ)
    (a : SurfaceBasisLabel .plane) :
    remainderContraction .plane v main
      (GetzlerGraphs.join (m := 0) (n := 2) 0 1
        (fundamental 2 (Fin 1) (by norm_num [StableArity]))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (by exact (k, (0 : Fin 3 → ℕ)))
      (by exact ((inferInstance : DecidableEq (Fin 1)),
        (inferInstance : DecidableEq (Fin 3)))) 0 n ![a, .unit] =
      main n 2 (Fin 1) (by norm_num [StableArity]) k inferInstance 0 ![a] := by
  have hs (t : SurfaceBasisLabel .plane) :
      SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane)
        0 0 (![a, t.dual, .unit] : Fin 3 → _) = if t = a then 1 else 0 := by
    cases a <;> cases t
    all_goals first | exact Fin.elim0 (show Fin 0 from ‹Fin 0›) | decide +kernel
  have hw : a.inverseWeight = 1 := by
    cases a with
    | exceptional i => exact Fin.elim0 i
    | unit | hyperplane | point => rfl
  rw [remainderContraction_plane_inner_zero]
  simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, hw, one_mul]

/-- Two classical hyperplanes place their product, the point, on the main node. -/
theorem remainderContraction_plane_inner_two_hyperplanes_zero (v : Variable .plane)
    (main : ℕ → SurfaceCotangentVertexValues .plane ℚ) (n : ℕ) (k : Fin 1 → ℕ) :
    remainderContraction .plane v main
      (GetzlerGraphs.join (m := 0) (n := 2) 0 1
        (fundamental 2 (Fin 1) (by norm_num [StableArity]))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (by exact (k, (0 : Fin 3 → ℕ)))
      (by exact ((inferInstance : DecidableEq (Fin 1)),
        (inferInstance : DecidableEq (Fin 3)))) 0 n ![.hyperplane, .hyperplane] =
      main n 2 (Fin 1) (by norm_num [StableArity]) k inferInstance 0 ![.point] := by
  have hs (t : SurfaceBasisLabel .plane) :
      SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane)
        0 0 (![.hyperplane, t.dual, .hyperplane] : Fin 3 → _) =
        if t = .point then 1 else 0 := by
    cases t with
    | exceptional i => exact Fin.elim0 i
    | unit | hyperplane | point => decide +kernel
  rw [remainderContraction_plane_inner_zero]
  simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, SurfaceBasisLabel.inverseWeight, one_mul]

/-- A point and a hyperplane exceed the classical surface dimension. -/
theorem remainderContraction_plane_inner_point_hyperplane_zero (v : Variable .plane)
    (main : ℕ → SurfaceCotangentVertexValues .plane ℚ) (n : ℕ) (k : Fin 1 → ℕ) :
    remainderContraction .plane v main
      (GetzlerGraphs.join (m := 0) (n := 2) 0 1
        (fundamental 2 (Fin 1) (by norm_num [StableArity]))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (by exact (k, (0 : Fin 3 → ℕ)))
      (by exact ((inferInstance : DecidableEq (Fin 1)),
        (inferInstance : DecidableEq (Fin 3)))) 0 n ![.point, .hyperplane] = 0 := by
  have hs (t : SurfaceBasisLabel .plane) :
      SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane)
        0 0 (![.point, t.dual, .hyperplane] : Fin 3 → _) = 0 := by
    cases t with
    | exceptional i => exact Fin.elim0 i
    | unit | hyperplane | point => decide +kernel
  rw [remainderContraction_plane_inner_zero]
  simp only [hs, mul_zero, Finset.sum_const_zero]

end AxiomaticGW.SurfaceGenusTwo

namespace AxiomaticGW.SurfaceGenusZero

/-- Swap the first two external states without moving the fourth, nodal state. -/
theorem primaryScalar_plane_four_swap_left (delta : SurfaceTarget.plane.Curve)
    (n : ℕ) (a b c t : SurfaceBasisLabel .plane) :
    primaryScalar .plane (pointValue .plane) delta n (![a, b, c, t] : Fin 4 → _) =
      primaryScalar .plane (pointValue .plane) delta n (![b, a, c, t] : Fin 4 → _) := by
  simp only [primaryScalar, Fin.sum_univ_four, Fin.prod_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    Matrix.cons_val_succ]
  rw [add_comm a.codimension b.codimension, mul_comm a.value b.value,
    mul_comm (a.primaryFactor delta) (b.primaryFactor delta)]

/-- Swap the last two external states while retaining the fourth, nodal state. -/
theorem primaryScalar_plane_four_swap_right (delta : SurfaceTarget.plane.Curve)
    (n : ℕ) (a b c t : SurfaceBasisLabel .plane) :
    primaryScalar .plane (pointValue .plane) delta n (![a, b, c, t] : Fin 4 → _) =
      primaryScalar .plane (pointValue .plane) delta n (![a, c, b, t] : Fin 4 → _) := by
  simp only [primaryScalar, Fin.sum_univ_four, Fin.prod_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    Matrix.cons_val_succ]
  rw [add_right_comm a.codimension b.codimension c.codimension,
    mul_right_comm a.value b.value c.value,
    mul_right_comm (a.primaryFactor delta) (b.primaryFactor delta) (c.primaryFactor delta)]

end AxiomaticGW.SurfaceGenusZero

namespace AxiomaticGW.BelorousskiPandharipande
open SurfacePolynomialReduction SurfaceGenusTwo GluingExpression

/-- The second diagram is symmetric in its first two external states. -/
theorem plane_paper_one_swap_left (v : Variable .plane) (n : ℕ)
    (delta : SurfaceTarget.plane.Curve) (a b c : SurfaceBasisLabel .plane) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm 1) delta n ![a, b, c] =
      remainderPointCoefficient .plane v (planeCoefficientVertex v)
        (paperCotangentTerm 1) delta n ![b, a, c] := by
  rw [plane_paper_one_sum, plane_paper_one_sum]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    SurfaceGenusZero.primaryScalar_plane_four_swap_left (a := a) (b := b)]

/-- The second diagram is symmetric in its last two external states. -/
theorem plane_paper_one_swap_right (v : Variable .plane) (n : ℕ)
    (delta : SurfaceTarget.plane.Curve) (a b c : SurfaceBasisLabel .plane) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm 1) delta n ![a, b, c] =
      remainderPointCoefficient .plane v (planeCoefficientVertex v)
        (paperCotangentTerm 1) delta n ![a, c, b] := by
  rw [plane_paper_one_sum, plane_paper_one_sum]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    SurfaceGenusZero.primaryScalar_plane_four_swap_right (a := a) (b := b) (c := c)]

/-- In the first HPP diagram the outer line leaves two classical hyperplanes. -/
theorem plane_paper_zero_hyperplane_two_points (v : Variable .plane) (n : ℕ) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm 0) ![1] n ![.hyperplane, .point, .point] =
      remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 1)
        (by norm_num [StableArity]) 0 inferInstance 0 ![.point] := by
  rw [plane_paper_zero_pair]
  erw [remainderContraction_plane_two_points_join,
    remainderContraction_plane_inner_two_hyperplanes_zero]
  rw [show (![0] : Fin 1 → ℕ) = 0 from by decide +kernel]

/-- In the other HPP placement, only the classical point/unit inner pair survives. -/
theorem plane_paper_zero_point_hyperplane_point (v : Variable .plane) (n : ℕ) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm 0) ![1] n ![.point, .hyperplane, .point] =
      remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 1)
        (by norm_num [StableArity]) 0 inferInstance 0 ![.point] := by
  rw [plane_paper_zero_pair]
  erw [remainderContraction_plane_hyperplane_point_join,
    remainderContraction_plane_inner_unit_zero,
    remainderContraction_plane_inner_point_hyperplane_zero]
  simp only [mul_zero, add_zero]
  rw [show (![0] : Fin 1 → ℕ) = 0 from by decide +kernel]

/-- Each genus-two diagram is symmetric in the two rational external slots. -/
theorem plane_paper_first_four_swap_right (v : Variable .plane) (n : ℕ)
    (delta : SurfaceTarget.plane.Curve) (i : Fin 4) (a b c : SurfaceBasisLabel .plane) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm (Fin.castAdd 16 i)) delta n ![a, b, c] =
      remainderPointCoefficient .plane v (planeCoefficientVertex v)
        (paperCotangentTerm (Fin.castAdd 16 i)) delta n ![a, c, b] := by
  fin_cases i
  · change remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm 0) delta n ![a, b, c] =
      remainderPointCoefficient .plane v (planeCoefficientVertex v)
        (paperCotangentTerm 0) delta n ![a, c, b]
    rw [plane_paper_zero_pair, plane_paper_zero_pair]
    exact remainderContraction_plane_pair_swap v _ n _ _ _ delta a b c
  · exact plane_paper_one_swap_right v n delta a b c
  · change remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm (if (0 : Fin 2) = 0 then 2 else 3)) delta n ![a, b, c] =
      remainderPointCoefficient .plane v (planeCoefficientVertex v)
        (paperCotangentTerm (if (0 : Fin 2) = 0 then 2 else 3)) delta n ![a, c, b]
    rw [plane_paper_onePsi_pair, plane_paper_onePsi_pair]
    exact remainderContraction_plane_pair_swap v _ n _ _ _ delta a b c
  · change remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm (if (1 : Fin 2) = 0 then 2 else 3)) delta n ![a, b, c] =
      remainderPointCoefficient .plane v (planeCoefficientVertex v)
        (paperCotangentTerm (if (1 : Fin 2) = 0 then 2 else 3)) delta n ![a, c, b]
    rw [plane_paper_onePsi_pair, plane_paper_onePsi_pair]
    exact remainderContraction_plane_pair_swap v _ n _ _ _ delta a b c

/-- All four actual genus-two diagrams and all six marking occurrences in
HPP reduce to these component coefficients, with their raw signs retained. -/
theorem planeRemainderPointCoefficient_hyperplane_two_points (v : Variable .plane) (n : ℕ) :
    let main := remainderVertex .plane v (planeCoefficientVertex v)
    let R := fun m s a ↦ main m 2 (Fin 2) (by norm_num [StableArity])
      (Pi.single s 1) inferInstance 0 a
    planeRemainderPointCoefficient n ![1] ![.hyperplane, .point, .point] v =
      -12 * main n 2 (Fin 1) (by norm_num [StableArity]) 0 inferInstance 0 ![.point] +
      12 * main n 2 (Fin 1) (by norm_num [StableArity])
        (Pi.single 0 1) inferInstance 0 ![.hyperplane] +
      6 * (R n 0 ![.hyperplane, .hyperplane] - R n 1 ![.hyperplane, .hyperplane]) +
      12 * (R n 0 ![.point, .unit] - R n 1 ![.point, .unit]) +
      12 * (n : ℚ) * (R (n - 1) 0 ![.point, .hyperplane] -
        R (n - 1) 1 ![.point, .hyperplane]) := by
  let f := fun i a ↦ remainderPointCoefficient .plane v (planeCoefficientVertex v)
    (paperCotangentTerm i) ![1] n a
  have hs (i : Fin 4) : f (Fin.castAdd 16 i) ![.point, .point, .hyperplane] =
      f (Fin.castAdd 16 i) ![.point, .hyperplane, .point] :=
    plane_paper_first_four_swap_right v n ![1] i _ _ _
  have hs0 : f 0 ![.point, .point, .hyperplane] = f 0 ![.point, .hyperplane, .point] := hs 0
  have hs1 : f 1 ![.point, .point, .hyperplane] = f 1 ![.point, .hyperplane, .point] := hs 1
  have hs2 : f 2 ![.point, .point, .hyperplane] = f 2 ![.point, .hyperplane, .point] := hs 2
  have hs3 : f 3 ![.point, .point, .hyperplane] = f 3 ![.point, .hyperplane, .point] := hs 3
  have h1 : f 1 ![.point, .hyperplane, .point] = f 1 ![.hyperplane, .point, .point] :=
    plane_paper_one_swap_left v n ![1] _ _ _
  have h2 := plane_paper_onePsi_hyperplane_point v n (0 : Fin 2) .point
  have h3 := plane_paper_onePsi_hyperplane_point v n (1 : Fin 2) .point
  simp only [ite_true] at h2
  simp only [if_neg (by decide : (1 : Fin 2) ≠ 0)] at h3
  dsimp only
  unfold planeRemainderPointCoefficient
  simp only [sum_plane_remainder_orbit, Fin.sum_univ_four]
  change (-2 : ℚ) *
      (f 0 ![.hyperplane, .point, .point] + f 0 ![.hyperplane, .point, .point] +
        f 0 ![.point, .hyperplane, .point] + f 0 ![.point, .hyperplane, .point] +
        f 0 ![.point, .point, .hyperplane] + f 0 ![.point, .point, .hyperplane]) +
    2 * (f 1 ![.hyperplane, .point, .point] + f 1 ![.hyperplane, .point, .point] +
        f 1 ![.point, .hyperplane, .point] + f 1 ![.point, .hyperplane, .point] +
        f 1 ![.point, .point, .hyperplane] + f 1 ![.point, .point, .hyperplane]) +
    3 * (f 2 ![.hyperplane, .point, .point] + f 2 ![.hyperplane, .point, .point] +
        f 2 ![.point, .hyperplane, .point] + f 2 ![.point, .hyperplane, .point] +
        f 2 ![.point, .point, .hyperplane] + f 2 ![.point, .point, .hyperplane]) +
    (-3) * (f 3 ![.hyperplane, .point, .point] + f 3 ![.hyperplane, .point, .point] +
        f 3 ![.point, .hyperplane, .point] + f 3 ![.point, .hyperplane, .point] +
        f 3 ![.point, .point, .hyperplane] + f 3 ![.point, .point, .hyperplane]) = _
  rw [hs0, hs1, hs2, hs3, h1]
  dsimp only [f]
  rw [plane_paper_zero_hyperplane_two_points, plane_paper_zero_point_hyperplane_point,
    plane_paper_one_hyperplane_two_points, plane_paper_two_two_points,
    plane_paper_three_two_points, h2, h3]
  rw [show (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 from by decide +kernel,
    show (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 from by decide +kernel,
    show (![1] : Fin 1 → ℕ) = Pi.single 0 1 from by decide +kernel]
  ring

/-- The complete HPP coefficient has only the three canonical requests at
a one-degree remainder. The formula includes zero degree and zero added points. -/
theorem planeRemainderPointCoefficient_hyperplane_two_points_canonical
    (v : Variable .plane) (n : ℕ) :
    let d := SurfaceGenusZero.variableCurve v 0
    planeRemainderPointCoefficient n ![1] ![.hyperplane, .point, .point] v =
      if n = 3 * d then
        -36 * (if Sum.inr (SurfaceQuery.points .plane 2 ![d] (n + 1)) = v then 1 else 0) +
        (12 - 12 * (n : ℚ)) *
          (if Sum.inr (SurfaceFirstDescendant.query 2 ![d] .hyperplane n) = v then 1 else 0) +
        12 * (n : ℚ) * (d : ℚ) *
          (if Sum.inr (SurfaceFirstDescendant.query 2 ![d] .point (n - 1)) = v then 1 else 0)
      else 0 := by
  let d := SurfaceGenusZero.variableCurve v 0
  have hp : Finset.univ.val.map (![.point] : Fin 1 → SurfaceBasisLabel .plane) =
      {.point} := by decide +kernel
  have hu : SurfaceBasisLabel.unit ∉
      Finset.univ.val.map (![.point] : Fin 1 → SurfaceBasisLabel .plane) := by
    rw [hp]
    decide
  dsimp only
  rw [planeRemainderPointCoefficient_hyperplane_two_points]
  simp only [remainderVertex_plane_two_hyperplanes_onePsi, sub_self, mul_zero, add_zero]
  rw [remainderVertex_plane_primary_canonical _ _ _ _ _ _ hu,
    remainderVertex_plane_single_hyperplane_onePsi,
    remainderVertex_plane_pair_primary_unit _ _ _ (by decide),
    remainderVertex_plane_pair_unit_onePsi _ _ _ (by decide),
    remainderVertex_plane_point_hyperplane, remainderVertex_plane_point_hyperplane]
  simp only [hp, Multiset.count_singleton, reduceCtorEq, ite_false, ite_true,
    pow_zero, one_mul, mul_one, if_neg (by decide : (1 : Fin 2) ≠ 0)]
  have hdim : n + 1 = 3 * SurfaceGenusZero.variableCurve v 0 + 1 ↔
      n = 3 * SurfaceGenusZero.variableCurve v 0 := by omega
  simp only [hdim]
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, mul_zero, zero_mul, sub_zero, add_zero]
    split_ifs <;> ring
  · have hn' : n - 1 + 1 = n := by omega
    simp only [hn']
    split_ifs <;> ring

/-- The full normalized HPP equation has exactly this coefficient on any
requested variable of degree d. It is an identity of the original equation,
including all cotangent pullback corrections, rather than a selected submatrix. -/
theorem normalized_plane_hyperplane_two_points_canonical (d : ℕ) (v : Variable .plane)
    (hv : SurfaceGenusZero.variableCurve v = ![d]) :
    RationalTerms.coefficient (normalizedGenusTwoTerms .plane (3 * d) ![d + 1] 0
      (SurfaceGenusZero.pointLabels ![.hyperplane, .point, .point] (3 * d))) {v} =
      -36 * (if Sum.inr (SurfaceQuery.points .plane 2 ![d] (3 * d + 1)) = v then 1 else 0) +
      (12 - 36 * (d : ℚ)) *
        (if Sum.inr (SurfaceFirstDescendant.query 2 ![d] .hyperplane (3 * d)) = v
          then 1 else 0) +
      36 * (d : ℚ) ^ 2 *
        (if Sum.inr (SurfaceFirstDescendant.query 2 ![d] .point (3 * d - 1)) = v
          then 1 else 0) := by
  have hc : SurfaceGenusZero.variableCurve v + ![1] =
      (![d + 1] : SurfaceTarget.plane.Curve) := by
    rw [hv]
    funext i
    fin_cases i
    rfl
  rw [← pointCoefficient_eq_full, ← hc, ← planeRemainderPointCoefficient_eq,
    planeRemainderPointCoefficient_hyperplane_two_points_canonical]
  simp only [hv, Matrix.cons_val_zero, ite_true, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- The complete HPP matrix row, in primary/hyperplane-descendant/point-descendant
order, is (-36, 12-36d, 36d²). No numerical invariant is assumed or computed here. -/
theorem normalized_plane_hyperplane_two_points_row (d : ℕ) :
    let p := normalizedGenusTwoTerms .plane (3 * d) ![d + 1] 0
      (SurfaceGenusZero.pointLabels ![.hyperplane, .point, .point] (3 * d))
    let f := fun q : SurfaceQuery .plane ↦ RationalTerms.coefficient p {Sum.inr q}
    (f (SurfaceQuery.points .plane 2 ![d] (3 * d + 1)),
      f (SurfaceFirstDescendant.query 2 ![d] .hyperplane (3 * d)),
      f (SurfaceFirstDescendant.query 2 ![d] .point (3 * d - 1))) =
        (-36, 12 - 36 * (d : ℚ), 36 * (d : ℚ) ^ 2) := by
  dsimp only
  rw [normalized_plane_hyperplane_two_points_canonical d _ rfl,
    normalized_plane_hyperplane_two_points_canonical d _ rfl,
    normalized_plane_hyperplane_two_points_canonical d _ rfl]
  simp only [SurfaceQuery.points, SurfaceFirstDescendant.query,
    Sum.inr.injEq, SurfaceQuery.mk.injEq, List.replicate_succ, List.cons.injEq,
    SurfaceInsertion.mk.injEq, reduceCtorEq, and_self, false_and, and_false,
    ite_false, ite_true, mul_zero, mul_one, zero_add, add_zero]

/-- After removing the three canonical degree-d variables, every surviving
genus-two coefficient in HPP has strictly smaller degree. -/
theorem normalized_plane_hyperplane_two_points_lower (d : ℕ) (v : Variable .plane)
    (hN : Sum.inr (SurfaceQuery.points .plane 2 ![d] (3 * d + 1)) ≠ v)
    (hH : Sum.inr (SurfaceFirstDescendant.query 2 ![d] .hyperplane (3 * d)) ≠ v)
    (hP : Sum.inr (SurfaceFirstDescendant.query 2 ![d] .point (3 * d - 1)) ≠ v)
    (hc : RationalTerms.coefficient (normalizedGenusTwoTerms .plane (3 * d) ![d + 1] 0
      (SurfaceGenusZero.pointLabels ![.hyperplane, .point, .point] (3 * d))) {v} ≠ 0) :
    SurfaceGenusZero.variableCurve v 0 < d := by
  have hb := normalized_plane_two_points_degree_lt v (3 * d) (d + 1)
    .hyperplane (Or.inl rfl) hc
  have hn : SurfaceGenusZero.variableCurve v 0 ≠ d := by
    intro he
    have hv : SurfaceGenusZero.variableCurve v = ![d] := by
      funext i
      fin_cases i
      exact he
    rw [normalized_plane_hyperplane_two_points_canonical d v hv] at hc
    simp only [if_neg hN, if_neg hH, if_neg hP, mul_zero, add_zero, ne_eq,
      not_true_eq_false] at hc
  omega

end AxiomaticGW.BelorousskiPandharipande

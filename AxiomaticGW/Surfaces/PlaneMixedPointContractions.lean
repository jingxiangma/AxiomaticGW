/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlanePointContractions

/-!
# Mixed plane insertions on rational complements

Hyperplane/point pairs on a line give binomial point-placement factors.
Two hyperplanes also admit a classical rational component; its point node
leaves the line remainder on the main component. All formulas below retain
the original marking and node slots and arbitrary main decorations.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusZero

/-- Interchanging the two external states preserves the primary scalar,
including the classical branch and every added-point count. -/
theorem primaryScalar_plane_swap_pair (delta : SurfaceTarget.plane.Curve)
    (n : ℕ) (a b c : SurfaceBasisLabel .plane) :
    primaryScalar .plane (pointValue .plane) delta n (![a, b, c] : Fin 3 → _) =
      primaryScalar .plane (pointValue .plane) delta n (![b, a, c] : Fin 3 → _) := by
  simp only [primaryScalar, Fin.sum_univ_three, Fin.prod_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [add_comm a.codimension b.codimension, mul_comm a.value b.value,
    mul_comm (a.primaryFactor delta) (b.primaryFactor delta)]
  rfl

/-- A classical triple containing a hyperplane and a point vanishes. -/
theorem primaryScalar_plane_zero_hyperplane_point (n : ℕ) (b : SurfaceBasisLabel .plane) :
    primaryScalar .plane (pointValue .plane) 0 n
      (![.hyperplane, .point, b] : Fin 3 → _) = 0 := by
  cases b with
  | exceptional i => exact Fin.elim0 i
  | unit | hyperplane | point =>
    norm_num [primaryScalar, Fin.sum_univ_three, Matrix.cons_val_two,
      SurfaceBasisLabel.codimension]
    omega

/-- Two points also force classical vanishing when the node is the middle slot. -/
theorem primaryScalar_plane_zero_point_node_point (n : ℕ) (b : SurfaceBasisLabel .plane) :
    primaryScalar .plane (pointValue .plane) 0 n
      (![.point, b, .point] : Fin 3 → _) = 0 := by
  cases b with
  | exceptional i => exact Fin.elim0 i
  | unit | hyperplane | point =>
    norm_num [primaryScalar, Fin.sum_univ_three, Matrix.cons_val_two,
      SurfaceBasisLabel.codimension]
    omega

/-- The classical two-hyperplane triple has a unit node and no added points. -/
theorem primaryScalar_plane_zero_two_hyperplanes (n : ℕ) (b : SurfaceBasisLabel .plane) :
    primaryScalar .plane (pointValue .plane) 0 n
      (![.hyperplane, .hyperplane, b] : Fin 3 → _) =
      if n = 0 ∧ b = .unit then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    cases b with
    | exceptional i => exact Fin.elim0 i
    | unit | hyperplane | point => decide +kernel
  · have hc : n + Fintype.card (Fin 3) ≠ 3 := by
      simp only [Fintype.card_fin]
      omega
    simp only [primaryScalar, ne_eq, not_true_eq_false, false_and, ite_false,
      ite_true, if_neg hc, ite_self, hn]

/-- A classical two-hyperplane component receives none of the added points. -/
theorem sum_binomial_primary_plane_zero_two_hyperplanes (f : ℕ → ℚ) (n : ℕ)
    (b : SurfaceBasisLabel .plane) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * primaryScalar .plane (pointValue .plane) 0 ij.2
        (![.hyperplane, .hyperplane, b] : Fin 3 → _))) =
      if b = .unit then f n else 0 := by
  rw [SurfacePointPullback.sum_binomial_of_right_support f
    (fun j ↦ primaryScalar .plane (pointValue .plane) 0 j
      (![.hyperplane, .hyperplane, b] : Fin 3 → _)) n 0 (by
        intro j hj
        rw [primaryScalar_plane_zero_two_hyperplanes, if_neg (fun h ↦ hj h.1)])]
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul,
    primaryScalar_plane_zero_two_hyperplanes, true_and, mul_ite, mul_one, mul_zero]

/-- A line with an external hyperplane and point has either a point node
and no extra point, or a hyperplane node and one extra point. -/
theorem sum_binomial_primary_plane_hyperplane_point (f : ℕ → ℚ) (n : ℕ)
    (b : SurfaceBasisLabel .plane) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * primaryScalar .plane (pointValue .plane) ![1] ij.2
        (![.hyperplane, .point, b] : Fin 3 → _))) =
      if b = .point then f n else
        if b = .hyperplane then (n : ℚ) * f (n - 1) else 0 := by
  rw [sum_binomial_primary_plane_one]
  cases b with
  | exceptional i => exact Fin.elim0 i
  | unit => rfl
  | point =>
    change (n.choose 0 : ℚ) * f (n - 0) = f n
    rw [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul]
  | hyperplane =>
    change (n.choose 1 : ℚ) * f (n - 1) = (n : ℚ) * f (n - 1)
    rw [Nat.choose_one_right]

/-- Two external hyperplanes require one or two added points on a line,
according to its point or hyperplane node. -/
theorem sum_binomial_primary_plane_two_hyperplanes (f : ℕ → ℚ) (n : ℕ)
    (b : SurfaceBasisLabel .plane) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * primaryScalar .plane (pointValue .plane) ![1] ij.2
        (![.hyperplane, .hyperplane, b] : Fin 3 → _))) =
      if b = .point then (n : ℚ) * f (n - 1) else
        if b = .hyperplane then (n.choose 2 : ℚ) * f (n - 2) else 0 := by
  rw [sum_binomial_primary_plane_one]
  cases b with
  | exceptional i => exact Fin.elim0 i
  | unit | hyperplane => rfl
  | point =>
    change (n.choose 1 : ℚ) * f (n - 1) = (n : ℚ) * f (n - 1)
    rw [Nat.choose_one_right]

/-- Every classical rational quadruple vanishes, even before using its states. -/
theorem primaryScalar_plane_zero_four (n : ℕ) (a : Fin 4 → SurfaceBasisLabel .plane) :
    primaryScalar .plane (pointValue .plane) 0 n a = 0 := by
  have hc : n + Fintype.card (Fin 4) ≠ 3 := by simp only [Fintype.card_fin]; omega
  simp only [primaryScalar, ne_eq, not_true_eq_false, false_and, ite_true,
    if_neg hc, ite_self]

/-- A line carrying HPP has a hyperplane node and no additional point. -/
theorem sum_binomial_primary_plane_hyperplane_two_points (f : ℕ → ℚ) (n : ℕ)
    (b : SurfaceBasisLabel .plane) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * primaryScalar .plane (pointValue .plane) ![1] ij.2
        (![.hyperplane, .point, .point, b] : Fin 4 → _))) =
      if b = .hyperplane then f n else 0 := by
  rw [sum_binomial_primary_plane_one]
  cases b with
  | exceptional i => exact Fin.elim0 i
  | unit | point => rfl
  | hyperplane =>
    change (n.choose 0 : ℚ) * f (n - 0) = f n
    rw [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul]

/-- A line carrying HHP has the same point placements as an HP pair. -/
theorem sum_binomial_primary_plane_two_hyperplanes_point (f : ℕ → ℚ) (n : ℕ)
    (b : SurfaceBasisLabel .plane) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * primaryScalar .plane (pointValue .plane) ![1] ij.2
        (![.hyperplane, .hyperplane, .point, b] : Fin 4 → _))) =
      if b = .point then f n else
        if b = .hyperplane then (n : ℚ) * f (n - 1) else 0 := by
  rw [sum_binomial_primary_plane_one]
  cases b with
  | exceptional i => exact Fin.elim0 i
  | unit => rfl
  | point =>
    change (n.choose 0 : ℚ) * f (n - 0) = f n
    rw [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul]
  | hyperplane =>
    change (n.choose 1 : ℚ) * f (n - 1) = (n : ℚ) * f (n - 1)
    rw [Nat.choose_one_right]

end AxiomaticGW.SurfaceGenusZero

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction GluingExpression

/-- Expand the actual external and node label maps of the BP two-state
rational complement. The main expression may itself contain boundary edges. -/
theorem remainderContraction_plane_pair_join (v : Variable .plane)
    (main : ℕ → SurfaceCotangentVertexValues .plane ℚ) (n : ℕ)
    (x : GluingExpression 2 (Fin 2)) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (delta : SurfaceTarget.plane.Curve) (a b c : SurfaceBasisLabel .plane) :
    let y := GetzlerGraphs.join (m := 1) (n := 2) 1 2 x
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
    remainderContraction .plane v main y (by exact (d, (0 : Fin 3 → ℕ)))
      (by exact (l, (inferInstance : DecidableEq (Fin 3)))) delta n ![a, b, c] =
      ∑ split ∈ SurfaceTarget.plane.splittings delta, ∑ t : SurfaceBasisLabel .plane,
        t.inverseWeight * ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          (n.choose ij.1 : ℚ) *
            (remainderContraction .plane v main x d l split.1 ij.1 ![a, t] *
              SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane)
                split.2 ij.2 (![b, c, t.dual] : Fin 3 → _)) := by
  dsimp only
  simp only [GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction]
  have hl (t : SurfaceBasisLabel .plane) :
      (Option.elim · t (((![a, b, c] : Fin 3 → _) ∘
        (finSumFinEquiv : Fin 1 ⊕ Fin 2 ≃ Fin 3)) ∘ Sum.inl)) ∘
        finSuccEquiv' 1 = ![a, t] := by
    funext i
    fin_cases i <;> rfl
  have hr (t : SurfaceBasisLabel .plane) :
      (Option.elim · t (((![a, b, c] : Fin 3 → _) ∘
        (finSumFinEquiv : Fin 1 ⊕ Fin 2 ≃ Fin 3)) ∘ Sum.inr)) ∘
        finSuccEquiv' 2 = ![b, c, t] := by
    funext i
    fin_cases i <;> rfl
  simp only [hl, hr, primaryPointVertex, and_self, ite_true]

/-- The two external slots on a primary rational complement are symmetric;
the original main marking and every main decoration stay fixed. -/
theorem remainderContraction_plane_pair_swap (v : Variable .plane)
    (main : ℕ → SurfaceCotangentVertexValues .plane ℚ) (n : ℕ)
    (x : GluingExpression 2 (Fin 2)) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (delta : SurfaceTarget.plane.Curve) (a b c : SurfaceBasisLabel .plane) :
    let y := GetzlerGraphs.join (m := 1) (n := 2) 1 2 x
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
    remainderContraction .plane v main y (by exact (d, (0 : Fin 3 → ℕ)))
      (by exact (l, (inferInstance : DecidableEq (Fin 3)))) delta n ![a, b, c] =
      remainderContraction .plane v main y (by exact (d, (0 : Fin 3 → ℕ)))
        (by exact (l, (inferInstance : DecidableEq (Fin 3)))) delta n ![a, c, b] := by
  dsimp only
  rw [remainderContraction_plane_pair_join, remainderContraction_plane_pair_join]
  simp only [SurfaceGenusZero.primaryScalar_plane_swap_pair (a := b) (b := c)]

/-- At zero remainder a point together with a positive-codimension state
forces the whole rational complement to vanish, independently of the main side. -/
theorem remainderContraction_plane_pair_zero_of_point (v : Variable .plane)
    (main : ℕ → SurfaceCotangentVertexValues .plane ℚ) (n : ℕ)
    (x : GluingExpression 2 (Fin 2)) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (a b : SurfaceBasisLabel .plane) (hb : b = .hyperplane ∨ b = .point) :
    let y := GetzlerGraphs.join (m := 1) (n := 2) 1 2 x
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
    remainderContraction .plane v main y (by exact (d, (0 : Fin 3 → ℕ)))
      (by exact (l, (inferInstance : DecidableEq (Fin 3)))) 0 n ![a, b, .point] = 0 := by
  dsimp only
  rw [remainderContraction_plane_pair_join,
    (SurfaceTarget.plane.splittings_eq 0).trans SurfaceTarget.plane.effective.splittings_zero]
  simp only [Finset.sum_singleton]
  apply Finset.sum_eq_zero
  intro t _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rcases hb with rfl | rfl
  · rw [SurfaceGenusZero.primaryScalar_plane_zero_hyperplane_point]
    simp only [mul_zero]
  · rw [SurfaceGenusZero.primaryScalar_plane_zero_two_points]
    simp only [mul_zero]

/-- With no remainder, the two-hyperplane rational complement contributes
exactly its classical point node on the main side. -/
theorem remainderContraction_plane_two_hyperplanes_zero (v : Variable .plane)
    (main : ℕ → SurfaceCotangentVertexValues .plane ℚ) (n : ℕ)
    (x : GluingExpression 2 (Fin 2)) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (a : SurfaceBasisLabel .plane) :
    let y := GetzlerGraphs.join (m := 1) (n := 2) 1 2 x
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
    remainderContraction .plane v main y (by exact (d, (0 : Fin 3 → ℕ)))
      (by exact (l, (inferInstance : DecidableEq (Fin 3)))) 0 n ![a, .hyperplane, .hyperplane] =
      remainderContraction .plane v main x d l 0 n ![a, .point] := by
  dsimp only
  rw [remainderContraction_plane_pair_join,
    (SurfaceTarget.plane.splittings_eq 0).trans SurfaceTarget.plane.effective.splittings_zero]
  simp only [Finset.sum_singleton]
  have hsum (b : SurfaceBasisLabel .plane) :=
    SurfaceGenusZero.sum_binomial_primary_plane_zero_two_hyperplanes
      (fun m ↦ remainderContraction .plane v main x d l 0 m ![a, b]) n b.dual
  simp only [hsum]
  rw [SurfaceBasisLabel.sum_labels]
  simp only [SurfaceBasisLabel.inverseWeight, SurfaceBasisLabel.dual,
    one_mul, Fin.sum_univ_zero, add_zero, reduceCtorEq, ite_false, ite_true, zero_add]

/-- A hyperplane/point complement exhausts the line remainder. A point node
on the rational side is a unit on the main side, with no lost marking factor. -/
theorem remainderContraction_plane_hyperplane_point_join (v : Variable .plane)
    (main : ℕ → SurfaceCotangentVertexValues .plane ℚ) (n : ℕ)
    (x : GluingExpression 2 (Fin 2)) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (a : SurfaceBasisLabel .plane) :
    let y := GetzlerGraphs.join (m := 1) (n := 2) 1 2 x
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
    remainderContraction .plane v main y (by exact (d, (0 : Fin 3 → ℕ)))
      (by exact (l, (inferInstance : DecidableEq (Fin 3))))
      ![1] n ![a, .hyperplane, .point] =
      remainderContraction .plane v main x d l 0 n ![a, .unit] +
        (n : ℚ) * remainderContraction .plane v main x d l 0 (n - 1)
          ![a, .hyperplane] := by
  dsimp only
  rw [remainderContraction_plane_pair_join, SurfaceTarget.sum_plane_splittings_one]
  dsimp only
  have hsum (b : SurfaceBasisLabel .plane) :=
    SurfaceGenusZero.sum_binomial_primary_plane_hyperplane_point
      (fun m ↦ remainderContraction .plane v main x d l 0 m ![a, b]) n b.dual
  simp only [hsum]
  rw [SurfaceBasisLabel.sum_labels]
  simp only [SurfaceBasisLabel.inverseWeight, SurfaceBasisLabel.dual,
    one_mul, Fin.sum_univ_zero, add_zero, reduceCtorEq, ite_false, ite_true]
  apply add_eq_left.mpr
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [SurfaceGenusZero.primaryScalar_plane_zero_hyperplane_point]
  simp only [mul_zero]

/-- Two hyperplanes retain the classical rational component as well as the
line component. Its point node leaves remainder one on the main expression. -/
theorem remainderContraction_plane_two_hyperplanes_join (v : Variable .plane)
    (main : ℕ → SurfaceCotangentVertexValues .plane ℚ) (n : ℕ)
    (x : GluingExpression 2 (Fin 2)) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (a : SurfaceBasisLabel .plane) :
    let y := GetzlerGraphs.join (m := 1) (n := 2) 1 2 x
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
    remainderContraction .plane v main y (by exact (d, (0 : Fin 3 → ℕ)))
      (by exact (l, (inferInstance : DecidableEq (Fin 3))))
      ![1] n ![a, .hyperplane, .hyperplane] =
      (n : ℚ) * remainderContraction .plane v main x d l 0 (n - 1) ![a, .unit] +
        (n.choose 2 : ℚ) * remainderContraction .plane v main x d l 0 (n - 2)
          ![a, .hyperplane] +
        remainderContraction .plane v main x d l ![1] n ![a, .point] := by
  dsimp only
  rw [remainderContraction_plane_pair_join, SurfaceTarget.sum_plane_splittings_one]
  dsimp only
  have hline (b : SurfaceBasisLabel .plane) :=
    SurfaceGenusZero.sum_binomial_primary_plane_two_hyperplanes
      (fun m ↦ remainderContraction .plane v main x d l 0 m ![a, b]) n b.dual
  have hzero (b : SurfaceBasisLabel .plane) :=
    SurfaceGenusZero.sum_binomial_primary_plane_zero_two_hyperplanes
      (fun m ↦ remainderContraction .plane v main x d l ![1] m ![a, b]) n b.dual
  simp only [hline, hzero]
  simp only [SurfaceBasisLabel.sum_labels,
    SurfaceBasisLabel.inverseWeight, SurfaceBasisLabel.dual,
    one_mul, Fin.sum_univ_zero, add_zero, reduceCtorEq, ite_false, ite_true, zero_add]

/-- The inner rational component of the first BP diagram vanishes at zero
remainder if its two external states are points. Its node is at index one. -/
theorem remainderContraction_plane_inner_two_points_zero (v : Variable .plane)
    (main : ℕ → SurfaceCotangentVertexValues .plane ℚ) (n : ℕ) (k : Fin 1 → ℕ) :
    remainderContraction .plane v main
      (GetzlerGraphs.join (m := 0) (n := 2) 0 1
        (fundamental 2 (Fin 1) (by norm_num [StableArity]))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (by exact (k, (0 : Fin 3 → ℕ)))
      (by exact ((inferInstance : DecidableEq (Fin 1)),
        (inferInstance : DecidableEq (Fin 3)))) 0 n ![.point, .point] = 0 := by
  simp only [GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction]
  have hr (b : SurfaceBasisLabel .plane) :
      (Option.elim · b (((![.point, .point] : Fin 2 → SurfaceBasisLabel .plane) ∘
        (finSumFinEquiv : Fin 0 ⊕ Fin 2 ≃ Fin 2)) ∘ Sum.inr)) ∘
        finSuccEquiv' 1 = ![.point, b, .point] := by
    funext i
    fin_cases i <;> rfl
  simp only [hr, primaryPointVertex, and_self, ite_true]
  rw [(SurfaceTarget.plane.splittings_eq 0).trans
    SurfaceTarget.plane.effective.splittings_zero]
  simp only [Finset.sum_singleton]
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [SurfaceGenusZero.primaryScalar_plane_zero_point_node_point]
  simp only [mul_zero]

/-- For two equal point states at zero remainder, interchanging the single
psi preserves the terminal insertion multiset, and neither unit correction occurs. -/
theorem remainderVertex_plane_two_points_onePsi_zero_swap (v : Variable .plane) (n : ℕ) :
    remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0 ![.point, .point] =
      remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 2)
        (by norm_num [StableArity]) (Pi.single 1 1) inferInstance 0 ![.point, .point] := by
  have hq : SurfaceAncestorKey.ofLabels (X := .plane) 2 (Fin 2)
      (by norm_num [StableArity]) (SurfaceGenusZero.variableCurve v)
      (Pi.single 0 1) ![.point, .point] =
      SurfaceAncestorKey.ofLabels 2 (Fin 2) (by norm_num [StableArity])
        (SurfaceGenusZero.variableCurve v) (Pi.single 1 1) ![.point, .point] := by
    apply (SurfaceAncestorKey.eq_iff _ _).mpr
    refine ⟨rfl, rfl, ?_⟩
    dsimp only [SurfaceAncestorKey.ofLabels]
    decide +kernel
  rw [remainderVertex_onePsi_plane_zero, remainderVertex_onePsi_plane_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, reduceCtorEq, ite_false, sub_zero]
  rw [hq]

end AxiomaticGW.SurfaceGenusTwo

namespace AxiomaticGW.BelorousskiPandharipande
open SurfacePolynomialReduction SurfaceGenusTwo GluingExpression

/-- Expose the outer rational pair in the first BP diagram, retaining the
actual inner node at index one and all three primary decorations. -/
theorem plane_paper_zero_pair (v : Variable .plane) (n : ℕ)
    (delta : SurfaceTarget.plane.Curve) (a b c : SurfaceBasisLabel .plane) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm 0) delta n ![a, b, c] =
      remainderContraction .plane v (remainderVertex .plane v (planeCoefficientVertex v))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          (GetzlerGraphs.join (m := 0) (n := 2) 0 1
            (fundamental 2 (Fin 1) (by norm_num [StableArity]))
            (fundamental 0 (Fin 3) (by norm_num [StableArity])))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        ((![0], (0 : Fin 3 → ℕ)), (0 : Fin 3 → ℕ))
        (((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 3))),
          (inferInstance : DecidableEq (Fin 3))) delta n ![a, b, c] := by
  have hz : (![0, 0, 0] : Fin 3 → ℕ) = 0 := by decide +kernel
  rw [remainderPointCoefficient, if_pos (by decide +kernel)]
  change remainderContraction .plane v (remainderVertex .plane v (planeCoefficientVertex v))
    (GetzlerGraphs.join (m := 1) (n := 2) 1 2
      (GetzlerGraphs.join (m := 0) (n := 2) 0 1
        (fundamental 2 (Fin 1) (by norm_num [StableArity]))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (fundamental 0 (Fin 3) (by norm_num [StableArity])))
    ((![0], ![0, 0, 0]), ![0, 0, 0]) _ delta n ![a, b, c] = _
  rw [hz]
  rfl

/-- The second BP diagram puts all three external states on the rational
component and psi on the single main node. -/
theorem plane_paper_one_sum (v : Variable .plane) (n : ℕ)
    (delta : SurfaceTarget.plane.Curve) (a : Fin 3 → SurfaceBasisLabel .plane) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm 1) delta n a =
      ∑ split ∈ SurfaceTarget.plane.splittings delta, ∑ b : SurfaceBasisLabel .plane,
        b.inverseWeight * ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          (n.choose ij.1 : ℚ) *
            (remainderVertex .plane v (planeCoefficientVertex v) ij.1 2 (Fin 1)
              (by norm_num [StableArity]) ![1] inferInstance split.1 ![b] *
              SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane)
                split.2 ij.2 (![a 0, a 1, a 2, b.dual] : Fin 4 → _)) := by
  have hx : (paperCotangentTerm 1).expression.maxComponentGenus = 2 := by decide +kernel
  rw [remainderPointCoefficient, if_pos hx]
  change remainderContraction .plane v (remainderVertex .plane v (planeCoefficientVertex v))
    (GetzlerGraphs.join (m := 0) (n := 3) 0 3
      (fundamental 2 (Fin 1) (by norm_num [StableArity]))
      (fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (![1], (0 : Fin 4 → ℕ))
    ((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 4)))
    delta n a = _
  simp only [GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction]
  have hl (b : SurfaceBasisLabel .plane) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 0 ⊕ Fin 3 ≃ Fin 3)) ∘ Sum.inl)) ∘
        finSuccEquiv' 0 = ![b] := by
    funext i
    fin_cases i
    rfl
  have hr (b : SurfaceBasisLabel .plane) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 0 ⊕ Fin 3 ≃ Fin 3)) ∘ Sum.inr)) ∘
        finSuccEquiv' 3 = ![a 0, a 1, a 2, b] := by
    funext i
    fin_cases i <;> rfl
  simp only [hl, hr, primaryPointVertex, and_self, ite_true]

/-- HPP forces a hyperplane at the main psi node of the second BP diagram. -/
theorem plane_paper_one_hyperplane_two_points (v : Variable .plane) (n : ℕ) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm 1) ![1] n ![.hyperplane, .point, .point] =
      remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 1)
        (by norm_num [StableArity]) ![1] inferInstance 0 ![.hyperplane] := by
  rw [plane_paper_one_sum, SurfaceTarget.sum_plane_splittings_one]
  dsimp only
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  have hsum (b : SurfaceBasisLabel .plane) :=
    SurfaceGenusZero.sum_binomial_primary_plane_hyperplane_two_points
      (fun m ↦ remainderVertex .plane v (planeCoefficientVertex v) m 2 (Fin 1)
        (by norm_num [StableArity]) ![1] inferInstance 0 ![b]) n b.dual
  simp only [hsum]
  rw [SurfaceBasisLabel.sum_labels]
  simp only [SurfaceBasisLabel.inverseWeight, SurfaceBasisLabel.dual,
    one_mul, Fin.sum_univ_zero, add_zero, reduceCtorEq, ite_false, ite_true, zero_add]
  apply add_eq_left.mpr
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [SurfaceGenusZero.primaryScalar_plane_zero_four]
  simp only [mul_zero]

/-- HHP retains both a unit psi node and the n placements of a hyperplane
psi node. The later unit cotangent correction has not been discarded. -/
theorem plane_paper_one_two_hyperplanes_point (v : Variable .plane) (n : ℕ) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm 1) ![1] n ![.hyperplane, .hyperplane, .point] =
      remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 1)
        (by norm_num [StableArity]) ![1] inferInstance 0 ![.unit] +
        (n : ℚ) * remainderVertex .plane v (planeCoefficientVertex v) (n - 1) 2 (Fin 1)
          (by norm_num [StableArity]) ![1] inferInstance 0 ![.hyperplane] := by
  rw [plane_paper_one_sum, SurfaceTarget.sum_plane_splittings_one]
  dsimp only
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  have hsum (b : SurfaceBasisLabel .plane) :=
    SurfaceGenusZero.sum_binomial_primary_plane_two_hyperplanes_point
      (fun m ↦ remainderVertex .plane v (planeCoefficientVertex v) m 2 (Fin 1)
        (by norm_num [StableArity]) ![1] inferInstance 0 ![b]) n b.dual
  simp only [hsum]
  rw [SurfaceBasisLabel.sum_labels]
  simp only [SurfaceBasisLabel.inverseWeight, SurfaceBasisLabel.dual,
    one_mul, Fin.sum_univ_zero, add_zero, reduceCtorEq, ite_false, ite_true]
  apply add_eq_left.mpr
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [SurfaceGenusZero.primaryScalar_plane_zero_four]
  simp only [mul_zero]

/-- The third and fourth diagrams have the same node map, with psi on the
specified original marking (s = 0) or the main node (s = 1), respectively. -/
theorem plane_paper_onePsi_pair (v : Variable .plane) (n : ℕ) (s : Fin 2)
    (delta : SurfaceTarget.plane.Curve) (a b c : SurfaceBasisLabel .plane) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm (if s = 0 then 2 else 3)) delta n ![a, b, c] =
      remainderContraction .plane v (remainderVertex .plane v (planeCoefficientVertex v))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          (fundamental 2 (Fin 2) (by norm_num [StableArity]))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        (by exact (Pi.single s 1, (0 : Fin 3 → ℕ)))
        (by exact ((inferInstance : DecidableEq (Fin 2)),
          (inferInstance : DecidableEq (Fin 3)))) delta n ![a, b, c] := by
  have h0 : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
  have h1 : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
  have hs : s = 0 ∨ s = 1 := by omega
  rcases hs with rfl | rfl
  · rw [if_pos rfl, ← h0]
    rfl
  · rw [if_neg (by decide : (1 : Fin 2) ≠ 0), ← h1]
    rfl

/-- The single-psi HP contractions preserve their distinct psi slots. -/
theorem plane_paper_onePsi_hyperplane_point (v : Variable .plane) (n : ℕ) (s : Fin 2)
    (a : SurfaceBasisLabel .plane) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm (if s = 0 then 2 else 3)) ![1] n ![a, .hyperplane, .point] =
      remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 2)
        (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0 ![a, .unit] +
        (n : ℚ) * remainderVertex .plane v (planeCoefficientVertex v) (n - 1) 2 (Fin 2)
          (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0 ![a, .hyperplane] := by
  rw [plane_paper_onePsi_pair, remainderContraction_plane_hyperplane_point_join]
  rfl

/-- The HH contraction keeps the line-remainder term on the main component,
including its original psi slot and all signed cotangent corrections. -/
theorem plane_paper_onePsi_two_hyperplanes (v : Variable .plane) (n : ℕ) (s : Fin 2)
    (a : SurfaceBasisLabel .plane) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm (if s = 0 then 2 else 3)) ![1] n ![a, .hyperplane, .hyperplane] =
      (n : ℚ) * remainderVertex .plane v (planeCoefficientVertex v) (n - 1) 2 (Fin 2)
        (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0 ![a, .unit] +
        (n.choose 2 : ℚ) * remainderVertex .plane v (planeCoefficientVertex v) (n - 2) 2
          (Fin 2) (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0
          ![a, .hyperplane] +
        remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 2)
          (by norm_num [StableArity]) (Pi.single s 1) inferInstance ![1] ![a, .point] := by
  rw [plane_paper_onePsi_pair, remainderContraction_plane_two_hyperplanes_join]
  rfl

/-- At zero remainder the two-hyperplane component has just its classical
point node, with psi still in the original specified main slot. -/
theorem plane_paper_onePsi_two_hyperplanes_zero (v : Variable .plane) (n : ℕ) (s : Fin 2)
    (a : SurfaceBasisLabel .plane) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm (if s = 0 then 2 else 3)) 0 n ![a, .hyperplane, .hyperplane] =
      remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 2)
        (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0 ![a, .point] := by
  rw [plane_paper_onePsi_pair, remainderContraction_plane_two_hyperplanes_zero]
  rfl

end AxiomaticGW.BelorousskiPandharipande

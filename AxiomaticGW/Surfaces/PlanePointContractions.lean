/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlanePointNormalization
public import AxiomaticGW.Surfaces.GenusTwoCoefficientRelations

/-!
# Plane point constraints on rational complements

Two specified point insertions force a degree-one rational complement and
its hyperplane node. These reductions preserve the actual gluing label maps
and arbitrary cotangent powers on the main component. They identify the full
three-point BP row with `(0, -18, 18d)` at every positive plane degree.
The other shifted rows and reconstruction are separate proof obligations.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusZero

/-- A classical rational triple cannot contain two point classes. -/
theorem primaryScalar_plane_zero_two_points (n : ℕ) (b : SurfaceBasisLabel .plane) :
    primaryScalar .plane (pointValue .plane) 0 n (![.point, .point, b] : Fin 3 → _) = 0 := by
  cases b with
  | exceptional i => exact Fin.elim0 i
  | unit | hyperplane | point =>
    norm_num [primaryScalar, Fin.sum_univ_three, SurfaceBasisLabel.codimension]
    omega

/-- A point and a hyperplane already exceed the classical surface dimension. -/
theorem primaryScalar_plane_zero_point_hyperplane (n : ℕ) (b : SurfaceBasisLabel .plane) :
    primaryScalar .plane (pointValue .plane) 0 n
      (![.point, b, .hyperplane] : Fin 3 → _) = 0 := by
  cases b with
  | exceptional i => exact Fin.elim0 i
  | unit | hyperplane | point =>
    norm_num [primaryScalar, Fin.sum_univ_three, Matrix.cons_val_two,
      SurfaceBasisLabel.codimension]
    omega

/-- Three specified points cannot lie on a rational component of degree zero
or one in this primary contraction. No added-point count can change this. -/
theorem primaryScalar_plane_three_points (n : ℕ) (b : SurfaceBasisLabel .plane)
    (delta : SurfaceTarget.plane.Curve) (hd : delta = 0 ∨ delta = ![1]) :
    primaryScalar .plane (pointValue .plane) delta n
      (![.point, .point, .point, b] : Fin 4 → _) = 0 := by
  rcases hd with rfl | rfl
  · have hc : n + Fintype.card (Fin 4) ≠ 3 := by simp only [Fintype.card_fin]; omega
    simp only [primaryScalar, ne_eq, not_true_eq_false, false_and, ite_true,
      if_neg hc, ite_self]
  · rw [primaryScalar_plane_one]
    cases b with
    | exceptional i => exact Fin.elim0 i
    | unit => rfl
    | hyperplane =>
      change (if n + 3 = 2 then (1 : ℚ) else 0) = 0
      rw [if_neg (by omega)]
    | point =>
      change (if n + 4 = 2 then (1 : ℚ) else 0) = 0
      rw [if_neg (by omega)]

/-- A line through the two specified points accepts precisely a hyperplane
node and no further point. The main factor is otherwise arbitrary. -/
theorem sum_binomial_primary_plane_two_points (f : ℕ → ℚ) (n : ℕ)
    (b : SurfaceBasisLabel .plane) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * primaryScalar .plane (pointValue .plane) ![1] ij.2
        (![.point, .point, b] : Fin 3 → _))) =
      if b = .hyperplane then f n else 0 := by
  rw [sum_binomial_primary_plane_one]
  cases b with
  | exceptional i => exact Fin.elim0 i
  | unit => rfl
  | point => rfl
  | hyperplane =>
    change (n.choose 0 : ℚ) * f (n - 0) = f n
    rw [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul]

end AxiomaticGW.SurfaceGenusZero

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction GluingExpression

/-- The actual BP gluing with two points on the rational component contracts
to the hyperplane node at zero main remainder. The first external state and
every main cotangent power are retained in their original slots. -/
theorem remainderContraction_plane_two_points_join (v : Variable .plane)
    (main : ℕ → SurfaceCotangentVertexValues .plane ℚ) (n : ℕ)
    (x : GluingExpression 2 (Fin 2)) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (a : SurfaceBasisLabel .plane) :
    let y := GetzlerGraphs.join (m := 1) (n := 2) 1 2 x
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
    remainderContraction .plane v main y (by exact (d, (0 : Fin 3 → ℕ)))
      (by exact (l, (inferInstance : DecidableEq (Fin 3))))
      ![1] n ![a, .point, .point] =
      remainderContraction .plane v main x d l 0 n ![a, .hyperplane] := by
  dsimp only
  simp only [GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction]
  have hl (b : SurfaceBasisLabel .plane) :
      (Option.elim · b (((![a, .point, .point] : Fin 3 → _) ∘
        (finSumFinEquiv : Fin 1 ⊕ Fin 2 ≃ Fin 3)) ∘ Sum.inl)) ∘
        finSuccEquiv' 1 = ![a, b] := by
    funext i
    fin_cases i <;> rfl
  have hr (b : SurfaceBasisLabel .plane) :
      (Option.elim · b (((![a, .point, .point] : Fin 3 → _) ∘
        (finSumFinEquiv : Fin 1 ⊕ Fin 2 ≃ Fin 3)) ∘ Sum.inr)) ∘
        finSuccEquiv' 2 = ![.point, .point, b] := by
    funext i
    fin_cases i <;> rfl
  simp only [hl, hr, primaryPointVertex, and_self, ite_true]
  rw [SurfaceTarget.sum_plane_splittings_one]
  dsimp only
  have hsum (b : SurfaceBasisLabel .plane) :=
    SurfaceGenusZero.sum_binomial_primary_plane_two_points
      (fun m ↦ remainderContraction .plane v main x d l 0 m ![a, b])
      n b.dual
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
  rw [SurfaceGenusZero.primaryScalar_plane_zero_two_points]
  simp only [mul_zero]

/-- In the two single-psi BP diagrams the surviving main component is a
fundamental vertex. The original marking and node retain their slots. -/
theorem remainderContraction_plane_two_points (v : Variable .plane)
    (main : ℕ → SurfaceCotangentVertexValues .plane ℚ) (n : ℕ)
    (k : Fin 2 → ℕ) (a : SurfaceBasisLabel .plane) :
    let x := GetzlerGraphs.join (m := 1) (n := 2) 1 2
      (fundamental 2 (Fin 2) (by norm_num [StableArity]))
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
    remainderContraction .plane v main x (by exact (k, (0 : Fin 3 → ℕ)))
      (by exact ((inferInstance : DecidableEq (Fin 2)),
        (inferInstance : DecidableEq (Fin 3)))) ![1] n ![a, .point, .point] =
      main n 2 (Fin 2) (by norm_num [StableArity]) k inferInstance 0 ![a, .hyperplane] := by
  dsimp only
  rw [remainderContraction_plane_two_points_join]
  rfl

private theorem point_hyperplane_dimension (d n : ℕ) (s : Fin 2) :
    ((SurfaceAncestorKey.ofLabels (X := .plane) 2 (Fin 2) (by norm_num [StableArity]) ![d]
      (Pi.single s 1) ![.point, .hyperplane]).addPoints n).DimensionCompatible ↔
      n + 1 = 3 * d := by
  have hc : SurfaceTarget.plane.c1Degree ![d] = 3 * (d : ℤ) := by
    rw [SurfaceTarget.c1Degree_eq_intersection]
    change 3 * (d : ℤ) - ∑ _ : Fin 0, _ = _
    rw [Fin.sum_univ_zero, sub_zero]
  fin_cases s <;>
    simp only [SurfaceAncestorKey.DimensionCompatible, SurfaceAncestorKey.totalCodimension,
      SurfaceAncestorKey.addPoints, SurfaceAncestorKey.ofLabels,
      Multiset.map_add, Multiset.map_replicate, Multiset.sum_add, Multiset.sum_replicate,
      Multiset.card_add, Multiset.card_replicate, Multiset.card_map, Finset.card_val,
      Finset.card_univ, Fintype.card_fin, hc, SurfaceBasisLabel.codimension, add_zero,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  all_goals
    change (n : ℤ) * 2 + 4 = 3 * (d : ℤ) + 2 - 1 + ((n : ℤ) + 2) ↔ _
    omega

/-- The two surviving components select their actual canonical descendant
requests. Their common signed dimension test fixes the degree without any
positivity assumption or truncated subtraction. -/
theorem remainderVertex_plane_point_hyperplane (v : Variable .plane) (n : ℕ) (s : Fin 2) :
    let d := SurfaceGenusZero.variableCurve v 0
    remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0 ![.point, .hyperplane] =
      if n + 1 = 3 * d then
        if s = 0 then (d : ℚ) *
          (if Sum.inr (SurfaceFirstDescendant.query 2 ![d] .point n) = v then 1 else 0)
        else if Sum.inr (SurfaceFirstDescendant.query 2 ![d] .hyperplane (n + 1)) = v
          then 1 else 0
      else 0 := by
  let d := SurfaceGenusZero.variableCurve v 0
  have hv : SurfaceGenusZero.variableCurve v = ![d] := by
    funext i
    fin_cases i
    rfl
  dsimp only
  rw [remainderVertex_onePsi_plane_zero_normalized, hv]
  simp only [point_hyperplane_dimension, Matrix.cons_val_zero]
  have hs : s = 0 ∨ s = 1 := by omega
  rcases hs with rfl | rfl
  · have hm : ((Finset.univ.erase (0 : Fin 2)).val.map
        (![.point, .hyperplane] : Fin 2 → SurfaceBasisLabel .plane)) = {.hyperplane} :=
      by decide +kernel
    have hu : SurfaceBasisLabel.unit ∉
        (Multiset.replicate n .point + {.hyperplane} : Multiset (SurfaceBasisLabel .plane)) := by
      simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton,
        reduceCtorEq, and_false, or_self, not_false_eq_true]
    simp only [hm, Matrix.cons_val_zero, reduceCtorEq, ite_false, ite_true, sub_zero]
    rw [SurfaceFirstDescendant.terms_plane_point 2 d _ hu]
    simp only [Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton,
      reduceCtorEq, ite_false, ite_true, zero_add, add_zero, pow_one]
    by_cases hd : n + 1 = 3 * d
    · have hq : (SurfaceFirstDescendant.query (X := .plane) 2 ![d]
        .point n).DimensionCompatible := by
        rw [SurfaceQuery.dimensionCompatible_first_plane]
        change n + 2 + 1 = 3 * d + 2
        omega
      simp only [if_pos hd, SurfaceFirstDescendant.dimensionTerms, if_pos hq,
        RationalTerms.rename, RationalTerms.scale, RationalTerms.term, one_ne_zero,
        ite_false, Multiset.map_singleton]
      have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
      simp only [if_neg hd0, Multiset.map_singleton, RationalTerms.coefficient,
        Multiset.sum_singleton, Multiset.singleton_inj, mul_one]
      split_ifs <;> simp only [mul_one, mul_zero]
    · simp only [if_neg hd]
  · have hm : ((Finset.univ.erase (1 : Fin 2)).val.map
        (![.point, .hyperplane] : Fin 2 → SurfaceBasisLabel .plane)) = {.point} :=
      by decide +kernel
    have hu : SurfaceBasisLabel.unit ∉
        (Multiset.replicate n .point + {.point} : Multiset (SurfaceBasisLabel .plane)) := by
      simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton,
        reduceCtorEq, and_false, or_self, not_false_eq_true]
    simp only [hm, Matrix.cons_val_one, Matrix.cons_val_zero, reduceCtorEq,
      ite_false, sub_zero]
    rw [SurfaceFirstDescendant.terms_plane_hyperplane 2 d _ hu]
    simp only [Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton,
      reduceCtorEq, ite_false, ite_true, add_zero, pow_zero, Nat.cast_zero,
      zero_mul, RationalTerms.scale, one_ne_zero]
    by_cases hd : n + 1 = 3 * d
    · have hq : (SurfaceFirstDescendant.query (X := .plane) 2 ![d]
        .hyperplane (n + 1)).DimensionCompatible := by
        rw [SurfaceQuery.dimensionCompatible_first_plane]
        change n + 1 + 1 + 1 = 3 * d + 2
        omega
      simp only [if_pos hd, SurfaceFirstDescendant.dimensionTerms, if_pos hq,
        RationalTerms.rename, RationalTerms.term, one_ne_zero, ite_false,
        Multiset.map_singleton, RationalTerms.coefficient, Multiset.sum_singleton,
        Multiset.singleton_inj, one_mul]
      rfl
    · simp only [if_neg hd]

end AxiomaticGW.SurfaceGenusTwo

namespace AxiomaticGW.BelorousskiPandharipande
open SurfacePolynomialReduction SurfaceGenusTwo GluingExpression

/-- The two-edge diagram first consumes the line on its two-point tail.
Its remaining classical rational component contains a point and hyperplane,
and therefore vanishes, with every added-point placement retained. -/
theorem plane_paper_zero_three_points (v : Variable .plane) (n : ℕ) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm 0) ![1] n ![.point, .point, .point] = 0 := by
  have hx : (paperCotangentTerm 0).expression.maxComponentGenus = 2 := by decide +kernel
  rw [remainderPointCoefficient, if_pos hx]
  change remainderContraction .plane v (remainderVertex .plane v (planeCoefficientVertex v))
    (GetzlerGraphs.join (m := 1) (n := 2) 1 2
      (GetzlerGraphs.join (m := 0) (n := 2) 0 1
        (fundamental 2 (Fin 1) (by norm_num [StableArity]))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (fundamental 0 (Fin 3) (by norm_num [StableArity])))
    ((![0], ![0, 0, 0]), ![0, 0, 0])
    (((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 3))),
      (inferInstance : DecidableEq (Fin 3))) ![1] n ![.point, .point, .point] = 0
  have hz : (![0, 0, 0] : Fin 3 → ℕ) = 0 := by decide +kernel
  simp only [hz]
  erw [remainderContraction_plane_two_points_join]
  simp only [GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction]
  have hr (b : SurfaceBasisLabel .plane) :
      (Option.elim · b (((![.point, .hyperplane] : Fin 2 → SurfaceBasisLabel .plane) ∘
        (finSumFinEquiv : Fin 0 ⊕ Fin 2 ≃ Fin 2)) ∘ Sum.inr)) ∘
        finSuccEquiv' 1 = ![.point, b, .hyperplane] := by
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
  rw [SurfaceGenusZero.primaryScalar_plane_zero_point_hyperplane]
  simp only [mul_zero]

/-- The second diagram would put all three specified points on a rational
component with at most line degree, so its complete coefficient vanishes. -/
theorem plane_paper_one_three_points (v : Variable .plane) (n : ℕ) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm 1) ![1] n ![.point, .point, .point] = 0 := by
  have hx : (paperCotangentTerm 1).expression.maxComponentGenus = 2 := by decide +kernel
  rw [remainderPointCoefficient, if_pos hx]
  change remainderContraction .plane v (remainderVertex .plane v (planeCoefficientVertex v))
    (GetzlerGraphs.join (m := 0) (n := 3) 0 3
      (fundamental 2 (Fin 1) (by norm_num [StableArity]))
      (fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (![1], (0 : Fin 4 → ℕ))
    ((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 4)))
    ![1] n ![.point, .point, .point] = 0
  simp only [GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction]
  have hr (b : SurfaceBasisLabel .plane) :
      (Option.elim · b (((![.point, .point, .point] : Fin 3 → SurfaceBasisLabel .plane) ∘
        (finSumFinEquiv : Fin 0 ⊕ Fin 3 ≃ Fin 3)) ∘ Sum.inr)) ∘
        finSuccEquiv' 3 = ![.point, .point, .point, b] := by
    funext i
    fin_cases i <;> rfl
  simp only [hr, primaryPointVertex, and_self, ite_true]
  rw [SurfaceTarget.sum_plane_splittings_one]
  trans (0 : ℚ) + 0
  · congr 1 <;>
    (apply Finset.sum_eq_zero
     intro b _
     apply mul_eq_zero_of_right
     apply Finset.sum_eq_zero
     intro ij _
     first
     | rw [SurfaceGenusZero.primaryScalar_plane_three_points _ _ _ (Or.inl rfl)]
     | rw [SurfaceGenusZero.primaryScalar_plane_three_points _ _ _ (Or.inr rfl)]
     simp only [mul_zero])
  · exact add_zero 0

/-- In the third published diagram psi stays on the original external
marking; the two rational points force a primary hyperplane at the node. -/
theorem plane_paper_two_two_points (v : Variable .plane) (n : ℕ)
    (a : SurfaceBasisLabel .plane) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm 2) ![1] n ![a, .point, .point] =
      remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 2)
        (by norm_num [StableArity]) ![1, 0] inferInstance 0 ![a, .hyperplane] := by
  have hx : (paperCotangentTerm 2).expression.maxComponentGenus = 2 := by decide +kernel
  rw [remainderPointCoefficient, if_pos hx]
  change remainderContraction .plane v (remainderVertex .plane v (planeCoefficientVertex v))
    (GetzlerGraphs.join (m := 1) (n := 2) 1 2
      (fundamental 2 (Fin 2) (by norm_num [StableArity]))
      (fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (![1, 0], (0 : Fin 3 → ℕ))
    ((inferInstance : DecidableEq (Fin 2)), (inferInstance : DecidableEq (Fin 3)))
    ![1] n ![a, .point, .point] = _
  exact remainderContraction_plane_two_points v _ n ![1, 0] a

/-- In the fourth published diagram psi is on the node. This is a different
descendant state from the third diagram even with identical external labels. -/
theorem plane_paper_three_two_points (v : Variable .plane) (n : ℕ)
    (a : SurfaceBasisLabel .plane) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm 3) ![1] n ![a, .point, .point] =
      remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 2)
        (by norm_num [StableArity]) ![0, 1] inferInstance 0 ![a, .hyperplane] := by
  have hx : (paperCotangentTerm 3).expression.maxComponentGenus = 2 := by decide +kernel
  rw [remainderPointCoefficient, if_pos hx]
  change remainderContraction .plane v (remainderVertex .plane v (planeCoefficientVertex v))
    (GetzlerGraphs.join (m := 1) (n := 2) 1 2
      (fundamental 2 (Fin 2) (by norm_num [StableArity]))
      (fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (![0, 1], (0 : Fin 3 → ℕ))
    ((inferInstance : DecidableEq (Fin 2)), (inferInstance : DecidableEq (Fin 3)))
    ![1] n ![a, .point, .point] = _
  exact remainderContraction_plane_two_points v _ n ![0, 1] a

/-- All six original marking permutations agree when every external state
is a point. The published orbit sum still counts all six occurrences. -/
theorem plane_orbit_three_points (v : Variable .plane) (n : ℕ) (i : Fin 20) (e : Fin 6) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (orbitCotangentTerm i e) ![1] n ![.point, .point, .point] =
      remainderPointCoefficient .plane v (planeCoefficientVertex v)
        (paperCotangentTerm i) ![1] n ![.point, .point, .point] := by
  have hc : (![.point, .point, .point] : Fin 3 → SurfaceBasisLabel .plane) =
      fun _ ↦ .point := by decide +kernel
  simp only [hc, orbitCotangentTerm, CotangentTerm.relabel, remainderPointCoefficient,
    GluingExpression.maxComponentGenus, remainderContraction, Function.comp_def]

/-- The complete shifted BP row with three specified points has just the
two surviving first-power components, with their raw coefficients and all six
marking assignments. It holds for every requested variable and point count. -/
theorem planeRemainderPointCoefficient_three_points (v : Variable .plane) (n : ℕ) :
    planeRemainderPointCoefficient n ![1] ![.point, .point, .point] v =
      18 * (remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 2)
          (by norm_num [StableArity]) ![1, 0] inferInstance 0 ![.point, .hyperplane] -
        remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 2)
          (by norm_num [StableArity]) ![0, 1] inferInstance 0 ![.point, .hyperplane]) := by
  simp only [planeRemainderPointCoefficient, plane_orbit_three_points,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Fin.sum_univ_four]
  simp only [show Fin.castAdd 16 (0 : Fin 4) = (0 : Fin 20) from rfl,
    show Fin.castAdd 16 (1 : Fin 4) = (1 : Fin 20) from rfl,
    show Fin.castAdd 16 (2 : Fin 4) = (2 : Fin 20) from rfl,
    show Fin.castAdd 16 (3 : Fin 4) = (3 : Fin 20) from rfl]
  rw [plane_paper_zero_three_points, plane_paper_one_three_points,
    plane_paper_two_two_points, plane_paper_three_two_points]
  change (-2 : ℚ) * (6 * 0) + 2 * (6 * 0) + 3 * (6 * _) + (-3) * (6 * _) = _
  ring

/-- Exact canonical support of the complete three-point row at a one-degree
remainder. The dimension guard fixes the requested degree, and only the two
displayed descendant queries survive. This does not address larger remainders
or the source-degree variables. -/
theorem planeRemainderPointCoefficient_three_points_canonical (v : Variable .plane) (n : ℕ) :
    let d := SurfaceGenusZero.variableCurve v 0
    planeRemainderPointCoefficient n ![1] ![.point, .point, .point] v =
      if n + 1 = 3 * d then
        18 * ((d : ℚ) *
          (if Sum.inr (SurfaceFirstDescendant.query 2 ![d] .point n) = v then 1 else 0) -
          if Sum.inr (SurfaceFirstDescendant.query 2 ![d] .hyperplane (n + 1)) = v
            then 1 else 0)
      else 0 := by
  dsimp only
  rw [planeRemainderPointCoefficient_three_points]
  have h0 : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
  have h1 : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
  rw [h0, h1, remainderVertex_plane_point_hyperplane, remainderVertex_plane_point_hyperplane]
  simp only [ite_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]
  split_ifs <;> ring

/-- The complete PPP matrix row at every positive plane degree, ordered as
primary, hyperplane descendant, point descendant. These are coefficients of
the original normalized BP equation, not values supplied as numerical seeds. -/
theorem planeRemainderPointCoefficient_three_points_row (d : ℕ) (hd : 0 < d) :
    let f := fun q : SurfaceQuery .plane ↦
      planeRemainderPointCoefficient (3 * d - 1) ![1] ![.point, .point, .point] (.inr q)
    (f (SurfaceQuery.points .plane 2 ![d] (3 * d + 1)),
      f (SurfaceFirstDescendant.query 2 ![d] .hyperplane (3 * d)),
      f (SurfaceFirstDescendant.query 2 ![d] .point (3 * d - 1))) =
        (0, -18, 18 * (d : ℚ)) := by
  have hn : 3 * d - 1 + 1 = 3 * d := by omega
  dsimp only
  simp only [planeRemainderPointCoefficient_three_points_canonical,
    SurfaceGenusZero.variableCurve, SurfaceQuery.points, SurfaceFirstDescendant.query,
    Matrix.cons_val_zero, hn, Sum.inr.injEq, SurfaceQuery.mk.injEq,
    List.replicate_succ, List.cons.injEq, SurfaceInsertion.mk.injEq,
    reduceCtorEq, and_self, false_and, and_false, ite_false,
    ite_true, mul_zero, sub_zero, zero_sub, mul_one]
  norm_num

/-- The uniform PPP row is a coefficient identity in the entire original
normalized degree-`d+1` BP equation, including its signed cotangent pullback. -/
theorem normalized_plane_three_points_row (d : ℕ) (hd : 0 < d) :
    let p := normalizedGenusTwoTerms .plane (3 * d - 1) ![d + 1] 0
      (SurfaceGenusZero.pointLabels ![.point, .point, .point] (3 * d - 1))
    let f := fun q : SurfaceQuery .plane ↦ RationalTerms.coefficient p {Sum.inr q}
    (f (SurfaceQuery.points .plane 2 ![d] (3 * d + 1)),
      f (SurfaceFirstDescendant.query 2 ![d] .hyperplane (3 * d)),
      f (SurfaceFirstDescendant.query 2 ![d] .point (3 * d - 1))) =
        (0, -18, 18 * (d : ℚ)) := by
  have hf (q : SurfaceQuery .plane) (hq : q.beta = ![d]) :
      RationalTerms.coefficient (normalizedGenusTwoTerms .plane (3 * d - 1) ![d + 1] 0
        (SurfaceGenusZero.pointLabels ![.point, .point, .point] (3 * d - 1))) {Sum.inr q} =
        planeRemainderPointCoefficient (3 * d - 1) ![1] ![.point, .point, .point] (.inr q) := by
    have hc : SurfaceGenusZero.variableCurve (Sum.inr q : Variable .plane) + ![1] =
        (![d + 1] : SurfaceTarget.plane.Curve) := by
      change q.beta + ![1] = _
      rw [hq]
      funext i
      fin_cases i
      rfl
    rw [← pointCoefficient_eq_full, ← hc, ← planeRemainderPointCoefficient_eq]
  dsimp only
  rw [hf _ rfl, hf _ rfl, hf _ rfl]
  exact planeRemainderPointCoefficient_three_points_row d hd

end AxiomaticGW.BelorousskiPandharipande

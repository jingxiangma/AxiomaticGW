/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneMixedRows
public import Mathlib.Data.Nat.Choose.Cast

/-!
# The two-hyperplane row of the shifted plane equations

The HHP row retains the classical outer rational component and the line
remainder on the inner component. Its two main point states have equal
single-psi coefficients, so their signed contributions cancel only after
both terms have been included.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusZero

/-- A line through two external points has a hyperplane at the middle node,
and none of the additional point markings lies on this component. -/
theorem sum_binomial_primary_plane_point_node_point (f : ℕ → ℚ) (n : ℕ)
    (b : SurfaceBasisLabel .plane) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * primaryScalar .plane (pointValue .plane) ![1] ij.2
        (![.point, b, .point] : Fin 3 → _))) =
      if b = .hyperplane then f n else 0 := by
  rw [sum_binomial_primary_plane_one]
  cases b with
  | exceptional i => exact Fin.elim0 i
  | unit | point => rfl
  | hyperplane =>
    change (n.choose 0 : ℚ) * f (n - 0) = f n
    rw [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul]

end AxiomaticGW.SurfaceGenusZero

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction GluingExpression

/-- The inner line through two points places a hyperplane on its main node.
The classical two-point rational branch vanishes, for arbitrary main data. -/
theorem remainderContraction_plane_inner_two_points_line (v : Variable .plane)
    (main : ℕ → SurfaceCotangentVertexValues .plane ℚ) (n : ℕ) (k : Fin 1 → ℕ) :
    remainderContraction .plane v main
      (GetzlerGraphs.join (m := 0) (n := 2) 0 1
        (fundamental 2 (Fin 1) (by norm_num [StableArity]))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (by exact (k, (0 : Fin 3 → ℕ)))
      (by exact ((inferInstance : DecidableEq (Fin 1)),
        (inferInstance : DecidableEq (Fin 3)))) ![1] n ![.point, .point] =
      main n 2 (Fin 1) (by norm_num [StableArity]) k inferInstance 0 ![.hyperplane] := by
  rw [remainderContraction_plane_inner_join, SurfaceTarget.sum_plane_splittings_one]
  have hs (t : SurfaceBasisLabel .plane) :=
    SurfaceGenusZero.sum_binomial_primary_plane_point_node_point
      (fun m ↦ main m 2 (Fin 1) (by norm_num [StableArity]) k inferInstance 0 ![t])
      n t.dual
  simp only [hs, SurfaceGenusZero.primaryScalar_plane_zero_point_node_point,
    mul_zero, Finset.sum_const_zero, add_zero]
  rw [SurfaceBasisLabel.sum_labels]
  simp only [SurfaceBasisLabel.inverseWeight, SurfaceBasisLabel.dual,
    reduceCtorEq, ite_false, ite_true, mul_zero, one_mul, Fin.sum_univ_zero,
    zero_add, add_zero]

/-- The equal point states also allow the psi slot to be swapped when a line
remainder is present. Both sides include the same negative cotangent tail. -/
theorem remainderVertex_plane_two_points_onePsi_line_swap (v : Variable .plane) (n : ℕ) :
    remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single 0 1) inferInstance ![1] ![.point, .point] =
      remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 2)
        (by norm_num [StableArity]) (Pi.single 1 1) inferInstance ![1] ![.point, .point] := by
  have h0 : Function.update (![.point, .point] : Fin 2 → SurfaceBasisLabel .plane)
      0 .hyperplane = ![.hyperplane, .point] := by decide +kernel
  have h1 : Function.update (![.point, .point] : Fin 2 → SurfaceBasisLabel .plane)
      1 .hyperplane = ![.point, .hyperplane] := by decide +kernel
  have hq : SurfaceAncestorKey.ofLabels (X := .plane) 2 (Fin 2)
      (by norm_num [StableArity]) (SurfaceGenusZero.variableCurve v) 0
      ![.hyperplane, .point] =
      SurfaceAncestorKey.ofLabels 2 (Fin 2) (by norm_num [StableArity])
        (SurfaceGenusZero.variableCurve v) 0 ![.point, .hyperplane] := by
    apply (SurfaceAncestorKey.eq_iff _ _).mpr
    refine ⟨rfl, rfl, ?_⟩
    dsimp only [SurfaceAncestorKey.ofLabels]
    decide +kernel
  rw [remainderVertex_onePsi_plane_line, remainderVertex_onePsi_plane_line]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h0, h1]
  rw [remainderVertex_plane_primary, remainderVertex_plane_primary, hq]

end AxiomaticGW.SurfaceGenusTwo

namespace AxiomaticGW.BelorousskiPandharipande
open SurfacePolynomialReduction SurfaceGenusTwo GluingExpression

/-- The first HHP placement has a classical hyperplane/unit inner pair, or
one added point on the outer line and two classical inner hyperplanes. -/
theorem plane_paper_zero_two_hyperplanes_point (v : Variable .plane) (n : ℕ) :
    let main := remainderVertex .plane v (planeCoefficientVertex v)
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm 0) ![1] n ![.hyperplane, .hyperplane, .point] =
      main n 2 (Fin 1) (by norm_num [StableArity]) 0 inferInstance 0 ![.hyperplane] +
      (n : ℚ) * main (n - 1) 2 (Fin 1) (by norm_num [StableArity])
        0 inferInstance 0 ![.point] := by
  dsimp only
  rw [plane_paper_zero_pair]
  erw [remainderContraction_plane_hyperplane_point_join,
    remainderContraction_plane_inner_unit_zero,
    remainderContraction_plane_inner_two_hyperplanes_zero]
  rw [show (![0] : Fin 1 → ℕ) = 0 from by decide +kernel]

/-- The other first-diagram HHP placement includes the inner line branch.
Together with the outer-line contribution it gives the same primary terms. -/
theorem plane_paper_zero_point_two_hyperplanes (v : Variable .plane) (n : ℕ) :
    let main := remainderVertex .plane v (planeCoefficientVertex v)
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm 0) ![1] n ![.point, .hyperplane, .hyperplane] =
      main n 2 (Fin 1) (by norm_num [StableArity]) 0 inferInstance 0 ![.hyperplane] +
      (n : ℚ) * main (n - 1) 2 (Fin 1) (by norm_num [StableArity])
        0 inferInstance 0 ![.point] := by
  dsimp only
  rw [plane_paper_zero_pair]
  erw [remainderContraction_plane_two_hyperplanes_join,
    remainderContraction_plane_inner_unit_zero,
    remainderContraction_plane_inner_point_hyperplane_zero,
    remainderContraction_plane_inner_two_points_line]
  rw [show (![0] : Fin 1 → ℕ) = 0 from by decide +kernel]
  simp only [mul_zero, add_zero]
  exact add_comm _ _

/-- Sum the four genus-two diagrams over all six marking occurrences. The
equal-hyperplane and equal-point psi contributions cancel with their original
opposite signs; the remaining unit and mixed-state corrections are retained. -/
theorem planeRemainderPointCoefficient_two_hyperplanes_point (v : Variable .plane) (n : ℕ) :
    let main := remainderVertex .plane v (planeCoefficientVertex v)
    let R := fun m s a ↦ main m 2 (Fin 2) (by norm_num [StableArity])
      (Pi.single s 1) inferInstance 0 a
    planeRemainderPointCoefficient n ![1] ![.hyperplane, .hyperplane, .point] v =
      -12 * (main n 2 (Fin 1) (by norm_num [StableArity]) 0 inferInstance 0 ![.hyperplane] +
        (n : ℚ) * main (n - 1) 2 (Fin 1) (by norm_num [StableArity])
          0 inferInstance 0 ![.point]) +
      12 * (main n 2 (Fin 1) (by norm_num [StableArity])
        (Pi.single 0 1) inferInstance 0 ![.unit] +
        (n : ℚ) * main (n - 1) 2 (Fin 1) (by norm_num [StableArity])
          (Pi.single 0 1) inferInstance 0 ![.hyperplane]) +
      12 * (R n 0 ![.hyperplane, .unit] - R n 1 ![.hyperplane, .unit]) +
      6 * (n : ℚ) * (R (n - 1) 0 ![.point, .unit] - R (n - 1) 1 ![.point, .unit]) +
      6 * (n.choose 2 : ℚ) * (R (n - 2) 0 ![.point, .hyperplane] -
        R (n - 2) 1 ![.point, .hyperplane]) := by
  let f := fun i a ↦ remainderPointCoefficient .plane v (planeCoefficientVertex v)
    (paperCotangentTerm i) ![1] n a
  have hs (i : Fin 4) : f (Fin.castAdd 16 i) ![.hyperplane, .point, .hyperplane] =
      f (Fin.castAdd 16 i) ![.hyperplane, .hyperplane, .point] :=
    plane_paper_first_four_swap_right v n ![1] i _ _ _
  have hs0 : f 0 ![.hyperplane, .point, .hyperplane] =
      f 0 ![.hyperplane, .hyperplane, .point] := hs 0
  have hs1 : f 1 ![.hyperplane, .point, .hyperplane] =
      f 1 ![.hyperplane, .hyperplane, .point] := hs 1
  have hs2 : f 2 ![.hyperplane, .point, .hyperplane] =
      f 2 ![.hyperplane, .hyperplane, .point] := hs 2
  have hs3 : f 3 ![.hyperplane, .point, .hyperplane] =
      f 3 ![.hyperplane, .hyperplane, .point] := hs 3
  have h1 : f 1 ![.point, .hyperplane, .hyperplane] = f 1 ![.hyperplane, .hyperplane, .point] :=
    (plane_paper_one_swap_left v n ![1] _ _ _).trans hs1
  have h2 := plane_paper_onePsi_hyperplane_point v n (0 : Fin 2) .hyperplane
  have h3 := plane_paper_onePsi_hyperplane_point v n (1 : Fin 2) .hyperplane
  have h2' := plane_paper_onePsi_two_hyperplanes v n (0 : Fin 2) .point
  have h3' := plane_paper_onePsi_two_hyperplanes v n (1 : Fin 2) .point
  simp only [ite_true] at h2 h2'
  simp only [if_neg (by decide : (1 : Fin 2) ≠ 0)] at h3 h3'
  dsimp only
  unfold planeRemainderPointCoefficient
  simp only [sum_plane_remainder_orbit, Fin.sum_univ_four]
  change (-2 : ℚ) *
      (f 0 ![.hyperplane, .hyperplane, .point] + f 0 ![.hyperplane, .point, .hyperplane] +
        f 0 ![.hyperplane, .hyperplane, .point] + f 0 ![.point, .hyperplane, .hyperplane] +
        f 0 ![.hyperplane, .point, .hyperplane] + f 0 ![.point, .hyperplane, .hyperplane]) +
    2 * (f 1 ![.hyperplane, .hyperplane, .point] + f 1 ![.hyperplane, .point, .hyperplane] +
        f 1 ![.hyperplane, .hyperplane, .point] + f 1 ![.point, .hyperplane, .hyperplane] +
        f 1 ![.hyperplane, .point, .hyperplane] + f 1 ![.point, .hyperplane, .hyperplane]) +
    3 * (f 2 ![.hyperplane, .hyperplane, .point] + f 2 ![.hyperplane, .point, .hyperplane] +
        f 2 ![.hyperplane, .hyperplane, .point] + f 2 ![.point, .hyperplane, .hyperplane] +
        f 2 ![.hyperplane, .point, .hyperplane] + f 2 ![.point, .hyperplane, .hyperplane]) +
    (-3) * (f 3 ![.hyperplane, .hyperplane, .point] + f 3 ![.hyperplane, .point, .hyperplane] +
        f 3 ![.hyperplane, .hyperplane, .point] + f 3 ![.point, .hyperplane, .hyperplane] +
        f 3 ![.hyperplane, .point, .hyperplane] + f 3 ![.point, .hyperplane, .hyperplane]) = _
  rw [hs0, hs1, hs2, hs3, h1]
  dsimp only [f]
  rw [plane_paper_zero_two_hyperplanes_point, plane_paper_zero_point_two_hyperplanes,
    plane_paper_one_two_hyperplanes_point, h2, h3, h2', h3']
  rw [remainderVertex_plane_two_points_onePsi_line_swap,
    remainderVertex_plane_two_hyperplanes_onePsi,
    remainderVertex_plane_two_hyperplanes_onePsi]
  rw [show (![1] : Fin 1 → ℕ) = Pi.single 0 1 from by decide +kernel]
  ring

/-- At one degree of remainder, HHP has only the canonical primary and first
descendant requests. The dimension guard and binomial factors retain the
zero- and one-point boundaries without natural-subtraction artifacts. -/
theorem planeRemainderPointCoefficient_two_hyperplanes_point_canonical
    (v : Variable .plane) (n : ℕ) :
    let d := SurfaceGenusZero.variableCurve v 0
    planeRemainderPointCoefficient n ![1] ![.hyperplane, .hyperplane, .point] v =
      if n = 3 * d + 1 then
        (24 - 36 * (d : ℚ) - 24 * (n : ℚ)) *
          (if Sum.inr (SurfaceQuery.points .plane 2 ![d] n) = v then 1 else 0) +
        (12 * (n : ℚ) - 6 * (n.choose 2 : ℚ)) *
          (if Sum.inr (SurfaceFirstDescendant.query 2 ![d] .hyperplane (n - 1)) = v
            then 1 else 0) +
        6 * (n.choose 2 : ℚ) * (d : ℚ) *
          (if Sum.inr (SurfaceFirstDescendant.query 2 ![d] .point (n - 2)) = v
            then 1 else 0)
      else 0 := by
  have mh : Finset.univ.val.map (![.hyperplane] : Fin 1 → SurfaceBasisLabel .plane) =
      {.hyperplane} := by decide +kernel
  have mp : Finset.univ.val.map (![.point] : Fin 1 → SurfaceBasisLabel .plane) =
      {.point} := by decide +kernel
  have huH : SurfaceBasisLabel.unit ∉
      Finset.univ.val.map (![.hyperplane] : Fin 1 → SurfaceBasisLabel .plane) := by
    rw [mh]
    decide
  have huP : SurfaceBasisLabel.unit ∉
      Finset.univ.val.map (![.point] : Fin 1 → SurfaceBasisLabel .plane) := by
    rw [mp]
    decide
  dsimp only
  rw [planeRemainderPointCoefficient_two_hyperplanes_point]
  dsimp only
  rw [remainderVertex_plane_primary_canonical _ _ _ _ _ _ huH,
    remainderVertex_plane_primary_canonical _ _ _ _ _ _ huP,
    remainderVertex_plane_single_unit_onePsi,
    remainderVertex_plane_single_hyperplane_onePsi,
    remainderVertex_plane_pair_primary_unit v n .hyperplane (by decide),
    remainderVertex_plane_pair_unit_onePsi v n .hyperplane (by decide),
    remainderVertex_plane_pair_primary_unit v (n - 1) .point (by decide),
    remainderVertex_plane_pair_unit_onePsi v (n - 1) .point (by decide),
    remainderVertex_plane_point_hyperplane, remainderVertex_plane_point_hyperplane]
  simp only [mh, mp, Multiset.count_singleton, reduceCtorEq, ite_false, ite_true,
    pow_zero, pow_one, one_mul, mul_one, add_zero,
    if_neg (by decide : (1 : Fin 2) ≠ 0)]
  by_cases hn0 : n = 0
  · subst n
    have hd : ¬0 = 3 * SurfaceGenusZero.variableCurve v 0 + 1 := by omega
    simp only [if_neg hd, Nat.cast_zero, Nat.choose_eq_zero_of_lt (by omega : 0 < 2),
      mul_zero, zero_mul, add_zero, sub_self]
  · have hn : n - 1 + 1 = n := by omega
    have he : n - 1 = 3 * SurfaceGenusZero.variableCurve v 0 ↔
        n = 3 * SurfaceGenusZero.variableCurve v 0 + 1 := by omega
    simp only [hn, he]
    by_cases hn1 : n = 1
    · subst n
      simp only [Nat.choose_eq_zero_of_lt (by omega : 1 < 2), Nat.cast_zero,
        mul_zero, zero_mul, add_zero]
      split_ifs <;> ring
    · have hn' : n - 2 + 1 = n - 1 := by omega
      simp only [hn', he]
      split_ifs <;> ring

/-- The full normalized HHP equation has this coefficient on every variable
of degree d, including higher-ancestor tags and noncanonical marking counts. -/
theorem normalized_plane_two_hyperplanes_point_canonical (d : ℕ) (v : Variable .plane)
    (hv : SurfaceGenusZero.variableCurve v = ![d]) :
    RationalTerms.coefficient (normalizedGenusTwoTerms .plane (3 * d + 1) ![d + 1] 0
      (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .point] (3 * d + 1))) {v} =
      -108 * (d : ℚ) *
        (if Sum.inr (SurfaceQuery.points .plane 2 ![d] (3 * d + 1)) = v then 1 else 0) +
      (-27 * (d : ℚ) ^ 2 + 27 * (d : ℚ) + 12) *
        (if Sum.inr (SurfaceFirstDescendant.query 2 ![d] .hyperplane (3 * d)) = v
          then 1 else 0) +
      (27 * (d : ℚ) ^ 3 + 9 * (d : ℚ) ^ 2) *
        (if Sum.inr (SurfaceFirstDescendant.query 2 ![d] .point (3 * d - 1)) = v
          then 1 else 0) := by
  have hc : SurfaceGenusZero.variableCurve v + ![1] =
      (![d + 1] : SurfaceTarget.plane.Curve) := by
    rw [hv]
    funext i
    fin_cases i
    rfl
  have hn : 3 * d + 1 - 2 = 3 * d - 1 := by omega
  rw [← pointCoefficient_eq_full, ← hc, ← planeRemainderPointCoefficient_eq,
    planeRemainderPointCoefficient_two_hyperplanes_point_canonical]
  simp only [hv, Matrix.cons_val_zero, ite_true, Nat.add_sub_cancel, hn,
    Nat.cast_choose_two, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

/-- The complete HHP row in primary/hyperplane-descendant/point-descendant
order. Its degree-zero row is included; no invariant value is assumed here. -/
theorem normalized_plane_two_hyperplanes_point_row (d : ℕ) :
    let p := normalizedGenusTwoTerms .plane (3 * d + 1) ![d + 1] 0
      (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .point] (3 * d + 1))
    let f := fun q : SurfaceQuery .plane ↦ RationalTerms.coefficient p {Sum.inr q}
    (f (SurfaceQuery.points .plane 2 ![d] (3 * d + 1)),
      f (SurfaceFirstDescendant.query 2 ![d] .hyperplane (3 * d)),
      f (SurfaceFirstDescendant.query 2 ![d] .point (3 * d - 1))) =
        (-108 * (d : ℚ), -27 * (d : ℚ) ^ 2 + 27 * (d : ℚ) + 12,
          27 * (d : ℚ) ^ 3 + 9 * (d : ℚ) ^ 2) := by
  dsimp only
  rw [normalized_plane_two_hyperplanes_point_canonical d _ rfl,
    normalized_plane_two_hyperplanes_point_canonical d _ rfl,
    normalized_plane_two_hyperplanes_point_canonical d _ rfl]
  simp only [SurfaceQuery.points, SurfaceFirstDescendant.query,
    Sum.inr.injEq, SurfaceQuery.mk.injEq, List.replicate_succ, List.cons.injEq,
    SurfaceInsertion.mk.injEq, reduceCtorEq, and_self, false_and, and_false,
    ite_false, ite_true, mul_zero, mul_one, zero_add, add_zero]

/-- Removing the three canonical degree-d variables leaves only strictly
smaller degrees in the complete normalized HHP equation. -/
theorem normalized_plane_two_hyperplanes_point_lower (d : ℕ) (v : Variable .plane)
    (hN : Sum.inr (SurfaceQuery.points .plane 2 ![d] (3 * d + 1)) ≠ v)
    (hH : Sum.inr (SurfaceFirstDescendant.query 2 ![d] .hyperplane (3 * d)) ≠ v)
    (hP : Sum.inr (SurfaceFirstDescendant.query 2 ![d] .point (3 * d - 1)) ≠ v)
    (hc : RationalTerms.coefficient
      (normalizedGenusTwoTerms .plane (3 * d + 1) ![d + 1] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .point] (3 * d + 1)))
      {v} ≠ 0) :
    SurfaceGenusZero.variableCurve v 0 < d := by
  have hb := normalized_plane_two_hyperplanes_degree_lt v (3 * d + 1) (d + 1) hc
  have hn : SurfaceGenusZero.variableCurve v 0 ≠ d := by
    intro he
    have hv : SurfaceGenusZero.variableCurve v = ![d] := by
      funext i
      fin_cases i
      exact he
    rw [normalized_plane_two_hyperplanes_point_canonical d v hv] at hc
    simp only [if_neg hN, if_neg hH, if_neg hP, mul_zero, add_zero, ne_eq,
      not_true_eq_false] at hc
  omega

end AxiomaticGW.BelorousskiPandharipande

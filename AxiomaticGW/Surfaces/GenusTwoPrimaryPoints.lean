/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PrimaryPointPullback
public import AxiomaticGW.Surfaces.GenusTwoPointCoefficients
public import AxiomaticGW.Surfaces.GenusZeroScalar
public import AxiomaticGW.Surfaces.PlaneNormalization

/-!
# Closed primary rational components in genus-two coefficients

The reconstructed constant on a primary rational component agrees with the
existing scalar primary formula, including the signed dimension condition,
classical degree zero and all divisor signs. This identifies the rational
factors in signed point contraction without evaluating the marking recursion.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction

/-- A primary genus-two component also reduces to a single insertion key;
only its requested normalized coefficient is retained. -/
theorem vertex_primary_genusTwo_eq {X : SurfaceTarget} (v : Variable X)
    (n : ℕ) (S : Type) [Fintype S] (h : StableArity 2 S) (l : DecidableEq S)
    (beta : X.Curve) (a : S → SurfaceBasisLabel X) :
    SurfacePointPullback.vertex X (coefficientVertex X v) n 2 S h 0 l beta a =
      RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
        (residualTerms ((SurfaceAncestorKey.ofLabels 2 S h beta 0 a).addPoints n))) {v} := by
  exact SurfacePointPullback.vertex_primary_eq X (coefficientVertex X v)
    (fun q ↦ RationalTerms.coefficient
      (RationalTerms.affineSubstitute normalizedTerms (residualTerms q)) {v}) 2
    (fun T _ h gamma b ↦ by simp only [coefficientVertex, ite_true, vertexTerms])
    n S h l beta a

/-- A primary unit on the main component vanishes after any number of point
pullbacks, including at zero curve class and with repeated original labels. -/
theorem vertex_primary_genusTwo_unit_zero {X : SurfaceTarget} (v : Variable X)
    (n : ℕ) (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S)
    (beta : X.Curve) (a : S → SurfaceBasisLabel X) (s : S) :
    SurfacePointPullback.vertex X (coefficientVertex X v) n 2 S h 0 inferInstance
      beta (Function.update a s .unit) = 0 := by
  rw [vertex_primary_genusTwo_eq]
  let q := (SurfaceAncestorKey.ofLabels 2 S h beta 0 (Function.update a s .unit)).addPoints n
  have hp : q.IsPrimary := by
    intro t ht
    rcases Multiset.mem_add.mp ht with ht | ht
    · exact congrArg SurfaceInsertion.psi (Multiset.mem_replicate.mp ht).2
    · obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp ht
      rfl
  have hu : SurfaceBasisLabel.unit ∈ q.primaryLabels := by
    apply Multiset.mem_map.mpr
    refine ⟨⟨.unit, 0⟩, Multiset.mem_add.mpr (Or.inr ?_), rfl⟩
    apply Multiset.mem_map.mpr
    exact ⟨s, Finset.mem_univ s, by simp only [Function.update_self, Pi.zero_apply]⟩
  have hn : ¬(2 ≤ q.genus ∧ q.totalPsi = 1) := by
    rw [q.totalPsi_eq_zero_iff.mpr hp]
    exact fun h ↦ Nat.zero_ne_one h.2
  change RationalTerms.coefficient
    (RationalTerms.affineSubstitute normalizedTerms (residualTerms q)) {v} = 0
  simp only [residualTerms, if_neg (show ¬q.genus ≤ 1 from Nat.not_succ_le_self 1)]
  split_ifs with hd
  · simp only [RationalTerms.coefficient_affineSubstitute_term,
      Multiset.map_singleton, Multiset.sum_singleton, one_mul]
    rw [normalizedTerms, dif_neg hn, canonicalPrimaryTerms, if_pos ⟨le_rfl, hp⟩,
      primaryTerms_unit_zero _ _ _ hu]
    rfl
  · exact RationalTerms.coefficient_affineSubstitute_zero _ _

/-- Primary rational constants agree with evaluation of the original reduction. -/
theorem coefficient_residualTerms_genusZero_primary {X : SurfaceTarget}
    (q : SurfaceAncestorKey X) (hg : q.genus = 0) (hp : q.IsPrimary) :
    RationalTerms.coefficient (residualTerms q) 0 =
      RationalTerms.eval (fun u ↦ SurfaceGenusZero.pointValue X
        (SurfaceGenusZero.variableCurve u)) (primaryTerms q) := by
  rw [SurfaceGenusZero.eval_primaryTerms_curve _ q hg hp]
  by_cases hd : q.DimensionCompatible
  · rw [residualTerms, if_pos hd, if_pos (by omega : q.genus ≤ 1),
      RationalTerms.coefficient_term, if_pos rfl, SurfaceGenusOne.componentValue, if_pos hg,
      SurfaceGenusZero.ancestorValue, q.totalPsi_eq_zero_iff.mpr hp,
      SurfaceGenusZero.ancestorValueFuel, if_pos ⟨hg, hp⟩, if_pos hd]
    unfold SurfaceGenusZero.primaryValue
    by_cases hb : q.beta = 0
    · rw [if_pos hb, if_pos hb]
    · rw [if_neg hb, if_neg hb]
      by_cases hc : q.primaryCoefficient = 0
      · change (if _ then q.primaryCoefficient * _ else 0) = _
        rw [hc, zero_mul, ite_self]
      · rw [if_pos (q.point_count_of_genus_zero hg hp hd hc)]
        rfl
  · rw [residualTerms, if_neg hd, RationalTerms.coefficient_zero, if_neg hd]

/-- Every added primary point is accounted for by the closed genus-zero scalar. -/
theorem vertex_primary_genusZero_eq {X : SurfaceTarget} (v : Variable X)
    (n : ℕ) (S : Type) [Fintype S] (h : StableArity 0 S) (l : DecidableEq S)
    (beta : X.Curve) (a : S → SurfaceBasisLabel X) :
    SurfacePointPullback.vertex X (coefficientVertex X v) n 0 S h 0 l beta a =
      SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) beta n a := by
  rw [SurfacePointPullback.vertex_primary_eq X (coefficientVertex X v)
    (fun q ↦ RationalTerms.coefficient (residualTerms q) 0) 0
    (fun T _ h gamma b ↦ by
      simp only [coefficientVertex, Nat.reduceEqDiff, ite_false, vertexTerms])]
  rw [SurfaceGenusZero.primaryScalar_eq _ S h beta n a]
  apply coefficient_residualTerms_genusZero_primary _ rfl
  intro s hs
  rcases Multiset.mem_add.mp hs with hs | hs
  · exact congrArg SurfaceInsertion.psi (Multiset.mem_replicate.mp hs).2
  · obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hs
    rfl

/-- Use the closed primary scalar precisely on undecorated rational vertices. -/
def primaryPointVertex (X : SurfaceTarget) (v : Variable X) (n : ℕ) :
    SurfaceCotangentVertexValues X ℚ :=
  fun g S _ h d l beta a ↦
    if g = 0 ∧ d = 0 then
      SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) beta n a
    else SurfacePointPullback.vertex X (coefficientVertex X v) n g S h d l beta a

/-- The shortcut preserves all component values, including nonzero powers. -/
theorem primaryPointVertex_eq (X : SurfaceTarget) (v : Variable X) :
    primaryPointVertex X v = SurfacePointPullback.vertex X (coefficientVertex X v) := by
  funext n g S _ h d l beta a
  unfold primaryPointVertex
  split_ifs with hz
  · obtain ⟨rfl, rfl⟩ := hz
    exact (vertex_primary_genusZero_eq v n S h l beta a).symm
  · rfl

/-- A stable primary degree-zero rational component admits no added points. -/
theorem vertex_primary_genusZero_zero_of_pos {X : SurfaceTarget} (v : Variable X)
    (n : ℕ) (hn : 0 < n) (S : Type) [Fintype S] (h : StableArity 0 S)
    (l : DecidableEq S) (a : S → SurfaceBasisLabel X) :
    SurfacePointPullback.vertex X (coefficientVertex X v) n 0 S h 0 l 0 a = 0 := by
  rw [vertex_primary_genusZero_eq]
  have hs : 3 ≤ Fintype.card S := by
    simpa only [StableArity, mul_zero, zero_add] using h
  have hcard : n + Fintype.card S ≠ 3 := by omega
  simp only [SurfaceGenusZero.primaryScalar, ne_eq, not_true_eq_false, false_and,
    ite_true, if_neg hcard, ite_self]

/-- A stable primary zero-class component forces all added points to the
other side of an edge, with the original classical factor retained. -/
theorem sum_binomial_primary_zero {X : SurfaceTarget} (v : Variable X)
    (f : ℕ → ℚ) (n : ℕ) (S : Type) [Fintype S] (h : StableArity 0 S)
    (l : DecidableEq S) (a : S → SurfaceBasisLabel X) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * SurfacePointPullback.vertex X (coefficientVertex X v)
        ij.2 0 S h 0 l 0 a)) =
      f n * coefficientVertex X v 0 S h 0 0 a := by
  rw [SurfacePointPullback.sum_binomial_of_right_support f _ n 0
    (fun j hj ↦ vertex_primary_genusZero_zero_of_pos v j (Nat.pos_of_ne_zero hj) S h l a)]
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul,
    SurfacePointPullback.vertex]

end AxiomaticGW.SurfaceGenusTwo

namespace AxiomaticGW.SurfaceGenusZero

/-- In plane degree one, primary insertions contribute one precisely when
there is no unit and exactly two points in total. -/
theorem primaryScalar_plane_one (n : ℕ) {S : Type} [Fintype S]
    (a : S → SurfaceBasisLabel .plane) :
    primaryScalar .plane (pointValue .plane) ![1] n a =
      if .unit ∈ (Finset.univ.val.map a) then 0 else
        if n + (Finset.univ.val.map a).count .point = 2 then 1 else 0 := by
  have hv : pointValue .plane ![1] = 1 := by
    rw [pointValue_initial .plane ![1] (Or.inr (by decide +kernel))]
    decide +kernel
  have hb : (![1] : SurfaceTarget.plane.Curve) ≠ 0 := by decide
  have he : SurfaceTarget.plane.c1Degree ![1] = 3 := by decide +kernel
  have hf : (∏ s, (a s).primaryFactor ![1]) =
      if .unit ∈ Finset.univ.val.map a then (0 : ℚ) else 1 := by
    have hf := SurfaceFirstDescendant.primaryCoefficient_plane 1 (Finset.univ.val.map a)
    simpa only [SurfaceFirstDescendant.primaryCoefficient, Multiset.map_map,
      Function.comp_def, Nat.cast_one, one_pow, Finset.prod_eq_multiset_prod] using hf
  rw [primaryScalar, hv, if_neg (by norm_num), he, if_neg hb, hf, mul_one]
  by_cases hu : SurfaceBasisLabel.unit ∈ Finset.univ.val.map a
  · simp only [if_pos hu, ite_self]
  · rw [if_neg hu]
    have hc := SurfaceBasisLabel.sum_codimension_add_units (Finset.univ.val.map a)
    rw [Multiset.count_eq_zero.mpr hu, add_zero, Multiset.card_map,
      Finset.card_val, Finset.card_univ, Multiset.map_map] at hc
    have hd : ((∑ s, (a s).codimension : ℕ) : ℤ) + (n : ℤ) =
        3 - 1 + (Fintype.card S : ℤ) ↔
        n + (Finset.univ.val.map a).count .point = 2 := by
      change (∑ s, (a s).codimension) = _ at hc
      omega
    simp only [hd, if_neg hu]

/-- A line component leaves a single binomial placement count. The guard
keeps excess original points separate from natural-number subtraction. -/
theorem sum_binomial_primary_plane_one (f : ℕ → ℚ) (n : ℕ)
    {S : Type} [Fintype S] (a : S → SurfaceBasisLabel .plane) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * primaryScalar .plane (pointValue .plane) ![1] ij.2 a)) =
      if .unit ∈ Finset.univ.val.map a then 0 else
        if (Finset.univ.val.map a).count .point ≤ 2 then
          (n.choose (2 - (Finset.univ.val.map a).count .point) : ℚ) *
            f (n - (2 - (Finset.univ.val.map a).count .point))
        else 0 := by
  by_cases hu : SurfaceBasisLabel.unit ∈ Finset.univ.val.map a
  · simp only [primaryScalar_plane_one, if_pos hu, mul_zero, Finset.sum_const_zero]
  · by_cases hp : (Finset.univ.val.map a).count .point ≤ 2
    · rw [if_neg hu, if_pos hp, SurfacePointPullback.sum_binomial_of_right_support
        f (fun j ↦ primaryScalar .plane (pointValue .plane) ![1] j a)
        n (2 - (Finset.univ.val.map a).count .point) (by
          intro j hj
          rw [primaryScalar_plane_one, if_neg hu, if_neg (by omega)])]
      rw [primaryScalar_plane_one, if_neg hu, if_pos (by omega), mul_one]
    · rw [if_neg hu, if_neg hp]
      apply Finset.sum_eq_zero
      intro ij _
      rw [primaryScalar_plane_one, if_neg hu, if_neg (by omega), mul_zero, mul_zero]

end AxiomaticGW.SurfaceGenusZero

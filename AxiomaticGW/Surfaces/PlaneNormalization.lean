/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.OnePsiSupport
public import AxiomaticGW.Surfaces.Fixtures.FirstCalibration

/-!
# Plane normalization and canonical coefficient formulas

The plane first calibration has image in the unit direction. Every correction
in the genus-at-least-two normalizer is therefore a primary unit term and
vanishes by the existing string reduction. Equality holds for the complete
uncollected expression, at every degree; no geometric input or new seed is
added. Divisor counts and the signed dimension condition give closed formulas
for its primary and first-descendant terms, including degree zero.
-/

@[expose] public section

namespace AxiomaticGW
namespace SurfaceFirstCalibration

/-- The sparse first calibration can output only the unit on the plane. -/
theorem plane_row_zero (beta : SurfaceTarget.plane.Curve)
    (row col : SurfaceBasisLabel .plane) (hr : row ≠ .unit) :
    SurfaceDescendant.firstCalibrationMatrix .plane beta row col = 0 := by
  rw [← values_eq, values]
  split_ifs <;> first | rfl | exact if_neg (fun h ↦ hr h.1)

end SurfaceFirstCalibration
namespace SurfacePolynomialReduction

/-- A primary unit kills the canonical string/divisor reduction. -/
theorem primaryTerms_unit_zero {X : SurfaceTarget} (g : ℕ) (beta : X.Curve)
    (m : Multiset (SurfaceBasisLabel X)) (hm : .unit ∈ m) :
    SurfaceFirstDescendant.primaryTerms g beta m = 0 := by
  obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem hm
  simp only [SurfaceFirstDescendant.primaryTerms, SurfaceFirstDescendant.primaryCoefficient_cons,
    SurfaceBasisLabel.primaryFactor, zero_mul, RationalTerms.scale, ite_true]

private theorem primary_update_unit_zero {X : SurfaceTarget} (g : ℕ) (hg : 2 ≤ g)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity g S)
    (beta : X.Curve) (a : S → SurfaceBasisLabel X) (s : S) :
    canonicalPrimaryTerms (SurfaceAncestorKey.ofLabels g S h beta 0
      (Function.update a s .unit)) = 0 := by
  have hp : (SurfaceAncestorKey.ofLabels g S h beta 0 (Function.update a s .unit)).IsPrimary := by
    rw [← SurfaceAncestorKey.totalPsi_eq_zero_iff, SurfaceAncestorKey.totalPsi_ofLabels]
    exact Finset.sum_const_zero
  have hu : SurfaceBasisLabel.unit ∈
      (SurfaceAncestorKey.ofLabels g S h beta 0 (Function.update a s .unit)).primaryLabels := by
    simp only [SurfaceAncestorKey.primaryLabels, SurfaceAncestorKey.ofLabels, Multiset.map_map]
    apply Multiset.mem_map.mpr
    exact ⟨s, Finset.mem_univ s, by simp only [Function.comp_apply, Function.update_self]⟩
  rw [canonicalPrimaryTerms, if_pos ⟨hg, hp⟩, primaryTerms_unit_zero _ _ _ hu]
  rfl

/-- Every plane normalization tail vanishes as an entire primary-unit term.
The low-genus and higher-power branches are unchanged by both normalizers. -/
theorem normalizedTerms_plane_eq_direct (q : SurfaceAncestorKey .plane) :
    normalizedTerms q = directNormalizedTerms q := by
  unfold normalizedTerms directNormalizedTerms
  split_ifs with h
  · suffices hz : (∑ split ∈ SurfaceTarget.plane.positiveTailSplittings q.beta,
        ∑ b : SurfaceBasisLabel .plane,
          RationalTerms.scale
            (-SurfaceDescendant.firstCalibrationMatrix .plane split.2 b
              (q.orderedLabels (q.onePsiMark h.2)))
            (canonicalPrimaryTerms (SurfaceAncestorKey.ofLabels q.genus
              (Fin q.orderedInsertions.length) q.ordered_stable split.1 0
              (Function.update q.orderedLabels (q.onePsiMark h.2) b)))) = 0 by
      rw [hz, add_zero]
    apply Finset.sum_eq_zero
    intro split hs
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : b = .unit
    · subst b
      rw [primary_update_unit_zero _ h.1]
      unfold RationalTerms.scale
      split_ifs <;> rfl
    · rw [SurfaceFirstCalibration.plane_row_zero _ _ _ hb]
      simp only [neg_zero, RationalTerms.scale, ite_true]
  · rfl

/-- The cancellation holds simultaneously in every plane expression. -/
theorem affineSubstitute_normalizedTerms_plane_eq
    (p : RationalTerms (SurfaceAncestorKey .plane)) :
    RationalTerms.affineSubstitute normalizedTerms p =
      RationalTerms.affineSubstitute directNormalizedTerms p := by
  exact congrArg (fun f ↦ RationalTerms.affineSubstitute f p)
    (funext normalizedTerms_plane_eq_direct)

/-- A plane normalization term keeps the complete original curve class. -/
theorem normalizedTerms_plane_support (q : SurfaceAncestorKey .plane) (hg : 2 ≤ q.genus)
    {t : ℚ × Multiset (Variable .plane)} (ht : t ∈ normalizedTerms q) :
    ∃ v, t.2 = {v} ∧ SurfaceLowGenus.variableGenus v = q.genus ∧
      SurfaceGenusZero.variableCurve v = q.beta ∧ variableDimensionCompatible v := by
  rw [normalizedTerms_plane_eq_direct] at ht
  exact directNormalizedTerms_support q hg ht

end SurfacePolynomialReduction
end AxiomaticGW

namespace AxiomaticGW.SurfaceFirstDescendant

/-- A primary hyperplane contributes the degree; a primary unit gives zero.
The empty product at degree zero is retained as `0 ^ 0 = 1`. -/
theorem primaryCoefficient_plane (d : ℕ) (m : Multiset (SurfaceBasisLabel .plane)) :
    primaryCoefficient ![d] m =
      if .unit ∈ m then 0 else (d : ℚ) ^ m.count .hyperplane := by
  induction m using Multiset.induction_on with
  | empty =>
    simp only [primaryCoefficient, Multiset.map_zero, Multiset.prod_zero,
      Multiset.notMem_zero, ite_false, Multiset.count_zero, pow_zero]
  | cons b m ih =>
    rw [primaryCoefficient_cons, ih]
    cases b with
    | unit =>
      simp only [SurfaceBasisLabel.primaryFactor, zero_mul,
        Multiset.mem_cons, true_or, ite_true]
    | hyperplane =>
      have hf : (SurfaceBasisLabel.hyperplane : SurfaceBasisLabel .plane).primaryFactor ![d] =
          (d : ℚ) := by
        change ((d : ℤ) : ℚ) = d
        exact Int.cast_natCast d
      rw [hf]
      simp only [Multiset.mem_cons, reduceCtorEq, false_or, Multiset.count_cons_self]
      split_ifs <;> simp only [mul_zero, pow_succ']
    | exceptional i => exact Fin.elim0 i
    | point =>
      simp only [SurfaceBasisLabel.primaryFactor, one_mul, Multiset.mem_cons,
        reduceCtorEq, false_or, Multiset.count_cons_of_ne
          (by decide : (SurfaceBasisLabel.hyperplane : SurfaceBasisLabel .plane) ≠ .point)]

/-- Closed primary normalization retains the exact residual point count. -/
theorem primaryTerms_plane (g d : ℕ) (m : Multiset (SurfaceBasisLabel .plane)) :
    primaryTerms g ![d] m =
      if .unit ∈ m then 0 else
        RationalTerms.scale ((d : ℚ) ^ m.count .hyperplane)
          (dimensionTerms (SurfaceQuery.points .plane g ![d] (m.count .point))) := by
  rw [primaryTerms, primaryCoefficient_plane]
  split_ifs <;> simp only [RationalTerms.scale, ite_true]

/-- A point descendant has no divisor-product correction. -/
theorem terms_plane_point (g d : ℕ) (m : Multiset (SurfaceBasisLabel .plane))
    (hu : .unit ∉ m) :
    terms g ![d] .point m = RationalTerms.scale ((d : ℚ) ^ m.count .hyperplane)
      (dimensionTerms (query g ![d] .point (m.count .point))) := by
  simp only [terms, if_neg hu, reduceCtorEq, ite_false, primaryCoefficient_plane,
    correctionCoefficient, divisorSquare, zero_mul, RationalTerms.scale, ite_true, add_zero]

/-- Each primary hyperplane can pair with the descendant hyperplane.
The zero-count case is multiplied by zero, without division by the degree. -/
theorem terms_plane_hyperplane (g d : ℕ) (m : Multiset (SurfaceBasisLabel .plane))
    (hu : .unit ∉ m) :
    terms g ![d] .hyperplane m =
      RationalTerms.scale ((d : ℚ) ^ m.count .hyperplane)
        (dimensionTerms (query g ![d] .hyperplane (m.count .point))) +
      RationalTerms.scale ((m.count .hyperplane : ℚ) * (d : ℚ) ^ (m.count .hyperplane - 1))
        (dimensionTerms (SurfaceQuery.points .plane g ![d] (m.count .point + 1))) := by
  have hue : SurfaceBasisLabel.unit ∉ m.erase .hyperplane :=
    fun h ↦ hu (Multiset.mem_of_mem_erase h)
  simp only [terms, if_neg hu, reduceCtorEq, ite_false, primaryCoefficient_plane,
    correctionCoefficient, divisorSquare, one_mul, if_neg hue, Multiset.count_erase_self]

end AxiomaticGW.SurfaceFirstDescendant

namespace AxiomaticGW.SurfaceQuery

private theorem codimension_eq_list {X : SurfaceTarget} (q : SurfaceQuery X) :
    q.totalCodimension =
      (q.insertions.map (fun s ↦ s.label.codimension + s.psi)).sum := by
  unfold totalCodimension
  rw [← List.sum_ofFn]
  change (List.ofFn ((fun s : SurfaceInsertion X ↦ s.label.codimension + s.psi) ∘
    q.insertions.get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get]

private theorem c1_plane (d : ℕ) : SurfaceTarget.plane.c1Degree ![d] = 3 * (d : ℤ) := by
  rw [SurfaceTarget.c1Degree_eq_intersection]
  change 3 * (d : ℤ) - ∑ _ : Fin 0, _ = _
  rw [Fin.sum_univ_zero, sub_zero]

/-- The signed dimension equation fixes the canonical primary point count.
This arithmetic test does not assert that an unstable request is geometric. -/
theorem dimensionCompatible_points_plane (g d n : ℕ) :
    (points .plane g ![d] n).DimensionCompatible ↔ n + 1 = 3 * d + g := by
  rw [DimensionCompatible, codimension_eq_list]
  simp only [points, List.map_replicate, List.sum_replicate, SurfaceBasisLabel.codimension,
    add_zero, List.length_replicate, c1_plane, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  simp only [Nat.cast_id]
  omega

/-- The descendant label contributes its actual codimension to the point count. -/
theorem dimensionCompatible_first_plane (g d n : ℕ) (b : SurfaceBasisLabel .plane) :
    (SurfaceFirstDescendant.query g ![d] b n).DimensionCompatible ↔
      n + b.codimension + 1 = 3 * d + g := by
  rw [DimensionCompatible, codimension_eq_list]
  simp only [SurfaceFirstDescendant.query, List.map_cons, List.sum_cons, List.map_replicate,
    List.sum_replicate, SurfaceBasisLabel.codimension, add_zero, List.length_cons,
    List.length_replicate, c1_plane, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_one]
  simp only [Nat.cast_id]
  omega

end AxiomaticGW.SurfaceQuery

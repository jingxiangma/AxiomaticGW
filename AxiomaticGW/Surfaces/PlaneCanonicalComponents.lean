/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Coefficients.RenamedCoefficient
public import AxiomaticGW.Surfaces.PlaneMixedPointContractions

/-!
# Canonical coefficients of plane genus-two components

The primary component is reduced to its exact point query with its divisor
factor and integer dimension condition. Coefficient collection commutes with
the normalizer's renaming and scalar operations, including zero coefficients.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceFirstDescendant
open SurfacePolynomialReduction

/-- A dimension-filtered query contributes only to that exact renamed request. -/
theorem coefficient_rename_dimensionTerms {X : SurfaceTarget}
    (q : SurfaceQuery X) (v : Variable X) :
    RationalTerms.coefficient (RationalTerms.rename Sum.inr (dimensionTerms q)) {v} =
      if q.DimensionCompatible then if Sum.inr q = v then 1 else 0 else 0 := by
  unfold dimensionTerms
  by_cases hd : q.DimensionCompatible
  · rw [if_pos hd, if_pos hd, RationalTerms.coefficient_rename_term]
    simp only [Multiset.map_singleton, Multiset.singleton_inj]
  · rw [if_neg hd, if_neg hd]
    rfl

/-- Canonical primary coefficients retain the full query and every divisor factor. -/
theorem coefficient_rename_primaryTerms {X : SurfaceTarget} (g : ℕ) (beta : X.Curve)
    (m : Multiset (SurfaceBasisLabel X)) (v : Variable X) :
    RationalTerms.coefficient (RationalTerms.rename Sum.inr (primaryTerms g beta m)) {v} =
      primaryCoefficient beta m *
        (if (SurfaceQuery.points X g beta (m.count .point)).DimensionCompatible then
          if Sum.inr (SurfaceQuery.points X g beta (m.count .point)) = v then 1 else 0
        else 0) := by
  rw [primaryTerms, RationalTerms.coefficient_rename_scale, coefficient_rename_dimensionTerms]

/-- Point descendants retain the exact count and full renamed request. -/
theorem coefficient_rename_terms_plane_point (g d : ℕ)
    (m : Multiset (SurfaceBasisLabel .plane)) (hu : .unit ∉ m) (v : Variable .plane) :
    RationalTerms.coefficient (RationalTerms.rename Sum.inr (terms g ![d] .point m)) {v} =
      (d : ℚ) ^ m.count .hyperplane *
        (if (query (X := .plane) g ![d] .point (m.count .point)).DimensionCompatible then
          if Sum.inr (query g ![d] .point (m.count .point)) = v then 1 else 0
        else 0) := by
  rw [terms_plane_point g d m hu, RationalTerms.coefficient_rename_scale,
    coefficient_rename_dimensionTerms]

/-- The hyperplane descendant retains its primary correction, including
zero degree and zero divisor count without dividing by either quantity. -/
theorem coefficient_rename_terms_plane_hyperplane (g d : ℕ)
    (m : Multiset (SurfaceBasisLabel .plane)) (hu : .unit ∉ m) (v : Variable .plane) :
    RationalTerms.coefficient (RationalTerms.rename Sum.inr (terms g ![d] .hyperplane m)) {v} =
      (d : ℚ) ^ m.count .hyperplane *
        (if (query (X := .plane) g ![d] .hyperplane (m.count .point)).DimensionCompatible then
          if Sum.inr (query g ![d] .hyperplane (m.count .point)) = v then 1 else 0
        else 0) +
      (m.count .hyperplane : ℚ) * (d : ℚ) ^ (m.count .hyperplane - 1) *
        (if (SurfaceQuery.points .plane g ![d] (m.count .point + 1)).DimensionCompatible then
          if Sum.inr (SurfaceQuery.points .plane g ![d] (m.count .point + 1)) = v
            then 1 else 0
        else 0) := by
  rw [terms_plane_hyperplane g d m hu, RationalTerms.coefficient_rename_add,
    RationalTerms.coefficient_rename_scale, RationalTerms.coefficient_rename_scale,
    coefficient_rename_dimensionTerms, coefficient_rename_dimensionTerms]

end AxiomaticGW.SurfaceFirstDescendant

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction

/-- A primary terminal key has the canonical primary expression, retaining
the original dimension check before any simplification of its states. -/
theorem coefficient_residualTerms_plane_primary (v : Variable .plane)
    (q : SurfaceAncestorKey .plane) (hg : q.genus = 2) (hp : q.IsPrimary) :
    RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
      (residualTerms q)) {v} =
      if q.DimensionCompatible then
        RationalTerms.coefficient (RationalTerms.rename Sum.inr
          (SurfaceFirstDescendant.primaryTerms 2 q.beta q.primaryLabels)) {v}
      else 0 := by
  have hpsi := q.totalPsi_eq_zero_iff.mpr hp
  have hn : ¬(2 ≤ q.genus ∧ q.totalPsi = 1) := by
    rw [hpsi]
    exact fun h ↦ Nat.zero_ne_one h.2
  rw [residualTerms]
  simp only [if_neg (by omega : ¬q.genus ≤ 1)]
  split_ifs with hd
  · simp only [RationalTerms.coefficient_affineSubstitute_term,
      Multiset.map_singleton, Multiset.sum_singleton, one_mul]
    rw [normalizedTerms, dif_neg hn, canonicalPrimaryTerms, if_pos ⟨by omega, hp⟩, hg]
  · exact RationalTerms.coefficient_affineSubstitute_zero _ _

/-- Without a primary unit, the signed dimension check is precisely the
canonical point count. This includes the degree-zero primary point query. -/
theorem primary_plane_dimension_iff (q : SurfaceAncestorKey .plane) (d : ℕ)
    (hg : q.genus = 2) (hb : q.beta = ![d]) (hp : q.IsPrimary)
    (hu : .unit ∉ q.primaryLabels) :
    q.DimensionCompatible ↔ q.primaryLabels.count .point = 3 * d + 1 := by
  have hcodim : q.totalCodimension =
      (q.primaryLabels.map SurfaceBasisLabel.codimension).sum := by
    unfold SurfaceAncestorKey.totalCodimension SurfaceAncestorKey.primaryLabels
    rw [Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro s hs
    exact Nat.add_eq_left.mpr (hp s hs)
  have hcount := SurfaceBasisLabel.sum_codimension_add_units q.primaryLabels
  rw [Multiset.count_eq_zero.mpr hu, add_zero, ← hcodim] at hcount
  have hcard : q.primaryLabels.card = q.insertions.card := Multiset.card_map _ _
  have he : SurfaceTarget.plane.c1Degree ![d] = 3 * (d : ℤ) := by
    rw [SurfaceTarget.c1Degree_eq_intersection]
    change 3 * (d : ℤ) - ∑ _ : Fin 0, _ = _
    rw [Fin.sum_univ_zero, sub_zero]
  unfold SurfaceAncestorKey.DimensionCompatible
  rw [hb, hg, he]
  omega

/-- The complete zero-remainder primary coefficient has one canonical point
request. No positivity assumption is imposed on the degree or marking count. -/
theorem remainderVertex_plane_primary_canonical (v : Variable .plane) (n : ℕ)
    (S : Type) [Fintype S] (h : StableArity 2 S) (l : DecidableEq S)
    (a : S → SurfaceBasisLabel .plane) (hu : .unit ∉ Finset.univ.val.map a) :
    let d := SurfaceGenusZero.variableCurve v 0
    let m := Finset.univ.val.map a
    remainderVertex .plane v (planeCoefficientVertex v) n 2 S h 0 l 0 a =
      if n + m.count .point = 3 * d + 1 then
        (d : ℚ) ^ m.count .hyperplane *
          (if Sum.inr (SurfaceQuery.points .plane 2 ![d] (n + m.count .point)) = v
            then 1 else 0)
      else 0 := by
  let d := SurfaceGenusZero.variableCurve v 0
  let m := Finset.univ.val.map a
  let q := (SurfaceAncestorKey.ofLabels 2 S h (SurfaceGenusZero.variableCurve v) 0 a).addPoints n
  have hv : SurfaceGenusZero.variableCurve v = ![d] := by
    funext i
    fin_cases i
    rfl
  have hp : q.IsPrimary := by
    intro t ht
    rcases Multiset.mem_add.mp ht with ht | ht
    · exact congrArg SurfaceInsertion.psi (Multiset.mem_replicate.mp ht).2
    · obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp ht
      rfl
  have hm : q.primaryLabels = Multiset.replicate n .point + m := by
    simp only [q, SurfaceAncestorKey.primaryLabels, SurfaceAncestorKey.addPoints,
      SurfaceAncestorKey.ofLabels, Multiset.map_add, Multiset.map_replicate,
      Multiset.map_map, Function.comp_def]
    rfl
  have hqu : .unit ∉ q.primaryLabels := by
    rw [hm]
    simpa only [Multiset.mem_add, Multiset.mem_replicate, reduceCtorEq, and_false,
      false_or] using hu
  have hdim : q.DimensionCompatible ↔ n + m.count .point = 3 * d + 1 := by
    rw [primary_plane_dimension_iff q d rfl hv hp hqu, hm]
    simp only [Multiset.count_add, Multiset.count_replicate, ite_true]
  dsimp only
  rw [remainderVertex_plane_primary, if_pos rfl]
  change RationalTerms.coefficient
    (RationalTerms.affineSubstitute normalizedTerms (residualTerms q)) {v} =
      if n + m.count .point = 3 * d + 1 then
        (d : ℚ) ^ m.count .hyperplane *
          (if Sum.inr (SurfaceQuery.points .plane 2 ![d] (n + m.count .point)) = v
            then 1 else 0)
      else 0
  rw [coefficient_residualTerms_plane_primary v q rfl hp,
    SurfaceFirstDescendant.coefficient_rename_primaryTerms]
  have hbeta : q.beta = ![d] := hv
  rw [hbeta, SurfaceFirstDescendant.primaryCoefficient_plane, if_neg hqu, hm]
  simp only [hdim, Multiset.count_add, Multiset.count_replicate, reduceCtorEq,
    ite_false, ite_true, zero_add, SurfaceQuery.dimensionCompatible_points_plane]
  by_cases hd : n + m.count .point = 3 * d + 1
  · have hd' : n + m.count .point + 1 = 3 * d + 2 := by omega
    simp only [if_pos hd, if_pos hd']
  · simp only [if_neg hd]

private theorem single_onePsi_dimension (d n : ℕ) (a : SurfaceBasisLabel .plane) :
    ((SurfaceAncestorKey.ofLabels 2 (Fin 1) (by norm_num [StableArity]) ![d]
      (Pi.single 0 1) ![a]).addPoints n).DimensionCompatible ↔
      n + a.codimension = 3 * d + 1 := by
  have he : SurfaceTarget.plane.c1Degree ![d] = 3 * (d : ℤ) := by
    rw [SurfaceTarget.c1Degree_eq_intersection]
    change 3 * (d : ℤ) - ∑ _ : Fin 0, _ = _
    rw [Fin.sum_univ_zero, sub_zero]
  simp only [SurfaceAncestorKey.DimensionCompatible, SurfaceAncestorKey.totalCodimension,
    SurfaceAncestorKey.addPoints, SurfaceAncestorKey.ofLabels, Multiset.map_add,
    Multiset.map_replicate, Multiset.sum_add, Multiset.sum_replicate,
    Multiset.card_add, Multiset.card_replicate, Multiset.card_map, Finset.card_val,
    Finset.card_univ, Fintype.card_fin, he, SurfaceBasisLabel.codimension, add_zero,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  change (n : ℤ) * 2 + ((a.codimension : ℤ) + 1) =
    3 * (d : ℤ) + 2 - 1 + ((n : ℤ) + 1) ↔ n + a.codimension = 3 * d + 1
  omega

private theorem pair_onePsi_dimension (d n : ℕ) (a b : SurfaceBasisLabel .plane)
    (s : Fin 2) :
    ((SurfaceAncestorKey.ofLabels 2 (Fin 2) (by norm_num [StableArity]) ![d]
      (Pi.single s 1) ![a, b]).addPoints n).DimensionCompatible ↔
      n + a.codimension + b.codimension = 3 * d + 2 := by
  have he : SurfaceTarget.plane.c1Degree ![d] = 3 * (d : ℤ) := by
    rw [SurfaceTarget.c1Degree_eq_intersection]
    change 3 * (d : ℤ) - ∑ _ : Fin 0, _ = _
    rw [Fin.sum_univ_zero, sub_zero]
  fin_cases s <;>
    simp only [SurfaceAncestorKey.DimensionCompatible, SurfaceAncestorKey.totalCodimension,
      SurfaceAncestorKey.addPoints, SurfaceAncestorKey.ofLabels, Multiset.map_add,
      Multiset.map_replicate, Multiset.sum_add, Multiset.sum_replicate,
      Multiset.card_add, Multiset.card_replicate, Multiset.card_map, Finset.card_val,
      Finset.card_univ, Fintype.card_fin, he, SurfaceBasisLabel.codimension, add_zero,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  · change (n : ℤ) * 2 + ((a.codimension + 1 : ℕ) + (b.codimension : ℤ)) =
      3 * (d : ℤ) + 2 - 1 + ((n : ℤ) + 2) ↔
        n + a.codimension + b.codimension = 3 * d + 2
    omega
  · change (n : ℤ) * 2 + ((a.codimension : ℤ) + (b.codimension + 1 : ℕ)) =
      3 * (d : ℤ) + 2 - 1 + ((n : ℤ) + 2) ↔
        n + a.codimension + b.codimension = 3 * d + 2
    omega

/-- The single hyperplane psi component is exactly its canonical descendant,
with no primary correction because it has no retained primary divisor. -/
theorem remainderVertex_plane_single_hyperplane_onePsi (v : Variable .plane) (n : ℕ) :
    let d := SurfaceGenusZero.variableCurve v 0
    remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 1)
      (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0 ![.hyperplane] =
      if n = 3 * d then
        if Sum.inr (SurfaceFirstDescendant.query 2 ![d] .hyperplane n) = v then 1 else 0
      else 0 := by
  let d := SurfaceGenusZero.variableCurve v 0
  have hv : SurfaceGenusZero.variableCurve v = ![d] := by
    funext i
    fin_cases i
    rfl
  have hm : ((Finset.univ.erase (0 : Fin 1)).val.map
      (![.hyperplane] : Fin 1 → SurfaceBasisLabel .plane)) = 0 := by decide +kernel
  have hu : SurfaceBasisLabel.unit ∉
      (Multiset.replicate n .point : Multiset (SurfaceBasisLabel .plane)) := by
    simp only [Multiset.mem_replicate, reduceCtorEq, and_false, not_false_eq_true]
  dsimp only
  rw [remainderVertex_onePsi_plane_zero_normalized, hv]
  simp only [single_onePsi_dimension, SurfaceBasisLabel.codimension, hm, add_zero,
    Matrix.cons_val_zero, reduceCtorEq, ite_false, sub_zero]
  rw [SurfaceFirstDescendant.coefficient_rename_terms_plane_hyperplane 2 d _ hu]
  simp only [Multiset.count_replicate, reduceCtorEq, ite_false, ite_true, pow_zero,
    one_mul, Nat.cast_zero, zero_mul, add_zero, SurfaceQuery.dimensionCompatible_first_plane,
    SurfaceBasisLabel.codimension]
  by_cases hn : n = 3 * d
  · have hn1 : n + 1 = 3 * d + 1 := by omega
    have hn2 : n + 1 + 1 = 3 * d + 2 := by omega
    simp only [if_pos hn1, if_pos hn2]
    change (if Sum.inr (SurfaceFirstDescendant.query 2 ![d] .hyperplane n) = v
      then (1 : ℚ) else 0) = if n = 3 * d then _ else _
    rw [if_pos hn]
    rfl
  · have hn1 : n + 1 ≠ 3 * d + 1 := by omega
    simp only [if_neg hn1]
    change (0 : ℚ) = if n = 3 * d then _ else _
    rw [if_neg hn]

/-- The single dilaton marking contributes two copies of the primary query
after subtracting the signed classical point-tail correction. -/
theorem remainderVertex_plane_single_unit_onePsi (v : Variable .plane) (n : ℕ) :
    let d := SurfaceGenusZero.variableCurve v 0
    remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 1)
      (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0 ![.unit] =
      if n = 3 * d + 1 then
        2 * (if Sum.inr (SurfaceQuery.points .plane 2 ![d] n) = v then 1 else 0)
      else 0 := by
  let d := SurfaceGenusZero.variableCurve v 0
  have hv : SurfaceGenusZero.variableCurve v = ![d] := by
    funext i
    fin_cases i
    rfl
  have hm : ((Finset.univ.erase (0 : Fin 1)).val.map
      (![.unit] : Fin 1 → SurfaceBasisLabel .plane)) = 0 := by decide +kernel
  have hu : SurfaceBasisLabel.unit ∉
      (Multiset.replicate n .point : Multiset (SurfaceBasisLabel .plane)) := by
    simp only [Multiset.mem_replicate, reduceCtorEq, and_false, not_false_eq_true]
  have ha : Function.update (![.unit] : Fin 1 → SurfaceBasisLabel .plane) 0 .point =
      ![.point] := by
    funext i
    fin_cases i
    rfl
  have hp : (Finset.univ.val.map (![.point] : Fin 1 → SurfaceBasisLabel .plane)) =
      {.point} := by decide +kernel
  have hpu : SurfaceBasisLabel.unit ∉
      Finset.univ.val.map (![.point] : Fin 1 → SurfaceBasisLabel .plane) := by
    rw [hp]
    decide
  dsimp only
  rw [remainderVertex_onePsi_plane_zero_normalized, hv]
  simp only [single_onePsi_dimension, SurfaceBasisLabel.codimension, hm, add_zero,
    Matrix.cons_val_zero, ite_true, ha]
  rw [SurfaceFirstDescendant.terms, if_neg hu, if_pos rfl,
    RationalTerms.coefficient_rename_scale,
    SurfaceFirstDescendant.coefficient_rename_primaryTerms,
    SurfaceFirstDescendant.primaryCoefficient_plane, if_neg hu,
    remainderVertex_plane_primary_canonical _ _ _ _ _ _ hpu]
  simp only [hp, Multiset.count_replicate, Multiset.count_singleton, reduceCtorEq,
    ite_false, ite_true, pow_zero, one_mul, Multiset.card_replicate,
    SurfaceQuery.dimensionCompatible_points_plane, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  change (if n = 3 * d + 1 then ((2 * 2 + (n : ℚ)) - 2) *
      (if n + 1 = 3 * d + 2 then
        if Sum.inr (SurfaceQuery.points .plane 2 ![d] n) = v then 1 else 0
      else 0) else 0) -
      (n : ℚ) * (if n - 1 + 1 = 3 * d + 1 then
        if Sum.inr (SurfaceQuery.points .plane 2 ![d] (n - 1 + 1)) = v then 1 else 0
      else 0) =
    if n = 3 * d + 1 then
      2 * (if Sum.inr (SurfaceQuery.points .plane 2 ![d] n) = v then 1 else 0)
    else 0
  by_cases hn : n = 0
  · subst n
    have hd : ¬0 = 3 * d + 1 := by omega
    simp only [if_neg hd, Nat.cast_zero, zero_mul, sub_zero]
  · have hn' : n - 1 + 1 = n := by omega
    rw [hn']
    by_cases hd : n = 3 * d + 1
    · have hd' : n + 1 = 3 * d + 2 := by omega
      rw [if_pos hd, if_pos hd, if_pos hd, if_pos hd']
      ring
    · rw [if_neg hd, if_neg hd, if_neg hd, mul_zero, sub_zero]

/-- With one primary hyperplane, either location of the hyperplane psi
contributes the descendant divisor factor and one primary point correction. -/
theorem remainderVertex_plane_two_hyperplanes_onePsi (v : Variable .plane) (n : ℕ)
    (s : Fin 2) :
    let d := SurfaceGenusZero.variableCurve v 0
    remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0
      ![.hyperplane, .hyperplane] =
      if n = 3 * d then
        (d : ℚ) *
          (if Sum.inr (SurfaceFirstDescendant.query 2 ![d] .hyperplane n) = v then 1 else 0) +
        (if Sum.inr (SurfaceQuery.points .plane 2 ![d] (n + 1)) = v then 1 else 0)
      else 0 := by
  let d := SurfaceGenusZero.variableCurve v 0
  have hv : SurfaceGenusZero.variableCurve v = ![d] := by
    funext i
    fin_cases i
    rfl
  have ha : (![.hyperplane, .hyperplane] : Fin 2 → SurfaceBasisLabel .plane) s =
      .hyperplane := by fin_cases s <;> rfl
  have hm : ((Finset.univ.erase s).val.map
      (![.hyperplane, .hyperplane] : Fin 2 → SurfaceBasisLabel .plane)) =
      {.hyperplane} := by fin_cases s <;> decide +kernel
  have hu : SurfaceBasisLabel.unit ∉
      (Multiset.replicate n .point + {.hyperplane} : Multiset (SurfaceBasisLabel .plane)) := by
    simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton,
      reduceCtorEq, and_false, or_self, not_false_eq_true]
  dsimp only
  rw [remainderVertex_onePsi_plane_zero_normalized, hv]
  simp only [pair_onePsi_dimension, SurfaceBasisLabel.codimension, hm, ha,
    reduceCtorEq, ite_false, sub_zero]
  rw [SurfaceFirstDescendant.coefficient_rename_terms_plane_hyperplane 2 d _ hu]
  simp only [Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton,
    reduceCtorEq, ite_false, ite_true, zero_add, add_zero, pow_one, Nat.sub_self,
    pow_zero, Nat.cast_one, one_mul, mul_one,
    SurfaceQuery.dimensionCompatible_first_plane, SurfaceQuery.dimensionCompatible_points_plane,
    SurfaceBasisLabel.codimension]
  by_cases hn : n = 3 * d
  · have hn' : n + 1 + 1 = 3 * d + 2 := by omega
    simp only [if_pos hn']
    change _ = if n = 3 * d then _ else _
    rw [if_pos hn]
    rfl
  · have hn' : n + 1 + 1 ≠ 3 * d + 2 := by omega
    simp only [if_neg hn']
    change (0 : ℚ) = if n = 3 * d then _ else _
    rw [if_neg hn]

/-- A retained primary unit removes the single cotangent power by string.
The original non-unit state retains its primary divisor factor. -/
theorem remainderVertex_plane_pair_primary_unit (v : Variable .plane) (n : ℕ)
    (a : SurfaceBasisLabel .plane) (ha : a ≠ .unit) :
    let d := SurfaceGenusZero.variableCurve v 0
    let m : Multiset (SurfaceBasisLabel .plane) := {a}
    remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0 ![a, .unit] =
      if n + m.count .point = 3 * d + 1 then
        (d : ℚ) ^ m.count .hyperplane *
          (if Sum.inr (SurfaceQuery.points .plane 2 ![d] (n + m.count .point)) = v
            then 1 else 0)
      else 0 := by
  let d := SurfaceGenusZero.variableCurve v 0
  let m : Multiset (SurfaceBasisLabel .plane) := {a}
  have hv : SurfaceGenusZero.variableCurve v = ![d] := by
    funext i
    fin_cases i
    rfl
  have hm : ((Finset.univ.erase (0 : Fin 2)).val.map
      (![a, .unit] : Fin 2 → SurfaceBasisLabel .plane)) = {.unit} := by
    change Multiset.map (![a, .unit] : Fin 2 → SurfaceBasisLabel .plane) {1} = _
    rfl
  have hu : SurfaceBasisLabel.unit ∈
      (Multiset.replicate n .point + {.unit} : Multiset (SurfaceBasisLabel .plane)) := by
    exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _))
  have he : (Multiset.replicate n (SurfaceBasisLabel.point : SurfaceBasisLabel .plane) +
      {SurfaceBasisLabel.unit}).erase .unit =
        Multiset.replicate n .point := by
    rw [Multiset.erase_add_right_pos _ (Multiset.mem_singleton_self _),
      Multiset.erase_singleton, add_zero]
  have hmu : SurfaceBasisLabel.unit ∉ a ::ₘ Multiset.replicate n .point := by
    simp only [Multiset.mem_cons, Multiset.mem_replicate, reduceCtorEq, and_false,
      or_false, ne_eq]
    exact Ne.symm ha
  have hdim : n + a.codimension +
      (SurfaceBasisLabel.unit : SurfaceBasisLabel .plane).codimension = 3 * d + 2 ↔
      n + m.count .point = 3 * d + 1 := by
    cases a with
    | unit => exact (ha rfl).elim
    | exceptional i => exact Fin.elim0 i
    | hyperplane =>
      simp only [m, Multiset.count_singleton, reduceCtorEq, ite_false,
        SurfaceBasisLabel.codimension, add_zero]
      omega
    | point =>
      simp only [m, Multiset.count_singleton, ite_true,
        SurfaceBasisLabel.codimension, add_zero]
      omega
  dsimp only
  rw [remainderVertex_onePsi_plane_zero_normalized, hv]
  simp only [pair_onePsi_dimension, hdim, Matrix.cons_val_zero, hm, if_neg ha, sub_zero]
  rw [SurfaceFirstDescendant.terms, if_pos hu, he,
    SurfaceFirstDescendant.coefficient_rename_primaryTerms,
    SurfaceFirstDescendant.primaryCoefficient_plane, if_neg hmu]
  have hpoint : (a ::ₘ Multiset.replicate n .point).count .point = n + m.count .point := by
    simp only [Multiset.count_cons, Multiset.count_replicate, ite_true, m,
      Multiset.count_singleton]
  have hhyper : (a ::ₘ Multiset.replicate n .point).count .hyperplane =
      m.count .hyperplane := by
    simp only [Multiset.count_cons, Multiset.count_replicate, reduceCtorEq,
      ite_false, zero_add, m, Multiset.count_singleton]
  simp only [hpoint, hhyper, SurfaceQuery.dimensionCompatible_points_plane]
  change (if n + m.count .point = 3 * d + 1 then
      (d : ℚ) ^ m.count .hyperplane *
        (if n + m.count .point + 1 = 3 * d + 2 then
          if Sum.inr (SurfaceQuery.points .plane 2 ![d] (n + m.count .point)) = v
            then 1 else 0
        else 0)
      else 0) =
    if n + m.count .point = 3 * d + 1 then
      (d : ℚ) ^ m.count .hyperplane *
        (if Sum.inr (SurfaceQuery.points .plane 2 ![d] (n + m.count .point)) = v
          then 1 else 0)
    else 0
  by_cases hd : n + m.count .point = 3 * d + 1
  · have hd' : n + m.count .point + 1 = 3 * d + 2 := by omega
    simp only [if_pos hd, if_pos hd']
  · simp only [if_neg hd]

/-- A unit psi beside one non-unit state contributes three copies of that
primary query. The negative point-tail correction removes the added-point
part of the dilaton factor. -/
theorem remainderVertex_plane_pair_unit_onePsi (v : Variable .plane) (n : ℕ)
    (a : SurfaceBasisLabel .plane) (ha : a ≠ .unit) :
    let d := SurfaceGenusZero.variableCurve v 0
    let m : Multiset (SurfaceBasisLabel .plane) := {a}
    remainderVertex .plane v (planeCoefficientVertex v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single 1 1) inferInstance 0 ![a, .unit] =
      if n + m.count .point = 3 * d + 1 then
        3 * (d : ℚ) ^ m.count .hyperplane *
          (if Sum.inr (SurfaceQuery.points .plane 2 ![d] (n + m.count .point)) = v
            then 1 else 0)
      else 0 := by
  let d := SurfaceGenusZero.variableCurve v 0
  let m : Multiset (SurfaceBasisLabel .plane) := {a}
  have hv : SurfaceGenusZero.variableCurve v = ![d] := by
    funext i
    fin_cases i
    rfl
  have hm : ((Finset.univ.erase (1 : Fin 2)).val.map
      (![a, .unit] : Fin 2 → SurfaceBasisLabel .plane)) = m := by
    change Multiset.map (![a, .unit] : Fin 2 → SurfaceBasisLabel .plane) {0} = _
    rfl
  have hu : SurfaceBasisLabel.unit ∉ Multiset.replicate n .point + m := by
    simp only [m, Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton,
      reduceCtorEq, and_false, false_or, ne_eq]
    exact Ne.symm ha
  have hap : Function.update (![a, .unit] : Fin 2 → SurfaceBasisLabel .plane) 1 .point =
      ![a, .point] := by
    funext i
    fin_cases i <;> rfl
  have hp : Finset.univ.val.map (![a, .point] : Fin 2 → SurfaceBasisLabel .plane) =
      m + {.point} := by
    change Multiset.map (![a, .point] : Fin 2 → SurfaceBasisLabel .plane) {0, 1} = _
    rfl
  have hpu : SurfaceBasisLabel.unit ∉
      Finset.univ.val.map (![a, .point] : Fin 2 → SurfaceBasisLabel .plane) := by
    rw [hp]
    simp only [m, Multiset.mem_add, Multiset.mem_singleton, reduceCtorEq, or_false]
    exact Ne.symm ha
  have hdim : n + a.codimension +
      (SurfaceBasisLabel.unit : SurfaceBasisLabel .plane).codimension = 3 * d + 2 ↔
      n + m.count .point = 3 * d + 1 := by
    cases a with
    | unit => exact (ha rfl).elim
    | exceptional i => exact Fin.elim0 i
    | hyperplane =>
      simp only [m, Multiset.count_singleton, reduceCtorEq, ite_false,
        SurfaceBasisLabel.codimension, add_zero]
      omega
    | point =>
      simp only [m, Multiset.count_singleton, ite_true,
        SurfaceBasisLabel.codimension, add_zero]
      omega
  dsimp only
  rw [remainderVertex_onePsi_plane_zero_normalized, hv]
  simp only [pair_onePsi_dimension, hdim, Matrix.cons_val_one, Matrix.cons_val_zero,
    hm, ite_true, hap]
  rw [SurfaceFirstDescendant.terms, if_neg hu, if_pos rfl,
    RationalTerms.coefficient_rename_scale,
    SurfaceFirstDescendant.coefficient_rename_primaryTerms,
    SurfaceFirstDescendant.primaryCoefficient_plane, if_neg hu,
    remainderVertex_plane_primary_canonical _ _ _ _ _ _ hpu]
  have hcp : ({SurfaceBasisLabel.point} : Multiset (SurfaceBasisLabel .plane)).count .point = 1 :=
    Multiset.count_singleton_self _
  have hch : ({SurfaceBasisLabel.point} : Multiset (SurfaceBasisLabel .plane)).count
      .hyperplane = 0 := by decide +kernel
  simp only [hp, Multiset.count_add, Multiset.count_replicate, hcp, hch,
    reduceCtorEq, ite_false, ite_true, zero_add, add_zero,
    Multiset.card_add, Multiset.card_replicate,
    SurfaceQuery.dimensionCompatible_points_plane, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  have hcard : m.card = 1 := rfl
  rw [hcard]
  simp only [Nat.cast_one]
  change (if n + m.count .point = 3 * d + 1 then
      ((2 * 2 + ((n : ℚ) + 1)) - 2) * ((d : ℚ) ^ m.count .hyperplane *
        (if n + m.count .point + 1 = 3 * d + 2 then
          if Sum.inr (SurfaceQuery.points .plane 2 ![d] (n + m.count .point)) = v
            then 1 else 0
        else 0)) else 0) -
      (n : ℚ) * (if n - 1 + (m.count .point + 1) = 3 * d + 1 then
        (d : ℚ) ^ m.count .hyperplane *
          (if Sum.inr (SurfaceQuery.points .plane 2 ![d]
            (n - 1 + (m.count .point + 1))) = v then 1 else 0)
        else 0) =
    if n + m.count .point = 3 * d + 1 then
      3 * (d : ℚ) ^ m.count .hyperplane *
        (if Sum.inr (SurfaceQuery.points .plane 2 ![d] (n + m.count .point)) = v
          then 1 else 0)
    else 0
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, zero_mul, sub_zero]
    by_cases hd : 0 + m.count .point = 3 * d + 1
    · have hd' : 0 + m.count .point + 1 = 3 * d + 2 := by omega
      rw [if_pos hd, if_pos hd, if_pos hd']
      ring
    · rw [if_neg hd, if_neg hd]
  · have hn' : n - 1 + (m.count .point + 1) = n + m.count .point := by omega
    rw [hn']
    by_cases hd : n + m.count .point = 3 * d + 1
    · have hd' : n + m.count .point + 1 = 3 * d + 2 := by omega
      rw [if_pos hd, if_pos hd, if_pos hd, if_pos hd']
      ring
    · rw [if_neg hd, if_neg hd, if_neg hd, mul_zero, sub_zero]

end AxiomaticGW.SurfaceGenusTwo

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module
public import AxiomaticGW.Surfaces.GenusTwoBlowupNCoefficients
public import AxiomaticGW.Surfaces.GenusTwoBlowupNExceptionalRational

/-!
# Exceptional columns at proper remainders of the mixed BP equations

At a nonzero full effective remainder of plane degree zero, the complete EHH
row has no nonprimary coefficient. The complete EEH row has canonical K_j
coefficient `-6 * planeDegree(beta)` exactly when the remainder is `E_i` and
the requested exceptional label is `i`; all other such K coefficients vanish.
The source remains `beta + E_i` with `energy(beta)` additional points.

The proof retains every effective split, node state, binomial distribution,
marking assignment, signed cotangent tail and normalization coefficient. The
rational EE triple uses the existing exceptional seed one and the proved
higher-energy point vanishing. The positive remainder's inverse exceptional
pairing sign is retained. No recurrence or additional geometric or numerical
input is assumed. The cancellation with the EEE row and full canonical order
support are separate consumers of these original-row coefficient identities.
-/
@[expose] public section
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwo GluingExpression
set_option maxRecDepth 20000
namespace AxiomaticGW.SurfaceGenusTwoBlowupNMixedKSupport
open SurfaceGenusTwoBlowupNCoefficients
variable {X : SurfaceTarget}
/-- At a proper plane-zero remainder, an actual rational EE cotangent pair retains only its own
  exceptional-generator split. -/
theorem paper_pair_ee_nonprimary_pos (X : SurfaceTarget) (i : Fin X.blowups)
    (v : Variable X) (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (delta : X.Curve) (hd : X.planeDegree delta = 0) (hz : delta ≠ 0) (n : ℕ) (s : Fin 2) (a :
      SurfaceBasisLabel X) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![a, .exceptional i, .exceptional i] =
      if delta = X.exceptionalCurve i then
        remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
          (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0
            ![a, .exceptional i]
      else 0 := by
  have h0 : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
  have h1 : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
  have he : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![a, .exceptional i, .exceptional i] =
      remainderContraction X v (remainderVertex X v (coefficientVertex X v))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          (fundamental 2 (Fin 2) (by norm_num [StableArity]))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        (by exact (Pi.single s 1, (0 : Fin 3 → ℕ)))
        (by exact ((inferInstance : DecidableEq (Fin 2)),
          (inferInstance : DecidableEq (Fin 3)))) delta n
            ![a, .exceptional i, .exceptional i] := by
    have hs : s = 0 ∨ s = 1 := by omega
    rcases hs with rfl | rfl
    · rw [if_pos rfl, ← h0]; rfl
    · rw [if_neg (by decide : (1 : Fin 2) ≠ 0), ← h1]; rfl
  rw [he, SurfaceGenusTwoBlowupPCoefficients.pair_join]
  simp only [remainderContraction, ite_true]
  rw [Finset.sum_eq_single (0, delta)]
  · have ht (b : SurfaceBasisLabel X) :=
    SurfaceGenusTwoBlowupNExceptionalRational.triple_points_pos X i delta hd hz
      (fun m ↦ remainderVertex X v (coefficientVertex X v) m 2 (Fin 2)
        (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0 ![a, b]) n b.dual
    simp only [ht]
    by_cases hdi : delta = X.exceptionalCurve i
    · rw [if_pos hdi]
      simp only [hdi, true_and]
      rw [Finset.sum_eq_single (.exceptional i)]
      · simp only [SurfaceBasisLabel.inverseWeight, SurfaceBasisLabel.dual, ite_true,
          neg_one_mul, neg_neg]
      · intro b _ hb
        have hbd : b.dual ≠ .exceptional i := by
          cases b with
          | unit | hyperplane | point => intro h; cases h
          | exceptional j => intro h; cases h; exact hb rfl
        rw [if_neg hbd, mul_zero]
      · exact fun h ↦ (h (Finset.mem_univ _)).elim
    · rw [if_neg hdi]
      simp only [hdi, false_and, ite_false, mul_zero, Finset.sum_const_zero]
  · intro split hsplit hne
    have hs : split.1 + split.2 = delta := by
      rw [X.splittings_eq] at hsplit
      exact (X.effective.mem_splittings _ _ _).mp hsplit
    have h0 : split.1 ≠ 0 := by
      intro h0
      have hh : split.2 = delta := by simpa only [h0, zero_add] using hs
      exact hne (Prod.ext h0 hh)
    apply Finset.sum_eq_zero
    intro b _
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro ij _
    rw [remainderVertex_onePsi_of_not_points v hv, if_neg h0, zero_mul, mul_zero]
  · intro hnot
    apply (hnot ?_).elim
    rw [X.splittings_eq, X.effective.mem_splittings]
    exact zero_add _



/-- The H/E_i main pair has K_j coefficient d only when psi lies on E_i and j is i. -/
theorem main_hyperplane_exceptional_k (X : SurfaceTarget) (i j : Fin X.blowups)
    (beta : X.Curve) (s : Fin 2) :
    let v : Variable X := .inr (SurfaceFirstDescendant.query 2 beta (.exceptional j)
      (X.effective.energy beta))
    remainderVertex X v (coefficientVertex X v) (X.effective.energy beta) 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0
        ![.hyperplane, .exceptional i] =
      if s = 1 ∧ i = j then (X.planeDegree beta : ℚ) else 0 := by
  let v : Variable X := .inr (SurfaceFirstDescendant.query 2 beta (.exceptional j)
    (X.effective.energy beta))
  have hv : ∀ gamma n, Sum.inr (SurfaceQuery.points X 2 gamma n) ≠ v :=
    fun gamma n ↦ SurfaceFirstDescendant.query_ne_points beta gamma (.exceptional j)
      (X.effective.energy beta) n
  have hvar : SurfaceGenusZero.variableCurve v = beta := rfl
  have hdim : ((SurfaceAncestorKey.ofLabels 2 (Fin 2) (by norm_num [StableArity]) beta
      (Pi.single s 1) (![.hyperplane, .exceptional i] : Fin 2 → SurfaceBasisLabel X)).addPoints
      (X.effective.energy beta)).DimensionCompatible := by
    fin_cases s <;> simp only [SurfaceAncestorKey.DimensionCompatible,
      SurfaceAncestorKey.totalCodimension, SurfaceAncestorKey.addPoints,
        SurfaceAncestorKey.ofLabels,
      Multiset.map_add, Multiset.map_replicate, Multiset.sum_add, Multiset.sum_replicate,
      Multiset.card_add, Multiset.card_replicate, Multiset.card_map, Finset.card_val,
      Finset.card_univ, Fintype.card_fin, SurfaceTarget.c1Degree, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    all_goals change (X.effective.energy beta : ℤ) * 2 + 3 =
      (X.effective.energy beta : ℤ) + 2-1 + ((X.effective.energy beta : ℤ) + 2)
    all_goals omega
  dsimp only
  rw [remainderVertex_onePsi_of_not_points v hv, if_pos rfl,
    coefficient_residualTerms_onePsi_of_not_points v hv]
  simp only [hvar]
  rw [if_pos hdim]
  have h0 : ((Finset.univ.erase (0 : Fin 2)).val.map
      (![.hyperplane, .exceptional i] : Fin 2 → SurfaceBasisLabel X)) = {.exceptional i} := rfl
  have h1 : ((Finset.univ.erase (1 : Fin 2)).val.map
      (![.hyperplane, .exceptional i] : Fin 2 → SurfaceBasisLabel X)) = {.hyperplane} := rfl
  have hu (a : SurfaceBasisLabel X) (ha : a ≠ .unit) : SurfaceBasisLabel.unit ∉
      (Multiset.replicate (X.effective.energy beta) .point + {a} : Multiset (SurfaceBasisLabel X))
        := by
    simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton, reduceCtorEq,
      and_false, false_or, ne_eq]
    exact Ne.symm ha
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
  · rw [h0, Matrix.cons_val_zero, SurfaceFirstDescendant.terms,
      if_neg (hu _ (by intro h; cases h)), if_neg (show (SurfaceBasisLabel.hyperplane :
        SurfaceBasisLabel X) ≠ .unit by intro h; cases h)]
    rw [RationalTerms.coefficient_rename_add, RationalTerms.coefficient_rename_scale,
      RationalTerms.coefficient_rename_scale]
    simp only [SurfaceFirstDescendant.primaryCoefficient, Multiset.map_add, Multiset.map_replicate,
      Multiset.map_singleton, Multiset.prod_add, Multiset.prod_replicate, Multiset.prod_singleton,
      SurfaceBasisLabel.primaryFactor, one_pow, one_mul,
      SurfaceFirstDescendant.correctionCoefficient, SurfaceFirstDescendant.divisorSquare,
      Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton, reduceCtorEq,
      ite_false, ite_true, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    rw [SurfaceFirstDescendant.dimensionTerms,
      if_pos (by
        rw [SurfaceQuery.dimensionCompatible_first]
        rfl),
      RationalTerms.coefficient_rename_term]
    have hn : Sum.inr (SurfaceFirstDescendant.query 2 beta .hyperplane (X.effective.energy beta))
      ≠ v :=
      SurfaceGenusTwoBlowupPCoefficients.first_queries_ne beta .hyperplane (.exceptional j) _ _
        (by intro h; cases h)
    simp only [Multiset.map_singleton, Multiset.singleton_inj, if_neg hn, mul_zero,
      show (0 : Fin 2) ≠ 1 by decide, false_and, ite_false]
  · rw [h1, Matrix.cons_val_one, Matrix.cons_val_zero, SurfaceFirstDescendant.terms,
      if_neg (hu _ (by intro h; cases h)), if_neg (show (SurfaceBasisLabel.exceptional i :
        SurfaceBasisLabel X) ≠ .unit by intro h; cases h)]
    rw [RationalTerms.coefficient_rename_add, RationalTerms.coefficient_rename_scale,
      RationalTerms.coefficient_rename_scale]
    simp only [SurfaceFirstDescendant.primaryCoefficient, Multiset.map_add, Multiset.map_replicate,
      Multiset.map_singleton, Multiset.prod_add, Multiset.prod_replicate, Multiset.prod_singleton,
      SurfaceBasisLabel.primaryFactor, one_pow, one_mul,
      SurfaceFirstDescendant.correctionCoefficient, SurfaceFirstDescendant.divisorSquare,
      Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton, reduceCtorEq,
      ite_false, ite_true, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    rw [SurfaceFirstDescendant.dimensionTerms,
      if_pos (by
        rw [SurfaceQuery.dimensionCompatible_first]
        rfl),
      RationalTerms.coefficient_rename_term]
    simp only [Multiset.map_singleton, Multiset.singleton_inj, true_and]
    rw [← X.planeDegree_eq_divisorIntersections]
    simp only [Int.cast_natCast]
    by_cases hij : i = j
    · subst j
      simp only [v, ite_true, mul_one]
    · have hn : Sum.inr (SurfaceFirstDescendant.query 2 beta (.exceptional i) (X.effective.energy
      beta)) ≠ v :=
        SurfaceGenusTwoBlowupPCoefficients.first_queries_ne beta (.exceptional i) (.exceptional j)
          _ _
          (fun h ↦ hij (SurfaceBasisLabel.exceptional.inj h))
      rw [if_neg hn, if_neg hij, mul_zero]

/-- The actual EHH equation has no nonprimary coefficient at a proper plane-zero remainder. -/
theorem pointCoefficient_ehh_nonprimary_pos (X : SurfaceTarget) (i : Fin X.blowups)
    (v : Variable X) (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (delta : X.Curve) (hd : X.planeDegree delta = 0) (hz : delta ≠ 0) (n : ℕ) :
    BelorousskiPandharipande.pointCoefficient X n (SurfaceGenusZero.variableCurve v + delta)
      ![.exceptional i, .hyperplane, .hyperplane] v = 0 := by
  have hterm (j : Fin 20) (e : Fin 6) :
      SurfaceGenusTwo.pointCoefficient X v (BelorousskiPandharipande.orbitCotangentTerm j e)
        (SurfaceGenusZero.variableCurve v + delta) n ![.exceptional i, .hyperplane, .hyperplane] =
      remainderPointCoefficient X v (coefficientVertex X v)
        (BelorousskiPandharipande.orbitCotangentTerm j e) delta n
          ![.exceptional i, .hyperplane, .hyperplane] :=
    (remainderPointCoefficient_eq X v (coefficientVertex X v) rfl
      (BelorousskiPandharipande.orbitCotangentTerm j e) delta n _).symm
  have hzero (e : Fin 6) : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 0 e) delta n
      ![.exceptional i, .hyperplane, .hyperplane] = 0 := by
    rw [SurfaceGenusTwoBlowupPCoefficients.remainder_orbit,
      SurfaceGenusTwoBlowupPCoefficients.paper_zero v hv]
  have hone (e : Fin 6) : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 1 e) delta n
      ![.exceptional i, .hyperplane, .hyperplane] = 0 := by
    rw [SurfaceGenusTwoBlowupPCoefficients.remainder_orbit]
    apply paper_one_of_hyperplane_of_planeDegree_zero v delta hd n _
      ((BelorousskiPandharipande.labelPermutation e).symm 1)
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero]
  have hpair (s : Fin 2) := pair_markings_ehh_of_planeDegree_zero i v n s delta hd
  simp only [remainderVertex_onePsi_of_not_points v hv, if_neg hz, mul_zero] at hpair
  have h2 := hpair (0 : Fin 2)
  have h3 := hpair (1 : Fin 2)
  simp only [ite_true, if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h2 h3
  simp only [BelorousskiPandharipande.pointCoefficient, hterm]
  rw [Fin.sum_univ_four]
  change -2 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 0 e) delta n
        ![.exceptional i, .hyperplane, .hyperplane]) +
    2 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 1 e) delta n
        ![.exceptional i, .hyperplane, .hyperplane]) +
    3 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 2 e) delta n
        ![.exceptional i, .hyperplane, .hyperplane]) +
    -3 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 3 e) delta n
        ![.exceptional i, .hyperplane, .hyperplane]) = 0
  simp only [hzero, hone, h2, h3, Finset.sum_const_zero, mul_zero, add_zero]

/-- The six original EEH assignments retain twice the H/E_i main pair only at remainder E_i. -/
theorem pair_markings_eeh_nonprimary_pos (X : SurfaceTarget) (i : Fin X.blowups)
    (v : Variable X) (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (delta : X.Curve) (hd : X.planeDegree delta = 0) (hz : delta ≠ 0) (n : ℕ) (s : Fin 2) :
    (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm (if s = 0 then 2 else 3) e) delta n
        ![.exceptional i, .exceptional i, .hyperplane]) =
      2 * (if delta = X.exceptionalCurve i then
        remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
          (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0 ![.hyperplane, .exceptional i]
        else 0) := by
  simp only [SurfaceGenusTwoBlowupPCoefficients.remainder_orbit, eeh_permutation]
  rw [Fin.sum_univ_six]
  have hHE : (.hyperplane : SurfaceBasisLabel X).value *
      (SurfaceBasisLabel.exceptional i : SurfaceBasisLabel X).value = 0 :=
    SurfaceCohomology.hyperplane_mul_exceptional X.blowups i
  have hEH : (.exceptional i : SurfaceBasisLabel X).value *
      (SurfaceBasisLabel.hyperplane : SurfaceBasisLabel X).value = 0 := by rw [mul_comm]; exact hHE
  have h0 := paper_pair_orthogonal_of_planeDegree_zero v n s delta hd
    (.exceptional i) (.exceptional i) .hyperplane hEH (Or.inr rfl)
  have h1 := paper_pair_orthogonal_of_planeDegree_zero v n s delta hd
    (.exceptional i) .hyperplane (.exceptional i) hHE (Or.inl rfl)
  change remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![.exceptional i, .exceptional i, .hyperplane] +
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![.exceptional i, .hyperplane, .exceptional i] +
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![.exceptional i, .exceptional i, .hyperplane] +
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![.hyperplane, .exceptional i, .exceptional i] +
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![.exceptional i, .hyperplane, .exceptional i] +
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![.hyperplane, .exceptional i, .exceptional i] = _
  simp only [h0, h1, zero_add, add_zero, paper_pair_ee_nonprimary_pos X i v hv delta hd hz n s
    .hyperplane]
  ring

/-- The actual EEH nonprimary coefficient at a proper plane-zero remainder keeps its two H/E_i
  cotangent positions. -/
theorem pointCoefficient_eeh_nonprimary_pos (X : SurfaceTarget) (i : Fin X.blowups)
    (v : Variable X) (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (delta : X.Curve) (hd : X.planeDegree delta = 0) (hz : delta ≠ 0) (n : ℕ) :
    BelorousskiPandharipande.pointCoefficient X n (SurfaceGenusZero.variableCurve v + delta)
      ![.exceptional i, .exceptional i, .hyperplane] v =
      if delta = X.exceptionalCurve i then
        6 * remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
          (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0 ![.hyperplane, .exceptional
            i] -
        6 * remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
          (by norm_num [StableArity]) (Pi.single 1 1) inferInstance 0 ![.hyperplane, .exceptional i]
      else 0 := by
  have hterm (j : Fin 20) (e : Fin 6) :
      SurfaceGenusTwo.pointCoefficient X v (BelorousskiPandharipande.orbitCotangentTerm j e)
        (SurfaceGenusZero.variableCurve v + delta) n ![.exceptional i, .exceptional i,
          .hyperplane] =
      remainderPointCoefficient X v (coefficientVertex X v)
        (BelorousskiPandharipande.orbitCotangentTerm j e) delta n
          ![.exceptional i, .exceptional i, .hyperplane] :=
    (remainderPointCoefficient_eq X v (coefficientVertex X v) rfl
      (BelorousskiPandharipande.orbitCotangentTerm j e) delta n _).symm
  have hzero (e : Fin 6) : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 0 e) delta n
      ![.exceptional i, .exceptional i, .hyperplane] = 0 := by
    rw [SurfaceGenusTwoBlowupPCoefficients.remainder_orbit,
      SurfaceGenusTwoBlowupPCoefficients.paper_zero v hv]
  have hone (e : Fin 6) : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 1 e) delta n
      ![.exceptional i, .exceptional i, .hyperplane] = 0 := by
    rw [SurfaceGenusTwoBlowupPCoefficients.remainder_orbit]
    apply paper_one_of_hyperplane_of_planeDegree_zero v delta hd n _
      ((BelorousskiPandharipande.labelPermutation e).symm 2)
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Matrix.cons_val_two]
    rfl
  have h2 := pair_markings_eeh_nonprimary_pos X i v hv delta hd hz n (0 : Fin 2)
  have h3 := pair_markings_eeh_nonprimary_pos X i v hv delta hd hz n (1 : Fin 2)
  simp only [ite_true, if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h2 h3
  simp only [BelorousskiPandharipande.pointCoefficient, hterm]
  rw [Fin.sum_univ_four]
  change -2 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 0 e) delta n
        ![.exceptional i, .exceptional i, .hyperplane]) +
    2 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 1 e) delta n
        ![.exceptional i, .exceptional i, .hyperplane]) +
    3 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 2 e) delta n
        ![.exceptional i, .exceptional i, .hyperplane]) +
    -3 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 3 e) delta n
        ![.exceptional i, .exceptional i, .hyperplane]) = _
  simp only [hzero, hone, Finset.sum_const_zero, mul_zero, zero_add]
  rw [h2, h3]
  split_ifs <;> ring

/-- The full normalized EEH row has K_j coefficient minus six d exactly at its E_i remainder with
  j equal to i. -/
theorem normalized_eeh_k_proper_remainder (X : SurfaceTarget) (i j : Fin X.blowups)
    (beta gamma delta : X.Curve) (hs : gamma + delta = beta + X.exceptionalCurve i)
    (hd : X.planeDegree delta = 0) (hz : delta ≠ 0) :
    RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.bpRow X (X.effective.energy beta)
      (beta + X.exceptionalCurve i) ![.exceptional i, .exceptional i, .hyperplane])
      {Sum.inr (SurfaceFirstDescendant.query 2 gamma (.exceptional j) (X.effective.energy gamma))}
        =
      if delta = X.exceptionalCurve i ∧ i = j then -6 * (X.planeDegree beta : ℚ) else 0 := by
  let v : Variable X := .inr (SurfaceFirstDescendant.query 2 gamma (.exceptional j)
    (X.effective.energy gamma))
  have hv : ∀ eta m, Sum.inr (SurfaceQuery.points X 2 eta m) ≠ v :=
    fun eta m ↦ SurfaceFirstDescendant.query_ne_points gamma eta (.exceptional j)
      (X.effective.energy gamma) m
  have hc := pointCoefficient_eeh_nonprimary_pos X i v hv delta hd hz (X.effective.energy beta)
  have hvar : SurfaceGenusZero.variableCurve v = gamma := rfl
  rw [hvar] at hc
  rw [SurfaceGenusTwoBlowupNRelation.bpRow, ← BelorousskiPandharipande.pointCoefficient_eq_full,
    ← hs, hc]
  by_cases hdi : delta = X.exceptionalCurve i
  · have hg : gamma = beta := by rw [hdi] at hs; exact add_right_cancel hs
    rw [if_pos hdi, ← hg, main_hyperplane_exceptional_k X i j gamma 0,
      main_hyperplane_exceptional_k X i j gamma 1]
    simp only [show (0 : Fin 2) ≠ 1 by decide, false_and, ite_false, true_and, mul_zero, zero_sub,
      hdi, true_and]
    by_cases hij : i = j <;> simp only [hij, ite_true, ite_false] <;> ring
  · rw [if_neg hdi, if_neg (fun h ↦ hdi h.1)]

/-- Bind the EHH proper-remainder nonprimary vanishing to the complete original normalized
  polynomial. -/
theorem normalized_ehh_nonprimary_proper_remainder (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) (v : Variable X)
    (hv : ∀ gamma m, Sum.inr (SurfaceQuery.points X 2 gamma m) ≠ v)
    (delta : X.Curve) (hs : SurfaceGenusZero.variableCurve v + delta = beta + X.exceptionalCurve i)
    (hd : X.planeDegree delta = 0) (hz : delta ≠ 0) :
    RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.bpRow X (X.effective.energy beta)
      (beta + X.exceptionalCurve i) ![.exceptional i, .hyperplane, .hyperplane]) {v} = 0 := by
  rw [SurfaceGenusTwoBlowupNRelation.bpRow,
    ← BelorousskiPandharipande.pointCoefficient_eq_full, ← hs]
  exact pointCoefficient_ehh_nonprimary_pos X i v hv delta hd hz (X.effective.energy beta)

end AxiomaticGW.SurfaceGenusTwoBlowupNMixedKSupport

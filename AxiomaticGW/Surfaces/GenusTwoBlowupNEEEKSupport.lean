/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupNEEEPrimary
public import AxiomaticGW.Surfaces.GenusTwoBlowupNExceptionalRational
public import AxiomaticGW.Surfaces.GenusTwoBlowupNRelation

/-!
# Exceptional descendant columns at proper same-plane remainders

For a full effective splitting `gamma + delta = beta + E_i`, with nonzero
`delta` of plane degree zero, the complete normalized exceptional BP triple
has coefficient `-12` at `K_j(gamma)` exactly when `delta = E_i` and `i = j`.
All full coordinates are retained, including reducible exceptional remainders
and class-zero requested queries. No energy or plane-degree positivity premise
is added to the final coefficient identity.

The generic nonprimary calculation keeps the original four graphs and six
marking assignments. The two pair graphs cancel after swapping equal markings;
the one-marking graph retains the rational exceptional four-point scalar and
the metric sign. Its rational support is imported from the shared lower module.
Primary columns are excluded explicitly from these intermediate statements,
since their calibration corrections need not vanish.

This proves one proper-remainder coefficient identity, not combined N-row
cancellation, support for every family, a recurrence, or geometric applicability.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupNEEEKSupport
open SurfacePolynomialReduction SurfaceGenusTwo GluingExpression
open SurfaceGenusTwoBlowupPCoefficients SurfaceGenusTwoBlowupKCoefficients
open SurfaceGenusTwoBlowupNExceptionalRational

-- Actual decorated join constructors require this depth during elaboration.
set_option maxRecDepth 20000

variable {X : SurfaceTarget}

/-- The actual one-marking BP graph has only the selected exceptional rational remainder. -/
theorem paper_one_eee (X : SurfaceTarget) (i : Fin X.blowups)
    (v : Variable X) (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (delta : X.Curve) (hd : X.planeDegree delta = 0) (n : ℕ) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 1) delta n
        ![.exceptional i, .exceptional i, .exceptional i] =
      if delta = X.exceptionalCurve i then
        -remainderVertex X v (coefficientVertex X v) n 2 (Fin 1)
          (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0 ![.exceptional i]
      else 0 := by
  have hx : (BelorousskiPandharipande.paperCotangentTerm 1).expression.maxComponentGenus = 2 :=
    by decide +kernel
  rw [remainderPointCoefficient, if_pos hx]
  change remainderContraction X v (remainderVertex X v (coefficientVertex X v))
    (GetzlerGraphs.join (m := 0) (n := 3) 0 3
      (fundamental 2 (Fin 1) (by norm_num [StableArity]))
      (fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (![1], (0 : Fin 4 → ℕ))
    ((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 4)))
    delta n ![.exceptional i, .exceptional i, .exceptional i] = _
  let a : Fin 3 → SurfaceBasisLabel X := ![.exceptional i, .exceptional i, .exceptional i]
  have hl (b : SurfaceBasisLabel X) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 0 ⊕ Fin 3 ≃ Fin 3)) ∘ Sum.inl)) ∘
        finSuccEquiv' 0 = ![b] := by ext j; fin_cases j; rfl
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 0 ⊕ Fin 3 ≃ Fin 3)) ∘ Sum.inr)) ∘
        finSuccEquiv' 3 = ![.exceptional i, .exceptional i, .exceptional i, b] := by
    ext j; fin_cases j <;> rfl
  have hp : (![1] : Fin 1 → ℕ) = Pi.single 0 1 := by ext j; fin_cases j; rfl
  change remainderContraction X v (remainderVertex X v (coefficientVertex X v)) _ _ _ delta n a = _
  simp only [GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction, hl, hr, primaryPointVertex, and_self, hp]
  rw [Finset.sum_eq_single (0, delta)]
  · change (∑ b : SurfaceBasisLabel X, b.inverseWeight *
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
        (remainderVertex X v (coefficientVertex X v) ij.1 2 (Fin 1)
          (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0 ![b] *
          SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) delta ij.2
            ![.exceptional i, .exceptional i, .exceptional i, b.dual])) = _
    have hq (b : SurfaceBasisLabel X) := quad_points X i delta hd
      (fun m ↦ remainderVertex X v (coefficientVertex X v) m 2 (Fin 1)
        (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0 ![b]) n b.dual
    simp only [hq]
    by_cases hdEi : delta = X.exceptionalCurve i
    · rw [if_pos hdEi]
      simp only [hdEi, true_and]
      rw [Finset.sum_eq_single (.exceptional i)]
      · simp only [SurfaceBasisLabel.inverseWeight, SurfaceBasisLabel.dual, ite_true,
          neg_one_mul]
      · intro b _ hb
        have hbd : b.dual ≠ .exceptional i := by
          cases b with
          | unit | hyperplane | point => intro h; cases h
          | exceptional j => intro h; cases h; exact hb rfl
        rw [if_neg hbd, mul_zero]
      · exact fun h ↦ (h (Finset.mem_univ _)).elim
    · rw [if_neg hdEi]
      simp only [hdEi, false_and, ite_false, mul_zero, Finset.sum_const_zero]
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

/-- The one-marking exceptional cotangent main has dimension exactly when added points
equal energy. -/
theorem main_one_dimension (X : SurfaceTarget) (beta : X.Curve) (i : Fin X.blowups) (n : ℕ) :
    SurfaceAncestorKey.DimensionCompatible
      ((SurfaceAncestorKey.ofLabels 2 (Fin 1) (by norm_num [StableArity]) beta
        (Pi.single 0 1) (![.exceptional i] : Fin 1 → SurfaceBasisLabel X)).addPoints n) ↔
      X.effective.energy beta = n := by
  simp only [SurfaceAncestorKey.DimensionCompatible, SurfaceAncestorKey.totalCodimension,
    SurfaceAncestorKey.addPoints, SurfaceAncestorKey.ofLabels, Multiset.map_add,
    Multiset.map_replicate, Multiset.sum_add, Multiset.sum_replicate,
    Multiset.card_add, Multiset.card_replicate, Multiset.card_map, Finset.card_val,
    Finset.card_univ, Fintype.card_fin, SurfaceTarget.c1Degree, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  change (n : ℤ)*2+2 = (X.effective.energy beta : ℤ)+2-1+((n : ℤ)+1) ↔ _
  omega

/-- A dimension-compatible one-marking main isolates its complete exceptional descendant request. -/
theorem main_one (X : SurfaceTarget) (i : Fin X.blowups) (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (n : ℕ) (he : X.effective.energy (SurfaceGenusZero.variableCurve v) = n) :
    remainderVertex X v (coefficientVertex X v) n 2 (Fin 1)
      (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0 ![.exceptional i] =
      if Sum.inr (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
        (.exceptional i) n) = v then 1 else 0 := by
  have hm : ((Finset.univ.erase (0 : Fin 1)).val.map
      (![.exceptional i] : Fin 1 → SurfaceBasisLabel X)) = 0 := rfl
  have hu : SurfaceBasisLabel.unit ∉
      (Multiset.replicate n .point : Multiset (SurfaceBasisLabel X)) := by
    simp only [Multiset.mem_replicate, reduceCtorEq, and_false, not_false_eq_true]
  have hd : (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
      (.exceptional i) n).DimensionCompatible := by
    rw [SurfaceQuery.dimensionCompatible_first, he]
    rfl
  rw [remainderVertex_onePsi_of_not_points v hv, if_pos rfl,
    coefficient_residualTerms_onePsi_of_not_points v hv,
    if_pos ((main_one_dimension X _ i n).mpr he)]
  simp only [hm, add_zero, Matrix.cons_val_zero]
  rw [SurfaceFirstDescendant.terms, if_neg hu,
    if_neg (show (SurfaceBasisLabel.exceptional i : SurfaceBasisLabel X) ≠ .unit from by
      intro heq; cases heq)]
  rw [RationalTerms.coefficient_rename_add, RationalTerms.coefficient_rename_scale,
    RationalTerms.coefficient_rename_scale]
  simp only [SurfaceFirstDescendant.primaryCoefficient, Multiset.map_replicate,
    Multiset.prod_replicate, SurfaceBasisLabel.primaryFactor, one_pow,
    SurfaceFirstDescendant.correctionCoefficient, SurfaceFirstDescendant.divisorSquare,
    Multiset.count_replicate, reduceCtorEq, ite_false, ite_true, Nat.cast_zero, mul_zero, zero_mul,
    one_mul, add_zero]
  rw [SurfaceFirstDescendant.dimensionTerms, if_pos hd,
    RationalTerms.coefficient_rename_term]
  simp only [Multiset.map_singleton, Multiset.singleton_inj]

/-- At a nonzero plane-zero remainder, both actual pair graphs have only the selected
exceptional branch. -/
theorem paper_pair_eee_pos (X : SurfaceTarget) (i : Fin X.blowups)
    (v : Variable X) (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (delta : X.Curve) (hd : X.planeDegree delta = 0) (hz : delta ≠ 0) (n : ℕ) (s : Fin 2) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![.exceptional i, .exceptional i, .exceptional i] =
      if delta = X.exceptionalCurve i then
        remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
          (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0
            ![.exceptional i, .exceptional i]
      else 0 := by
  by_cases hdi : delta = X.exceptionalCurve i
  · subst delta
    rw [if_pos rfl,
      SurfaceGenusTwoBlowupNEEEPrimary.paper_pair_exceptional i v n s (.exceptional i)]
    have hmain :
        remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
          (by norm_num [StableArity]) (Pi.single s 1) inferInstance (X.exceptionalCurve i)
          ![.exceptional i, .point] = 0 := by
      have hne : X.exceptionalCurve i ≠ 0 := by
        intro hzero
        have he := X.energy_exceptionalCurve i
        rw [hzero, map_zero] at he
        cases he
      rw [remainderVertex_onePsi_of_not_points v hv, if_neg hne]
    rw [hmain, sub_zero]
  · have h0 : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
    have h1 : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
    have he : remainderPointCoefficient X v (coefficientVertex X v)
        (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
          ![.exceptional i, .exceptional i, .exceptional i] =
        remainderContraction X v (remainderVertex X v (coefficientVertex X v))
          (GetzlerGraphs.join (m := 1) (n := 2) 1 2
            (fundamental 2 (Fin 2) (by norm_num [StableArity]))
            (fundamental 0 (Fin 3) (by norm_num [StableArity])))
          (by exact (Pi.single s 1, (0 : Fin 3 → ℕ)))
          (by exact ((inferInstance : DecidableEq (Fin 2)),
            (inferInstance : DecidableEq (Fin 3)))) delta n
              ![.exceptional i, .exceptional i, .exceptional i] := by
      have hs : s = 0 ∨ s = 1 := by omega
      rcases hs with rfl | rfl
      · rw [if_pos rfl, ← h0]; rfl
      · rw [if_neg (by decide : (1 : Fin 2) ≠ 0), ← h1]; rfl
    rw [he, pair_join]
    simp only [remainderContraction, ite_true]
    rw [Finset.sum_eq_single (0, delta)]
    · have ht (b : SurfaceBasisLabel X) := triple_points_pos X i delta hd hz
        (fun m ↦ remainderVertex X v (coefficientVertex X v) m 2 (Fin 2)
          (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0 ![.exceptional i, b]) n b.dual
      simp only [ht]
      rw [if_neg hdi]
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

/-- The two equal exceptional markings give identical nonprimary main coefficients
after swapping the psi flag. -/
theorem main_pair_symmetric (X : SurfaceTarget) (i : Fin X.blowups)
    (v : Variable X) (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (n : ℕ) :
    remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0
        ![.exceptional i, .exceptional i] =
    remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single 1 1) inferInstance 0
        ![.exceptional i, .exceptional i] := by
  have hq : SurfaceAncestorKey.ofLabels 2 (Fin 2) (by norm_num [StableArity])
      (SurfaceGenusZero.variableCurve v) (Pi.single 0 1)
      (![.exceptional i, .exceptional i] : Fin 2 → SurfaceBasisLabel X) =
    SurfaceAncestorKey.ofLabels 2 (Fin 2) (by norm_num [StableArity])
      (SurfaceGenusZero.variableCurve v) (Pi.single 1 1)
      (![.exceptional i, .exceptional i] : Fin 2 → SurfaceBasisLabel X) := by
    simp only [SurfaceAncestorKey.ofLabels, SurfaceAncestorKey.mk.injEq, true_and]
    change ({⟨.exceptional i, 1⟩, ⟨.exceptional i, 0⟩} : Multiset (SurfaceInsertion X)) =
      {⟨.exceptional i, 0⟩, ⟨.exceptional i, 1⟩}
    exact Multiset.pair_comm _ _
  rw [remainderVertex_onePsi_of_not_points v hv,
    remainderVertex_onePsi_of_not_points v hv, if_pos rfl, if_pos rfl, hq]

/-- The complete original four-graph, six-marking BP coefficient retains only the
one-marking exceptional branch. -/
theorem pointCoefficient_eee_pos (X : SurfaceTarget) (i : Fin X.blowups)
    (v : Variable X) (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (delta : X.Curve) (hd : X.planeDegree delta = 0) (hz : delta ≠ 0) (n : ℕ) :
    BelorousskiPandharipande.pointCoefficient X n
      (SurfaceGenusZero.variableCurve v + delta)
      ![.exceptional i, .exceptional i, .exceptional i] v =
      if delta = X.exceptionalCurve i then
        -12 * remainderVertex X v (coefficientVertex X v) n 2 (Fin 1)
          (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0 ![.exceptional i]
      else 0 := by
  have hlabel (e : Fin 6) :
      (![.exceptional i, .exceptional i, .exceptional i] : Fin 3 → SurfaceBasisLabel X) ∘
        BelorousskiPandharipande.labelPermutation e =
        ![.exceptional i, .exceptional i, .exceptional i] := by
    have ha : (![.exceptional i, .exceptional i, .exceptional i] : Fin 3 → SurfaceBasisLabel X) =
        fun _ ↦ .exceptional i := by ext j; fin_cases j <;> rfl
    rw [ha]; rfl
  have hterm (j : Fin 20) (e : Fin 6) :
      SurfaceGenusTwo.pointCoefficient X v (BelorousskiPandharipande.orbitCotangentTerm j e)
        (SurfaceGenusZero.variableCurve v + delta) n
        ![.exceptional i, .exceptional i, .exceptional i] =
      remainderPointCoefficient X v (coefficientVertex X v)
        (BelorousskiPandharipande.paperCotangentTerm j) delta n
          ![.exceptional i, .exceptional i, .exceptional i] := by
    rw [← remainderPointCoefficient_eq X v (coefficientVertex X v) rfl]
    simp only [BelorousskiPandharipande.orbitCotangentTerm, CotangentTerm.relabel,
      remainderPointCoefficient, GluingExpression.maxComponentGenus, remainderContraction, hlabel]
  simp only [BelorousskiPandharipande.pointCoefficient, hterm,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fin.sum_univ_four]
  change -2 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 0) delta n
        ![.exceptional i, .exceptional i, .exceptional i]) +
    2 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 1) delta n
        ![.exceptional i, .exceptional i, .exceptional i]) +
    3 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 2) delta n
        ![.exceptional i, .exceptional i, .exceptional i]) +
    -3 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 3) delta n
        ![.exceptional i, .exceptional i, .exceptional i]) = _
  rw [paper_zero v hv, paper_one_eee X i v hv delta hd]
  have h2 := paper_pair_eee_pos X i v hv delta hd hz n (0 : Fin 2)
  have h3 := paper_pair_eee_pos X i v hv delta hd hz n (1 : Fin 2)
  simp only [ite_true, if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h2 h3
  rw [h2, h3, ← main_pair_symmetric X i v hv]
  split_ifs <;> ring

/-- The complete normalized EEE row has proper same-plane K coefficient minus twelve
precisely at the selected exceptional remainder and label. -/
theorem normalized_eee_k_proper_remainder (X : SurfaceTarget) (i j : Fin X.blowups)
    (beta gamma delta : X.Curve)
    (hs : gamma + delta = beta + X.exceptionalCurve i)
    (hd : X.planeDegree delta = 0) (hz : delta ≠ 0) :
    RationalTerms.coefficient
      (SurfaceGenusTwoBlowupNRelation.bpRow X (X.effective.energy beta)
        (beta + X.exceptionalCurve i) ![.exceptional i, .exceptional i, .exceptional i])
      {Sum.inr (SurfaceFirstDescendant.query 2 gamma (.exceptional j)
        (X.effective.energy gamma))} =
      if delta = X.exceptionalCurve i ∧ i = j then -12 else 0 := by
  let v : Variable X := .inr (SurfaceFirstDescendant.query 2 gamma (.exceptional j)
    (X.effective.energy gamma))
  have hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v :=
    fun beta n ↦ SurfaceFirstDescendant.query_ne_points gamma beta (.exceptional j)
      (X.effective.energy gamma) n
  have hc := pointCoefficient_eee_pos X i v hv delta hd hz (X.effective.energy beta)
  have hvar : SurfaceGenusZero.variableCurve v = gamma := rfl
  rw [hvar] at hc
  rw [SurfaceGenusTwoBlowupNRelation.bpRow, ← BelorousskiPandharipande.pointCoefficient_eq_full,
    ← hs, hc]
  by_cases hdi : delta = X.exceptionalCurve i
  · have he : X.effective.energy gamma = X.effective.energy beta := by
      have h := congrArg X.effective.energy hs
      rw [map_add, X.energy_add_exceptionalCurve, hdi, X.energy_exceptionalCurve] at h
      omega
    rw [if_pos hdi, ← he]
    have hm := main_one X i v hv (X.effective.energy gamma) (by rw [hvar])
    rw [hvar] at hm
    rw [hm]
    by_cases hij : i = j
    · subst j
      simp only [v, hdi, and_self, ite_true, mul_one]
    · have hneq : Sum.inr (SurfaceFirstDescendant.query 2 gamma (.exceptional i)
          (X.effective.energy gamma)) ≠ v :=
        first_queries_ne gamma (.exceptional i) (.exceptional j)
          (X.effective.energy gamma) (X.effective.energy gamma)
          (fun h ↦ hij (SurfaceBasisLabel.exceptional.inj h))
      rw [if_neg hneq, if_neg (fun h ↦ hij h.2), mul_zero]
  · rw [if_neg hdi, if_neg (fun h ↦ hdi h.1)]

end AxiomaticGW.SurfaceGenusTwoBlowupNEEEKSupport

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupPPrimarySupport
public import AxiomaticGW.Surfaces.GenusTwoBlowupKCoefficients
public import AxiomaticGW.Surfaces.Fixtures.FirstCalibration
public import AxiomaticGW.Surfaces.GenusTwoBlowupNExceptionalRational

/-!
# The shifted primary column of the exceptional BP triple

For every full effective class `beta`, the original normalized BP row with
three copies of `E_i`, source class `beta + E_i`, and `energy(beta)` added
points has coefficient `12 - 18 * alpha_i` at the primary genus-two request
`N_beta`. Here `alpha_i` is the signed exceptional intersection, including
zero and negative values. Class zero is included.

The proof binds the actual first four BP graphs and all six marking assignments.
Their requested coefficients are `-1`, `0`, `-1-alpha_i`, and `-1` before their
original weights. The shared primary correction in the last two graphs cancels.
An exceptional cotangent tail carrying a point vanishes by the existing
low-genus reconstruction; the retained first-calibration matrix instead gives
the nonzero shifted primary factor. Neither correction is assumed away.

These are coefficient identities for the complete polynomial. They add no
geometric law, numerical seed, recurrence, or support/pivot hypothesis. Combined
row support and a complete reconstruction remain separate obligations.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwoBlowupNEEEPrimary
open SurfacePolynomialReduction SurfaceGenusTwo GluingExpression
open SurfaceGenusTwoBlowupPCoefficients SurfaceGenusTwoBlowupPPrimary
open SurfaceGenusTwoBlowupPPrimarySupport
set_option maxRecDepth 20000

variable {X : SurfaceTarget}

/-- The complete raised first-calibration matrix at an exceptional generator. -/
theorem firstCalibrationMatrix_exceptional_eq (X : SurfaceTarget) (i : Fin X.blowups) :
    SurfaceDescendant.firstCalibrationMatrix X (X.exceptionalCurve i) =
      SurfaceFirstCalibration.exceptionalMatrix X i := by
  rw [← SurfaceFirstCalibration.values_eq]
  cases X with
  | plane => exact Fin.elim0 i
  | hirzebruchOne => fin_cases i; decide +kernel
  | blowupTwo => fin_cases i <;> decide +kernel

/-- The exceptional input has its negative self-pairing and no other output row. -/
theorem firstCalibrationMatrix_exceptional_column (X : SurfaceTarget)
    (i : Fin X.blowups) (row : SurfaceBasisLabel X) :
    SurfaceDescendant.firstCalibrationMatrix X (X.exceptionalCurve i) row (.exceptional i) =
      if row = .exceptional i then -1 else 0 := by
  rw [firstCalibrationMatrix_exceptional_eq]
  simp only [SurfaceFirstCalibration.exceptionalMatrix, and_true]

private theorem primaryScalar_exceptional_point_tail_eq_zero (X : SurfaceTarget) (i : Fin X.blowups)
    (gamma : X.Curve) (hd : X.planeDegree gamma = 0) (n : ℕ) (b : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) gamma n
      (Option.elim · b (fun t : Bool ↦ if t then .point else .exceptional i)) = 0 := by
  by_cases he : 2 ≤ X.effective.energy gamma
  · have hn : gamma ≠ 0 := by intro hz; rw [hz, map_zero] at he; omega
    rw [SurfaceGenusZero.primaryScalar, if_pos ⟨hn,
      SurfaceGenusZero.pointValue_eq_zero_of_hyperplane_zero_of_energy_ge_two X gamma
      ((X.planeDegree_eq_zero_iff_divisorIntersections_eq_zero gamma).mp hd) he⟩]
  · by_cases hb : b = .unit
    · subst b
      by_cases hz : gamma = 0
      · subst gamma
        have hdim : ¬((((∑ j : Option Bool,
            ((Option.elim · .unit (fun t : Bool ↦
              if t then (SurfaceBasisLabel.point : SurfaceBasisLabel X)
              else .exceptional i)) j).codimension : ℕ) : ℤ)
            + (n : ℤ)) = X.c1Degree 0 - 1 + (Fintype.card (Option Bool) : ℤ)) := by
          simp only [Fintype.sum_option, Fintype.sum_bool, Option.elim_none, Option.elim_some,
            ite_true, Bool.false_eq_true, ite_false, SurfaceBasisLabel.codimension,
            Fintype.card_option, Fintype.card_bool, map_zero]
          norm_num only at *
          omega
        rw [SurfaceGenusZero.primaryScalar, if_neg (fun h ↦ h.1 rfl), if_neg hdim]
      · unfold SurfaceGenusZero.primaryScalar
        split_ifs with hv hdim
        · rfl
        · rw [Fintype.prod_option, Fintype.prod_bool]
          change (0 * (1 * (X.divisorIntersections gamma i.succ : ℚ))) * _ = 0
          ring
        · rfl
    · have hc : 1 ≤ b.codimension := by
        cases b <;> first | exact (hb rfl).elim | exact Nat.le_refl _ | exact Nat.le_succ _
      have hdim : ¬((((∑ j : Option Bool,
          ((Option.elim · b (fun t : Bool ↦
            if t then (SurfaceBasisLabel.point : SurfaceBasisLabel X)
            else .exceptional i)) j).codimension : ℕ) : ℤ)
          + (n : ℤ)) = X.c1Degree gamma - 1 + (Fintype.card (Option Bool) : ℤ)) := by
        simp only [Fintype.sum_option, Fintype.sum_bool, Option.elim_none, Option.elim_some,
          ite_true, Bool.false_eq_true, ite_false, SurfaceBasisLabel.codimension,
          Fintype.card_option, Fintype.card_bool,
          SurfaceTarget.c1Degree]
        change ¬(((b.codimension + (2 + 1) : ℕ) : ℤ) + (n : ℤ) =
          (X.effective.energy gamma : ℤ) - 1 + 3)
        omega
      rw [SurfaceGenusZero.primaryScalar]
      split_ifs <;> rfl

/-- The actual signed point-cotangent tail vanishes for an exceptional old state
at any plane-zero effective remainder, for every terminal callback. -/
theorem remainderContraction_exceptionalPsi_eq_zero_of_planeDegree_zero
    (i : Fin X.blowups) (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (delta : X.Curve) (hd : X.planeDegree delta = 0)
    (n : ℕ) (a : S → SurfaceBasisLabel X)
    (hs : a s = .exceptional i) :
    let z := CotangentTerm.tail h (Pi.single s 1) s
    remainderContraction X v main z.expression z.decoration z.labels
      delta n (Option.elim · .point a) = 0 := by
  have hp : Function.update (Pi.single s 1 : S → ℕ) s
      ((Pi.single s 1 : S → ℕ) s - 1) = (0 : S → ℕ) := by
    funext t
    by_cases ht : t = s
    · subst t
      simp only [Function.update_self, Pi.single_eq_same, Nat.sub_self, Pi.zero_apply]
    · rw [Function.update_of_ne ht, Pi.single_eq_of_ne ht]
      rfl
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b (((Option.elim · SurfaceBasisLabel.point a) ∘
        PsiBoundaryExpansion.tailLabels s) ∘ Sum.inr)) =
        (Option.elim · b (fun t : Bool ↦ if t then .point else a s)) := by
    funext t
    rcases t with _ | (_ | _) <;> rfl
  have hz : (fun _ : Option Bool ↦ (0 : ℕ)) = 0 := rfl
  dsimp only
  simp only [CotangentTerm.tail, CotangentTerm.relabel, CotangentTerm.separating,
    CotangentTerm.fundamental, remainderContraction, ite_true, hp,
    primaryPointVertex_eq, GluingExpression.pointContraction,
    hz, vertex_primary_genusZero_eq, hr]
  apply Finset.sum_eq_zero
  intro split hsplit
  have ha : split.1 + split.2 = delta := by
    rw [X.splittings_eq] at hsplit
    exact (X.effective.mem_splittings _ _ _).mp hsplit
  have ht : X.planeDegree split.2 = 0 := by
    have he := congrArg X.planeDegree ha
    rw [map_add, hd] at he
    omega
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  have hv : SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) split.2 ij.2
      (Option.elim · b.dual (fun t : Bool ↦ if t then .point else a s)) = 0 := by
    rw [hs]
    exact primaryScalar_exceptional_point_tail_eq_zero X i split.2 ht ij.2 b.dual
  rw [hv, mul_zero, mul_zero]

/-- At plane-zero remainders, an exceptional old cotangent state keeps its complete
normalized terminal expression, including its nonzero primary calibration. -/
theorem remainderVertex_exceptionalPsi_of_planeDegree_zero
    (i : Fin X.blowups) (v : Variable X) (n : ℕ)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (delta : X.Curve) (hd : X.planeDegree delta = 0)
    (a : S → SurfaceBasisLabel X) (hs : a s = .exceptional i) :
    remainderVertex X v (coefficientVertex X v) n 2 S h (Pi.single s 1)
      inferInstance delta a =
      RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
        (residualTerms ((SurfaceAncestorKey.ofLabels 2 S h
          (SurfaceGenusZero.variableCurve v + delta) (Pi.single s 1) a).addPoints n))) {v} := by
  induction n generalizing S with
  | zero =>
    simp only [remainderVertex, coefficientVertex, ite_true, vertexTerms,
      SurfaceAncestorKey.addPoints_zero]
  | succ n ih =>
    rw [remainderVertex_onePsi_step,
      remainderContraction_exceptionalPsi_eq_zero_of_planeDegree_zero i v _ S h s delta hd n a hs,
      sub_zero]
    rw [ih (Option S) h.option (some s) (Option.elim · .point a)
      (show (Option.elim · .point a) (some s) = .exceptional i from hs)]
    have hk : (Pi.single (some s) 1 : Option S → ℕ) =
        (Option.elim · 0 (Pi.single s 1)) := by
      funext t
      cases t with
      | none => simp only [Option.elim_none, Pi.single_eq_of_ne
          (show (none : Option S) ≠ some s from by intro he; cases he)]
      | some t =>
        by_cases ht : t = s
        · subst t
          simp only [Option.elim_some, Pi.single_eq_same]
        · simp only [Option.elim_some, Pi.single_eq_of_ne ht,
            Pi.single_eq_of_ne (fun he ↦ ht (Option.some.inj he))]
    rw [hk, SurfaceAncestorKey.addPoints_ofLabels_option_powers 2 S h
      (SurfaceGenusZero.variableCurve v + delta) (Pi.single s 1) a n]


/-- At a single exceptional shift, the complete primary calibration coefficient
is the unchanged primary label list at the requested main class. -/
theorem coefficient_normalizedTerms_shifted_exceptional
    (i : Fin X.blowups) (beta : X.Curve) (q : SurfaceAncestorKey X)
    (hg : q.genus = 2) (hp : q.totalPsi = 1)
    (hb : q.beta = beta + X.exceptionalCurve i)
    (hh : (q.onePsiInsertion hp).label = .exceptional i)
    (v : Variable X) (hv : SurfaceGenusZero.variableCurve v = beta) :
    RationalTerms.coefficient (normalizedTerms q) {v} =
      RationalTerms.coefficient (RationalTerms.rename Sum.inr
        (SurfaceFirstDescendant.primaryTerms 2 beta q.primaryLabels)) {v} := by
  have h : 2 ≤ q.genus ∧ q.totalPsi = 1 := ⟨by omega, hp⟩
  have hn : SurfaceGenusZero.variableCurve v ≠ q.beta := by
    rw [hv, hb]
    intro he
    have he' := congrArg X.effective.energy he
    rw [X.energy_add_exceptionalCurve] at he'
    omega
  have hd := coefficient_directNormalizedTerms_eq_zero q h.1 v hn
  unfold directNormalizedTerms at hd
  unfold normalizedTerms
  rw [dif_pos h] at hd ⊢
  rw [RationalTerms.coefficient_add, hd, zero_add, RationalTerms.coefficient_sum]
  have htail : X.exceptionalCurve i ≠ 0 := by
    intro he
    have he' := congrArg X.effective.energy he
    rw [X.energy_exceptionalCurve, map_zero] at he'
    cases he'
  have hm : (beta, X.exceptionalCurve i) ∈ X.positiveTailSplittings q.beta := by
    rw [X.positiveTailSplittings_eq, X.effective.mem_positiveTailSplittings]
    exact ⟨hb.symm, htail⟩
  rw [Finset.sum_eq_single (beta, X.exceptionalCurve i)]
  · rw [RationalTerms.coefficient_sum]
    rw [Finset.sum_eq_single (.exceptional i)]
    · rw [RationalTerms.coefficient_scale]
      change -SurfaceDescendant.firstCalibrationMatrix X (X.exceptionalCurve i)
        (.exceptional i) (q.onePsiInsertion hp).label * _ = _
      rw [hh, firstCalibrationMatrix_exceptional_column, if_pos rfl]
      norm_num only [neg_neg, one_mul]
      have hu : Function.update q.orderedLabels (q.onePsiMark hp) (.exceptional i) =
          q.orderedLabels := by
        rw [← hh]
        exact Function.update_eq_self _ _
      have hprim : (SurfaceAncestorKey.ofLabels q.genus (Fin q.orderedInsertions.length)
          q.ordered_stable beta 0 q.orderedLabels).IsPrimary := by
        intro t ht
        change t ∈ Finset.univ.val.map (fun s ↦
          (⟨q.orderedLabels s, 0⟩ : SurfaceInsertion X)) at ht
        obtain ⟨s, _, rfl⟩ := Multiset.mem_map.mp ht
        rfl
      rw [hu, canonicalPrimaryTerms, if_pos ⟨h.1, hprim⟩]
      have hl : (SurfaceAncestorKey.ofLabels q.genus (Fin q.orderedInsertions.length)
          q.ordered_stable beta 0 q.orderedLabels).primaryLabels = q.primaryLabels := by
        have he := congrArg SurfaceAncestorKey.primaryLabels q.of_ordered_eq
        simpa only [SurfaceAncestorKey.primaryLabels, SurfaceAncestorKey.ofLabels,
          Multiset.map_map, Function.comp_def] using he
      change RationalTerms.coefficient (RationalTerms.rename Sum.inr
        (SurfaceFirstDescendant.primaryTerms q.genus beta _)) {v} = _
      rw [hl, hg]
    · intro b _ hbi
      rw [RationalTerms.coefficient_scale]
      change -SurfaceDescendant.firstCalibrationMatrix X (X.exceptionalCurve i) b
        (q.onePsiInsertion hp).label * _ = 0
      rw [hh, firstCalibrationMatrix_exceptional_column, if_neg hbi, neg_zero, zero_mul]
    · exact fun hn ↦ (hn (Finset.mem_univ _)).elim
  · intro split hs hne
    rw [RationalTerms.coefficient_sum]
    apply Finset.sum_eq_zero
    intro b _
    rw [RationalTerms.coefficient_scale]
    apply mul_eq_zero_of_right
    apply coefficient_canonicalPrimaryTerms_eq_zero
      (SurfaceAncestorKey.ofLabels q.genus (Fin q.orderedInsertions.length)
        q.ordered_stable split.1 0 (Function.update q.orderedLabels (q.onePsiMark hp) b))
      h.1 v
    intro he
    have hc : split.1 + split.2 = q.beta := by
      rw [X.positiveTailSplittings_eq, X.effective.mem_positiveTailSplittings] at hs
      exact hs.1
    have hs1 : split.1 = beta := he.symm.trans hv
    have hs2 : split.2 = X.exceptionalCurve i := by
      rw [hs1, hb] at hc
      exact add_left_cancel hc
    exact hne (Prod.ext hs1 hs2)
  · exact fun hn ↦ (hn hm).elim

/-- Exceptional first-calibration converts the shifted Ei-psi/point terminal to
the signed divisor factor of the requested primary class. No positivity is needed. -/
theorem main_exceptional_point_shifted (i : Fin X.blowups) (beta : X.Curve) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))
    remainderVertex X v (coefficientVertex X v) (X.effective.energy beta) 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single 0 1) inferInstance (X.exceptionalCurve i)
      ![.exceptional i, .point] = (X.signedMultiplicity beta i : ℚ) := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))
  let q := (SurfaceAncestorKey.ofLabels 2 (Fin 2) (by norm_num [StableArity])
    (beta + X.exceptionalCurve i) (Pi.single 0 1)
    (![.exceptional i, .point] : Fin 2 → SurfaceBasisLabel X)).addPoints (X.effective.energy beta)
  have hi : q.insertions =
      Multiset.replicate (X.effective.energy beta) (⟨.point, 0⟩ : SurfaceInsertion X) +
      (⟨.exceptional i, 1⟩ ::ₘ {⟨.point, 0⟩}) := rfl
  have hp : q.totalPsi = 1 := by
    simp only [SurfaceAncestorKey.totalPsi, hi, Multiset.map_add, Multiset.map_replicate,
      Multiset.map_cons, Multiset.map_singleton, Multiset.sum_add,
      Multiset.sum_replicate, Multiset.sum_cons, Multiset.sum_singleton, nsmul_zero,
      zero_add, add_zero]
  have hh : (q.onePsiInsertion hp).label = .exceptional i := by
    have hm := q.onePsiInsertion_mem hp
    rw [hi, Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_cons,
      Multiset.mem_singleton] at hm
    rcases hm with hm | hm | hm
    · have he := q.onePsiInsertion_power hp
      rw [hm.2] at he
      cases he
    · rw [hm]
    · have he := q.onePsiInsertion_power hp
      rw [hm] at he
      cases he
  have hdim : q.DimensionCompatible := by
    change (((q.insertions.map (fun t ↦ t.label.codimension + t.psi)).sum : ℕ) : ℤ) =
      (X.c1Degree (beta + X.exceptionalCurve i) : ℤ) + 2 - 1 + (q.insertions.card : ℤ)
    simp only [hi, Multiset.map_add, Multiset.map_replicate, Multiset.map_cons,
      Multiset.map_singleton, Multiset.sum_add, Multiset.sum_replicate,
      Multiset.sum_cons, Multiset.sum_singleton, Multiset.card_add,
      Multiset.card_replicate, Multiset.card_cons, Multiset.card_singleton,
      SurfaceBasisLabel.codimension, nsmul_eq_mul, SurfaceTarget.c1Degree,
      Nat.cast_add, Nat.cast_one]
    change (((X.effective.energy beta * (2+0):ℕ):ℤ) + (1+1+(2+0))) =
      (X.effective.energy (beta + X.exceptionalCurve i) : ℤ) + 2 - 1 +
        ((X.effective.energy beta : ℤ) + (1+1))
    rw [X.energy_add_exceptionalCurve]
    push_cast
    omega
  dsimp only
  rw [remainderVertex_exceptionalPsi_of_planeDegree_zero i v _ (Fin 2) _ 0
    (X.exceptionalCurve i) (X.planeDegree_exceptionalCurve i) _ rfl]
  change RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
    (residualTerms q)) {v} = _
  rw [residualTerms, if_pos hdim, if_neg (show ¬q.genus ≤ 1 from by change ¬(2:ℕ)≤1; omega),
    RationalTerms.coefficient_affineSubstitute_term, Multiset.map_singleton,
    Multiset.sum_singleton, one_mul]
  rw [coefficient_normalizedTerms_shifted_exceptional i beta q rfl hp rfl hh v rfl]
  have hl : q.primaryLabels = Multiset.replicate (X.effective.energy beta) .point +
      ((.exceptional i) ::ₘ {.point}) := by
    simp only [SurfaceAncestorKey.primaryLabels, hi, Multiset.map_add,
      Multiset.map_replicate, Multiset.map_cons, Multiset.map_singleton]
  rw [hl, SurfaceFirstDescendant.primaryTerms, RationalTerms.coefficient_rename_scale]
  have hc : (Multiset.replicate (X.effective.energy beta) .point +
      ((.exceptional i) ::ₘ {.point}) : Multiset (SurfaceBasisLabel X)).count .point =
      X.effective.energy beta + 1 := by
    simp only [Multiset.count_add, Multiset.count_replicate, Multiset.count_cons,
      Multiset.count_singleton, reduceCtorEq, ite_false, ite_true, add_zero]
  rw [hc, SurfaceFirstDescendant.dimensionTerms, if_pos
    ((SurfaceQuery.dimensionCompatible_points 2 beta _).mpr (by omega)),
    RationalTerms.coefficient_rename_term]
  dsimp only [v]
  simp only [Multiset.map_singleton]
  simp only [SurfaceFirstDescendant.primaryCoefficient, Multiset.map_add,
    Multiset.map_replicate, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_add,
    Multiset.prod_replicate, Multiset.prod_cons, Multiset.prod_singleton,
    SurfaceBasisLabel.primaryFactor, one_pow, one_mul, mul_one,
    SurfaceTarget.signedMultiplicity, if_true, mul_one]

/-- Every exceptional generator has exactly the two ordered effective splittings. -/
theorem splittings_exceptional (X : SurfaceTarget) (i : Fin X.blowups) :
    X.splittings (X.exceptionalCurve i) =
      {(0, X.exceptionalCurve i), (X.exceptionalCurve i, 0)} := by
  cases X with
  | plane => exact Fin.elim0 i
  | hirzebruchOne => fin_cases i; decide +kernel
  | blowupTwo => fin_cases i <;> decide +kernel

private theorem exceptional_ee_scalar_points (X : SurfaceTarget) (i : Fin X.blowups)
    (f : ℕ → ℚ) (n : ℕ) (b : SurfaceBasisLabel X) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X)
        (X.exceptionalCurve i) ij.2 (![.exceptional i, .exceptional i, b] : Fin 3 → _))) =
      if b = .exceptional i then -f n else 0 := by
  have hz : X.exceptionalCurve i ≠ 0 := by
    intro he
    have hh := congrArg X.effective.energy he
    rw [X.energy_exceptionalCurve, map_zero] at hh
    cases hh
  simpa only [true_and] using
    SurfaceGenusTwoBlowupNExceptionalRational.triple_points_pos X i (X.exceptionalCurve i)
      (X.planeDegree_exceptionalCurve i) hz f n b

/-- At an exceptional remainder, the actual outer EE pair retains both its
positive exceptional node and negative classical point node. -/
theorem pair_ee_exceptional (i : Fin X.blowups) (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ) (n : ℕ)
    (x : GluingExpression 2 (Fin 2)) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (a : SurfaceBasisLabel X) :
    let y := GetzlerGraphs.join (m := 1) (n := 2) 1 2 x
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
    remainderContraction X v main y (by exact (d, (0 : Fin 3 → ℕ)))
      (by exact (l, (inferInstance : DecidableEq (Fin 3)))) (X.exceptionalCurve i) n
        ![a, .exceptional i, .exceptional i] =
      remainderContraction X v main x d l 0 n ![a, .exceptional i] -
        remainderContraction X v main x d l (X.exceptionalCurve i) n ![a, .point] := by
  have hn : (0, X.exceptionalCurve i) ≠ (X.exceptionalCurve i, 0) := by
    intro he
    have hh := congrArg (fun t : X.Curve × X.Curve ↦ X.effective.energy t.1) he
    rw [map_zero, X.energy_exceptionalCurve] at hh
    cases hh
  dsimp only
  rw [pair_join, splittings_exceptional, Finset.sum_pair hn]
  simp only
  have hs (b : SurfaceBasisLabel X) := exceptional_ee_scalar_points X i
    (fun m ↦ remainderContraction X v main x d l 0 m ![a,b]) n b.dual
  have ht (b : SurfaceBasisLabel X) := SurfaceGenusTwoBlowupKCoefficients.classical_ee_points i
    (fun m ↦ remainderContraction X v main x d l (X.exceptionalCurve i) m ![a,b]) n b.dual
  simp only [hs, ht]
  rw [SurfaceBasisLabel.sum_labels, SurfaceBasisLabel.sum_labels]
  simp only [SurfaceBasisLabel.inverseWeight, SurfaceBasisLabel.dual,
    reduceCtorEq, ite_false, ite_true, mul_zero, zero_add, add_zero,
    one_mul, SurfaceBasisLabel.exceptional.injEq, mul_ite, mul_neg, neg_mul,
    neg_neg, Finset.sum_const_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  ring

/-- A primary terminal preserves its full curve class, so a positive effective
remainder cannot supply the requested main-class variable. -/
theorem remainderVertex_primary_nonzero_remainder (v : Variable X) (n : ℕ)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S)
    (delta : X.Curve) (hd : delta ≠ 0) (a : S → SurfaceBasisLabel X) :
    remainderVertex X v (coefficientVertex X v) n 2 S h 0 inferInstance delta a = 0 := by
  rw [remainderVertex_eq X v _ rfl, vertex_primary_genusTwo_eq]
  let q := (SurfaceAncestorKey.ofLabels 2 S h
    (SurfaceGenusZero.variableCurve v + delta) 0 a).addPoints n
  have hp : q.IsPrimary := by
    intro t ht
    rcases Multiset.mem_add.mp ht with ht | ht
    · exact congrArg SurfaceInsertion.psi (Multiset.mem_replicate.mp ht).2
    · obtain ⟨s, _, rfl⟩ := Multiset.mem_map.mp ht
      rfl
  have hn : ¬(2 ≤ q.genus ∧ q.totalPsi = 1) := by
    rw [q.totalPsi_eq_zero_iff.mpr hp]
    exact fun h ↦ Nat.zero_ne_one h.2
  change RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
    (residualTerms q)) {v} = 0
  rw [residualTerms]
  split_ifs with hdim hg
  · have he : q.genus = 2 := rfl
    omega
  · rw [RationalTerms.coefficient_affineSubstitute_term, Multiset.map_singleton,
      Multiset.sum_singleton, one_mul, normalizedTerms, dif_neg hn]
    apply coefficient_canonicalPrimaryTerms_eq_zero q le_rfl v
    change SurfaceGenusZero.variableCurve v ≠ SurfaceGenusZero.variableCurve v + delta
    intro he
    have he' := congrArg X.effective.energy he
    rw [map_add] at he'
    have hz : X.effective.energy delta = 0 := by omega
    exact hd ((X.effective.energy_eq_zero_iff _).mp hz)
  · exact RationalTerms.coefficient_affineSubstitute_zero _ _

private theorem main_primary_one_flag (beta : X.Curve) (n : ℕ) (hn : n ≤ X.effective.energy beta)
    (b : SurfaceBasisLabel X) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))
    remainderVertex X v (coefficientVertex X v) n 2 (Fin 1)
      (by norm_num [StableArity]) 0 inferInstance 0 ![b] =
      if b = .point ∧ n = X.effective.energy beta then 1 else 0 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))
  let q := (SurfaceAncestorKey.ofLabels 2 (Fin 1) (by norm_num [StableArity]) beta 0
    (![b] : Fin 1 → SurfaceBasisLabel X)).addPoints n
  have hi : q.insertions = Multiset.replicate n (⟨.point, 0⟩ : SurfaceInsertion X) +
      {⟨b, 0⟩} := rfl
  have hp : q.IsPrimary := by
    intro t ht
    rw [hi, Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton] at ht
    rcases ht with ht | ht
    · exact congrArg SurfaceInsertion.psi ht.2
    · rw [ht]
  have hpsi : ¬(2 ≤ q.genus ∧ q.totalPsi = 1) := by
    rw [q.totalPsi_eq_zero_iff.mpr hp]
    exact fun h ↦ Nat.zero_ne_one h.2
  have hdim : q.DimensionCompatible ↔ n + b.codimension = X.effective.energy beta + 2 := by
    change (((q.insertions.map (fun t ↦ t.label.codimension + t.psi)).sum : ℕ) : ℤ) =
      X.c1Degree beta + 2 - 1 + (q.insertions.card : ℤ) ↔ _
    simp only [hi, Multiset.map_add, Multiset.map_replicate, Multiset.map_singleton,
      Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_singleton,
      Multiset.card_add, Multiset.card_replicate, Multiset.card_singleton,
      SurfaceBasisLabel.codimension, nsmul_eq_mul, SurfaceTarget.c1Degree, Nat.cast_add]
    change (((n * (2+0):ℕ):ℤ) + ((b.codimension + 0:ℕ):ℤ)) =
      (X.effective.energy beta : ℤ) + 2 - 1 + ((n:ℤ)+1) ↔
        n + b.codimension = X.effective.energy beta + 2
    omega
  dsimp only
  rw [remainderVertex_eq X v _ rfl, vertex_primary_genusTwo_eq, add_zero]
  change RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
    (residualTerms q)) {v} = _
  have hc : b.codimension ≤ 2 := by
    cases b <;> simp only [SurfaceBasisLabel.codimension] <;> omega
  by_cases h : b = .point ∧ n = X.effective.energy beta
  · rcases h with ⟨rfl, rfl⟩
    rw [if_pos ⟨rfl,rfl⟩, residualTerms,
      if_pos (hdim.mpr (by simp only [SurfaceBasisLabel.codimension])),
      if_neg (show ¬q.genus ≤ 1 from by change ¬(2:ℕ)≤1; omega),
      RationalTerms.coefficient_affineSubstitute_term, Multiset.map_singleton,
      Multiset.sum_singleton, one_mul, normalizedTerms, dif_neg hpsi,
      canonicalPrimaryTerms, if_pos ⟨le_rfl,hp⟩]
    have hl : q.primaryLabels = Multiset.replicate (X.effective.energy beta) .point + {.point} := by
      simp only [SurfaceAncestorKey.primaryLabels, hi, Multiset.map_add,
        Multiset.map_replicate, Multiset.map_singleton]
    change RationalTerms.coefficient (RationalTerms.rename Sum.inr
      (SurfaceFirstDescendant.primaryTerms 2 beta q.primaryLabels)) {v} = 1
    rw [hl, SurfaceFirstDescendant.primaryTerms, RationalTerms.coefficient_rename_scale]
    simp only [SurfaceFirstDescendant.primaryCoefficient, Multiset.map_add,
      Multiset.map_replicate, Multiset.map_singleton, Multiset.prod_add,
      Multiset.prod_replicate, Multiset.prod_singleton, SurfaceBasisLabel.primaryFactor,
      one_pow, one_mul, Multiset.count_add, Multiset.count_replicate,
      Multiset.count_singleton, ite_true, mul_one]
    rw [SurfaceFirstDescendant.dimensionTerms, if_pos
      ((SurfaceQuery.dimensionCompatible_points 2 beta _).mpr (by omega)),
      RationalTerms.coefficient_rename_term]
    dsimp only [v]
    simp only [Multiset.map_singleton, if_true]
  · have hz : ¬q.DimensionCompatible := by
      rw [hdim]
      intro he
      have hb2 : b.codimension = 2 := by omega
      have hb : b = .point := by
        cases b with
        | point => rfl
        | unit | hyperplane | exceptional j =>
          simp only [SurfaceBasisLabel.codimension] at hb2
          omega
      exact h ⟨hb, by omega⟩
    rw [if_neg h, residualTerms, if_neg hz, RationalTerms.coefficient_affineSubstitute_zero]

private theorem main_exceptional_exceptional (i : Fin X.blowups) (beta : X.Curve) (s : Fin 2) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))
    remainderVertex X v (coefficientVertex X v) (X.effective.energy beta) 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0
      ![.exceptional i, .exceptional i] = -1 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))
  have hs : (![.exceptional i,.exceptional i] : Fin 2 → SurfaceBasisLabel X) s ≠ .unit := by
    fin_cases s <;> intro he <;> cases he
  have hm : ((Finset.univ.erase s).val.map
      (![.exceptional i,.exceptional i] : Fin 2 → SurfaceBasisLabel X)) = {.exceptional i} := by
    fin_cases s <;> rfl
  have hd : ((SurfaceAncestorKey.ofLabels 2 (Fin 2) (by norm_num [StableArity]) beta
      (Pi.single s 1) (![.exceptional i,.exceptional i] : Fin 2 → SurfaceBasisLabel X)).addPoints
      (X.effective.energy beta)).DimensionCompatible := by
    fin_cases s <;> simp only [SurfaceAncestorKey.DimensionCompatible,
      SurfaceAncestorKey.totalCodimension, SurfaceAncestorKey.addPoints,
      SurfaceAncestorKey.ofLabels,
      Multiset.map_add, Multiset.map_replicate, Multiset.sum_add, Multiset.sum_replicate,
      Multiset.card_add, Multiset.card_replicate, Multiset.card_map, Finset.card_val,
      Finset.card_univ, Fintype.card_fin, SurfaceTarget.c1Degree, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    all_goals change (X.effective.energy beta : ℤ) * 2 + 3 =
      (X.effective.energy beta : ℤ) + 2 - 1 + ((X.effective.energy beta : ℤ) + 2)
    all_goals omega
  dsimp only
  rw [remainderVertex_onePsi_zero_of_ne_unit v _ (Fin 2) _ s _ hs,
    coefficient_residualTerms_eq_direct_at_class v _ rfl rfl]
  have hvb : SurfaceGenusZero.variableCurve v = beta := rfl
  simp only [hvb]
  rw [if_pos hd, directNormalizedTerms_onePsi_ofLabels 2 le_rfl (Fin 2) _ s beta _ _, hm]
  have he : (![.exceptional i,.exceptional i] : Fin 2 → SurfaceBasisLabel X) s =
      .exceptional i := by fin_cases s <;> rfl
  rw [he, SurfaceFirstDescendant.terms,
    if_neg (show SurfaceBasisLabel.unit ∉
      (Multiset.replicate (X.effective.energy beta) .point + {.exceptional i} :
        Multiset (SurfaceBasisLabel X)) from by simp only [Multiset.mem_add,
      Multiset.mem_replicate, Multiset.mem_singleton, reduceCtorEq, and_false, or_self,
      not_false_eq_true]),
    if_neg (show (SurfaceBasisLabel.exceptional i : SurfaceBasisLabel X) ≠ .unit from by
      intro hh; cases hh), RationalTerms.coefficient_rename_add,
    RationalTerms.coefficient_rename_scale, RationalTerms.coefficient_rename_scale,
    coefficient_dimensionTerms_primary_zero]
  have herase : (Multiset.replicate (X.effective.energy beta) .point +
      {.exceptional i} : Multiset (SurfaceBasisLabel X)).erase (.exceptional i) =
      Multiset.replicate (X.effective.energy beta) .point := by
    rw [Multiset.erase_add_right_pos _ (Multiset.mem_singleton_self _),
      Multiset.erase_singleton, add_zero]
  simp only [mul_zero, zero_add, SurfaceFirstDescendant.correctionCoefficient,
    SurfaceFirstDescendant.divisorSquare, Multiset.count_add, Multiset.count_replicate,
    Multiset.count_singleton, reduceCtorEq, ite_false, ite_true, zero_add, Nat.cast_one,
    herase, add_zero,
    SurfaceFirstDescendant.primaryCoefficient, Multiset.map_replicate,
    Multiset.prod_replicate, SurfaceBasisLabel.primaryFactor, one_pow, mul_one,
    Multiset.count_replicate]
  rw [SurfaceFirstDescendant.dimensionTerms, if_pos
    ((SurfaceQuery.dimensionCompatible_points 2 beta _).mpr (by omega)),
    RationalTerms.coefficient_rename_term]
  dsimp only [v]
  simp only [Multiset.map_singleton, if_true, mul_one]

private theorem primaryScalar_swap_last (X : SurfaceTarget) (f : X.Curve → ℚ) (gamma : X.Curve)
    (n : ℕ) (a b c : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X f gamma n (![a,b,c] : Fin 3 → _) =
    SurfaceGenusZero.primaryScalar X f gamma n (![a,c,b] : Fin 3 → _) := by
  have h : (![a,c,b] : Fin 3 → _) ∘ Equiv.swap 1 2 = (![a,b,c] : Fin 3 → _) := by
    ext j
    fin_cases j <;> rfl
  rw [← h, SurfaceGenusZero.primaryScalar_relabel]


/-- The original primary BP inner join, shared by the mixed divisor rows. -/
def primaryInner : GluingExpression 2 (Fin 2) :=
  GetzlerGraphs.join (m := 0) (n := 2) 0 1
    (fundamental 2 (Fin 1) (by norm_num [StableArity]))
    (fundamental 0 (Fin 3) (by norm_num [StableArity]))

private theorem primaryInner_ee_zero (i : Fin X.blowups) (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ) (n : ℕ) :
    remainderContraction X v main primaryInner ((0 : Fin 1 → ℕ),(0 : Fin 3 → ℕ))
      (inferInstance, inferInstance) 0 n ![.exceptional i,.exceptional i] =
      -main n 2 (Fin 1) (by norm_num [StableArity]) 0 inferInstance 0 ![.point] := by
  have hl (b : SurfaceBasisLabel X) :
      (Option.elim · b (((![.exceptional i,.exceptional i] : Fin 2 → _)
        ∘ (finSumFinEquiv : Fin 0 ⊕ Fin 2 ≃ Fin 2)) ∘ Sum.inl)) ∘
        finSuccEquiv' 0 = ![b] := by ext k; fin_cases k; rfl
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b (((![.exceptional i,.exceptional i] : Fin 2 → _)
        ∘ (finSumFinEquiv : Fin 0 ⊕ Fin 2 ≃ Fin 2)) ∘ Sum.inr)) ∘
        finSuccEquiv' 1 = ![.exceptional i,b,.exceptional i] := by ext k; fin_cases k <;> rfl
  simp only [primaryInner, GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction, hl, hr, primaryPointVertex, and_self, ite_true]
  rw [(X.splittings_eq 0).trans X.effective.splittings_zero]
  simp only [Finset.sum_singleton]
  change (∑ b : SurfaceBasisLabel X, b.inverseWeight *
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (main ij.1 2 (Fin 1) (by norm_num [StableArity]) 0 inferInstance 0 ![b] *
        SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) 0 ij.2
          ![.exceptional i,b.dual,.exceptional i])) = _
  have hscalar (b : SurfaceBasisLabel X) (m : ℕ) :
      SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) 0 m
        ![.exceptional i,b.dual,.exceptional i] =
      SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) 0 m
        ![.exceptional i,.exceptional i,b.dual] := primaryScalar_swap_last X _ _ _ _ _ _
  simp only [hscalar]
  have ht (b : SurfaceBasisLabel X) := SurfaceGenusTwoBlowupKCoefficients.classical_ee_points i
    (fun m ↦ main m 2 (Fin 1) (by norm_num [StableArity]) 0 inferInstance 0 ![b]) n b.dual
  simp only [ht]
  rw [SurfaceBasisLabel.sum_labels]
  simp only [SurfaceBasisLabel.inverseWeight, SurfaceBasisLabel.dual,
    reduceCtorEq, ite_false, ite_true, mul_zero, zero_add, add_zero, one_mul,
    Finset.sum_const_zero]

private theorem primaryScalar_exceptional_node_point_zero (i : Fin X.blowups)
    (delta : X.Curve) (hd : X.planeDegree delta = 0) (n : ℕ) (b : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) delta n
      (![.exceptional i,b,.point] : Fin 3 → _) = 0 := by
  let e : Fin 3 ≃ Option Bool :=
    { toFun := ![some false,none,some true]
      invFun := fun t ↦ match t with | none => 1 | some false => 0 | some true => 2
      left_inv := by intro j; fin_cases j <;> rfl
      right_inv := by intro t; rcases t with _ | (_ | _) <;> rfl }
  have he : (Option.elim · b (fun t : Bool ↦ if t then .point else .exceptional i)) ∘ e =
      (![.exceptional i,b,.point] : Fin 3 → SurfaceBasisLabel X) := by
    ext j
    fin_cases j <;> rfl
  rw [← he,SurfaceGenusZero.primaryScalar_relabel]
  exact primaryScalar_exceptional_point_tail_eq_zero X i delta hd n b

/-- The original primary BP inner join vanishes when its rational component
contains Ei and a point, at every plane-zero remainder and terminal callback. -/
theorem primaryInner_exceptional_point_zero (i : Fin X.blowups) (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ) (delta : X.Curve)
    (hd : X.planeDegree delta = 0) (n : ℕ) :
    remainderContraction X v main primaryInner ((0 : Fin 1 → ℕ),(0 : Fin 3 → ℕ))
      (inferInstance, inferInstance) delta n ![.exceptional i,.point] = 0 := by
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b (((![.exceptional i,.point] : Fin 2 → _)
        ∘ (finSumFinEquiv : Fin 0 ⊕ Fin 2 ≃ Fin 2)) ∘ Sum.inr)) ∘
        finSuccEquiv' 1 = ![.exceptional i,b,.point] := by ext k; fin_cases k <;> rfl
  simp only [primaryInner, GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction, hr, primaryPointVertex, and_self, ite_true]
  apply Finset.sum_eq_zero
  intro split hs
  have ha : split.1 + split.2 = delta := by
    rw [X.splittings_eq] at hs
    exact (X.effective.mem_splittings _ _ _).mp hs
  have ht : X.planeDegree split.2 = 0 := by
    have he := congrArg X.planeDegree ha
    rw [map_add, hd] at he
    omega
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [primaryScalar_exceptional_node_point_zero i _ ht]
  simp only [mul_zero]

private theorem paper_zero_primary_shifted (i : Fin X.blowups) (beta : X.Curve) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 0) (X.exceptionalCurve i)
      (X.effective.energy beta) ![.exceptional i,.exceptional i,.exceptional i] = -1 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))
  have hx : (BelorousskiPandharipande.paperCotangentTerm 0).expression.maxComponentGenus = 2 :=
    by decide +kernel
  dsimp only
  rw [remainderPointCoefficient, if_pos hx]
  have hz1 : (![0] : Fin 1 → ℕ) = 0 := by ext j; fin_cases j; rfl
  simp only [BelorousskiPandharipande.paperCotangentTerm,
    BelorousskiPandharipande.paperTerm, BelorousskiPandharipande.paperExpression,
    Matrix.cons_val_zero, hz1]
  change remainderContraction X v (remainderVertex X v (coefficientVertex X v))
    (GetzlerGraphs.join (m := 1) (n := 2) 1 2 primaryInner
      (fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (((0 : Fin 1 → ℕ),(0 : Fin 3 → ℕ)), (0 : Fin 3 → ℕ))
    (((inferInstance : DecidableEq (Fin 1)),(inferInstance : DecidableEq (Fin 3))),
      (inferInstance : DecidableEq (Fin 3))) (X.exceptionalCurve i)
    (X.effective.energy beta) ![.exceptional i,.exceptional i,.exceptional i] = -1
  trans remainderContraction X v (remainderVertex X v (coefficientVertex X v))
    primaryInner ((0 : Fin 1 → ℕ),(0 : Fin 3 → ℕ)) (inferInstance,inferInstance) 0
    (X.effective.energy beta) ![.exceptional i,.exceptional i] -
    remainderContraction X v (remainderVertex X v (coefficientVertex X v))
    primaryInner ((0 : Fin 1 → ℕ),(0 : Fin 3 → ℕ)) (inferInstance,inferInstance)
    (X.exceptionalCurve i) (X.effective.energy beta) ![.exceptional i,.point]
  · exact pair_ee_exceptional i v _ _ primaryInner _ _ (.exceptional i)
  rw [primaryInner_ee_zero, primaryInner_exceptional_point_zero i v _
    (X.exceptionalCurve i) (X.planeDegree_exceptionalCurve i)]
  rw [main_primary_one_flag beta _ le_rfl, if_pos ⟨rfl,rfl⟩]
  norm_num only

/-- A point cotangent state with one exceptional primary has no primary
coefficient at any plane-zero remainder, after full normalization. -/
theorem main_point_exceptional_primary_zero (i : Fin X.blowups) (gamma : X.Curve) (m : ℕ)
    (delta : X.Curve) (hd : X.planeDegree delta = 0) (n : ℕ) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 gamma m)
    remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single 1 1) inferInstance delta
      ![.exceptional i,.point] = 0 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 gamma m)
  have hp : X.planeDegree (SurfaceGenusZero.variableCurve v) =
      X.planeDegree (SurfaceGenusZero.variableCurve v + delta) := by
    rw [map_add, hd, add_zero]
  dsimp only
  rw [remainderVertex_onePsi_of_planeDegree_zero v n (Fin 2) _ 1 delta hd _ (Or.inr rfl),
    coefficient_residualTerms_onePsi_same_planeDegree v (Fin 2) _ 1 _ _ (Or.inr rfl) hp n]
  split_ifs with hdim
  · rw [directNormalizedTerms_onePsi_ofLabels 2 le_rfl (Fin 2) _ 1 _ _ n]
    have hm : ((Finset.univ.erase (1 : Fin 2)).val.map
        (![.exceptional i,.point] : Fin 2 → SurfaceBasisLabel X)) = {.exceptional i} := rfl
    rw [hm, Matrix.cons_val_one, Matrix.cons_val_zero]
    apply coefficient_terms_primary_zero
    · simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton,
        reduceCtorEq, and_false, or_self, not_false_eq_true]
    · intro he; cases he
    · simp only [SurfaceFirstDescendant.correctionCoefficient,
        SurfaceFirstDescendant.divisorSquare, zero_mul]
  · rfl

/-- Both actual BP cotangent diagrams at an exceptional remainder retain the
positive exceptional node minus the classical point node. -/
theorem paper_pair_exceptional (i : Fin X.blowups) (v : Variable X) (n : ℕ) (s : Fin 2)
    (a : SurfaceBasisLabel X) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3))
      (X.exceptionalCurve i) n ![a,.exceptional i,.exceptional i] =
      remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
        (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0 ![a,.exceptional i] -
      remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
        (by norm_num [StableArity]) (Pi.single s 1) inferInstance (X.exceptionalCurve i)
        ![a,.point] := by
  have h0 : (![1,0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
  have h1 : (![0,1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
  have he : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3))
      (X.exceptionalCurve i) n ![a,.exceptional i,.exceptional i] =
      remainderContraction X v (remainderVertex X v (coefficientVertex X v))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          (fundamental 2 (Fin 2) (by norm_num [StableArity]))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        (by exact (Pi.single s 1, (0 : Fin 3 → ℕ)))
        (by exact ((inferInstance : DecidableEq (Fin 2)),
          (inferInstance : DecidableEq (Fin 3)))) (X.exceptionalCurve i) n
          ![a,.exceptional i,.exceptional i] := by
    rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
    · rw [if_pos rfl, ← h0]
      rfl
    · rw [if_neg (by decide : (1 : Fin 2) ≠ 0), ← h1]
      rfl
  rw [he]
  exact pair_ee_exceptional i v _ n
    (fundamental 2 (Fin 2) (by norm_num [StableArity])) _ _ a

private theorem paper_two_primary_shifted (i : Fin X.blowups) (beta : X.Curve) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 2) (X.exceptionalCurve i)
      (X.effective.energy beta) ![.exceptional i,.exceptional i,.exceptional i] =
      -1 - (X.signedMultiplicity beta i : ℚ) := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))
  have he := paper_pair_exceptional i v (X.effective.energy beta) 0 (.exceptional i)
  rw [if_pos rfl, main_exceptional_exceptional, main_exceptional_point_shifted] at he
  exact he

private theorem paper_three_primary_shifted (i : Fin X.blowups) (beta : X.Curve) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 3) (X.exceptionalCurve i)
      (X.effective.energy beta) ![.exceptional i,.exceptional i,.exceptional i] = -1 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))
  have he := paper_pair_exceptional i v (X.effective.energy beta) 1 (.exceptional i)
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0), main_exceptional_exceptional,
    main_point_exceptional_primary_zero i beta _ (X.exceptionalCurve i)
      (X.planeDegree_exceptionalCurve i), sub_zero] at he
  exact he

private theorem paper_one_at_exceptional (i : Fin X.blowups) (v : Variable X) (n : ℕ) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 1) (X.exceptionalCurve i) n
        ![.exceptional i,.exceptional i,.exceptional i] =
      -remainderVertex X v (coefficientVertex X v) n 2 (Fin 1)
        (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0 ![.exceptional i] := by
  have hx : (BelorousskiPandharipande.paperCotangentTerm 1).expression.maxComponentGenus = 2 :=
    by decide +kernel
  rw [remainderPointCoefficient,if_pos hx]
  change remainderContraction X v (remainderVertex X v (coefficientVertex X v))
    (GetzlerGraphs.join (m := 0) (n := 3) 0 3
      (fundamental 2 (Fin 1) (by norm_num [StableArity]))
      (fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (![1],(0 : Fin 4 → ℕ))
    ((inferInstance : DecidableEq (Fin 1)),(inferInstance : DecidableEq (Fin 4)))
    (X.exceptionalCurve i) n ![.exceptional i,.exceptional i,.exceptional i] = _
  let a : Fin 3 → SurfaceBasisLabel X := ![.exceptional i,.exceptional i,.exceptional i]
  have hl (b : SurfaceBasisLabel X) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 0 ⊕ Fin 3 ≃ Fin 3)) ∘ Sum.inl)) ∘
        finSuccEquiv' 0 = ![b] := by ext j; fin_cases j; rfl
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 0 ⊕ Fin 3 ≃ Fin 3)) ∘ Sum.inr)) ∘
        finSuccEquiv' 3 = ![.exceptional i,.exceptional i,.exceptional i,b] := by
    ext j; fin_cases j <;> rfl
  have hp : (![1] : Fin 1 → ℕ)=Pi.single 0 1 := by ext j; fin_cases j; rfl
  change remainderContraction X v (remainderVertex X v (coefficientVertex X v)) _ _ _
    (X.exceptionalCurve i) n a = _
  simp only [GetzlerGraphs.join,remainderContraction,ite_true,
    GluingExpression.pointContraction,hl,hr,primaryPointVertex,and_self,hp]
  rw [Finset.sum_eq_single (0,X.exceptionalCurve i)]
  · change (∑ b : SurfaceBasisLabel X, b.inverseWeight *
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
        (remainderVertex X v (coefficientVertex X v) ij.1 2 (Fin 1)
          (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0 ![b] *
          SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X)
            (X.exceptionalCurve i) ij.2
            ![.exceptional i,.exceptional i,.exceptional i,b.dual])) = _
    have hq (b : SurfaceBasisLabel X) :=
      SurfaceGenusTwoBlowupNExceptionalRational.quad_points X i (X.exceptionalCurve i)
      (X.planeDegree_exceptionalCurve i)
      (fun m ↦ remainderVertex X v (coefficientVertex X v) m 2 (Fin 1)
        (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0 ![b]) n b.dual
    simp only [hq, true_and]
    rw [Finset.sum_eq_single (.exceptional i)]
    · simp only [SurfaceBasisLabel.inverseWeight,SurfaceBasisLabel.dual,ite_true,
        neg_one_mul]
    · intro b _ hb
      have hbd : b.dual ≠ .exceptional i := by
        cases b with
        | unit | hyperplane | point => intro h; cases h
        | exceptional j => intro h; cases h; exact hb rfl
      rw [if_neg hbd,mul_zero]
    · exact fun h ↦ (h (Finset.mem_univ _)).elim
  · intro split hsplit hne
    have hs : split.1+split.2=X.exceptionalCurve i := by
      rw [X.splittings_eq] at hsplit
      exact (X.effective.mem_splittings _ _ _).mp hsplit
    have hd : X.planeDegree split.2=0 := by
      have he := congrArg X.planeDegree hs
      rw [map_add,X.planeDegree_exceptionalCurve] at he
      omega
    have h2 : split.2 ≠ X.exceptionalCurve i := by
      intro h2
      have h0 : split.1=0 := by
        rw [h2] at hs
        exact add_right_cancel (hs.trans (zero_add _).symm)
      exact hne (Prod.ext h0 h2)
    apply Finset.sum_eq_zero
    intro b _
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro ij _
    rw [SurfaceGenusTwoBlowupNExceptionalRational.quad_support X i split.2 hd ij.2 b.dual,
      if_neg (fun h ↦ h2 h.1),mul_zero,mul_zero]
  · intro hnot
    apply (hnot ?_).elim
    rw [X.splittings_eq,X.effective.mem_splittings]
    exact zero_add _

private theorem main_exceptional_one_flag_primary_zero
    (i : Fin X.blowups) (beta : X.Curve) (n : ℕ) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))
    remainderVertex X v (coefficientVertex X v) n 2 (Fin 1)
      (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0 ![.exceptional i] = 0 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))
  dsimp only
  rw [remainderVertex_onePsi_zero_of_ne_unit v n (Fin 1) _ 0 _
    (show (![.exceptional i] : Fin 1 → SurfaceBasisLabel X) 0 ≠ .unit from by intro he; cases he),
    coefficient_residualTerms_eq_direct_at_class v _ rfl rfl]
  split_ifs with hd
  · rw [directNormalizedTerms_onePsi_ofLabels 2 le_rfl (Fin 1) _ 0 _ _ n]
    have hm : ((Finset.univ.erase (0 : Fin 1)).val.map
        (![.exceptional i] : Fin 1 → SurfaceBasisLabel X)) = 0 := rfl
    rw [hm,add_zero,Matrix.cons_val_zero]
    apply coefficient_terms_primary_zero
    · simp only [Multiset.mem_replicate,reduceCtorEq,and_false,not_false_eq_true]
    · intro he; cases he
    · simp only [SurfaceFirstDescendant.correctionCoefficient,Multiset.count_replicate,
        reduceCtorEq,ite_false,Nat.cast_zero,mul_zero,zero_mul]
  · rfl

private theorem paper_one_primary_shifted (i : Fin X.blowups) (beta : X.Curve) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 1) (X.exceptionalCurve i)
      (X.effective.energy beta) ![.exceptional i,.exceptional i,.exceptional i] = 0 := by
  dsimp only
  rw [paper_one_at_exceptional, main_exceptional_one_flag_primary_zero,neg_zero]

private theorem eee_permutation (i : Fin X.blowups) (e : Fin 6) :
    (![.exceptional i,.exceptional i,.exceptional i] : Fin 3 → SurfaceBasisLabel X) ∘
      BelorousskiPandharipande.labelPermutation e =
      ![.exceptional i,.exceptional i,.exceptional i] := by
  have hh : (![.exceptional i,.exceptional i,.exceptional i] : Fin 3 → SurfaceBasisLabel X) =
      fun _ ↦ .exceptional i := by ext k; fin_cases k <;> rfl
  rw [hh]
  rfl

/-- The actual four-graph/six-marking BP constructor has shifted primary
coefficient `12 - 18 alpha_i`, for every full effective class including zero. -/
theorem pointCoefficient_primary_shifted (i : Fin X.blowups) (beta : X.Curve) :
    BelorousskiPandharipande.pointCoefficient X (X.effective.energy beta)
      (beta + X.exceptionalCurve i) ![.exceptional i,.exceptional i,.exceptional i]
      (.inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))) =
      12 - 18 * (X.signedMultiplicity beta i : ℚ) := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))
  have hv : SurfaceGenusZero.variableCurve v = beta := rfl
  have hterm (j : Fin 20) (e : Fin 6) :
      SurfaceGenusTwo.pointCoefficient X v (BelorousskiPandharipande.orbitCotangentTerm j e)
        (beta + X.exceptionalCurve i) (X.effective.energy beta)
        ![.exceptional i,.exceptional i,.exceptional i] =
      remainderPointCoefficient X v (coefficientVertex X v)
        (BelorousskiPandharipande.paperCotangentTerm j) (X.exceptionalCurve i)
        (X.effective.energy beta) ![.exceptional i,.exceptional i,.exceptional i] := by
    have h := remainderPointCoefficient_eq X v (coefficientVertex X v) rfl
      (BelorousskiPandharipande.orbitCotangentTerm j e) (X.exceptionalCurve i)
      (X.effective.energy beta)
      (![.exceptional i,.exceptional i,.exceptional i] : Fin 3 → SurfaceBasisLabel X)
    have ho : remainderPointCoefficient X v (coefficientVertex X v)
        (BelorousskiPandharipande.orbitCotangentTerm j e) (X.exceptionalCurve i)
        (X.effective.energy beta) ![.exceptional i,.exceptional i,.exceptional i] =
        remainderPointCoefficient X v (coefficientVertex X v)
          (BelorousskiPandharipande.paperCotangentTerm j) (X.exceptionalCurve i)
          (X.effective.energy beta) ![.exceptional i,.exceptional i,.exceptional i] := by
      simp only [BelorousskiPandharipande.orbitCotangentTerm, CotangentTerm.relabel,
        remainderPointCoefficient, GluingExpression.maxComponentGenus,
        remainderContraction, eee_permutation]
    rw [ho,hv] at h
    exact h.symm
  change BelorousskiPandharipande.pointCoefficient X _ _ _ v = _
  simp only [BelorousskiPandharipande.pointCoefficient,hterm,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [Fin.sum_univ_four]
  change -2 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 0) (X.exceptionalCurve i)
      (X.effective.energy beta) ![.exceptional i,.exceptional i,.exceptional i]) +
    2 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 1) (X.exceptionalCurve i)
      (X.effective.energy beta) ![.exceptional i,.exceptional i,.exceptional i]) +
    3 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 2) (X.exceptionalCurve i)
      (X.effective.energy beta) ![.exceptional i,.exceptional i,.exceptional i]) +
    -3 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 3) (X.exceptionalCurve i)
      (X.effective.energy beta) ![.exceptional i,.exceptional i,.exceptional i]) = _
  rw [paper_zero_primary_shifted,paper_one_primary_shifted,
    paper_two_primary_shifted,paper_three_primary_shifted]
  ring

/-- Bind the uniform shifted primary coefficient to the complete original
normalized BP polynomial, preserving all other columns and rational tails. -/
theorem normalizedCoefficient_primary_shifted (i : Fin X.blowups) (beta : X.Curve) :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X (X.effective.energy beta)
        (beta + X.exceptionalCurve i) 0 (SurfaceGenusZero.pointLabels
          (![.exceptional i,.exceptional i,.exceptional i] : Fin 3 → SurfaceBasisLabel X)
          (X.effective.energy beta)))
      {(.inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1)))} =
      12 - 18 * (X.signedMultiplicity beta i : ℚ) := by
  rw [← BelorousskiPandharipande.pointCoefficient_eq_full]
  exact pointCoefficient_primary_shifted i beta

end AxiomaticGW.SurfaceGenusTwoBlowupNEEEPrimary

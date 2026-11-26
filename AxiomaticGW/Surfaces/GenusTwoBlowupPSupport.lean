/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupPPrimary

/-!
# Nonprimary support of the complete BP HHH row

A nonprimary genus-two request receives no coefficient from primary calibration
or cotangent tails. Its main component consumes no effective remainder. Every
nonzero rational complement of plane degree zero in the HHH row contains a
hyperplane insertion, whose divisor factor is zero. These arguments apply to
the complete normalized row and retain arbitrary signed exceptional
multiplicities and every original marking assignment.

Primary requests are outside this support statement. Their same-class
coefficient and hyperplane-input calibration cancellation are proved in
`GenusTwoBlowupPPrimary`; remaining primary support requires separate analysis.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupPSupport
open SurfacePolynomialReduction SurfaceGenusTwo GluingExpression
open SurfaceGenusTwoBlowupPCoefficients
variable {X : SurfaceTarget}

set_option maxRecDepth 20000

/-- A positive-class primary rational component with a hyperplane insertion
vanishes at plane degree zero, independently of its candidate point value. -/
theorem primaryScalar_hyperplane_eq_zero (values : X.Curve → ℚ) (gamma : X.Curve)
    (hg : gamma ≠ 0) (hd : X.planeDegree gamma = 0)
    (S : Type) [Fintype S] (a : S → SurfaceBasisLabel X)
    (s : S) (hs : a s = .hyperplane) (n : ℕ) :
    SurfaceGenusZero.primaryScalar X values gamma n a = 0 := by
  have hh : (SurfaceBasisLabel.hyperplane : SurfaceBasisLabel X).primaryFactor gamma = 0 := by
    change (X.divisorIntersections gamma 0 : ℚ) = 0
    rw [← X.planeDegree_eq_divisorIntersections gamma, hd]
    rfl
  have hp : (∏ t, (a t).primaryFactor gamma) = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by rw [hs, hh])
  simp only [SurfaceGenusZero.primaryScalar, if_neg hg, hp, zero_mul, ite_self]

private theorem splitting_add {delta : X.Curve} {split : X.Curve × X.Curve}
    (hs : split ∈ X.splittings delta) : split.1 + split.2 = delta := by
  rw [X.splittings_eq] at hs
  exact (X.effective.mem_splittings _ _ _).mp hs

private theorem splitting_planeDegree_right {delta : X.Curve}
    (hd : X.planeDegree delta = 0) {split : X.Curve × X.Curve}
    (hs : split ∈ X.splittings delta) : X.planeDegree split.2 = 0 := by
  have he := congrArg X.planeDegree (splitting_add hs)
  rw [map_add, hd] at he
  omega

private theorem paper_zero (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (delta : X.Curve) (n : ℕ) (a : Fin 3 → SurfaceBasisLabel X) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 0) delta n a = 0 := by
  have hz : (![0] : Fin 1 → ℕ) = 0 := by
    funext i
    fin_cases i
    rfl
  simp only [BelorousskiPandharipande.paperCotangentTerm,
    BelorousskiPandharipande.paperTerm, BelorousskiPandharipande.paperExpression,
    Matrix.cons_val_zero, GetzlerGraphs.join, GluingExpression.maxComponentGenus,
    max_eq_left (show (0 : ℕ) ≤ 2 by decide),
    remainderPointCoefficient, ite_true, if_neg (show (0 : ℕ) ≠ 2 by decide),
    remainderContraction, hz,
    remainderVertex_primary_eq_zero_of_not_points v hv,
    mul_zero, zero_mul, Finset.sum_const_zero]

private theorem paper_one (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (delta : X.Curve) (hdelta : delta ≠ 0) (hd : X.planeDegree delta = 0) (n : ℕ) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 1) delta n
        ![.hyperplane, .hyperplane, .hyperplane] = 0 := by
  have hx : (BelorousskiPandharipande.paperCotangentTerm 1).expression.maxComponentGenus = 2 :=
    by decide +kernel
  have hk : (![1] : Fin 1 → ℕ) = Pi.single 0 1 := by decide +kernel
  rw [remainderPointCoefficient, if_pos hx]
  change remainderContraction X v (remainderVertex X v (coefficientVertex X v))
    (GetzlerGraphs.join (m := 0) (n := 3) 0 3
      (fundamental 2 (Fin 1) (by norm_num [StableArity]))
      (fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (![1], (0 : Fin 4 → ℕ))
    ((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 4)))
    delta n ![.hyperplane, .hyperplane, .hyperplane] = _
  simp only [GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction]
  have hl (b : SurfaceBasisLabel X) :
      (Option.elim · b
        (((![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) ∘
          (finSumFinEquiv : Fin 0 ⊕ Fin 3 ≃ Fin 3)) ∘ Sum.inl)) ∘
        finSuccEquiv' 0 = ![b] := by
    funext i
    fin_cases i
    rfl
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b
        (((![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) ∘
          (finSumFinEquiv : Fin 0 ⊕ Fin 3 ≃ Fin 3)) ∘ Sum.inr)) ∘
        finSuccEquiv' 3 = ![.hyperplane, .hyperplane, .hyperplane, b] := by
    funext i
    fin_cases i <;> rfl
  simp only [hl, hr, primaryPointVertex, and_self, ite_true]
  apply Finset.sum_eq_zero
  intro split hs
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  by_cases hz : split.1 = 0
  · have hg : split.2 ≠ 0 := by
      intro he
      have ha := splitting_add hs
      rw [hz, he, add_zero] at ha
      exact hdelta ha.symm
    rw [primaryScalar_hyperplane_eq_zero (SurfaceGenusZero.pointValue X) split.2 hg
      (splitting_planeDegree_right hd hs) (Fin 4) _ 0 rfl]
    simp only [mul_zero]
  · rw [hk, remainderVertex_onePsi_of_not_points v hv, if_neg hz]
    simp only [zero_mul, mul_zero]

private theorem paper_pair (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (delta : X.Curve) (hdelta : delta ≠ 0) (hd : X.planeDegree delta = 0)
    (n : ℕ) (s : Fin 2) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![.hyperplane, .hyperplane, .hyperplane] = 0 := by
  have h0 : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
  have h1 : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
  have he : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![.hyperplane, .hyperplane, .hyperplane] =
      remainderContraction X v (remainderVertex X v (coefficientVertex X v))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          (fundamental 2 (Fin 2) (by norm_num [StableArity]))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        (by exact (Pi.single s 1, (0 : Fin 3 → ℕ)))
        (by exact ((inferInstance : DecidableEq (Fin 2)),
          (inferInstance : DecidableEq (Fin 3)))) delta n
        ![.hyperplane, .hyperplane, .hyperplane] := by
    rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
    · rw [if_pos rfl, ← h0]
      rfl
    · rw [if_neg (by decide : (1 : Fin 2) ≠ 0), ← h1]
      rfl
  rw [he, pair_join]
  apply Finset.sum_eq_zero
  intro split hs
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  by_cases hz : split.1 = 0
  · have hg : split.2 ≠ 0 := by
      intro he
      have ha := splitting_add hs
      rw [hz, he, add_zero] at ha
      exact hdelta ha.symm
    rw [primaryScalar_hyperplane_eq_zero (SurfaceGenusZero.pointValue X) split.2 hg
      (splitting_planeDegree_right hd hs) (Fin 3) _ 0 rfl]
    simp only [mul_zero]
  · rw [remainderContraction, if_pos rfl,
      remainderVertex_onePsi_of_not_points v hv, if_neg hz]
    simp only [zero_mul, mul_zero]

/-- Constant HHH labels preserve each original BP marking occurrence after
transport, at every full effective remainder and point count. -/
theorem remainder_orbit (v : Variable X) (delta : X.Curve) (n : ℕ)
    (i : Fin 20) (e : Fin 6) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm i e) delta n
        ![.hyperplane, .hyperplane, .hyperplane] =
      remainderPointCoefficient X v (coefficientVertex X v)
        (BelorousskiPandharipande.paperCotangentTerm i) delta n
        ![.hyperplane, .hyperplane, .hyperplane] := by
  have hh : (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) =
      fun _ ↦ .hyperplane := by
    funext t
    fin_cases t <;> rfl
  simp only [BelorousskiPandharipande.orbitCotangentTerm, CotangentTerm.relabel,
    remainderPointCoefficient, GluingExpression.maxComponentGenus, remainderContraction, hh]
  rfl

/-- The actual compressed HHH row receives no nonprimary coefficient when its
nonzero effective remainder has plane degree zero. All primary tails and
other-class rational complements remain in the full row on the left. -/
theorem pointCoefficient_eq_zero_of_exceptional_remainder (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (delta : X.Curve) (hdelta : delta ≠ 0) (hd : X.planeDegree delta = 0) (n : ℕ) :
    BelorousskiPandharipande.pointCoefficient X n
      (SurfaceGenusZero.variableCurve v + delta)
      ![.hyperplane, .hyperplane, .hyperplane] v = 0 := by
  have hterm (i : Fin 20) (e : Fin 6) :
      SurfaceGenusTwo.pointCoefficient X v (BelorousskiPandharipande.orbitCotangentTerm i e)
        (SurfaceGenusZero.variableCurve v + delta) n
        ![.hyperplane, .hyperplane, .hyperplane] =
      remainderPointCoefficient X v (coefficientVertex X v)
        (BelorousskiPandharipande.paperCotangentTerm i) delta n
        ![.hyperplane, .hyperplane, .hyperplane] := by
    have h := remainderPointCoefficient_eq X v (coefficientVertex X v) rfl
      (BelorousskiPandharipande.orbitCotangentTerm i e) delta n
      (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
    rw [remainder_orbit] at h
    exact h.symm
  simp only [BelorousskiPandharipande.pointCoefficient, hterm,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fin.sum_univ_four]
  change -2 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 0) delta n
        ![.hyperplane, .hyperplane, .hyperplane]) +
    2 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 1) delta n
        ![.hyperplane, .hyperplane, .hyperplane]) +
    3 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 2) delta n
        ![.hyperplane, .hyperplane, .hyperplane]) +
    -3 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 3) delta n
        ![.hyperplane, .hyperplane, .hyperplane]) = 0
  have h2 := paper_pair v hv delta hdelta hd n (0 : Fin 2)
  have h3 := paper_pair v hv delta hdelta hd n (1 : Fin 2)
  simp only [ite_true, if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h2 h3
  rw [paper_zero v hv, paper_one v hv delta hdelta hd, h2, h3]
  ring

/-- Different full classes of equal plane degree have zero nonprimary
coefficient in the complete original normalized BP HHH equation. No effective
subclass assumption is imposed: incomparable requests are excluded by the
existing full-class support bound. The marking count is arbitrary. -/
theorem nonprimary_coefficient_eq_zero_of_same_planeDegree (beta : X.Curve)
    (v : Variable X)
    (hv : ∀ gamma m, Sum.inr (SurfaceQuery.points X 2 gamma m) ≠ v)
    (hne : SurfaceGenusZero.variableCurve v ≠ beta)
    (hd : X.planeDegree (SurfaceGenusZero.variableCurve v) = X.planeDegree beta) (n : ℕ) :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X n beta 0
        (SurfaceGenusZero.pointLabels
          (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) n))
      {v} = 0 := by
  by_cases hle : SurfaceGenusZero.variableCurve v ≤ beta
  · have hsplit : SurfaceGenusZero.variableCurve v +
        (beta - SurfaceGenusZero.variableCurve v) = beta := by
      funext i
      exact Nat.add_sub_of_le (hle i)
    have hz : beta - SurfaceGenusZero.variableCurve v ≠ 0 := by
      intro he
      rw [he, add_zero] at hsplit
      exact hne hsplit
    have hzero : X.planeDegree (beta - SurfaceGenusZero.variableCurve v) = 0 := by
      have he := congrArg X.planeDegree hsplit
      rw [map_add] at he
      omega
    rw [← BelorousskiPandharipande.pointCoefficient_eq_full, ← hsplit]
    exact pointCoefficient_eq_zero_of_exceptional_remainder v hv _ hz hzero n
  · exact SurfaceGenusTwo.TermsBound.normalized_coefficient_eq_zero_of_not_le
      (BelorousskiPandharipande.genusTwoTerms_bound X n beta 0
      (SurfaceGenusZero.pointLabels
        (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) n))
      le_rfl v hle

/-- Any surviving nonprimary coefficient in the full HHH row has either its
original full class or strictly smaller plane degree. Smaller energy alone is
not used as a substitute for this conclusion. -/
theorem nonprimary_coefficient_support (beta : X.Curve) (v : Variable X)
    (hv : ∀ gamma m, Sum.inr (SurfaceQuery.points X 2 gamma m) ≠ v) (n : ℕ)
    (hc : RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X n beta 0
        (SurfaceGenusZero.pointLabels
          (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) n))
      {v} ≠ 0) :
    X.planeDegree (SurfaceGenusZero.variableCurve v) < X.planeDegree beta ∨
      SurfaceGenusZero.variableCurve v = beta := by
  have hle : SurfaceGenusZero.variableCurve v ≤ beta := by
    by_contra hn
    exact hc (SurfaceGenusTwo.TermsBound.normalized_coefficient_eq_zero_of_not_le
      (BelorousskiPandharipande.genusTwoTerms_bound X n beta 0
      (SurfaceGenusZero.pointLabels
        (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) n))
      le_rfl v hn)
  have hdle : X.planeDegree (SurfaceGenusZero.variableCurve v) ≤ X.planeDegree beta :=
    hle (Fin.last X.blowups)
  by_cases he : SurfaceGenusZero.variableCurve v = beta
  · exact Or.inr he
  · left
    by_contra hn
    have hd : X.planeDegree (SurfaceGenusZero.variableCurve v) = X.planeDegree beta := by omega
    exact hc (nonprimary_coefficient_eq_zero_of_same_planeDegree beta v hv he hd n)

/-- In a positive-energy canonical P row, an exceptional first-descendant
column can survive only at strictly smaller plane degree. Equal-degree
columns of smaller energy are therefore absent from the complete equation. -/
theorem exceptional_coefficient_support (beta gamma : X.Curve) (i : Fin X.blowups)
    (hbeta : 0 < X.effective.energy beta)
    (hc : RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X (X.effective.energy beta - 1)
        beta 0 (SurfaceGenusZero.pointLabels
          (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
          (X.effective.energy beta - 1)))
      {Sum.inr (SurfaceFirstDescendant.query 2 gamma (.exceptional i)
        (X.effective.energy gamma))} ≠ 0) :
    X.planeDegree gamma < X.planeDegree beta := by
  obtain hd | he := nonprimary_coefficient_support beta
    (.inr (SurfaceFirstDescendant.query 2 gamma (.exceptional i) (X.effective.energy gamma)))
    (fun delta m ↦ SurfaceFirstDescendant.query_ne_points gamma delta (.exceptional i)
      (X.effective.energy gamma) m) (X.effective.energy beta - 1) hc
  · exact hd
  · change gamma = beta at he
    subst gamma
    exact (hc (exceptional_coefficient beta i hbeta)).elim

/-- All exceptional descendant columns at equal or higher plane degree have
zero coefficient in the complete canonical P row. Positive energy specifies
the source's exact marking count; no extra numerical values are assumed. -/
theorem exceptional_coefficient_eq_zero_of_planeDegree_ge (beta gamma : X.Curve)
    (i : Fin X.blowups) (hbeta : 0 < X.effective.energy beta)
    (hd : X.planeDegree beta ≤ X.planeDegree gamma) :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X (X.effective.energy beta - 1)
        beta 0 (SurfaceGenusZero.pointLabels
          (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
          (X.effective.energy beta - 1)))
      {Sum.inr (SurfaceFirstDescendant.query 2 gamma (.exceptional i)
        (X.effective.energy gamma))} = 0 := by
  by_contra hc
  have hl := exceptional_coefficient_support beta gamma i hbeta hc
  omega

end AxiomaticGW.SurfaceGenusTwoBlowupPSupport

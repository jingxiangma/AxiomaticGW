/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupNMixedKSupport
public import AxiomaticGW.Surfaces.GenusTwoBlowupNEEEKSupport
public import AxiomaticGW.Surfaces.GenusTwoBlowupNForeignSupport
public import AxiomaticGW.Surfaces.GenusTwoBlowupNSourcePrimary

/-!
# Strict canonical support of the complete shifted N equation

For the actual four-row relation, every nonzero canonical coefficient is the
requested primary N state or a strictly earlier full-class state. No positive
energy or plane-degree premise is required for this support theorem.

Same-plane exceptional descendant columns cancel using the original scalar
coefficients: the EEH contribution is minus six times the plane degree, while
the EEE contribution is minus twelve. Their retained row weights cancel them.
The source-class cancellation and all effective-subclass bounds come from the
original normalized polynomials. The primary branch uses actual source-class
and foreign-generator vanishing for the zero and energy-one remainder cases.

This module proves support, not a pivot or a recurrence. Nonzero primary pivot
use still requires positive plane degree in the companion coefficient module.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupNCanonicalSupport
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
open SurfaceGenusTwoBlowupNForeignSupport SurfaceGenusTwoBlowupNSourcePrimary
open SurfaceGenusTwoBlowupNCoefficients SurfaceGenusTwoBlowupNMixedKSupport

variable {X : SurfaceTarget}

/-- The original four row weights cancel every proper same-plane exceptional
column; the full effective splitting is retained in the hypothesis. -/
theorem row_exceptional_coefficient_eq_zero_of_proper_remainder (i j : Fin X.blowups)
    (beta gamma delta : X.Curve) (hs : gamma + delta = beta + X.exceptionalCurve i)
    (hd : X.planeDegree delta = 0) (hz : delta ≠ 0) :
    RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row X i beta)
      {Sum.inr ((Family.exceptional j).query gamma)} = 0 := by
  let v : Variable X := .inr ((Family.exceptional j).query gamma)
  have hv : ∀ eta m, Sum.inr (SurfaceQuery.points X 2 eta m) ≠ v :=
    fun eta m ↦ SurfaceFirstDescendant.query_ne_points gamma eta (.exceptional j)
      (X.effective.energy gamma) m
  have hvar : SurfaceGenusZero.variableCurve v = gamma := rfl
  have hsv : SurfaceGenusZero.variableCurve v + delta = beta + X.exceptionalCurve i := by
    rw [hvar]
    exact hs
  have hEHH := normalized_ehh_nonprimary_proper_remainder X i beta v hv delta hsv hd hz
  have hEEH := normalized_eeh_k_proper_remainder X i j beta gamma delta hs hd hz
  have hEEE := SurfaceGenusTwoBlowupNEEEKSupport.normalized_eee_k_proper_remainder
    X i j beta gamma delta hs hd hz
  change RationalTerms.coefficient
    (SurfaceGenusTwoBlowupNRelation.bpRow X (X.effective.energy beta)
      (beta + X.exceptionalCurve i) ![.exceptional i, .exceptional i, .hyperplane]) {v} =
      (if delta = X.exceptionalCurve i ∧ i = j then -6 * (X.planeDegree beta : ℚ) else 0)
    at hEEH
  change RationalTerms.coefficient
    (SurfaceGenusTwoBlowupNRelation.bpRow X (X.effective.energy beta)
      (beta + X.exceptionalCurve i) ![.exceptional i, .exceptional i, .exceptional i]) {v} =
      (if delta = X.exceptionalCurve i ∧ i = j then -12 else 0) at hEEE
  have hne : SurfaceGenusZero.variableCurve v ≠ beta + X.exceptionalCurve i := by
    rw [hvar]
    intro h
    have he : gamma + delta = gamma + 0 := by rw [hs, h, add_zero]
    exact hz (add_left_cancel he)
  have hplane : X.planeDegree (SurfaceGenusZero.variableCurve v) =
      X.planeDegree (beta + X.exceptionalCurve i) := by
    rw [hvar, X.planeDegree_add_exceptionalCurve]
    exact (X.planeDegree_eq_of_shifted_add_eq_iff i hs).mpr hd
  have hHHH := SurfaceGenusTwoBlowupPSupport.nonprimary_coefficient_eq_zero_of_same_planeDegree
    (beta + X.exceptionalCurve i) v hv hne hplane (X.effective.energy beta)
  change RationalTerms.coefficient
    (SurfaceGenusTwoBlowupNRelation.bpRow X (X.effective.energy beta)
      (beta + X.exceptionalCurve i) ![.hyperplane, .hyperplane, .hyperplane]) {v} = 0 at hHHH
  change RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row X i beta) {v} = 0
  simp only [SurfaceGenusTwoBlowupNRelation.row, RationalTerms.coefficient_add,
    RationalTerms.coefficient_scale, hEHH, hEEH, hEEE, hHHH]
  split_ifs <;> ring

/-- The effective-subclass bound removes incomparable requests. Source-class
cancellation and the actual proper-remainder calculation remove every other
same-plane exceptional column, with no supplied splitting assumption. -/
theorem row_exceptional_coefficient_eq_zero_of_same_planeDegree (i j : Fin X.blowups)
    (beta gamma : X.Curve) (hd : X.planeDegree gamma = X.planeDegree beta) :
    RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row X i beta)
      {Sum.inr ((Family.exceptional j).query gamma)} = 0 := by
  by_contra hc
  obtain ⟨delta, hs⟩ := SurfaceGenusTwoBlowupNRelation.canonical_coefficient_subclass
    i beta gamma (.exceptional j) hc
  have hdelta : X.planeDegree delta = 0 :=
    (X.planeDegree_eq_of_shifted_add_eq_iff i hs).mp hd
  by_cases hz : delta = 0
  · have hg : gamma = beta + X.exceptionalCurve i := by
      simpa only [hz, add_zero] using hs
    let v : Variable X := .inr ((Family.exceptional j).query gamma)
    have hv : ∀ eta m, Sum.inr (SurfaceQuery.points X 2 eta m) ≠ v :=
      fun eta m ↦ SurfaceFirstDescendant.query_ne_points gamma eta (.exceptional j)
        (X.effective.energy gamma) m
    have hcurve : SurfaceGenusZero.variableCurve v = beta + X.exceptionalCurve i := by
      exact hg
    exact hc (row_source_nonprimary_coefficient_eq_zero i beta v hv hcurve)
  · exact hc (row_exceptional_coefficient_eq_zero_of_proper_remainder i j beta gamma
      delta hs hdelta hz)

/-- The actual primary column is self or earlier; zero and energy-one shifted
remainders use checked full-row coefficients, rather than the order alone. -/
theorem primary_coefficient_support (i : Fin X.blowups) (beta gamma : X.Curve)
    (hc : RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row X i beta)
      {Sum.inr (Family.primary.query gamma)} ≠ 0) :
    gamma = beta ∨ Earlier X (gamma, .primary) (beta, .primary) := by
  obtain ⟨delta, hs⟩ := SurfaceGenusTwoBlowupNRelation.canonical_coefficient_subclass
    i beta gamma .primary hc
  have hle := X.planeDegree_le_of_shifted_add_eq i hs
  by_cases hdlt : X.planeDegree gamma < X.planeDegree beta
  · exact Or.inr (earlier_of_planeDegree_lt X _ _ hdlt)
  have hd : X.planeDegree gamma = X.planeDegree beta := by omega
  have hdelta : X.planeDegree delta = 0 :=
    (X.planeDegree_eq_of_shifted_add_eq_iff i hs).mp hd
  by_cases hz : delta = 0
  · have hg : gamma = beta + X.exceptionalCurve i := by
      simpa only [hz, add_zero] using hs
    have hzero := row_source_primary_eq_zero i beta (X.effective.energy gamma + 1)
    have hh : RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row X i beta)
        {Sum.inr (Family.primary.query gamma)} = 0 := by
      change RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row X i beta)
        {Sum.inr (SurfaceQuery.points X 2 gamma (X.effective.energy gamma + 1))} = 0
      simpa only [hg] using hzero
    exact (hc hh).elim
  by_cases he : X.effective.energy delta = 1
  · obtain ⟨j, rfl⟩ := X.eq_exceptionalCurve_of_energy_one_of_planeDegree_zero delta he hdelta
    by_cases hij : i = j
    · subst j
      exact Or.inl (add_right_cancel hs)
    · exact (hc (row_foreign_primary_coefficient_zero i j hij beta gamma hs
        (X.effective.energy gamma + 1))).elim
  · have hpos : 0 < X.effective.energy delta := Nat.pos_of_ne_zero
      (fun h ↦ hz ((X.effective.energy_eq_zero_iff delta).mp h))
    exact Or.inr (earlier_of_shifted_subclass_energy_lt X i .primary hs (by omega))

/-- Every nonzero canonical coefficient of the complete original N relation
is the requested primary full-class state or an earlier state. -/
theorem canonical_coefficient_support (i : Fin X.blowups) (beta gamma : X.Curve)
    (family : Family X)
    (hc : RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row X i beta)
      {Sum.inr (family.query gamma)} ≠ 0) :
    (gamma = beta ∧ family = .primary) ∨ Earlier X (gamma, family) (beta, .primary) := by
  have hdle := SurfaceGenusTwoBlowupNRelation.canonical_coefficient_planeDegree_le
    i beta gamma family hc
  cases family with
  | hyperplane =>
      exact Or.inr (earlier_of_rank_lt X _ _ hdle (by change 0 < 2; omega))
  | point =>
      exact Or.inr (earlier_of_rank_lt X _ _ hdle (by change 1 < 2; omega))
  | primary =>
      rcases primary_coefficient_support i beta gamma hc with hg | he
      · exact Or.inl ⟨hg, rfl⟩
      · exact Or.inr he
  | exceptional j =>
      by_cases hdlt : X.planeDegree gamma < X.planeDegree beta
      · exact Or.inr (earlier_of_planeDegree_lt X _ _ hdlt)
      · exact (hc (row_exceptional_coefficient_eq_zero_of_same_planeDegree i j
          beta gamma (by omega))).elim

end AxiomaticGW.SurfaceGenusTwoBlowupNCanonicalSupport

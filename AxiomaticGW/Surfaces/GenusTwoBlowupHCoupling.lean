/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupHSupport
public import AxiomaticGW.Surfaces.GenusTwoBlowupOrder

/-!
# Cancellation of equal-measure shifted hyperplane columns

An effective split of the shifted source that preserves both target plane degree
and energy has a single exceptional generator as remainder. If its main full
class differs from the requested target, this generator differs from the shift.
The actual cross-generator coefficient vanishes in the complete normalized L24
row, so these equal-measure hyperplane columns do not obstruct recursion.

This result retains all curve coordinates and does not identify classes by
energy alone. At positive target energy, the subcritical source-column
vanishing also implies that every nonzero H coefficient belongs to the exact
requested class or an earlier H state. Other canonical sectors and complete
blowup reconstruction remain open.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupHCoupling
open SurfacePolynomialReduction SurfaceGenusTwoBlowupHPivots

/-- Every different full-class hyperplane column of equal plane degree and
energy in an effective shifted split has coefficient zero in the original row. -/
theorem same_planeDegree_and_energy_coefficient_eq_zero (X : SurfaceTarget) (i : Fin X.blowups)
    {beta gamma delta : X.Curve} (hbeta : 0 < X.effective.energy beta)
    (h : gamma + delta = beta + X.exceptionalCurve i)
    (hd : X.planeDegree gamma = X.planeDegree beta)
    (he : X.effective.energy gamma = X.effective.energy beta) (hne : gamma ≠ beta) :
    RationalTerms.coefficient (row X i beta) {hColumn X gamma} = 0 := by
  obtain ⟨j, hdelta⟩ := X.exceptional_remainder_of_shifted_same_planeDegree_and_energy
    i h hd he
  have hij : i ≠ j := by
    intro hij
    subst j
    apply hne
    exact add_right_cancel (by simpa only [hdelta] using h)
  have hn : pointCount X beta = pointCount X gamma := by
    unfold pointCount
    rw [he]
  have hgamma : 0 < X.effective.energy gamma := by rw [he]; exact hbeta
  rw [row, ← L24Relation.pointCoefficient_eq_full, sourceCurve, ← h, hdelta, hn,
    SurfaceGenusTwoBlowupHContributions.pointCoefficient_at_exceptional_generator
      X i j gamma hgamma, if_neg hij]


/-- A nonzero equal-measure H coefficient retains the exact original class;
the full-row support bound supplies the effective remainder. -/
theorem hyperplane_coefficient_nonzero_same_measure (X : SurfaceTarget)
    (i : Fin X.blowups) (beta gamma : X.Curve)
    (hbeta : 0 < X.effective.energy beta)
    (hd : X.planeDegree gamma = X.planeDegree beta)
    (he : X.effective.energy gamma = X.effective.energy beta)
    (hc : RationalTerms.coefficient (row X i beta) {hColumn X gamma} ≠ 0) :
    gamma = beta := by
  have hle : gamma ≤ sourceCurve X i beta := by
    by_contra hn
    have hb := L24Relation.genusTwoTerms_bound X (pointCount X beta) (sourceCurve X i beta)
      0 (SurfaceGenusZero.pointLabels (labels X i) (pointCount X beta))
    exact hc (hb.normalized_coefficient_eq_zero_of_not_le le_rfl (hColumn X gamma) hn)
  have hsplit : gamma + (sourceCurve X i beta - gamma) = beta + X.exceptionalCurve i := by
    funext k
    exact Nat.add_sub_of_le (hle k)
  by_contra hne
  exact hc (same_planeDegree_and_energy_coefficient_eq_zero X i hbeta hsplit hd he hne)

/-- Every surviving H column in the original shifted row is either its exact
requested class or earlier in the established reconstruction order. This is
coefficient support after cancellations, not a claim about uncollected terms. -/
theorem hyperplane_coefficient_support (X : SurfaceTarget) (i : Fin X.blowups)
    (beta gamma : X.Curve) (hbeta : 0 < X.effective.energy beta)
    (hc : RationalTerms.coefficient (row X i beta) {hColumn X gamma} ≠ 0) :
    gamma = beta ∨ SurfaceGenusTwoBlowupOrder.Earlier X
      (gamma, .hyperplane) (beta, .hyperplane) := by
  have hle : gamma ≤ sourceCurve X i beta := by
    by_contra hn
    have hb := L24Relation.genusTwoTerms_bound X (pointCount X beta) (sourceCurve X i beta)
      0 (SurfaceGenusZero.pointLabels (labels X i) (pointCount X beta))
    exact hc (hb.normalized_coefficient_eq_zero_of_not_le le_rfl (hColumn X gamma) hn)
  have hsplit : gamma + (sourceCurve X i beta - gamma) = beta + X.exceptionalCurve i := by
    funext k
    exact Nat.add_sub_of_le (hle k)
  have hdelta : sourceCurve X i beta - gamma ≠ 0 := by
    intro hz
    rw [hz, add_zero] at hsplit
    have hg : gamma = sourceCurve X i beta := hsplit
    rw [hg] at hc
    exact hc (SurfaceGenusTwoBlowupHSupport.source_column_row_coefficient_eq_zero
      X i beta hbeta)
  have hpos : 0 < X.effective.energy (sourceCurve X i beta - gamma) :=
    Nat.pos_of_ne_zero (fun hz ↦ hdelta ((X.effective.energy_eq_zero_iff _).mp hz))
  have henergy := congrArg X.effective.energy hsplit
  rw [map_add, X.energy_add_exceptionalCurve] at henergy
  have heg : X.effective.energy gamma ≤ X.effective.energy beta := by omega
  have hdle := X.planeDegree_le_of_shifted_add_eq i hsplit
  rcases Nat.lt_or_eq_of_le hdle with hd | hd
  · exact Or.inr (SurfaceGenusTwoBlowupOrder.earlier_of_planeDegree_lt X _ _ hd)
  · rcases Nat.lt_or_eq_of_le heg with he | he
    · exact Or.inr (SurfaceGenusTwoBlowupOrder.earlier_of_energy_lt X _ _ hdle rfl he)
    · exact Or.inl (hyperplane_coefficient_nonzero_same_measure X i beta gamma hbeta hd he hc)

end AxiomaticGW.SurfaceGenusTwoBlowupHCoupling

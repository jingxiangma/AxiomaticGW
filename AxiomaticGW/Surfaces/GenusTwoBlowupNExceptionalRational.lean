/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupKCoefficients
public import AxiomaticGW.Surfaces.GenusZeroExceptionalPoints

/-!
# Rational exceptional complements of the shifted BP rows

For a full effective remainder of plane degree zero, the rational triple with
external labels `E_i, E_i` has only the classical unit-node value minus one and
its own exceptional-generator node value minus one. The rational quadruple
with labels `E_i, E_i, E_i` has only the latter value, with sign plus one.

These formulas retain all effective classes, including reducible exceptional
classes. The energy-one exceptional point seed is one; vanishing at energy at
least two follows from the checked genus-zero reconstruction. The binomial
point-distribution formulas apply to arbitrary main-component coefficients.
No genus-two recurrence, support assumption or numerical seed is added.
-/

@[expose] public section

set_option maxRecDepth 20000

namespace AxiomaticGW.SurfaceGenusTwoBlowupNExceptionalRational

open SurfacePolynomialReduction SurfaceGenusTwo GluingExpression
open SurfaceGenusTwoBlowupPCoefficients SurfaceGenusTwoBlowupKCoefficients

/-- The exceptional generator quadruple keeps its energy-one seed and exact node sign. -/
private theorem quad_at_generator (X : SurfaceTarget) (i k : Fin X.blowups)
    (n : ℕ) (b : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X)
      (X.exceptionalCurve k) n ![.exceptional i, .exceptional i, .exceptional i, b] =
      if i = k ∧ n = 0 ∧ b = .exceptional i then 1 else 0 := by
  have hz : X.exceptionalCurve k ≠ 0 := by
    intro hz
    have he := X.energy_exceptionalCurve k
    rw [hz, map_zero] at he
    cases he
  simp only [SurfaceGenusZero.primaryScalar,
    SurfaceGenusZero.pointValue_exceptional_generator, X.c1Degree_exceptionalCurve,
    one_ne_zero, and_false, ite_false, if_neg hz, Fintype.card_fin]
  cases X <;> fin_cases i <;> fin_cases k <;> cases b with
  | unit | hyperplane | point =>
      norm_num [Fin.sum_univ_four, Fin.prod_univ_four,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, SurfaceBasisLabel.codimension, SurfaceBasisLabel.primaryFactor,
        SurfaceTarget.divisorIntersections, SurfaceTarget.latticeCoordinates,
        SurfaceTarget.exceptionalCurve, Pi.single_apply, Fin.castSucc]
      all_goals simp only [reduceCtorEq, and_false, ite_false]
      all_goals first | exact fun _ h ↦ h | (split_ifs <;> first | rfl | omega)
  | exceptional j =>
      fin_cases j <;>
        norm_num [Fin.sum_univ_four, Fin.prod_univ_four,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, SurfaceBasisLabel.codimension, SurfaceBasisLabel.primaryFactor,
          SurfaceTarget.divisorIntersections, SurfaceTarget.latticeCoordinates,
          SurfaceTarget.exceptionalCurve, Pi.single_apply, Fin.castSucc]
      all_goals rfl

/-- The exceptional generator triple keeps its energy-one seed and exact node sign. -/
private theorem triple_at_generator (X : SurfaceTarget) (i k : Fin X.blowups)
    (n : ℕ) (b : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X)
      (X.exceptionalCurve k) n ![.exceptional i, .exceptional i, b] =
      if i = k ∧ n = 0 ∧ b = .exceptional i then -1 else 0 := by
  have hz : X.exceptionalCurve k ≠ 0 := by
    intro hz
    have he := X.energy_exceptionalCurve k
    rw [hz, map_zero] at he
    cases he
  simp only [SurfaceGenusZero.primaryScalar,
    SurfaceGenusZero.pointValue_exceptional_generator, X.c1Degree_exceptionalCurve,
    one_ne_zero, and_false, ite_false, if_neg hz, Fintype.card_fin]
  cases X <;> fin_cases i <;> fin_cases k <;> cases b with
  | unit | hyperplane | point =>
      norm_num [Fin.sum_univ_three, Fin.prod_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, SurfaceBasisLabel.codimension, SurfaceBasisLabel.primaryFactor,
        SurfaceTarget.divisorIntersections, SurfaceTarget.latticeCoordinates,
        SurfaceTarget.exceptionalCurve, Pi.single_apply, Fin.castSucc]
      all_goals simp only [reduceCtorEq, and_false, ite_false]
      all_goals first | exact fun _ h ↦ h | (split_ifs <;> first | rfl | omega)
  | exceptional j =>
      fin_cases j <;>
        norm_num [Fin.sum_univ_three, Fin.prod_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, SurfaceBasisLabel.codimension, SurfaceBasisLabel.primaryFactor,
          SurfaceTarget.divisorIntersections, SurfaceTarget.latticeCoordinates,
          SurfaceTarget.exceptionalCurve, Pi.single_apply, Fin.castSucc]
      all_goals rfl

/-- Exact full-class support of the rational exceptional triple, including class zero. -/
theorem triple_support (X : SurfaceTarget) (i : Fin X.blowups)
    (delta : X.Curve) (hd : X.planeDegree delta = 0) (n : ℕ) (b : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X)
      delta n ![.exceptional i, .exceptional i, b] =
      if delta = 0 ∧ n = 0 ∧ b = .unit then -1 else
        if delta = X.exceptionalCurve i ∧ n = 0 ∧ b = .exceptional i then -1 else 0 := by
  by_cases hz : delta = 0
  · subst delta
    have hi : (0 : X.Curve) ≠ X.exceptionalCurve i := by
      intro h
      have he := X.energy_exceptionalCurve i
      rw [← h, map_zero] at he
      cases he
    simp only [SurfaceGenusTwoBlowupKCoefficients.classical_ee, true_and, hi, false_and,
      ite_false]
  · by_cases he : X.effective.energy delta = 1
    · obtain ⟨k, rfl⟩ := X.eq_exceptionalCurve_of_energy_one_of_planeDegree_zero delta he hd
      have hie : X.exceptionalCurve k = X.exceptionalCurve i ↔ i = k := by
        cases X <;> fin_cases i <;> fin_cases k <;> decide +kernel
      rw [triple_at_generator]
      simp only [hz, false_and, ite_false, hie]
    · have hp : 2 ≤ X.effective.energy delta := by
        have hne : X.effective.energy delta ≠ 0 :=
          fun h ↦ hz ((X.effective.energy_eq_zero_iff delta).mp h)
        omega
      have hv := SurfaceGenusZero.pointValue_eq_zero_of_hyperplane_zero_of_energy_ge_two
        X delta ((X.planeDegree_eq_zero_iff_divisorIntersections_eq_zero delta).mp hd) hp
      have hdi : delta ≠ X.exceptionalCurve i := by
        intro h; rw [h, X.energy_exceptionalCurve] at he; exact he rfl
      rw [SurfaceGenusZero.primaryScalar, if_pos ⟨hz, hv⟩, if_neg (by intro h; exact hz h.1),
        if_neg (by intro h; exact hdi h.1)]

/-- Exact full-class support of the rational exceptional quadruple. -/
theorem quad_support (X : SurfaceTarget) (i : Fin X.blowups)
    (delta : X.Curve) (hd : X.planeDegree delta = 0) (n : ℕ) (b : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X)
      delta n ![.exceptional i, .exceptional i, .exceptional i, b] =
      if delta = X.exceptionalCurve i ∧ n = 0 ∧ b = .exceptional i then 1 else 0 := by
  by_cases hz : delta = 0
  · subst delta
    have hi : (0 : X.Curve) ≠ X.exceptionalCurve i := by
      intro h
      have he := X.energy_exceptionalCurve i
      rw [← h, map_zero] at he
      cases he
    rw [classical_four, if_neg (by intro h; exact hi h.1)]
  · by_cases he : X.effective.energy delta = 1
    · obtain ⟨k, rfl⟩ := X.eq_exceptionalCurve_of_energy_one_of_planeDegree_zero delta he hd
      have hie : X.exceptionalCurve k = X.exceptionalCurve i ↔ i = k := by
        cases X <;> fin_cases i <;> fin_cases k <;> decide +kernel
      rw [quad_at_generator]
      simp only [hie]
    · have hp : 2 ≤ X.effective.energy delta := by
        have hne : X.effective.energy delta ≠ 0 :=
          fun h ↦ hz ((X.effective.energy_eq_zero_iff delta).mp h)
        omega
      have hv := SurfaceGenusZero.pointValue_eq_zero_of_hyperplane_zero_of_energy_ge_two
        X delta ((X.planeDegree_eq_zero_iff_divisorIntersections_eq_zero delta).mp hd) hp
      have hdi : delta ≠ X.exceptionalCurve i := by
        intro h; rw [h, X.energy_exceptionalCurve] at he; exact he rfl
      rw [SurfaceGenusZero.primaryScalar, if_pos ⟨hz, hv⟩, if_neg (by intro h; exact hdi h.1)]

/-- The quadruple receives no added points; all labelled points stay on the main factor. -/
theorem quad_points (X : SurfaceTarget) (i : Fin X.blowups)
    (delta : X.Curve) (hd : X.planeDegree delta = 0) (f : ℕ → ℚ) (n : ℕ)
    (b : SurfaceBasisLabel X) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) delta ij.2
        (![.exceptional i, .exceptional i, .exceptional i, b] : Fin 4 → _))) =
      if delta = X.exceptionalCurve i ∧ b = .exceptional i then f n else 0 := by
  rw [SurfacePointPullback.sum_binomial_of_right_support f
    (fun j ↦ SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) delta j
      (![.exceptional i, .exceptional i, .exceptional i, b] : Fin 4 → _)) n 0 (by
        intro j hj
        rw [quad_support X i delta hd j b, if_neg (fun h ↦ hj h.2.1)])]
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul,
    quad_support X i delta hd, true_and, mul_ite, mul_one, mul_zero]

/-- At positive remainder the triple receives no added points, with sign minus one. -/
theorem triple_points_pos (X : SurfaceTarget) (i : Fin X.blowups)
    (delta : X.Curve) (hd : X.planeDegree delta = 0) (hz : delta ≠ 0) (f : ℕ → ℚ) (n : ℕ)
    (b : SurfaceBasisLabel X) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) delta ij.2
        (![.exceptional i, .exceptional i, b] : Fin 3 → _))) =
      if delta = X.exceptionalCurve i ∧ b = .exceptional i then -f n else 0 := by
  rw [SurfacePointPullback.sum_binomial_of_right_support f
    (fun j ↦ SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) delta j
      (![.exceptional i, .exceptional i, b] : Fin 3 → _)) n 0 (by
        intro j hj
        rw [triple_support X i delta hd j b, if_neg (fun h ↦ hz h.1),
          if_neg (fun h ↦ hj h.2.1)])]
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul,
    triple_support X i delta hd, hz, false_and, ite_false, true_and,
    mul_ite, mul_neg, mul_one, mul_zero]

end AxiomaticGW.SurfaceGenusTwoBlowupNExceptionalRational

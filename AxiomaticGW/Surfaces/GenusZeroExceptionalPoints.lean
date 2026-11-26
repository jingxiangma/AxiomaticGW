/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroScalar
/-!
# Genus-zero point values on exceptional classes

For the three fixed surface targets, vanishing intersection with H means that
an effective class is supported on exceptional generators. The existing
reconstructed genus-zero point value is zero on every such class of
anticanonical energy at least two. At energy at least four this follows from
the actual guarded WDVV step: positive rational H components have zero divisor
factor, and the remaining full-class candidate is removed by the existing
energy guard. Energies two and three are checked from the existing finite
reconstruction, including its original initial sector.

The exceptional generators retain their initial point value one. Nevertheless,
the actual rational tail carrying a node and two primary point states has zero
value at every exceptional class and every additional-point count. At energies
zero and one this follows from the dimension condition, and at higher energies
from the reconstructed point-value vanishing.

This module stays at the genus-zero layer. Its hypothesis is the primitive
H intersection, with no genus-two order or plane-degree API. All full effective
classes, node states and splitting contributions are retained; no seed or
additional reconstruction premise is supplied.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusZero
open SurfacePolynomialReduction GluingExpression

private theorem hyperplane_intersection_eq_last (X : SurfaceTarget) (beta : X.Curve) :
    X.divisorIntersections beta 0 = (beta (Fin.last X.blowups) : ℤ) := by
  cases X <;> rfl

/-- A positive-class primary rational component carrying H has zero divisor
factor when its H intersection is zero, for any candidate point valuation. -/
theorem primaryScalar_eq_zero_of_hyperplane_zero {X : SurfaceTarget}
    (values : X.Curve → ℚ) (beta : X.Curve) (hb : beta ≠ 0)
    (hd : X.divisorIntersections beta 0 = 0)
    (S : Type) [Fintype S] (a : S → SurfaceBasisLabel X)
    (s : S) (hs : a s = .hyperplane) (n : ℕ) :
    primaryScalar X values beta n a = 0 := by
  have hh : (SurfaceBasisLabel.hyperplane : SurfaceBasisLabel X).primaryFactor beta = 0 := by
    change (X.divisorIntersections beta 0 : ℚ) = 0
    rw [hd]
    rfl
  have hp : (∏ t, (a t).primaryFactor beta) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ s) (by rw [hs, hh])
  simp only [primaryScalar, if_neg hb, hp, zero_mul, ite_self]

private theorem classical_h_point_option {X : SurfaceTarget} (values : X.Curve → ℚ)
    (n : ℕ) (b : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X values 0 n
      (Option.elim · b (![.hyperplane, .point] : Fin 2 → SurfaceBasisLabel X)) = 0 := by
  have hd : ¬((((∑ s : Option (Fin 2),
      ((Option.elim · b (![.hyperplane, .point] : Fin 2 → SurfaceBasisLabel X))
        s).codimension : ℕ) : ℤ) + (n : ℤ)) =
      X.c1Degree 0 - 1 + (Fintype.card (Option (Fin 2)) : ℤ)) := by
    simp only [Fintype.sum_option, Fin.sum_univ_two, Option.elim_none, Option.elim_some,
      Matrix.cons_val_zero, Matrix.cons_val_one, SurfaceBasisLabel.codimension,
      Fintype.card_option, Fintype.card_fin, map_zero]
    change ¬(((b.codimension + (1 + 2) : ℕ) : ℤ) + (n : ℤ) = 0 - 1 + (2 + 1))
    omega
  rw [SurfaceGenusZero.primaryScalar, if_neg (fun h ↦ h.1 rfl), if_neg hd]

private theorem pure_exceptional_candidate_hh (X : SurfaceTarget) (values : X.Curve → ℚ)
    (beta : X.Curve) (hb : beta ≠ 0) (hd : X.divisorIntersections beta 0 = 0)
    (hv : values beta = 0) (n : ℕ) :
    SurfaceGenusZero.compactEval X values (WDVV.expression 0) rfl beta n
      (WDVV.reconstructionLabels X) = 0 := by
  have hl : (((WDVV.reconstructionLabels X) ∘ WDVV.labels 0) ∘ Sum.inl) =
      (fun _ : Fin 2 ↦ (SurfaceBasisLabel.hyperplane : SurfaceBasisLabel X)) := by
    funext i
    fin_cases i <;> rfl
  have hr : (((WDVV.reconstructionLabels X) ∘ WDVV.labels 0) ∘ Sum.inr) =
      (fun _ : Fin 2 ↦ (SurfaceBasisLabel.point : SurfaceBasisLabel X)) := by
    funext i
    fin_cases i <;> rfl
  simp only [WDVV.expression, SurfaceGenusZero.compactEval, hl, hr]
  apply Finset.sum_eq_zero
  intro gamma hg
  have hgd : X.divisorIntersections gamma 0 = 0 := by
    have hi := Finset.mem_range.mp (Fintype.mem_piFinset.mp hg (Fin.last X.blowups))
    rw [hyperplane_intersection_eq_last] at hd
    rw [hyperplane_intersection_eq_last]
    omega
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  by_cases hz : gamma = 0
  · have hsub : beta - (0 : X.Curve) = beta := by
      funext i
      exact Nat.sub_zero _
    rw [hz, hsub]
    have hright : SurfaceGenusZero.primaryScalar X values beta ij.2
        (Option.elim · b.dual (fun _ : Fin 2 ↦ .point)) = 0 := by
      rw [SurfaceGenusZero.primaryScalar, if_pos ⟨hb, hv⟩]
    simp only [hright, mul_zero, ite_self]
  · rw [primaryScalar_eq_zero_of_hyperplane_zero values gamma hz hgd (Option (Fin 2))
      _ (some 0) rfl]
    simp only [ite_true, mul_zero]

private theorem pure_exceptional_candidate_cross (X : SurfaceTarget) (values : X.Curve → ℚ)
    (beta : X.Curve) (hd : X.divisorIntersections beta 0 = 0) (n : ℕ) :
    SurfaceGenusZero.compactEval X values (WDVV.expression 2) rfl beta n
      (WDVV.reconstructionLabels X) = 0 := by
  have hl : (((WDVV.reconstructionLabels X) ∘ WDVV.labels 2) ∘ Sum.inl) =
      (![.hyperplane, .point] : Fin 2 → SurfaceBasisLabel X) := by
    funext i
    fin_cases i <;> rfl
  have hr : (((WDVV.reconstructionLabels X) ∘ WDVV.labels 2) ∘ Sum.inr) =
      (![.point, .hyperplane] : Fin 2 → SurfaceBasisLabel X) := by
    funext i
    fin_cases i <;> rfl
  simp only [WDVV.expression, SurfaceGenusZero.compactEval, hl, hr]
  apply Finset.sum_eq_zero
  intro gamma hg
  have hgd : X.divisorIntersections gamma 0 = 0 := by
    have hi := Finset.mem_range.mp (Fintype.mem_piFinset.mp hg (Fin.last X.blowups))
    rw [hyperplane_intersection_eq_last] at hd
    rw [hyperplane_intersection_eq_last]
    omega
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  by_cases hz : gamma = 0
  · rw [hz, classical_h_point_option]
    simp only [ite_true, mul_zero]
  · rw [primaryScalar_eq_zero_of_hyperplane_zero values gamma hz hgd (Option (Fin 2))
      _ (some 0) rfl]
    simp only [ite_true, mul_zero]

/-- The actual guarded uniform WDVV step vanishes on every exceptional-supported
class of energy at least four; all ordered splittings and node states remain. -/
theorem pointValue_eq_zero_of_hyperplane_zero_of_energy_ge_four (X : SurfaceTarget) (beta : X.Curve)
    (hd : X.divisorIntersections beta 0 = 0) (he : 4 ≤ X.effective.energy beta) :
    SurfaceGenusZero.pointValue X beta = 0 := by
  have hb : beta ≠ 0 := by
    intro hz
    rw [hz, map_zero] at he
    omega
  have hthree : ¬X.effective.energy beta = 3 := by omega
  have hline : X.effective.energy X.lineCurve = 3 := by cases X <;> decide +kernel
  have hi : ¬SurfaceGenusZero.IsInitial X beta := by
    intro h
    rcases h with h | h
    · omega
    · rw [h, hline] at he
      omega
  let values : X.Curve → ℚ := fun gamma ↦
    if X.effective.energy gamma < X.effective.energy beta then
      SurfaceGenusZero.pointValue X gamma else 0
  have hv : values beta = 0 := if_neg (lt_irrefl _)
  have h0 := pure_exceptional_candidate_hh X values beta hb hd hv
    (X.effective.energy beta - 4)
  have h2 := pure_exceptional_candidate_cross X values beta hd
    (X.effective.energy beta - 4)
  calc SurfaceGenusZero.pointValue X beta =
      SurfaceGenusZero.compactReconstructionStep X beta
        (fun u ↦ SurfaceGenusZero.pointValue X (SurfaceGenusZero.variableCurve u)) := by
        rw [SurfaceGenusZero.compactReconstructionStep_eq X beta hi,
          SurfaceGenusZero.pointValue_step X beta hi]
    _ = SurfaceGenusZero.scalarReconstructionStep X beta (SurfaceGenusZero.pointValue X) :=
      (SurfaceGenusZero.scalarReconstructionStep_eq X beta _).symm
    _ = 0 := by
      rw [SurfaceGenusZero.scalarReconstructionStep, if_neg hthree]
      change -(∑ i : Fin 3, if WDVV.requested i = 0 then 0 else WDVV.requested i *
        SurfaceGenusZero.compactEval X values (WDVV.expression i) rfl beta
          (X.effective.energy beta - 4) (WDVV.reconstructionLabels X)) = 0
      rw [Fin.sum_univ_three]
      norm_num only [WDVV.requested, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, h0, h2]
      simp only [mul_zero, zero_mul, add_zero, neg_zero, ite_self]

private theorem pointValue_low_hyperplane_zero (X : SurfaceTarget) :
    ∀ gamma ∈ X.bounded 3, X.divisorIntersections gamma 0 = 0 →
      2 ≤ X.effective.energy gamma → SurfaceGenusZero.pointValue X gamma = 0 := by
  cases X <;> decide +kernel

/-- The reconstructed point function vanishes on every exceptional-supported
full effective class of energy at least two. Existing energies two and three
are checked in the kernel, and higher energy follows from the actual WDVV step. -/
theorem pointValue_eq_zero_of_hyperplane_zero_of_energy_ge_two (X : SurfaceTarget) (beta : X.Curve)
    (hd : X.divisorIntersections beta 0 = 0) (he : 2 ≤ X.effective.energy beta) :
    SurfaceGenusZero.pointValue X beta = 0 := by
  by_cases hh : 4 ≤ X.effective.energy beta
  · exact pointValue_eq_zero_of_hyperplane_zero_of_energy_ge_four X beta hd hh
  · apply pointValue_low_hyperplane_zero X beta _ hd he
    rw [X.bounded_eq, X.effective.mem_bounded]
    omega

/-- The actual node/old-point/new-point rational tail has zero value at every
exceptional-supported class, including energy zero and the generator seed. -/
theorem primaryScalar_point_point_tail_eq_zero (X : SurfaceTarget) (beta : X.Curve)
    (hd : X.divisorIntersections beta 0 = 0) (b : SurfaceBasisLabel X) (n : ℕ) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) beta n
      (Option.elim · b (fun _ : Bool ↦ .point)) = 0 := by
  by_cases he : 2 ≤ X.effective.energy beta
  · have hb : beta ≠ 0 := by
      intro hz
      rw [hz, map_zero] at he
      omega
    rw [SurfaceGenusZero.primaryScalar,
      if_pos ⟨hb, pointValue_eq_zero_of_hyperplane_zero_of_energy_ge_two X beta hd he⟩]
  · have hdim : ¬((((∑ s : Option Bool,
        ((Option.elim · b (fun _ : Bool ↦ (SurfaceBasisLabel.point : SurfaceBasisLabel X)))
          s).codimension : ℕ) : ℤ) + (n : ℤ)) =
        X.c1Degree beta - 1 + (Fintype.card (Option Bool) : ℤ)) := by
      simp only [Fintype.sum_option, Fintype.sum_bool, Option.elim_none, Option.elim_some,
        SurfaceBasisLabel.codimension, Fintype.card_option, Fintype.card_bool,
        SurfaceTarget.c1Degree]
      change ¬(((b.codimension + (2 + 2) : ℕ) : ℤ) + (n : ℤ) =
        (X.effective.energy beta : ℤ) - 1 + (2 + 1))
      omega
    rw [SurfaceGenusZero.primaryScalar]
    split_ifs with hzero
    · rfl
    · rfl

/-- The same rational point-pair tail in the usual three-flag vector convention. -/
theorem primaryScalar_node_point_point_eq_zero (X : SurfaceTarget) (beta : X.Curve)
    (hd : X.divisorIntersections beta 0 = 0) (n : ℕ) (b : SurfaceBasisLabel X) :
    primaryScalar X (pointValue X) beta n ![b, .point, .point] = 0 := by
  by_cases he : 2 ≤ X.effective.energy beta
  · have hb : beta ≠ 0 := by
      intro hz
      rw [hz, map_zero] at he
      omega
    rw [primaryScalar,
      if_pos ⟨hb, pointValue_eq_zero_of_hyperplane_zero_of_energy_ge_two X beta hd he⟩]
  · have hdim : ¬((((∑ s : Fin 3,
        ((![b, .point, .point] : Fin 3 → SurfaceBasisLabel X) s).codimension : ℕ) : ℤ)
        + (n : ℤ)) = X.c1Degree beta - 1 + (Fintype.card (Fin 3) : ℤ)) := by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, SurfaceBasisLabel.codimension, Fintype.card_fin,
        SurfaceTarget.c1Degree]
      change ¬(((b.codimension + 2 + 2 : ℕ) : ℤ) + (n : ℤ) =
        (X.effective.energy beta : ℤ) - 1 + 3)
      omega
    rw [primaryScalar]
    split_ifs with hzero
    · rfl
    · rfl

/-- The existing energy-one exceptional generator value remains one; it is
not covered by the energy-at-least-two vanishing theorem. -/
theorem pointValue_exceptional_generator (X : SurfaceTarget) (i : Fin X.blowups) :
    pointValue X (X.exceptionalCurve i) = 1 := by
  rw [pointValue_initial X (X.exceptionalCurve i) (Or.inl (by
    cases X <;> fin_cases i <;> decide +kernel))]
  cases X <;> fin_cases i <;> decide +kernel

end AxiomaticGW.SurfaceGenusZero

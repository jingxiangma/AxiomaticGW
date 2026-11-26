/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupHVanishing
public import AxiomaticGW.Surfaces.GenusZeroExceptionalPoints
public import AxiomaticGW.Surfaces.GenusTwoBlowupPPrimarySupport
public import AxiomaticGW.Surfaces.GenusTwoBlowupHCoupling

/-!
# Other-family support of the shifted hyperplane row

For labels `H, Eᵢ, Eᵢ, Eᵢ`, actual rational complements kill 25 of the 27 held
L24 terms containing a genus-two component at every full effective remainder
of plane degree zero. The two surviving terms, 57 and 64, have no primary
coefficient or first-descendant coefficient whose insertion differs from H.
These constructor calculations retain the original weights, calibration terms,
signed point tails and all exceptional coordinates. They do not assume that
exceptional-input calibration terms vanish.

Consequently the complete original shifted H row has no N, P or K coefficient
at the target plane degree. Combined with the existing exact H support and
full-row class bound, this proves canonical self-or-earlier support at positive
target energy. This file does not construct a solved row or a reconstruction
recurrence.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupHOtherFamilies

open SurfacePolynomialReduction SurfaceGenusTwo SurfaceGenusTwoBlowupHPivots
  GluingExpression SurfaceGenusTwoBlowupHVanishing

-- Actual held constructors and their finite flag permutations require this depth.
set_option maxRecDepth 20000

/-- A rational three-point scalar with a hyperplane and a point vanishes on every full effective
class of plane degree zero. -/
theorem primaryScalar_hyperplane_point_zero (X : SurfaceTarget) (gamma : X.Curve)
    (hd : X.planeDegree gamma = 0) (n : ℕ) (b : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) gamma n
      (![.hyperplane, .point, b] : Fin 3 → _) = 0 := by
  by_cases hz : gamma = 0
  · subst gamma
    have hdim : ¬((((∑ i : Fin 3,
        ((![.hyperplane, .point, b] : Fin 3 → SurfaceBasisLabel X) i).codimension : ℕ) : ℤ)
        + (n : ℤ)) = X.c1Degree 0 - 1 + (Fintype.card (Fin 3) : ℤ)) := by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, SurfaceBasisLabel.codimension, Fintype.card_fin, map_zero]
      change ¬(((1 + 2 + b.codimension : ℕ) : ℤ) + (n : ℤ) = 0 - 1 + 3)
      omega
    rw [SurfaceGenusZero.primaryScalar, if_neg (fun h ↦ h.1 rfl), if_neg hdim]
  · exact SurfaceGenusZero.primaryScalar_eq_zero_of_hyperplane_zero _ gamma hz
      ((X.planeDegree_eq_zero_iff_divisorIntersections_eq_zero gamma).mp hd)
      (Fin 3) _ 0 rfl n

/-- A rational three-point scalar with an exceptional divisor and a point vanishes on every full
effective class of plane degree zero, including energy one. -/
theorem primaryScalar_exceptional_point_zero (X : SurfaceTarget) (i : Fin X.blowups)
    (gamma : X.Curve) (hd : X.planeDegree gamma = 0) (n : ℕ) (b : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) gamma n
      (![.exceptional i, .point, b] : Fin 3 → _) = 0 := by
  by_cases he : 2 ≤ X.effective.energy gamma
  · have hn : gamma ≠ 0 := by intro hz; rw [hz, map_zero] at he; omega
    rw [SurfaceGenusZero.primaryScalar, if_pos ⟨hn,
      SurfaceGenusZero.pointValue_eq_zero_of_hyperplane_zero_of_energy_ge_two X gamma
      ((X.planeDegree_eq_zero_iff_divisorIntersections_eq_zero gamma).mp hd) he⟩]
  · by_cases hb : b = .unit
    · subst b
      by_cases hz : gamma = 0
      · subst gamma
        have hdim : ¬((((∑ j : Fin 3,
            ((![.exceptional i, .point, .unit] : Fin 3 → SurfaceBasisLabel X) j).codimension :
                ℕ) : ℤ)
            + (n : ℤ)) = X.c1Degree 0 - 1 + (Fintype.card (Fin 3) : ℤ)) := by
          simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_two, SurfaceBasisLabel.codimension, Fintype.card_fin, map_zero]
          norm_num only at *
          omega
        rw [SurfaceGenusZero.primaryScalar, if_neg (fun h ↦ h.1 rfl), if_neg hdim]
      · unfold SurfaceGenusZero.primaryScalar
        split_ifs with hv hdim
        · rfl
        · rw [Fin.prod_univ_three]
          change (((X.divisorIntersections gamma i.succ : ℚ) * 1) * 0) * _ = 0
          ring
        · rfl
    · have hc : 1 ≤ b.codimension := by
        cases b <;> first | exact (hb rfl).elim | exact Nat.le_refl _ | exact Nat.le_succ _
      have hdim : ¬((((∑ j : Fin 3,
          ((![.exceptional i, .point, b] : Fin 3 → SurfaceBasisLabel X) j).codimension : ℕ) : ℤ)
          + (n : ℤ)) = X.c1Degree gamma - 1 + (Fintype.card (Fin 3) : ℤ)) := by
        simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, SurfaceBasisLabel.codimension, Fintype.card_fin,
          SurfaceTarget.c1Degree]
        change ¬(((1 + 2 + b.codimension : ℕ) : ℤ) + (n : ℤ) = (X.effective.energy gamma : ℤ) -
            1 + 3)
        omega
      rw [SurfaceGenusZero.primaryScalar]
      split_ifs <;> rfl

/-- Reindexing every marking preserves the exact rational primary scalar,
including its dimension filter and its classical product. -/
private theorem primaryScalar_relabel (X : SurfaceTarget) (f : X.Curve → ℚ) (gamma : X.Curve)
    (n : ℕ) {S T : Type} [Fintype S] [Fintype T] (e : S ≃ T)
    (a : T → SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X f gamma n (a ∘ e) = SurfaceGenusZero.primaryScalar X f
        gamma n a :=
  SurfaceGenusZero.primaryScalar_relabel X f gamma n e a

private theorem primaryScalar_swap_last (X : SurfaceTarget) (f : X.Curve → ℚ) (gamma : X.Curve)
    (n : ℕ) (a b c : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X f gamma n (![a, b, c] : Fin 3 → _) =
        SurfaceGenusZero.primaryScalar X f gamma n (![a, c, b] : Fin 3 → _) := by
  have h : (![a, c, b] : Fin 3 → _) ∘ Equiv.swap 1 2 = (![a, b, c] : Fin 3 → _) := by
    ext j
    fin_cases j <;> rfl
  rw [← h, primaryScalar_relabel]

private theorem exceptional_pair_hyperplane_zero (X : SurfaceTarget) (i : Fin X.blowups)
    (v : Variable X) (delta : X.Curve) (hd : X.planeDegree delta = 0) (n : ℕ) :
    (GetzlerGraphs.join (m := 2) (n := 2) 2 1
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))).pointContraction X
      (primaryPointVertex X v) ((0 : Fin 3 → ℕ), (0 : Fin 3 → ℕ))
      ((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 3)))
      delta n ![.exceptional i, .exceptional i, .exceptional i, .hyperplane] = 0 := by
  have hl (b : SurfaceBasisLabel X) :
      (Option.elim · b (((![.exceptional i, .exceptional i, .exceptional i, .hyperplane] : Fin 4
          → _)
        ∘ (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)) ∘ Sum.inr)) ∘
        finSuccEquiv' 1 = ![.exceptional i, b, .hyperplane] := by
    ext k
    fin_cases k <;> rfl
  simp only [GetzlerGraphs.join, pointContraction, primaryPointVertex, and_self, ite_true, hl]
  apply Finset.sum_eq_zero
  intro split hs
  have hadd := (X.effective.mem_splittings _ _ _).mp ((X.splittings_eq _).symm ▸ hs)
  have hr : X.planeDegree split.2 = 0 := by
    have he := congrArg X.planeDegree hadd
    rw [map_add, hd] at he
    omega
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [primaryScalar_swap_last]
  have he : (![.exceptional i, .hyperplane, b.dual] : Fin 3 → SurfaceBasisLabel X) =
      (![.hyperplane, .exceptional i, b.dual] : Fin 3 → _) ∘ Equiv.swap 0 1 := by
    ext k
    fin_cases k <;> rfl
  rw [he, primaryScalar_relabel X _ split.2 ij.2 (Equiv.swap 0 1),
    primaryScalar_hyperplane_exceptional_eq_zero X i _ _ hr]
  simp only [mul_zero]

private theorem exceptional_pair_point_zero (X : SurfaceTarget) (i : Fin X.blowups)
    (v : Variable X) (delta : X.Curve) (hd : X.planeDegree delta = 0) (n : ℕ) :
    (GetzlerGraphs.join (m := 2) (n := 2) 2 1
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))).pointContraction X
      (primaryPointVertex X v) ((0 : Fin 3 → ℕ), (0 : Fin 3 → ℕ))
      ((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 3)))
      delta n ![.exceptional i, .exceptional i, .exceptional i, .point] = 0 := by
  have hl (b : SurfaceBasisLabel X) :
      (Option.elim · b (((![.exceptional i, .exceptional i, .exceptional i, .point] : Fin 4 → _)
        ∘ (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)) ∘ Sum.inr)) ∘
        finSuccEquiv' 1 = ![.exceptional i, b, .point] := by
    ext k
    fin_cases k <;> rfl
  simp only [GetzlerGraphs.join, pointContraction, primaryPointVertex, and_self, ite_true, hl]
  apply Finset.sum_eq_zero
  intro split hs
  have hadd := (X.effective.mem_splittings _ _ _).mp ((X.splittings_eq _).symm ▸ hs)
  have hr : X.planeDegree split.2 = 0 := by
    have he := congrArg X.planeDegree hadd
    rw [map_add, hd] at he
    omega
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [primaryScalar_swap_last, primaryScalar_exceptional_point_zero X i _ hr]
  simp only [mul_zero]

private theorem pair_mixed_right (X : SurfaceTarget) (i : Fin X.blowups)
    (v : Variable X) (delta : X.Curve) (hd : X.planeDegree delta = 0) (n : ℕ)
    (c : SurfaceBasisLabel X) :
    (GetzlerGraphs.join (m := 2) (n := 2) 2 1
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))).pointContraction X
      (primaryPointVertex X v) ((0 : Fin 3 → ℕ), (0 : Fin 3 → ℕ))
      ((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 3)))
      delta n ![.exceptional i, .exceptional i, .hyperplane, c] = 0 := by
  have hl (b : SurfaceBasisLabel X) :
      (Option.elim · b (((![.exceptional i, .exceptional i, .hyperplane, c] : Fin 4 → _)
        ∘ (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)) ∘ Sum.inl)) ∘
        finSuccEquiv' 2 = ![.exceptional i, .exceptional i, b] := by
    ext k
    fin_cases k <;> rfl
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b (((![.exceptional i, .exceptional i, .hyperplane, c] : Fin 4 → _)
        ∘ (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)) ∘ Sum.inr)) ∘
        finSuccEquiv' 1 = ![.hyperplane, b, c] := by
    ext k
    fin_cases k <;> rfl
  simp only [GetzlerGraphs.join, pointContraction, primaryPointVertex, and_self, ite_true, hl, hr]
  apply Finset.sum_eq_zero
  intro split hs
  have hadd := (X.effective.mem_splittings _ _ _).mp ((X.splittings_eq _).symm ▸ hs)
  have hleft : X.planeDegree split.1 = 0 := by
    have he := congrArg X.planeDegree hadd
    rw [map_add, hd] at he
    omega
  have hright : X.planeDegree split.2 = 0 := by
    have he := congrArg X.planeDegree hadd
    rw [map_add, hd] at he
    omega
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  cases b with
  | unit =>
    rw [show (SurfaceBasisLabel.unit : SurfaceBasisLabel X).dual = .point from rfl,
      primaryScalar_hyperplane_point_zero X _ hright]
    simp only [mul_zero]
  | exceptional j =>
    rw [show (SurfaceBasisLabel.exceptional j : SurfaceBasisLabel X).dual = .exceptional j from rfl,
      primaryScalar_hyperplane_exceptional_eq_zero X j _ _ hright]
    simp only [mul_zero]
  | hyperplane =>
    rw [primaryScalar_swap_last X _ split.1 ij.1]
    have he : (![.exceptional i, .hyperplane, .exceptional i] : Fin 3 → SurfaceBasisLabel X) =
        (![.hyperplane, .exceptional i, .exceptional i] : Fin 3 → _) ∘ Equiv.swap 0 1 := by
      ext k
      fin_cases k <;> rfl
    rw [he, primaryScalar_relabel X _ split.1 ij.1 (Equiv.swap 0 1),
      primaryScalar_hyperplane_exceptional_eq_zero X i _ _ hleft]
    simp only [zero_mul, mul_zero]
  | point =>
    rw [primaryScalar_swap_last X _ split.1 ij.1,
      primaryScalar_exceptional_point_zero X i _ hleft]
    simp only [zero_mul, mul_zero]

private theorem pair_zero_of_left (X : SurfaceTarget) (v : Variable X)
    (delta : X.Curve) (hd : X.planeDegree delta = 0) (n : ℕ)
    (a0 a1 a2 a3 : SurfaceBasisLabel X)
    (hz : ∀ gamma, X.planeDegree gamma = 0 → ∀ m b,
      SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) gamma m
        (![a0, a1, b] : Fin 3 → _) = 0) :
    (GetzlerGraphs.join (m := 2) (n := 2) 2 1
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))).pointContraction X
      (primaryPointVertex X v) ((0 : Fin 3 → ℕ), (0 : Fin 3 → ℕ))
      ((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 3)))
      delta n ![a0, a1, a2, a3] = 0 := by
  have hl (b : SurfaceBasisLabel X) :
      (Option.elim · b (((![a0, a1, a2, a3] : Fin 4 → _)
        ∘ (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)) ∘ Sum.inl)) ∘
        finSuccEquiv' 2 = ![a0, a1, b] := by
    ext k
    fin_cases k <;> rfl
  simp only [GetzlerGraphs.join, pointContraction, primaryPointVertex, and_self, ite_true, hl]
  apply Finset.sum_eq_zero
  intro split hs
  have hadd := (X.effective.mem_splittings _ _ _).mp ((X.splittings_eq _).symm ▸ hs)
  have hleft : X.planeDegree split.1 = 0 := by
    have he := congrArg X.planeDegree hadd
    rw [map_add, hd] at he
    omega
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [hz _ hleft ij.1 b]
  simp only [zero_mul, mul_zero]

private theorem pair_mixed (X : SurfaceTarget) (i : Fin X.blowups)
    (v : Variable X) (delta : X.Curve) (hd : X.planeDegree delta = 0) (n : ℕ)
    (c : SurfaceBasisLabel X) (k : Fin 3) :
    (GetzlerGraphs.join (m := 2) (n := 2) 2 1
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))).pointContraction X
      (primaryPointVertex X v) ((0 : Fin 3 → ℕ), (0 : Fin 3 → ℕ))
      ((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 3)))
      delta n ![if k = 0 then .hyperplane else .exceptional i,
        if k = 1 then .hyperplane else .exceptional i,
        if k = 2 then .hyperplane else .exceptional i, c] = 0 := by
  fin_cases k
  · apply pair_zero_of_left X v delta hd n .hyperplane (.exceptional i) (.exceptional i) c
    intro gamma hg m b
    exact primaryScalar_hyperplane_exceptional_eq_zero X i _ gamma hg m b
  · apply pair_zero_of_left X v delta hd n (.exceptional i) .hyperplane (.exceptional i) c
    intro gamma hg m b
    have he : (![.exceptional i, .hyperplane, b] : Fin 3 → SurfaceBasisLabel X) =
        (![.hyperplane, .exceptional i, b] : Fin 3 → _) ∘ Equiv.swap 0 1 := by
      ext j
      fin_cases j <;> rfl
    rw [he, primaryScalar_relabel X _ gamma m (Equiv.swap 0 1),
      primaryScalar_hyperplane_exceptional_eq_zero X i _ _ hg]
  · exact pair_mixed_right X i v delta hd n c

private theorem triple_chain_mixed (X : SurfaceTarget) (i : Fin X.blowups)
    (v : Variable X) (delta : X.Curve) (hd : X.planeDegree delta = 0) (n : ℕ)
    (c : SurfaceBasisLabel X) (k : Fin 4) :
    (GetzlerGraphs.join (m := 3) (n := 2) 3 1
      (GetzlerGraphs.join (m := 2) (n := 2) 2 1
        (fundamental 0 (Fin 3) (by norm_num [StableArity]))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))).pointContraction X
      (primaryPointVertex X v) (((0 : Fin 3 → ℕ), (0 : Fin 3 → ℕ)), (0 : Fin 3 → ℕ))
      (((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 3))),
        (inferInstance : DecidableEq (Fin 3))) delta n
      ![if k = 0 then .hyperplane else .exceptional i,
        if k = 1 then .hyperplane else .exceptional i,
        if k = 2 then .hyperplane else .exceptional i,
        if k = 3 then .hyperplane else .exceptional i, c] = 0 := by
  let a : Fin 5 → SurfaceBasisLabel X :=
    ![if k = 0 then .hyperplane else .exceptional i,
      if k = 1 then .hyperplane else .exceptional i,
      if k = 2 then .hyperplane else .exceptional i,
      if k = 3 then .hyperplane else .exceptional i, c]
  have hl (b : SurfaceBasisLabel X) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 2 ≃ Fin 5)) ∘ Sum.inl)) ∘
        finSuccEquiv' 3 = ![a 0, a 1, a 2, b] := by ext j; fin_cases j <;> rfl
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 2 ≃ Fin 5)) ∘ Sum.inr)) ∘
        finSuccEquiv' 1 = ![a 3, b, c] := by ext j; fin_cases j <;> rfl
  change (GetzlerGraphs.join (m := 3) (n := 2) 3 1
      (GetzlerGraphs.join (m := 2) (n := 2) 2 1
        (fundamental 0 (Fin 3) (by norm_num [StableArity]))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))).pointContraction X
      (primaryPointVertex X v) (((0 : Fin 3 → ℕ), (0 : Fin 3 → ℕ)), (0 : Fin 3 → ℕ))
      (((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 3))),
        (inferInstance : DecidableEq (Fin 3))) delta n a = 0
  simp only [GetzlerGraphs.join]
  rw [pointContraction, pointContraction]
  simp only [Algebra.algebraMap_self_apply]
  apply Finset.sum_eq_zero
  intro split hs
  have hadd := (X.effective.mem_splittings _ _ _).mp ((X.splittings_eq _).symm ▸ hs)
  have hleft : X.planeDegree split.1 = 0 := by
    have he := congrArg X.planeDegree hadd
    rw [map_add, hd] at he
    omega
  have hright : X.planeDegree split.2 = 0 := by
    have he := congrArg X.planeDegree hadd
    rw [map_add, hd] at he
    omega
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [pointContraction, hl]
  fin_cases k
  · apply mul_eq_zero_of_right
    apply mul_eq_zero_of_left
    exact pair_mixed X i v split.1 hleft ij.1 b 0
  · apply mul_eq_zero_of_right
    apply mul_eq_zero_of_left
    exact pair_mixed X i v split.1 hleft ij.1 b 1
  · apply mul_eq_zero_of_right
    apply mul_eq_zero_of_left
    exact pair_mixed X i v split.1 hleft ij.1 b 2
  · rw [show (![a 0, a 1, a 2, b] : Fin 4 → _) = ![.exceptional i, .exceptional i, .exceptional
      i, b] from rfl,
]
    cases b with
    | hyperplane =>
      apply mul_eq_zero_of_right
      apply mul_eq_zero_of_left
      exact exceptional_pair_hyperplane_zero X i v split.1 hleft ij.1
    | point =>
      apply mul_eq_zero_of_right
      apply mul_eq_zero_of_left
      exact exceptional_pair_point_zero X i v split.1 hleft ij.1
    | unit =>
      have hz : ((fundamental 0 (Fin 3) (by norm_num [StableArity])).relabel
          (finSuccEquiv' 1)).pointContraction X (primaryPointVertex X v) (0 : Fin 3 → ℕ)
          (inferInstance : DecidableEq (Fin 3)) split.2 ij.2 (Option.elim ·
              SurfaceBasisLabel.unit.dual
            ((a ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 2 ≃ Fin 5)) ∘ Sum.inr)) = 0 := by
        rw [pointContraction, pointContraction, hr]
        change SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) split.2 ij.2
          ![.hyperplane, .point, c] = 0
        exact primaryScalar_hyperplane_point_zero X _ hright ij.2 c
      rw [hz]
      simp only [mul_zero]
    | exceptional j =>
      have hz : ((fundamental 0 (Fin 3) (by norm_num [StableArity])).relabel
          (finSuccEquiv' 1)).pointContraction X (primaryPointVertex X v) (0 : Fin 3 → ℕ)
          (inferInstance : DecidableEq (Fin 3)) split.2 ij.2 (Option.elim ·
              (SurfaceBasisLabel.exceptional j).dual
            ((a ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 2 ≃ Fin 5)) ∘ Sum.inr)) = 0 := by
        rw [pointContraction, pointContraction, hr]
        change SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) split.2 ij.2
          ![.hyperplane, .exceptional j, c] = 0
        exact primaryScalar_hyperplane_exceptional_eq_zero X j _ _ hright ij.2 c
      rw [hz]
      simp only [mul_zero]

private theorem remainderPointCoefficient_relabel {X : SurfaceTarget}
    (v : SurfacePolynomialReduction.Variable X) (terminal : SurfaceVertexValues X ℚ)
    {S T : Type} [Fintype S] [Fintype T] (z : GluingExpression.CotangentTerm 2 S)
    (e : S ≃ T) (delta : X.Curve) (n : ℕ) (a : T → SurfaceBasisLabel X) :
    remainderPointCoefficient X v terminal (z.relabel e) delta n a = remainderPointCoefficient X
        v terminal z delta n (a ∘ e) := by
  simp only [remainderPointCoefficient, GluingExpression.CotangentTerm.relabel,
    GluingExpression.maxComponentGenus, remainderContraction]

private theorem primary_chain_zero (X : SurfaceTarget) (v : Variable X)
    (terminal : SurfaceVertexValues X ℚ) (delta : X.Curve) (hd : X.planeDegree delta = 0)
    (n : ℕ) (i : Fin X.blowups) (e : Equiv.Perm (Fin 4)) (k : Fin 4)
    (ha : labels X i ∘ e = ![if k = 0 then .hyperplane else .exceptional i,
        if k = 1 then .hyperplane else .exceptional i,
        if k = 2 then .hyperplane else .exceptional i,
        if k = 3 then .hyperplane else .exceptional i]) :
    remainderPointCoefficient X v terminal (L24Gluing.term120.relabel e)
      delta n (labels X i) = 0 := by
  rw [remainderPointCoefficient_relabel, ha]
  let a : Fin 4 → SurfaceBasisLabel X :=
    ![if k = 0 then .hyperplane else .exceptional i,
      if k = 1 then .hyperplane else .exceptional i,
      if k = 2 then .hyperplane else .exceptional i,
      if k = 3 then .hyperplane else .exceptional i]
  have hl (b : SurfaceBasisLabel X) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 4 ⊕ Fin 0 ≃ Fin 4)) ∘ Sum.inl)) ∘
        finSuccEquiv' 4 = ![a 0, a 1, a 2, a 3, b] := by ext j; fin_cases j <;> rfl
  change remainderPointCoefficient X v terminal L24Gluing.term120 delta n a = 0
  simp only [L24Gluing.term120, L24Gluing.expression50, GetzlerGraphs.join,
    GluingExpression.maxComponentGenus, Nat.zero_add, max_self,
    max_eq_right (show (0 : ℕ) ≤ 2 by decide), remainderPointCoefficient, ite_true,
    remainderContraction, if_neg (show (0 : ℕ) ≠ 2 by decide)]
  apply Finset.sum_eq_zero
  intro split hs
  have hadd := (X.effective.mem_splittings _ _ _).mp ((X.splittings_eq _).symm ▸ hs)
  have hleft : X.planeDegree split.1 = 0 := by
    have he := congrArg X.planeDegree hadd
    rw [map_add, hd] at he
    omega
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [pointContraction, hl]
  apply mul_eq_zero_of_right
  apply mul_eq_zero_of_left
  exact triple_chain_mixed X i v split.1 hleft ij.1 b k

private theorem primaryFrame_coefficient_zero_of_planeDegree_zero (X : SurfaceTarget)
    (v : Variable X) (terminal : SurfaceVertexValues X ℚ) (delta : X.Curve)
    (hd : X.planeDegree delta = 0) (n : ℕ) (i : Fin X.blowups) :
    ∀ j ∈ SurfaceGenusTwoBlowupHUniform.primaryFrame,
    remainderPointCoefficient X v terminal (L24Gluing.term j) delta n (labels X i) = 0 := by
  intro j hj
  simp only [SurfaceGenusTwoBlowupHUniform.primaryFrame, Finset.mem_insert,
      Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show L24Gluing.term (109 : Fin 815) = L24Gluing.term120.relabel
      L24Gluing.flagPermutation9 from rfl]
    apply primary_chain_zero X v terminal delta hd n i L24Gluing.flagPermutation9 3
    ext j
    fin_cases j <;> rfl
  · rw [show L24Gluing.term (110 : Fin 815) = L24Gluing.term120.relabel
      L24Gluing.flagPermutation1 from rfl]
    apply primary_chain_zero X v terminal delta hd n i L24Gluing.flagPermutation1 2
    ext j
    fin_cases j <;> rfl
  · rw [show L24Gluing.term (112 : Fin 815) = L24Gluing.term120.relabel
      L24Gluing.flagPermutation3 from rfl]
    apply primary_chain_zero X v terminal delta hd n i L24Gluing.flagPermutation3 3
    ext j
    fin_cases j <;> rfl
  · rw [show L24Gluing.term (113 : Fin 815) = L24Gluing.term120.relabel
      L24Gluing.flagPermutation2 from rfl]
    apply primary_chain_zero X v terminal delta hd n i L24Gluing.flagPermutation2 2
    ext j
    fin_cases j <;> rfl
  · rw [show L24Gluing.term (119 : Fin 815) = L24Gluing.term120.relabel
      L24Gluing.flagPermutation7 from rfl]
    apply primary_chain_zero X v terminal delta hd n i L24Gluing.flagPermutation7 0
    ext j
    fin_cases j <;> rfl
  · rw [show L24Gluing.term (120 : Fin 815) = L24Gluing.term120 from rfl]
    have hh := primary_chain_zero X v terminal delta hd n i (Equiv.refl _) 0
      (by ext j; fin_cases j <;> rfl)
    simpa only [remainderPointCoefficient_relabel, Equiv.refl_apply, Function.comp_def] using hh

private theorem external_chain_zero_of_planeDegree_zero (X : SurfaceTarget) (v : Variable X)
    (terminal : SurfaceVertexValues X ℚ) (delta : X.Curve) (hd : X.planeDegree delta = 0)
    (n : ℕ) (i : Fin X.blowups) (e : Equiv.Perm (Fin 4)) (k : Fin 3)
    (powers : Fin 2 → ℕ)
    (ha : labels X i ∘ e = ![if k = 0 then .hyperplane else .exceptional i,
        if k = 1 then .hyperplane else .exceptional i,
        if k = 2 then .hyperplane else .exceptional i, .exceptional i]) :
    remainderPointCoefficient X v terminal
      (⟨(GetzlerGraphs.join (m := 3) (n := 1) 3 1
          (GetzlerGraphs.join (m := 2) (n := 2) 2 1
            (fundamental 0 (Fin 3) (by norm_num [StableArity]))
            (fundamental 0 (Fin 3) (by norm_num [StableArity])))
          (fundamental 2 (Fin 2) (by norm_num [StableArity]))).relabel e,
        (((0 : Fin 3 → ℕ), (0 : Fin 3 → ℕ)), powers),
        (((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 3))),
          (inferInstance : DecidableEq (Fin 2)))⟩ : CotangentTerm 2 (Fin 4))
      delta n (labels X i) = 0 := by
  let a : Fin 4 → SurfaceBasisLabel X :=
    ![if k = 0 then .hyperplane else .exceptional i,
      if k = 1 then .hyperplane else .exceptional i,
      if k = 2 then .hyperplane else .exceptional i, .exceptional i]
  have hl (b : SurfaceBasisLabel X) :
      (Option.elim · b (((labels X i ∘ e) ∘
        (finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4)) ∘ Sum.inl)) ∘
        finSuccEquiv' 3 = ![a 0, a 1, a 2, b] := by
    rw [ha]
    ext j
    fin_cases j <;> rfl
  simp only [GetzlerGraphs.join, GluingExpression.maxComponentGenus, Nat.zero_add, max_self,
    max_eq_right (show (0 : ℕ) ≤ 2 by decide), remainderPointCoefficient, ite_true,
    remainderContraction, if_neg (show (0 : ℕ) ≠ 2 by decide)]
  apply Finset.sum_eq_zero
  intro split hs
  have hadd := (X.effective.mem_splittings _ _ _).mp ((X.splittings_eq _).symm ▸ hs)
  have hleft : X.planeDegree split.1 = 0 := by
    have he := congrArg X.planeDegree hadd
    rw [map_add, hd] at he
    omega
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [pointContraction, hl]
  apply mul_eq_zero_of_right
  apply mul_eq_zero_of_left
  exact pair_mixed X i v split.1 hleft ij.1 b k

private theorem externalExceptionalFrame_coefficient_zero_of_planeDegree_zero (X : SurfaceTarget)
    (v : Variable X) (terminal : SurfaceVertexValues X ℚ) (delta : X.Curve)
    (hd : X.planeDegree delta = 0) (n : ℕ) (i : Fin X.blowups) :
    ∀ j ∈ externalExceptionalFrame, remainderPointCoefficient X v terminal
      (L24Gluing.term j) delta n (labels X i) = 0 := by
  have hz : (![0, 0, 0] : Fin 3 → ℕ) = 0 := by ext j; fin_cases j <;> rfl
  intro j hj
  simp only [externalExceptionalFrame, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show L24Gluing.term (51 : Fin 815) = L24Gluing.term51 from rfl]
    unfold L24Gluing.term51 L24Gluing.expression12
    rw [hz]
    apply external_chain_zero_of_planeDegree_zero X v terminal delta hd n i _ 2 _
    ext j
    fin_cases j <;> rfl
  · rw [show L24Gluing.term (59 : Fin 815) = L24Gluing.term59 from rfl]
    unfold L24Gluing.term59 L24Gluing.expression16
    rw [hz]
    apply external_chain_zero_of_planeDegree_zero X v terminal delta hd n i _ 2 _
    ext j
    fin_cases j <;> rfl
  · rw [show L24Gluing.term (66 : Fin 815) = L24Gluing.term66 from rfl]
    unfold L24Gluing.term66 L24Gluing.expression20
    rw [hz]
    apply external_chain_zero_of_planeDegree_zero X v terminal delta hd n i _ 2 _
    ext j
    fin_cases j <;> rfl
  · rw [show L24Gluing.term (76 : Fin 815) = L24Gluing.term76 from rfl]
    unfold L24Gluing.term76 L24Gluing.expression24
    rw [hz]
    apply external_chain_zero_of_planeDegree_zero X v terminal delta hd n i _ 0 _
    ext j
    fin_cases j <;> rfl
  · rw [show L24Gluing.term (83 : Fin 815) = L24Gluing.term83 from rfl]
    unfold L24Gluing.term83 L24Gluing.expression27
    rw [hz]
    apply external_chain_zero_of_planeDegree_zero X v terminal delta hd n i _ 0 _
    ext j
    fin_cases j <;> rfl
  · rw [show L24Gluing.term (93 : Fin 815) = L24Gluing.term93 from rfl]
    unfold L24Gluing.term93 L24Gluing.expression31
    rw [hz]
    apply external_chain_zero_of_planeDegree_zero X v terminal delta hd n i _ 0 _
    ext j
    fin_cases j <;> rfl
  · rw [show L24Gluing.term (95 : Fin 815) = L24Gluing.term95 from rfl]
    unfold L24Gluing.term95 L24Gluing.expression32
    rw [hz]
    have hh := external_chain_zero_of_planeDegree_zero X v terminal delta hd n i
      (Equiv.refl _) 0 (![1, 0] : Fin 2 → ℕ) (by ext j; fin_cases j <;> rfl)
    exact hh

private theorem points_ne_first_query (X : SurfaceTarget) (gamma beta : X.Curve)
    (requested : SurfaceBasisLabel X) (count k : ℕ) :
    SurfaceQuery.points X 2 beta k ≠ SurfaceFirstDescendant.query 2 gamma requested count := by
  intro h
  exact SurfaceFirstDescendant.query_ne_points gamma beta requested count k
    (congrArg (Sum.inr : SurfaceQuery X → Variable X) h)

private theorem primaryTerms_first_zero (X : SurfaceTarget) (gamma beta : X.Curve)
    (requested : SurfaceBasisLabel X) (count : ℕ) (m : Multiset (SurfaceBasisLabel X)) :
    RationalTerms.coefficient (RationalTerms.rename (Sum.inr : SurfaceQuery X → Variable X)
      (SurfaceFirstDescendant.primaryTerms 2 beta m))
      {Sum.inr (SurfaceFirstDescendant.query 2 gamma requested count)} = 0 := by
  rw [SurfaceFirstDescendant.primaryTerms, RationalTerms.coefficient_rename_scale,
    SurfaceFirstDescendant.dimensionTerms]
  split_ifs with hd
  · rw [RationalTerms.coefficient_rename_term]
    simp only [Multiset.map_singleton, Multiset.singleton_inj, Sum.inr.injEq,
      if_neg (points_ne_first_query X gamma beta requested count _), mul_zero]
  · simp only [RationalTerms.rename_zero, RationalTerms.coefficient_zero, mul_zero]

private theorem firstTerms_wrong_state_zero (X : SurfaceTarget) (gamma beta : X.Curve)
    (requested b : SurfaceBasisLabel X) (count : ℕ) (hb : b ≠ requested)
    (m : Multiset (SurfaceBasisLabel X)) :
    RationalTerms.coefficient (RationalTerms.rename (Sum.inr : SurfaceQuery X → Variable X)
      (SurfaceFirstDescendant.terms 2 beta b m))
      {Sum.inr (SurfaceFirstDescendant.query 2 gamma requested count)} = 0 := by
  rw [SurfaceFirstDescendant.terms]
  split_ifs with hu hbunit
  · exact primaryTerms_first_zero X gamma beta requested count _
  · rw [RationalTerms.coefficient_rename_scale, primaryTerms_first_zero, mul_zero]
  · rw [RationalTerms.coefficient_rename_add, RationalTerms.coefficient_rename_scale,
      RationalTerms.coefficient_rename_scale]
    have hp : ∀ q : SurfaceQuery X, q ≠ SurfaceFirstDescendant.query 2 gamma requested count →
        RationalTerms.coefficient (RationalTerms.rename (Sum.inr : SurfaceQuery X → Variable X)
          (SurfaceFirstDescendant.dimensionTerms q))
          {Sum.inr (SurfaceFirstDescendant.query 2 gamma requested count)} = 0 := by
      intro q hq
      rw [SurfaceFirstDescendant.dimensionTerms]
      split_ifs
      · rw [RationalTerms.coefficient_rename_term]
        simp only [Multiset.map_singleton, Multiset.singleton_inj, Sum.inr.injEq, if_neg hq]
      · simp only [RationalTerms.rename_zero, RationalTerms.coefficient_zero]
    have hq : SurfaceFirstDescendant.query 2 beta b (m.count .point) ≠
        SurfaceFirstDescendant.query 2 gamma requested count := by
      intro he
      have hh := congrArg (fun q : SurfaceQuery X ↦
        q.insertions.head?.map SurfaceInsertion.label) he
      simp only [SurfaceFirstDescendant.query, List.head?_cons, Option.map_some,
          Option.some.injEq] at hh
      exact hb hh
    rw [hp _ hq, hp _ (points_ne_first_query X gamma beta requested count _)]
    simp only [mul_zero, add_zero]

private theorem main_hyperplane_first_other_zero (X : SurfaceTarget) (gamma delta : X.Curve)
    (requested : SurfaceBasisLabel X) (count n : ℕ) (hr : requested ≠ .hyperplane)
    (b : SurfaceBasisLabel X) :
    let v : Variable X := .inr (SurfaceFirstDescendant.query 2 gamma requested count)
    remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single 0 1) inferInstance delta
      ![.hyperplane, b] = 0 := by
  let v : Variable X := .inr (SurfaceFirstDescendant.query 2 gamma requested count)
  have hv : ∀ beta m, Sum.inr (SurfaceQuery.points X 2 beta m) ≠ v :=
    fun beta m ↦ SurfaceFirstDescendant.query_ne_points gamma beta requested count m
  dsimp only
  rw [remainderVertex_onePsi_of_not_points v hv]
  split_ifs with hz
  · rw [coefficient_residualTerms_onePsi_of_not_points v hv]
    split_ifs with hd
    · apply firstTerms_wrong_state_zero X gamma gamma requested .hyperplane count (Ne.symm hr)
    · rfl
  · rfl

open SurfaceGenusTwoBlowupPPrimarySupport SurfaceGenusTwoBlowupPPrimary

/-- The actual first-descendant hyperplane main vertex has no primary coefficient at the same
plane degree when its node state is neither the unit nor the hyperplane. -/
theorem main_hyperplane_primary_zero (X : SurfaceTarget) (gamma delta : X.Curve)
    (k m : ℕ) (hd : X.planeDegree delta = 0) (b : SurfaceBasisLabel X)
    (hbu : b ≠ .unit) (hbH : b ≠ .hyperplane) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 gamma k)
    remainderVertex X v (coefficientVertex X v) m 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single 0 1) inferInstance delta
      ![.hyperplane, b] = 0 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 gamma k)
  have hv : X.planeDegree (SurfaceGenusZero.variableCurve v) = X.planeDegree
      (SurfaceGenusZero.variableCurve v + delta) := by
    rw [map_add, hd, add_zero]
  dsimp only
  rw [remainderVertex_onePsi_of_planeDegree_zero v m (Fin 2) _ 0 delta hd _ (Or.inl rfl),
    coefficient_residualTerms_onePsi_same_planeDegree v (Fin 2) _ 0 _ _ (Or.inl rfl) hv m]
  split_ifs with hdim
  · rw [directNormalizedTerms_onePsi_ofLabels 2 le_rfl (Fin 2) _ 0
      (SurfaceGenusZero.variableCurve v + delta)
      (![.hyperplane, b] : Fin 2 → SurfaceBasisLabel X) m]
    have hm : ((Finset.univ.erase (0 : Fin 2)).val.map
        (![.hyperplane, b] : Fin 2 → SurfaceBasisLabel X)) = {b} := rfl
    rw [hm, Matrix.cons_val_zero]
    apply coefficient_terms_primary_zero
    · simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton,
        reduceCtorEq, and_false, false_or, ne_eq]
      exact Ne.symm hbu
    · intro h
      cases h
    · simp only [SurfaceFirstDescendant.correctionCoefficient,
        SurfaceFirstDescendant.divisorSquare, Multiset.count_add,
        Multiset.count_replicate, Multiset.count_singleton, reduceCtorEq,
        ite_false, zero_add, if_neg (Ne.symm hbH), Nat.cast_zero, mul_zero, zero_mul]
  · rfl

private theorem surviving_chain_primary_zero (X : SurfaceTarget) (gamma delta : X.Curve)
    (k n : ℕ) (hd : X.planeDegree delta = 0) (i : Fin X.blowups) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 gamma k)
    remainderPointCoefficient X v (coefficientVertex X v)
      (⟨GetzlerGraphs.join (m := 3) (n := 1) 3 1
          (GetzlerGraphs.join (m := 2) (n := 2) 2 1
            (fundamental 0 (Fin 3) (by norm_num [StableArity]))
            (fundamental 0 (Fin 3) (by norm_num [StableArity])))
          (fundamental 2 (Fin 2) (by norm_num [StableArity])),
        (((0 : Fin 3 → ℕ), (0 : Fin 3 → ℕ)), ![1, 0]),
        (((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 3))),
          (inferInstance : DecidableEq (Fin 2)))⟩ : CotangentTerm 2 (Fin 4))
      delta n ![.exceptional i, .exceptional i, .exceptional i, .hyperplane] = 0 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 gamma k)
  let a : Fin 4 → SurfaceBasisLabel X := ![.exceptional i, .exceptional i, .exceptional i,
      .hyperplane]
  have hl (b : SurfaceBasisLabel X) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4)) ∘ Sum.inl)) ∘
        finSuccEquiv' 3 = ![.exceptional i, .exceptional i, .exceptional i, b] := by
    ext j
    fin_cases j <;> rfl
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4)) ∘ Sum.inr)) ∘
        finSuccEquiv' 1 = ![.hyperplane, b] := by ext j; fin_cases j <;> rfl
  have hz : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by ext j; fin_cases j <;> rfl
  dsimp only
  change remainderPointCoefficient X v (coefficientVertex X v) _ delta n a = 0
  simp only [GetzlerGraphs.join, GluingExpression.maxComponentGenus, Nat.zero_add, max_self,
    max_eq_right (show (0 : ℕ) ≤ 2 by decide), remainderPointCoefficient, ite_true,
    remainderContraction, if_neg (show (0 : ℕ) ≠ 2 by decide), hz, hr]
  apply Finset.sum_eq_zero
  intro split hs
  have hadd := (X.effective.mem_splittings _ _ _).mp ((X.splittings_eq _).symm ▸ hs)
  have hleft : X.planeDegree split.1 = 0 := by
    have he := congrArg X.planeDegree hadd
    rw [map_add, hd] at he
    omega
  have hright : X.planeDegree split.2 = 0 := by
    have he := congrArg X.planeDegree hadd
    rw [map_add, hd] at he
    omega
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [pointContraction, hl]
  cases b with
  | hyperplane =>
    apply mul_eq_zero_of_right
    apply mul_eq_zero_of_left
    exact exceptional_pair_hyperplane_zero X i v split.1 hleft ij.1
  | point =>
    apply mul_eq_zero_of_right
    apply mul_eq_zero_of_left
    exact exceptional_pair_point_zero X i v split.1 hleft ij.1
  | unit =>
    apply mul_eq_zero_of_right
    apply mul_eq_zero_of_right
    exact main_hyperplane_primary_zero X gamma split.2 k ij.2 hright .point
      (by intro he; cases he) (by intro he; cases he)
  | exceptional j =>
    apply mul_eq_zero_of_right
    apply mul_eq_zero_of_right
    exact main_hyperplane_primary_zero X gamma split.2 k ij.2 hright (.exceptional j)
      (by intro he; cases he) (by intro he; cases he)

/-- Four primary flags have no classical degree-zero value, for any added points. -/
private theorem primaryScalar_quad_classical_zero (X : SurfaceTarget) (f : X.Curve → ℚ)
    (n : ℕ) (a : Fin 4 → SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X f 0 n a = 0 := by
  have hn : n + Fintype.card (Fin 4) ≠ 3 := by
    simp only [Fintype.card_fin]
    omega
  simp only [SurfaceGenusZero.primaryScalar, ne_eq, not_true_eq_false, false_and,
    ite_true, if_neg hn, ite_self]

/-- At plane degree zero, an H primary flag kills every four-flag scalar. -/
private theorem primaryScalar_quad_hyperplane_zero (X : SurfaceTarget) (f : X.Curve → ℚ)
    (gamma : X.Curve) (hd : X.planeDegree gamma = 0) (n : ℕ)
    (a : Fin 4 → SurfaceBasisLabel X) (s : Fin 4) (hs : a s = .hyperplane) :
    SurfaceGenusZero.primaryScalar X f gamma n a = 0 := by
  by_cases hz : gamma = 0
  · subst gamma
    exact primaryScalar_quad_classical_zero X f n a
  · exact SurfaceGenusZero.primaryScalar_eq_zero_of_hyperplane_zero f gamma hz
      ((X.planeDegree_eq_zero_iff_divisorIntersections_eq_zero gamma).mp hd)
      (Fin 4) a s hs n

/-- A primary unit kills every positive-class four-flag scalar; classical arity
four also vanishes. No plane-degree condition is required. -/
private theorem primaryScalar_quad_unit_zero (X : SurfaceTarget) (f : X.Curve → ℚ)
    (gamma : X.Curve) (n : ℕ) (a : Fin 4 → SurfaceBasisLabel X) (s : Fin 4)
    (hs : a s = .unit) :
    SurfaceGenusZero.primaryScalar X f gamma n a = 0 := by
  by_cases hz : gamma = 0
  · subst gamma
    exact primaryScalar_quad_classical_zero X f n a
  · have hp : (∏ t, (a t).primaryFactor gamma) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ s) (by rw [hs]; rfl)
    simp only [SurfaceGenusZero.primaryScalar, if_neg hz, hp, zero_mul, ite_self]

/-- Three exceptional divisor flags and a point have zero rational scalar at
plane degree zero. Energies zero/one fail dimension; higher energies use the
proved exceptional point-value vanishing. -/
private theorem primaryScalar_quad_exceptional_point_zero (X : SurfaceTarget)
    (i : Fin X.blowups) (gamma : X.Curve) (hd : X.planeDegree gamma = 0) (n : ℕ) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) gamma n
      (![.exceptional i, .exceptional i, .exceptional i, .point] : Fin 4 → _) = 0 := by
  by_cases he : 2 ≤ X.effective.energy gamma
  · have hz : gamma ≠ 0 := by intro hh; rw [hh, map_zero] at he; omega
    rw [SurfaceGenusZero.primaryScalar, if_pos ⟨hz,
      SurfaceGenusZero.pointValue_eq_zero_of_hyperplane_zero_of_energy_ge_two X gamma
        ((X.planeDegree_eq_zero_iff_divisorIntersections_eq_zero gamma).mp hd) he⟩]
  · have hdim : ¬((((∑ j : Fin 4,
        ((![.exceptional i, .exceptional i, .exceptional i, .point] :
          Fin 4 → SurfaceBasisLabel X) j).codimension : ℕ) : ℤ) + (n : ℤ)) = X.c1Degree gamma -
              1 + (Fintype.card (Fin 4) : ℤ)) := by
      simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, SurfaceBasisLabel.codimension,
        Fintype.card_fin, SurfaceTarget.c1Degree]
      change ¬(((1 + 1 + 1 + 2 : ℕ) : ℤ) + (n : ℤ) = (X.effective.energy gamma : ℤ) - 1 + 4)
      omega
    rw [SurfaceGenusZero.primaryScalar]
    split_ifs <;> rfl

/-- The actual triple/quad rational complement with H on any old external flag
has zero contraction for every full zero-plane-degree class and point budget. -/
private theorem triple_quad_mixed (X : SurfaceTarget) (i : Fin X.blowups)
    (v : Variable X) (delta : X.Curve) (hd : X.planeDegree delta = 0) (n : ℕ)
    (c : SurfaceBasisLabel X) (k : Fin 4) :
    (GetzlerGraphs.join (m := 2) (n := 3) 2 2
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
      (fundamental 0 (Fin 4) (by norm_num [StableArity]))).pointContraction X
      (primaryPointVertex X v) ((0 : Fin 3 → ℕ), (0 : Fin 4 → ℕ))
      ((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 4)))
      delta n ![if k = 0 then .hyperplane else .exceptional i,
        if k = 1 then .hyperplane else .exceptional i,
        if k = 2 then .hyperplane else .exceptional i,
        if k = 3 then .hyperplane else .exceptional i, c] = 0 := by
  let a : Fin 5 → SurfaceBasisLabel X :=
    ![if k = 0 then .hyperplane else .exceptional i,
      if k = 1 then .hyperplane else .exceptional i,
      if k = 2 then .hyperplane else .exceptional i,
      if k = 3 then .hyperplane else .exceptional i, c]
  have hl (b : SurfaceBasisLabel X) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 2 ⊕ Fin 3 ≃ Fin 5)) ∘ Sum.inl)) ∘
        finSuccEquiv' 2 = ![a 0, a 1, b] := by ext j; fin_cases j <;> rfl
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 2 ⊕ Fin 3 ≃ Fin 5)) ∘ Sum.inr)) ∘
        finSuccEquiv' 2 = ![a 2, a 3, b, c] := by ext j; fin_cases j <;> rfl
  change (GetzlerGraphs.join (m := 2) (n := 3) 2 2
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
      (fundamental 0 (Fin 4) (by norm_num [StableArity]))).pointContraction X
      (primaryPointVertex X v) ((0 : Fin 3 → ℕ), (0 : Fin 4 → ℕ))
      ((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 4)))
      delta n a = 0
  simp only [GetzlerGraphs.join, pointContraction, primaryPointVertex, and_self,
    ite_true, hl, hr]
  apply Finset.sum_eq_zero
  intro split hs
  have hadd := (X.effective.mem_splittings _ _ _).mp ((X.splittings_eq _).symm ▸ hs)
  have hleft : X.planeDegree split.1 = 0 := by
    have he := congrArg X.planeDegree hadd
    rw [map_add, hd] at he
    omega
  have hright : X.planeDegree split.2 = 0 := by
    have he := congrArg X.planeDegree hadd
    rw [map_add, hd] at he
    omega
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  fin_cases k
  · rw [show (![a 0, a 1, b] : Fin 3 → _) = ![.hyperplane, .exceptional i, b] from rfl,
      primaryScalar_hyperplane_exceptional_eq_zero X i _ _ hleft]
    simp only [zero_mul, mul_zero]
  · have he : (![a 0, a 1, b] : Fin 3 → _) = (![.hyperplane, .exceptional i, b] : Fin 3 → _) ∘
      Equiv.swap 0 1 := by
      ext j; fin_cases j <;> rfl
    rw [he, primaryScalar_relabel X _ split.1 ij.1 (Equiv.swap 0 1),
      primaryScalar_hyperplane_exceptional_eq_zero X i _ _ hleft]
    simp only [zero_mul, mul_zero]
  · rw [primaryScalar_quad_hyperplane_zero X _ split.2 hright ij.2
      (![a 2, a 3, b.dual, c] : Fin 4 → _) 0 rfl]
    simp only [mul_zero]
  · rw [primaryScalar_quad_hyperplane_zero X _ split.2 hright ij.2
      (![a 2, a 3, b.dual, c] : Fin 4 → _) 1 rfl]
    simp only [mul_zero]

/-- The actual quad/triple complement also vanishes. With H on the final triple,
the quad EEE component kills unit/H/point node states, and every exceptional
node makes the H/Ej triple vanish. -/
private theorem quad_triple_mixed (X : SurfaceTarget) (i : Fin X.blowups)
    (v : Variable X) (delta : X.Curve) (hd : X.planeDegree delta = 0) (n : ℕ)
    (c : SurfaceBasisLabel X) (k : Fin 4) :
    (GetzlerGraphs.join (m := 3) (n := 2) 3 1
      (fundamental 0 (Fin 4) (by norm_num [StableArity]))
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))).pointContraction X
      (primaryPointVertex X v) ((0 : Fin 4 → ℕ), (0 : Fin 3 → ℕ))
      ((inferInstance : DecidableEq (Fin 4)), (inferInstance : DecidableEq (Fin 3)))
      delta n ![if k = 0 then .hyperplane else .exceptional i,
        if k = 1 then .hyperplane else .exceptional i,
        if k = 2 then .hyperplane else .exceptional i,
        if k = 3 then .hyperplane else .exceptional i, c] = 0 := by
  let a : Fin 5 → SurfaceBasisLabel X :=
    ![if k = 0 then .hyperplane else .exceptional i,
      if k = 1 then .hyperplane else .exceptional i,
      if k = 2 then .hyperplane else .exceptional i,
      if k = 3 then .hyperplane else .exceptional i, c]
  have hl (b : SurfaceBasisLabel X) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 2 ≃ Fin 5)) ∘ Sum.inl)) ∘
        finSuccEquiv' 3 = ![a 0, a 1, a 2, b] := by ext j; fin_cases j <;> rfl
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 2 ≃ Fin 5)) ∘ Sum.inr)) ∘
        finSuccEquiv' 1 = ![a 3, b, c] := by ext j; fin_cases j <;> rfl
  change (GetzlerGraphs.join (m := 3) (n := 2) 3 1
      (fundamental 0 (Fin 4) (by norm_num [StableArity]))
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))).pointContraction X
      (primaryPointVertex X v) ((0 : Fin 4 → ℕ), (0 : Fin 3 → ℕ))
      ((inferInstance : DecidableEq (Fin 4)), (inferInstance : DecidableEq (Fin 3)))
      delta n a = 0
  simp only [GetzlerGraphs.join, pointContraction, primaryPointVertex, and_self,
    ite_true, hl, hr]
  apply Finset.sum_eq_zero
  intro split hs
  have hadd := (X.effective.mem_splittings _ _ _).mp ((X.splittings_eq _).symm ▸ hs)
  have hleft : X.planeDegree split.1 = 0 := by
    have he := congrArg X.planeDegree hadd
    rw [map_add, hd] at he
    omega
  have hright : X.planeDegree split.2 = 0 := by
    have he := congrArg X.planeDegree hadd
    rw [map_add, hd] at he
    omega
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  fin_cases k
  · rw [primaryScalar_quad_hyperplane_zero X _ split.1 hleft ij.1
      (![a 0, a 1, a 2, b] : Fin 4 → _) 0 rfl]
    simp only [zero_mul, mul_zero]
  · rw [primaryScalar_quad_hyperplane_zero X _ split.1 hleft ij.1
      (![a 0, a 1, a 2, b] : Fin 4 → _) 1 rfl]
    simp only [zero_mul, mul_zero]
  · rw [primaryScalar_quad_hyperplane_zero X _ split.1 hleft ij.1
      (![a 0, a 1, a 2, b] : Fin 4 → _) 2 rfl]
    simp only [zero_mul, mul_zero]
  · rw [show (![a 0, a 1, a 2, b] : Fin 4 → _) = ![.exceptional i, .exceptional i, .exceptional
      i, b] from rfl]
    cases b with
    | unit =>
      rw [primaryScalar_quad_unit_zero X _ split.1 ij.1
        (![.exceptional i, .exceptional i, .exceptional i, .unit] : Fin 4 → _) 3 rfl]
      simp only [zero_mul, mul_zero]
    | hyperplane =>
      rw [primaryScalar_quad_hyperplane_zero X _ split.1 hleft ij.1
        (![.exceptional i, .exceptional i, .exceptional i, .hyperplane] : Fin 4 → _) 3 rfl]
      simp only [zero_mul, mul_zero]
    | point =>
      rw [primaryScalar_quad_exceptional_point_zero X i split.1 hleft ij.1]
      simp only [zero_mul, mul_zero]
    | exceptional j =>
      rw [show (SurfaceBasisLabel.exceptional j : SurfaceBasisLabel X).dual = .exceptional j
          from rfl,
        show (![a 3, .exceptional j, c] : Fin 3 → _) = ![.hyperplane, .exceptional j, c] from rfl,
        primaryScalar_hyperplane_exceptional_eq_zero X j _ _ hright]
      simp only [mul_zero]

private theorem oneMarking_chain_zero_of_planeDegree_zero (X : SurfaceTarget) (v : Variable X)
    (terminal : SurfaceVertexValues X ℚ) (delta : X.Curve) (hd : X.planeDegree delta = 0)
    (n : ℕ) (i : Fin X.blowups) (x : GluingExpression 0 (Fin 5))
    (d : x.CotangentDecoration) (l : x.DecidableLabels) (e : Equiv.Perm (Fin 4)) (k : Fin 4)
    (ha : labels X i ∘ e = ![if k = 0 then .hyperplane else .exceptional i,
        if k = 1 then .hyperplane else .exceptional i,
        if k = 2 then .hyperplane else .exceptional i,
        if k = 3 then .hyperplane else .exceptional i])
    (hx : ∀ epsilon, X.planeDegree epsilon = 0 → ∀ m b,
      x.pointContraction X (primaryPointVertex X v) d l epsilon m
        ![if k = 0 then .hyperplane else .exceptional i,
          if k = 1 then .hyperplane else .exceptional i,
          if k = 2 then .hyperplane else .exceptional i,
          if k = 3 then .hyperplane else .exceptional i, b] = 0) :
    remainderPointCoefficient X v terminal
      (⟨(GetzlerGraphs.join (m := 4) (n := 0) 4 0 x
          (fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel e,
        (d, ![1]), (l, (inferInstance : DecidableEq (Fin 1)))⟩ : CotangentTerm 2 (Fin 4))
      delta n (labels X i) = 0 := by
  have hm : x.maxComponentGenus = 0 := Nat.eq_zero_of_le_zero x.maxComponentGenus_le
  have hl (b : SurfaceBasisLabel X) :
      (Option.elim · b (((labels X i ∘ e) ∘
        (finSumFinEquiv : Fin 4 ⊕ Fin 0 ≃ Fin 4)) ∘ Sum.inl)) ∘
        finSuccEquiv' 4 = ![if k = 0 then .hyperplane else .exceptional i,
          if k = 1 then .hyperplane else .exceptional i,
          if k = 2 then .hyperplane else .exceptional i,
          if k = 3 then .hyperplane else .exceptional i, b] := by
    rw [ha]
    ext j
    fin_cases j <;> rfl
  simp only [GetzlerGraphs.join, GluingExpression.maxComponentGenus, hm,
    max_eq_right (show (0 : ℕ) ≤ 2 by decide), remainderPointCoefficient, ite_true,
    remainderContraction, if_neg (show (0 : ℕ) ≠ 2 by decide)]
  apply Finset.sum_eq_zero
  intro split hs
  have hadd := (X.effective.mem_splittings _ _ _).mp ((X.splittings_eq _).symm ▸ hs)
  have hleft : X.planeDegree split.1 = 0 := by
    have he := congrArg X.planeDegree hadd
    rw [map_add, hd] at he
    omega
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [pointContraction, hl, hx _ hleft ij.1 b]
  simp only [zero_mul, mul_zero]

set_option maxHeartbeats 1200000 in
-- The nine actual held constructors require simultaneous finite flag normalization.

private theorem oneMarkingFrame_coefficient_zero_of_planeDegree_zero (X : SurfaceTarget)
    (v : Variable X) (terminal : SurfaceVertexValues X ℚ) (delta : X.Curve)
    (hd : X.planeDegree delta = 0) (n : ℕ) (i : Fin X.blowups) :
    ∀ j ∈ SurfaceGenusTwoBlowupHUniform.oneMarkingFrame,
    remainderPointCoefficient X v terminal (L24Gluing.term j) delta n (labels X i) = 0 := by
  have hz3 : (![0, 0, 0] : Fin 3 → ℕ) = 0 := by ext j; fin_cases j <;> rfl
  have hz4 : (![0, 0, 0, 0] : Fin 4 → ℕ) = 0 := by ext j; fin_cases j <;> rfl
  intro j hj
  simp only [SurfaceGenusTwoBlowupHUniform.oneMarkingFrame, Finset.mem_insert,
      Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show L24Gluing.term (56 : Fin 815) = L24Gluing.term56 from rfl]
    unfold L24Gluing.term56 L24Gluing.expression14
    rw [hz4, hz3]
    apply oneMarking_chain_zero_of_planeDegree_zero X v terminal delta hd n i _ _ _ _ 2
    · ext j
      fin_cases j <;> rfl
    · intro epsilon he m b
      exact triple_quad_mixed X i v epsilon he m b 2
  · rw [show L24Gluing.term (63 : Fin 815) = L24Gluing.term63 from rfl]
    unfold L24Gluing.term63 L24Gluing.expression18
    rw [hz4, hz3]
    apply oneMarking_chain_zero_of_planeDegree_zero X v terminal delta hd n i _ _ _ _ 2
    · ext j
      fin_cases j <;> rfl
    · intro epsilon he m b
      exact triple_quad_mixed X i v epsilon he m b 2
  · rw [show L24Gluing.term (70 : Fin 815) = L24Gluing.term70 from rfl]
    unfold L24Gluing.term70 L24Gluing.expression22
    rw [hz4, hz3]
    apply oneMarking_chain_zero_of_planeDegree_zero X v terminal delta hd n i _ _ _ _ 2
    · ext j
      fin_cases j <;> rfl
    · intro epsilon he m b
      exact triple_quad_mixed X i v epsilon he m b 2
  · rw [show L24Gluing.term (74 : Fin 815) = L24Gluing.term74 from rfl]
    unfold L24Gluing.term74 L24Gluing.expression23
    rw [hz4, hz3]
    apply oneMarking_chain_zero_of_planeDegree_zero X v terminal delta hd n i _ _ _ _ 3
    · ext j
      fin_cases j <;> rfl
    · intro epsilon he m b
      exact quad_triple_mixed X i v epsilon he m b 3
  · rw [show L24Gluing.term (81 : Fin 815) = L24Gluing.term81 from rfl]
    unfold L24Gluing.term81 L24Gluing.expression26
    rw [hz4, hz3]
    apply oneMarking_chain_zero_of_planeDegree_zero X v terminal delta hd n i _ _ _ _ 0
    · ext j
      fin_cases j <;> rfl
    · intro epsilon he m b
      exact triple_quad_mixed X i v epsilon he m b 0
  · rw [show L24Gluing.term (88 : Fin 815) = L24Gluing.term88 from rfl]
    unfold L24Gluing.term88 L24Gluing.expression29
    rw [hz4, hz3]
    apply oneMarking_chain_zero_of_planeDegree_zero X v terminal delta hd n i _ _ _ _ 0
    · ext j
      fin_cases j <;> rfl
    · intro epsilon he m b
      exact triple_quad_mixed X i v epsilon he m b 0
  · rw [show L24Gluing.term (97 : Fin 815) = L24Gluing.term97 from rfl]
    unfold L24Gluing.term97 L24Gluing.expression33
    rw [hz4, hz3]
    have hh := oneMarking_chain_zero_of_planeDegree_zero X v terminal delta hd n i
      (GetzlerGraphs.join (m := 2) (n := 3) 2 2
        (fundamental 0 (Fin 3) (by norm_num [StableArity]))
        (fundamental 0 (Fin 4) (by norm_num [StableArity])))
      ((0 : Fin 3 → ℕ), (0 : Fin 4 → ℕ))
      ((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 4)))
      (Equiv.refl _) 0 (by ext j; fin_cases j <;> rfl)
      (fun epsilon he m b ↦ triple_quad_mixed X i v epsilon he m b 0)
    exact hh
  · rw [show L24Gluing.term (101 : Fin 815) = L24Gluing.term101 from rfl]
    unfold L24Gluing.term101 L24Gluing.expression34
    rw [hz4, hz3]
    apply oneMarking_chain_zero_of_planeDegree_zero X v terminal delta hd n i _ _ _ _ 0
    · ext j
      fin_cases j <;> rfl
    · intro epsilon he m b
      exact quad_triple_mixed X i v epsilon he m b 0
  · rw [show L24Gluing.term (105 : Fin 815) = L24Gluing.term105 from rfl]
    unfold L24Gluing.term105 L24Gluing.expression35
    rw [hz4, hz3]
    have hh := oneMarking_chain_zero_of_planeDegree_zero X v terminal delta hd n i
      (GetzlerGraphs.join (m := 3) (n := 2) 3 1
        (fundamental 0 (Fin 4) (by norm_num [StableArity]))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      ((0 : Fin 4 → ℕ), (0 : Fin 3 → ℕ))
      ((inferInstance : DecidableEq (Fin 4)), (inferInstance : DecidableEq (Fin 3)))
      (Equiv.refl _) 0 (by ext j; fin_cases j <;> rfl)
      (fun epsilon he m b ↦ quad_triple_mixed X i v epsilon he m b 0)
    exact hh

private theorem outer_fork_zero (X : SurfaceTarget) (v : Variable X)
    (terminal : SurfaceVertexValues X ℚ) (delta : X.Curve)
    (hd : X.planeDegree delta = 0) (x : GluingExpression 2 (Fin 3))
    (d : x.CotangentDecoration) (l : x.DecidableLabels) (hx : x.maxComponentGenus = 2)
    (e : Equiv.Perm (Fin 4)) (n : ℕ) (i : Fin X.blowups)
    (a : Fin 4 → SurfaceBasisLabel X) (ha0 : a (e 0) = .hyperplane)
    (ha1 : a (e 1) = .exceptional i) :
    remainderPointCoefficient X v terminal
      (⟨(GetzlerGraphs.join (m := 2) (n := 2) 2 2
        (fundamental 0 (Fin 3) (by norm_num [StableArity])) x).relabel e,
        (![0, 0, 0], d), ((inferInstance : DecidableEq (Fin 3)), l)⟩ :
        CotangentTerm 2 (Fin 4)) delta n a = 0 := by
  have hzero : (![0, 0, 0] : Fin 3 → ℕ) = 0 := by decide +kernel
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b (((a ∘ e) ∘ (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)) ∘ Sum.inl)) ∘
        finSuccEquiv' 2 = ![a (e 0), a (e 1), b] := by
    funext k
    fin_cases k <;> rfl
  simp only [GetzlerGraphs.join, GluingExpression.maxComponentGenus, hx,
    max_eq_right (show (0 : ℕ) ≤ 2 by decide), remainderPointCoefficient,
    ite_true, remainderContraction, if_neg (show (0 : ℕ) ≠ 2 by decide),
    pointContraction, primaryPointVertex, hzero, and_self]
  apply Finset.sum_eq_zero
  intro split hsplit
  have hadd : split.1 + split.2 = delta := by
    rw [X.splittings_eq] at hsplit
    exact (X.effective.mem_splittings _ _ _).mp hsplit
  have hdegree : X.planeDegree split.1 = 0 := by
    have hle := X.planeDegree_le_of_add_eq hadd
    omega
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [hr, ha0, ha1,
    primaryScalar_hyperplane_exceptional_eq_zero X i _ split.1 hdegree ij.1 b,
    zero_mul, mul_zero]

private theorem rationalHyperplaneExceptionalFrame_coefficient_zero (X : SurfaceTarget)
    (v : Variable X) (terminal : SurfaceVertexValues X ℚ) (delta : X.Curve) (hd : X.planeDegree
        delta = 0) (n : ℕ)
    (i : Fin X.blowups) : ∀ j ∈ rationalHyperplaneExceptionalFrame,
    remainderPointCoefficient X v terminal
      (L24Gluing.term j) delta n (labels X i) = 0 := by
  intro j hj
  simp only [rationalHyperplaneExceptionalFrame, Finset.mem_insert,
    Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  · rw [show L24Gluing.term (52 : Fin 815) = L24Gluing.term52 from rfl]
    unfold L24Gluing.term52 L24Gluing.expression13
    have h := outer_fork_zero X v terminal delta hd
      (GetzlerGraphs.join (m := 2) (n := 1) 2 0
        (fundamental 0 (Fin 3) (by norm_num [StableArity]))
        (fundamental 2 (Fin 2) (by norm_num [StableArity])))
      (![0, 0, 0], ![1, 0])
      ((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 2)))
      (by simp only [GetzlerGraphs.join, GluingExpression.maxComponentGenus,
        max_eq_right (show (0 : ℕ) ≤ 2 by decide)])
      (Equiv.refl _) n i (labels X i) rfl rfl
    simpa only [remainderPointCoefficient, GluingExpression.maxComponentGenus,
      remainderContraction, Equiv.refl_apply, Function.comp_def] using h
  · rw [show L24Gluing.term (62 : Fin 815) = L24Gluing.term62 from rfl]
    unfold L24Gluing.term62 L24Gluing.expression17
    exact outer_fork_zero X v terminal delta hd _ _ _
      (by simp only [GetzlerGraphs.join, GluingExpression.maxComponentGenus,
        max_eq_right (show (0 : ℕ) ≤ 2 by decide)])
      _ n i (labels X i) rfl rfl
  · rw [show L24Gluing.term (69 : Fin 815) = L24Gluing.term69 from rfl]
    unfold L24Gluing.term69 L24Gluing.expression21
    exact outer_fork_zero X v terminal delta hd _ _ _
      (by simp only [GetzlerGraphs.join, GluingExpression.maxComponentGenus,
        max_eq_right (show (0 : ℕ) ≤ 2 by decide)])
      _ n i (labels X i) rfl rfl

private theorem discardedFrame_coefficient_zero (X : SurfaceTarget) (v : Variable X)
    (terminal : SurfaceVertexValues X ℚ) (delta : X.Curve)
    (hd : X.planeDegree delta = 0) (n : ℕ) (i : Fin X.blowups) :
    ∀ j ∈ SurfaceGenusTwoBlowupHUniform.genusTwoFrame \ survivingFrame,
    remainderPointCoefficient X v terminal (L24Gluing.term j) delta n (labels X i) = 0 := by
  have hp : SurfaceGenusTwoBlowupHUniform.genusTwoFrame \ survivingFrame =
      SurfaceGenusTwoBlowupHUniform.primaryFrame ∪ externalExceptionalFrame ∪
        rationalHyperplaneExceptionalFrame ∪ SurfaceGenusTwoBlowupHUniform.oneMarkingFrame :=
    by decide +kernel
  intro j hj
  rw [hp] at hj
  simp only [Finset.mem_union] at hj
  rcases hj with ((hj | hj) | hj) | hj
  · exact primaryFrame_coefficient_zero_of_planeDegree_zero X v terminal delta hd n i j hj
  · exact externalExceptionalFrame_coefficient_zero_of_planeDegree_zero X v terminal delta hd n
      i j hj
  · exact rationalHyperplaneExceptionalFrame_coefficient_zero X v terminal delta hd n i j hj
  · exact oneMarkingFrame_coefficient_zero_of_planeDegree_zero X v terminal delta hd n i j hj

/-- At any full effective remainder of plane degree zero, the original normalized L24
coefficient is exactly the two original weighted terms 57 and 64. No point-budget or
positive-energy premise is needed. -/
theorem pointCoefficient_eq_surviving_of_planeDegree_zero (X : SurfaceTarget)
    (v : Variable X) (delta : X.Curve) (hd : X.planeDegree delta = 0) (n : ℕ)
    (i : Fin X.blowups) :
    L24Relation.pointCoefficient X n (SurfaceGenusZero.variableCurve v + delta) (labels X i) v =
        ∑ j ∈ survivingFrame, L24CorrectionsReplay.fullClaim j *
        remainderPointCoefficient X v (coefficientVertex X v) (L24Gluing.term j)
          delta n (labels X i) := by
  unfold L24Relation.pointCoefficient L24Relation.cotangentRelation
  simp only [Multiset.map_map, Function.comp_def, ← Finset.sum_eq_multiset_sum]
  trans ∑ j ∈ SurfaceGenusTwoBlowupHUniform.genusTwoFrame,
    L24CorrectionsReplay.fullClaim j *
      remainderPointCoefficient X v (coefficientVertex X v) (L24Gluing.term j) delta n (labels X i)
  · symm
    trans ∑ j ∈ SurfaceGenusTwoBlowupHUniform.genusTwoFrame,
      L24CorrectionsReplay.fullClaim j *
        SurfaceGenusTwo.pointCoefficient X v (L24Gluing.term j)
          (SurfaceGenusZero.variableCurve v + delta) n (labels X i)
    · apply Finset.sum_congr rfl
      intro j _
      rw [remainderPointCoefficient_eq X v (coefficientVertex X v) rfl]
    · apply Finset.sum_subset
      · intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
          ((SurfaceGenusTwoBlowupHUniform.genusTwoFrame_checked j).mp hj).1⟩
      · intro j hj hnot
        have hne : (L24Gluing.term j).expression.maxComponentGenus ≠ 2 := by
          intro he
          exact hnot ((SurfaceGenusTwoBlowupHUniform.genusTwoFrame_checked j).mpr
            ⟨(Finset.mem_filter.mp hj).2, he⟩)
        rw [SurfaceGenusTwo.pointCoefficient, if_neg hne, mul_zero]
  · symm
    apply Finset.sum_subset (by decide +kernel : survivingFrame ⊆
        SurfaceGenusTwoBlowupHUniform.genusTwoFrame)
    intro j hj hnot
    rw [discardedFrame_coefficient_zero X v (coefficientVertex X v) delta hd n i j
      (Finset.mem_sdiff.mpr ⟨hj, hnot⟩), mul_zero]

private theorem surviving_chain_first_other_zero (X : SurfaceTarget) (gamma delta : X.Curve)
    (requested : SurfaceBasisLabel X) (count n : ℕ) (hrq : requested ≠ .hyperplane)
    (i : Fin X.blowups) :
    let v : Variable X := .inr (SurfaceFirstDescendant.query 2 gamma requested count)
    remainderPointCoefficient X v (coefficientVertex X v)
      (⟨GetzlerGraphs.join (m := 3) (n := 1) 3 1
          (GetzlerGraphs.join (m := 2) (n := 2) 2 1
            (fundamental 0 (Fin 3) (by norm_num [StableArity]))
            (fundamental 0 (Fin 3) (by norm_num [StableArity])))
          (fundamental 2 (Fin 2) (by norm_num [StableArity])),
        (((0 : Fin 3 → ℕ), (0 : Fin 3 → ℕ)), ![1, 0]),
        (((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 3))),
          (inferInstance : DecidableEq (Fin 2)))⟩ : CotangentTerm 2 (Fin 4))
      delta n ![.exceptional i, .exceptional i, .exceptional i, .hyperplane] = 0 := by
  let v : Variable X := .inr (SurfaceFirstDescendant.query 2 gamma requested count)
  let a : Fin 4 → SurfaceBasisLabel X := ![.exceptional i, .exceptional i, .exceptional i,
      .hyperplane]
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4)) ∘ Sum.inr)) ∘
        finSuccEquiv' 1 = ![.hyperplane, b] := by ext j; fin_cases j <;> rfl
  have hz : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by ext j; fin_cases j <;> rfl
  dsimp only
  change remainderPointCoefficient X v (coefficientVertex X v) _ delta n a = 0
  simp only [GetzlerGraphs.join, GluingExpression.maxComponentGenus, Nat.zero_add, max_self,
    max_eq_right (show (0 : ℕ) ≤ 2 by decide), remainderPointCoefficient, ite_true,
    remainderContraction, if_neg (show (0 : ℕ) ≠ 2 by decide), hz, hr]
  apply Finset.sum_eq_zero
  intro split _
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [main_hyperplane_first_other_zero X gamma split.2 requested count ij.2 hrq b.dual]
  simp only [mul_zero]

private theorem survivingFrame_primary_zero (X : SurfaceTarget) (gamma delta : X.Curve) (k n :
    ℕ) (hd : X.planeDegree delta = 0)
    (i : Fin X.blowups) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 gamma k)
    ∀ j ∈ survivingFrame, remainderPointCoefficient X v (coefficientVertex X v)
      (L24Gluing.term j) delta n (labels X i) = 0 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 gamma k)
  have hz : (![0, 0, 0] : Fin 3 → ℕ) = 0 := by ext j; fin_cases j <;> rfl
  dsimp only
  intro j hj
  simp only [survivingFrame, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · rw [show L24Gluing.term (57 : Fin 815) = L24Gluing.term57 from rfl]
    unfold L24Gluing.term57 L24Gluing.expression15
    rw [hz]
    have ha : labels X i ∘ L24Gluing.flagPermutation9 = ![.exceptional i, .exceptional i,
        .exceptional i, .hyperplane] := by
      ext j
      fin_cases j <;> rfl
    have hh := surviving_chain_primary_zero X gamma delta k n hd i
    simp only [remainderPointCoefficient, GluingExpression.maxComponentGenus,
      remainderContraction, ha] at hh ⊢
    exact hh
  · rw [show L24Gluing.term (64 : Fin 815) = L24Gluing.term64 from rfl]
    unfold L24Gluing.term64 L24Gluing.expression19
    rw [hz]
    have ha : labels X i ∘ L24Gluing.flagPermutation3 = ![.exceptional i, .exceptional i,
        .exceptional i, .hyperplane] := by
      ext j
      fin_cases j <;> rfl
    have hh := surviving_chain_primary_zero X gamma delta k n hd i
    simp only [remainderPointCoefficient, GluingExpression.maxComponentGenus,
      remainderContraction, ha] at hh ⊢
    exact hh

private theorem survivingFrame_first_other_zero (X : SurfaceTarget) (gamma delta : X.Curve)
    (requested : SurfaceBasisLabel X) (count n : ℕ)
    (hrq : requested ≠ .hyperplane)
    (i : Fin X.blowups) :
    let v : Variable X := .inr (SurfaceFirstDescendant.query 2 gamma requested count)
    ∀ j ∈ survivingFrame, remainderPointCoefficient X v (coefficientVertex X v)
      (L24Gluing.term j) delta n (labels X i) = 0 := by
  let v : Variable X := .inr (SurfaceFirstDescendant.query 2 gamma requested count)
  have hz : (![0, 0, 0] : Fin 3 → ℕ) = 0 := by ext j; fin_cases j <;> rfl
  dsimp only
  intro j hj
  simp only [survivingFrame, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · rw [show L24Gluing.term (57 : Fin 815) = L24Gluing.term57 from rfl]
    unfold L24Gluing.term57 L24Gluing.expression15
    rw [hz]
    have ha : labels X i ∘ L24Gluing.flagPermutation9 = ![.exceptional i, .exceptional i,
        .exceptional i, .hyperplane] := by
      ext j
      fin_cases j <;> rfl
    have hh := surviving_chain_first_other_zero X gamma delta requested count n hrq i
    simp only [remainderPointCoefficient, GluingExpression.maxComponentGenus,
      remainderContraction, ha] at hh ⊢
    exact hh
  · rw [show L24Gluing.term (64 : Fin 815) = L24Gluing.term64 from rfl]
    unfold L24Gluing.term64 L24Gluing.expression19
    rw [hz]
    have ha : labels X i ∘ L24Gluing.flagPermutation3 = ![.exceptional i, .exceptional i,
        .exceptional i, .hyperplane] := by
      ext j
      fin_cases j <;> rfl
    have hh := surviving_chain_first_other_zero X gamma delta requested count n hrq i
    simp only [remainderPointCoefficient, GluingExpression.maxComponentGenus,
      remainderContraction, ha] at hh ⊢
    exact hh

/-- Every primary column vanishes in the complete normalized coefficient with labels H, Eᵢ, Eᵢ,
Eᵢ and a plane-degree-zero remainder. -/
theorem pointCoefficient_primary_eq_zero_of_planeDegree_zero (X : SurfaceTarget)
    (gamma delta : X.Curve) (hd : X.planeDegree delta = 0) (n k : ℕ) (i : Fin X.blowups) :
    L24Relation.pointCoefficient X n (gamma+delta) (labels X i)
      (.inr (SurfaceQuery.points X 2 gamma k)) = 0 := by
  have hh := pointCoefficient_eq_surviving_of_planeDegree_zero X
    (.inr (SurfaceQuery.points X 2 gamma k)) delta hd n i
  have hv : SurfaceGenusZero.variableCurve (.inr (SurfaceQuery.points X 2 gamma k)) = gamma := rfl
  rw [hv] at hh
  rw [hh]
  apply Finset.sum_eq_zero
  intro j hj
  rw [survivingFrame_primary_zero X gamma delta k n hd i j hj, mul_zero]

/-- Every first-descendant column with insertion different from H vanishes in the complete
normalized coefficient at a plane-degree-zero remainder. -/
theorem pointCoefficient_first_other_eq_zero_of_planeDegree_zero (X : SurfaceTarget)
    (gamma delta : X.Curve) (hd : X.planeDegree delta = 0)
    (requested : SurfaceBasisLabel X) (count n : ℕ) (hr : requested ≠ .hyperplane)
    (i : Fin X.blowups) :
    L24Relation.pointCoefficient X n (gamma+delta) (labels X i)
      (.inr (SurfaceFirstDescendant.query 2 gamma requested count)) = 0 := by
  have hh := pointCoefficient_eq_surviving_of_planeDegree_zero X
    (.inr (SurfaceFirstDescendant.query 2 gamma requested count)) delta hd n i
  have hv : SurfaceGenusZero.variableCurve
      (.inr (SurfaceFirstDescendant.query 2 gamma requested count)) = gamma := rfl
  rw [hv] at hh
  rw [hh]
  apply Finset.sum_eq_zero
  intro j hj
  rw [survivingFrame_first_other_zero X gamma delta requested count n hr i j hj, mul_zero]

/-- The complete shifted H row has no primary column at the target plane degree, for any full
class and any requested point count. -/
theorem primary_row_coefficient_eq_zero_of_same_planeDegree (X : SurfaceTarget)
    (i : Fin X.blowups) (beta gamma : X.Curve) (k : ℕ)
    (hd : X.planeDegree gamma = X.planeDegree beta) :
    RationalTerms.coefficient (row X i beta) {.inr (SurfaceQuery.points X 2 gamma k)} = 0 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 gamma k)
  by_cases hle : gamma ≤ sourceCurve X i beta
  · let delta := sourceCurve X i beta - gamma
    have hsplit : gamma+delta = sourceCurve X i beta := by
      funext j
      exact Nat.add_sub_of_le (hle j)
    have hdelta : X.planeDegree delta = 0 := by
      have hh := congrArg X.planeDegree hsplit
      rw [map_add, sourceCurve, map_add, X.planeDegree_exceptionalCurve i, add_zero, hd] at hh
      omega
    rw [row, ← L24Relation.pointCoefficient_eq_full, ← hsplit]
    exact pointCoefficient_primary_eq_zero_of_planeDegree_zero X gamma delta hdelta _ k i
  · have hb := L24Relation.genusTwoTerms_bound X (pointCount X beta) (sourceCurve X i beta)
      0 (SurfaceGenusZero.pointLabels (labels X i) (pointCount X beta))
    exact hb.normalized_coefficient_eq_zero_of_not_le le_rfl v hle

/-- The complete shifted H row has no first-descendant column other than H at the target plane
degree, for any full class and requested point count. -/
theorem first_other_row_coefficient_eq_zero_of_same_planeDegree (X : SurfaceTarget)
    (i : Fin X.blowups) (beta gamma : X.Curve) (requested : SurfaceBasisLabel X)
    (count : ℕ) (hr : requested ≠ .hyperplane)
    (hd : X.planeDegree gamma = X.planeDegree beta) :
    RationalTerms.coefficient (row X i beta)
      {.inr (SurfaceFirstDescendant.query 2 gamma requested count)} = 0 := by
  let v : Variable X := .inr (SurfaceFirstDescendant.query 2 gamma requested count)
  by_cases hle : gamma ≤ sourceCurve X i beta
  · let delta := sourceCurve X i beta - gamma
    have hsplit : gamma+delta = sourceCurve X i beta := by
      funext j
      exact Nat.add_sub_of_le (hle j)
    have hdelta : X.planeDegree delta = 0 := by
      have hh := congrArg X.planeDegree hsplit
      rw [map_add, sourceCurve, map_add, X.planeDegree_exceptionalCurve i, add_zero, hd] at hh
      omega
    rw [row, ← L24Relation.pointCoefficient_eq_full, ← hsplit]
    exact pointCoefficient_first_other_eq_zero_of_planeDegree_zero X gamma delta hdelta
      requested count _ hr i
  · have hb := L24Relation.genusTwoTerms_bound X (pointCount X beta) (sourceCurve X i beta)
      0 (SurfaceGenusZero.pointLabels (labels X i) (pointCount X beta))
    exact hb.normalized_coefficient_eq_zero_of_not_le le_rfl v hle

/-- At positive target energy, a nonzero canonical coefficient of the original shifted H row is
the exact requested H state or a strictly earlier state. The original full-row class bound
supplies the effective remainder. -/
theorem canonical_coefficient_support (X : SurfaceTarget) (i : Fin X.blowups)
    (beta gamma : X.Curve) (family : SurfaceGenusTwoBlowupOrder.Family X)
    (hbeta : 0 < X.effective.energy beta)
    (hc : RationalTerms.coefficient (row X i beta) {Sum.inr (family.query gamma)} ≠ 0) :
    (family = .hyperplane ∧ gamma = beta) ∨
      SurfaceGenusTwoBlowupOrder.Earlier X (gamma, family) (beta, .hyperplane) := by
  have hle : gamma ≤ sourceCurve X i beta := by
    by_contra hn
    have hb := L24Relation.genusTwoTerms_bound X (pointCount X beta) (sourceCurve X i beta)
      0 (SurfaceGenusZero.pointLabels (labels X i) (pointCount X beta))
    have hv : SurfaceGenusZero.variableCurve (.inr (family.query gamma)) = gamma := by
      cases family <;> rfl
    exact hc (hb.normalized_coefficient_eq_zero_of_not_le le_rfl
      (.inr (family.query gamma)) (by rwa [hv]))
  have hsplit : gamma + (sourceCurve X i beta - gamma) = beta + X.exceptionalCurve i := by
    funext j
    exact Nat.add_sub_of_le (hle j)
  have hdle := X.planeDegree_le_of_shifted_add_eq i hsplit
  cases family with
  | hyperplane =>
    rcases SurfaceGenusTwoBlowupHCoupling.hyperplane_coefficient_support X i beta gamma hbeta hc
      with he | he
    · exact Or.inl ⟨rfl, he⟩
    · exact Or.inr he
  | primary =>
    right
    apply SurfaceGenusTwoBlowupOrder.earlier_of_planeDegree_lt
    change X.planeDegree gamma < X.planeDegree beta
    by_contra hn
    have he : X.planeDegree gamma = X.planeDegree beta := by omega
    exact hc (primary_row_coefficient_eq_zero_of_same_planeDegree X i beta gamma _ he)
  | point =>
    right
    apply SurfaceGenusTwoBlowupOrder.earlier_of_planeDegree_lt
    change X.planeDegree gamma < X.planeDegree beta
    by_contra hn
    have he : X.planeDegree gamma = X.planeDegree beta := by omega
    exact hc (first_other_row_coefficient_eq_zero_of_same_planeDegree X i beta gamma .point _
      (by intro hz; cases hz) he)
  | exceptional j =>
    right
    apply SurfaceGenusTwoBlowupOrder.earlier_of_planeDegree_lt
    change X.planeDegree gamma < X.planeDegree beta
    by_contra hn
    have he : X.planeDegree gamma = X.planeDegree beta := by omega
    exact hc (first_other_row_coefficient_eq_zero_of_same_planeDegree X i beta gamma
        (.exceptional j) _
      (by intro hz; cases hz) he)
end AxiomaticGW.SurfaceGenusTwoBlowupHOtherFamilies

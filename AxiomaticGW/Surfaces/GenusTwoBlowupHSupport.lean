/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupHContributions

/-!
# Subcritical hyperplane support in the original L24 equation

The selected first-descendant H column at full class gamma requires
energy(gamma)-1 added points on its two-flag genus-two component. If the total
point budget is strictly smaller, the two surviving H chains vanish at every
effective remainder. The existing six primary, nine one-flag, and ten other
constructor vanishings then remove the exact original 27-term genus-two frame
when the remainder has plane degree zero.

This proves a coefficient identity for the complete original normalized L24
equation at arbitrary subcritical point count. Applied at zero remainder and
gamma equal to beta+Ei, it excludes the source-class H column of the shifted
row whenever beta has positive energy. The natural subtraction at energy zero
is retained; it does not provide the strict inequality used here.

No curve coordinates, relation weights, primary corrections, rational
complements, or calibration tails are replaced by a support assumption.
These results are one support gate; a decreasing full reconstruction recurrence
and termination are separate obligations.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupHSupport
open SurfacePolynomialReduction SurfaceGenusTwo SurfaceGenusTwoBlowupHPivots
  SurfaceGenusTwoBlowupHContributions SurfaceGenusTwoBlowupHUniform
  SurfaceGenusTwoBlowupHVanishing GluingExpression
-- The exact original held-term dispatch has 815 cases.
set_option maxRecDepth 20000

/-- The exact main factor is zero for every node state when it receives fewer
than energy(gamma)-1 points. Its full effective remainder is unrestricted. -/
theorem remainderVertex_hyperplane_pair_eq_zero_of_subcritical (X : SurfaceTarget)
    (gamma delta : X.Curve) (m : ℕ) (hm : m < X.effective.energy gamma - 1)
    (b : SurfaceBasisLabel X) :
    remainderVertex X (hColumn X gamma) (coefficientVertex X (hColumn X gamma)) m
      2 (Fin 2) (by norm_num [StableArity]) (Pi.single 0 1) inferInstance delta
      ![.hyperplane, b] = 0 := by
  rw [main_hyperplane_pair X gamma delta (X.effective.energy gamma - 1) m
    (by omega) (by omega) b, if_neg (fun h ↦ by omega)]

private theorem hyperplane_chain_subcritical_zero (X : SurfaceTarget)
    (gamma delta : X.Curve) (x : GluingExpression 0 (Fin 4))
    (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (e : Equiv.Perm (Fin 4)) (n : ℕ) (hn : n < X.effective.energy gamma - 1)
    (a : Fin 4 → SurfaceBasisLabel X) (ha : a (e 3) = .hyperplane) :
    remainderPointCoefficient X (hColumn X gamma) (coefficientVertex X (hColumn X gamma))
      (⟨(GetzlerGraphs.join (m := 3) (n := 1) 3 1 x
        (fundamental 2 (Fin 2) (by norm_num [StableArity]))).relabel e,
        (d, Pi.single (0 : Fin 2) 1), (l, (inferInstance : DecidableEq (Fin 2)))⟩ :
        CotangentTerm 2 (Fin 4)) delta n a = 0 := by
  have hx : x.maxComponentGenus = 0 := Nat.eq_zero_of_le_zero x.maxComponentGenus_le
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b (((a ∘ e) ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4)) ∘ Sum.inr)) ∘
        finSuccEquiv' 1 = ![a (e 3), b] := by
    funext k
    fin_cases k <;> rfl
  simp only [GetzlerGraphs.join, GluingExpression.maxComponentGenus, hx,
    max_eq_right (show (0 : ℕ) ≤ 2 by decide), remainderPointCoefficient,
    ite_true, remainderContraction, if_neg (show (0 : ℕ) ≠ 2 by decide)]
  apply Finset.sum_eq_zero
  intro split _
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij hij
  have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [hr, ha, remainderVertex_hyperplane_pair_eq_zero_of_subcritical X gamma split.2
    ij.2 (by omega) b.dual, mul_zero, mul_zero]

/-- Both actual held H chains vanish at every remainder for a strictly
subcritical total point budget; no rational component is evaluated. -/
theorem survivingFrame_coefficient_zero_of_subcritical (X : SurfaceTarget)
    (i : Fin X.blowups) (gamma delta : X.Curve)
    (n : ℕ) (hn : n < X.effective.energy gamma - 1) :
    ∀ j ∈ survivingFrame,
      remainderPointCoefficient X (hColumn X gamma) (coefficientVertex X (hColumn X gamma))
        (L24Gluing.term j) delta n (labels X i) = 0 := by
  have hd : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by
    funext k
    fin_cases k <;> rfl
  intro j hj
  simp only [survivingFrame, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · rw [show L24Gluing.term (57 : Fin 815) = L24Gluing.term57 from rfl]
    unfold L24Gluing.term57 L24Gluing.expression15
    rw [hd]
    exact hyperplane_chain_subcritical_zero X gamma delta _ _ _ _ n hn (labels X i) rfl
  · rw [show L24Gluing.term (64 : Fin 815) = L24Gluing.term64 from rfl]
    unfold L24Gluing.term64 L24Gluing.expression19
    rw [hd]
    exact hyperplane_chain_subcritical_zero X gamma delta _ _ _ _ n hn (labels X i) rfl

private theorem genusTwoFrame_partition :
    genusTwoFrame = ((primaryFrame ∪ oneMarkingFrame) ∪ vanishingFrame) ∪ survivingFrame :=
  by decide +kernel

/-- The exact 27-term genus-two frame vanishes at zero-plane-degree remainders
and strictly subcritical point budget, using its checked constructor partition. -/
theorem genusTwoFrame_coefficient_zero_of_subcritical (X : SurfaceTarget)
    (i : Fin X.blowups) (gamma delta : X.Curve) (hd : X.planeDegree delta = 0)
    (n : ℕ) (hn : n < X.effective.energy gamma - 1) :
    ∀ j ∈ genusTwoFrame,
      remainderPointCoefficient X (hColumn X gamma) (coefficientVertex X (hColumn X gamma))
        (L24Gluing.term j) delta n (labels X i) = 0 := by
  intro j hj
  rw [genusTwoFrame_partition] at hj
  rcases Finset.mem_union.mp hj with hj | hj
  · rcases Finset.mem_union.mp hj with hj | hj
    · rcases Finset.mem_union.mp hj with hj | hj
      · exact primaryFrame_coefficient_zero X gamma delta n (labels X i) j hj
      · exact oneMarkingFrame_coefficient_zero X gamma delta n (by omega) (labels X i) j hj
    · exact vanishingFrame_coefficient_zero X gamma delta hd n (by omega) i j hj
  · exact survivingFrame_coefficient_zero_of_subcritical X i gamma delta n hn j hj

/-- Original L24 point coefficient at arbitrary point count: below the physical
H budget, no H_gamma column survives a zero-plane-degree effective remainder. -/
theorem pointCoefficient_eq_zero_of_subcritical (X : SurfaceTarget)
    (i : Fin X.blowups) (gamma delta : X.Curve) (hd : X.planeDegree delta = 0)
    (n : ℕ) (hn : n < X.effective.energy gamma - 1) :
    L24Relation.pointCoefficient X n (gamma + delta) (labels X i) (hColumn X gamma) = 0 := by
  unfold L24Relation.pointCoefficient L24Relation.cotangentRelation
  simp only [Multiset.map_map, Function.comp_def, ← Finset.sum_eq_multiset_sum]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases he : (L24Gluing.term j).expression.maxComponentGenus = 2
  · have hj' : j ∈ genusTwoFrame :=
      (genusTwoFrame_checked j).mpr ⟨(Finset.mem_filter.mp hj).2, he⟩
    have hc := remainderPointCoefficient_eq X (hColumn X gamma)
      (coefficientVertex X (hColumn X gamma)) rfl (L24Gluing.term j) delta n (labels X i)
    have hv : SurfaceGenusZero.variableCurve (hColumn X gamma) = gamma := rfl
    rw [hv] at hc
    rw [← hc, genusTwoFrame_coefficient_zero_of_subcritical
      X i gamma delta hd n hn j hj', mul_zero]
  · rw [SurfaceGenusTwo.pointCoefficient, if_neg he, mul_zero]

/-- The subcritical vanishing is a coefficient of the complete original
normalized equation, retaining its constants and all other variables. -/
theorem normalizedCoefficient_eq_zero_of_subcritical (X : SurfaceTarget)
    (i : Fin X.blowups) (gamma delta : X.Curve) (hd : X.planeDegree delta = 0)
    (n : ℕ) (hn : n < X.effective.energy gamma - 1) :
    RationalTerms.coefficient
      (L24Relation.normalizedGenusTwoTerms X n (gamma + delta) 0
        (SurfaceGenusZero.pointLabels (labels X i) n)) {hColumn X gamma} = 0 := by
  rw [← L24Relation.pointCoefficient_eq_full,
    pointCoefficient_eq_zero_of_subcritical X i gamma delta hd n hn]

/-- The source-class H column in the shifted row has too few points when the
original target has positive energy. The requested full class is beta+Ei. -/
theorem source_column_pointCoefficient_eq_zero (X : SurfaceTarget)
    (i : Fin X.blowups) (beta : X.Curve) (hbeta : 0 < X.effective.energy beta) :
    L24Relation.pointCoefficient X (pointCount X beta) (sourceCurve X i beta)
      (labels X i) (hColumn X (sourceCurve X i beta)) = 0 := by
  have h := pointCoefficient_eq_zero_of_subcritical X i (sourceCurve X i beta) 0
    (map_zero _) (pointCount X beta) (by rw [sourceCurve_energy]; unfold pointCount; omega)
  simpa only [add_zero] using h

/-- The source-class vanishing binds to the complete original normalized
shifted row, with its positive-original-energy premise explicit. -/
theorem source_column_row_coefficient_eq_zero (X : SurfaceTarget)
    (i : Fin X.blowups) (beta : X.Curve) (hbeta : 0 < X.effective.energy beta) :
    RationalTerms.coefficient (row X i beta) {hColumn X (sourceCurve X i beta)} = 0 := by
  rw [row, ← L24Relation.pointCoefficient_eq_full,
    source_column_pointCoefficient_eq_zero X i beta hbeta]

end AxiomaticGW.SurfaceGenusTwoBlowupHSupport

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupHVanishing
public import AxiomaticGW.Surfaces.GenusTwoCanonicalQueries
public import AxiomaticGW.Surfaces.GenusTwoBlowupExceptionalComplement

/-!
# The surviving shifted hyperplane contributions

The exact twelve-term coefficient reduces to held L24 terms 57 and 64 at
zero-plane-degree remainders. Here their common graph is evaluated uniformly:
the genus-two first-descendant factor selects a point node, zero remaining
class, and every added point. The rational complement therefore receives the
entire effective remainder, a unit node, and no added points.

At the selected exceptional generator the complement is minus one, and each
original relation weight is one half. This proves the full normalized shifted-H
coefficient is minus one for every positive-energy effective target class.
The same exact contraction vanishes at a different exceptional generator.
All full curve classes, signed marking corrections, ordered splittings, and
inverse-metric signs are retained. No additional invariant seed is supplied.
These results establish a uniform pivot and this exceptional cross-column
family; they do not classify all other columns or prove a reconstruction
recurrence, decreasing support, or termination.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupHContributions
open SurfacePolynomialReduction SurfaceGenusTwo SurfaceGenusTwoBlowupHPivots
-- The actual held-term dispatch has 815 cases.
set_option maxRecDepth 20000

private theorem pair_dimension (X : SurfaceTarget) (beta : X.Curve)
    (m : ℕ) (b : SurfaceBasisLabel X) :
    SurfaceAncestorKey.DimensionCompatible
      ((SurfaceAncestorKey.ofLabels 2 (Fin 2) (by norm_num [StableArity]) beta
        (Pi.single 0 1) (![.hyperplane, b] : Fin 2 → SurfaceBasisLabel X)).addPoints m) ↔
      (m : ℤ) + b.codimension = (X.effective.energy beta : ℤ) + 1 := by
  have hs : (Finset.univ : Finset (Fin 2)).val = (0 ::ₘ {1} : Multiset (Fin 2)) := by decide +kernel
  simp only [SurfaceAncestorKey.DimensionCompatible, SurfaceAncestorKey.totalCodimension,
    SurfaceAncestorKey.addPoints, SurfaceAncestorKey.ofLabels, Multiset.map_add,
    Multiset.map_replicate, Multiset.sum_add, Multiset.sum_replicate,
    Multiset.card_add, Multiset.card_replicate, SurfaceTarget.c1Degree,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hs,
    Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton, Multiset.card_cons, Multiset.card_singleton,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.single_eq_same, Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide),
    SurfaceBasisLabel.codimension, add_zero]
  change (m : ℤ) * 2 + ((2 + b.codimension : ℕ) : ℤ) =
    (X.effective.energy beta : ℤ) + 2 - 1 + ((m : ℤ) + 2) ↔
    (m : ℤ) + b.codimension = (X.effective.energy beta : ℤ) + 1
  simp only [Nat.cast_add, Nat.cast_ofNat]
  omega

/-- The exact genus-two factor selects a primary point at its node, zero main
remainder, and the full physical point budget. Unit and divisor node states
fail the dimension check; signed primary tails cannot contribute to H. -/
theorem main_hyperplane_pair (X : SurfaceTarget) (beta delta : X.Curve)
    (n m : ℕ) (hm : m ≤ n) (he : X.effective.energy beta = n + 1)
    (b : SurfaceBasisLabel X) :
    remainderVertex X (hColumn X beta) (coefficientVertex X (hColumn X beta)) m
      2 (Fin 2) (by norm_num [StableArity]) (Pi.single 0 1) inferInstance delta
      ![.hyperplane, b] =
      if delta = 0 ∧ b = .point ∧ m = n then 1 else 0 := by
  have hv : ∀ gamma k, Sum.inr (SurfaceQuery.points X 2 gamma k) ≠ hColumn X beta :=
    fun gamma k ↦ SurfaceFirstDescendant.query_ne_points beta gamma .hyperplane
      (X.effective.energy beta) k
  rw [remainderVertex_onePsi_of_not_points (hColumn X beta) hv]
  by_cases hz : delta = 0
  · rw [if_pos hz, coefficient_residualTerms_onePsi_of_not_points (hColumn X beta) hv]
    simp only [hz, true_and]
    change (if SurfaceAncestorKey.DimensionCompatible
        ((SurfaceAncestorKey.ofLabels 2 (Fin 2) (by norm_num [StableArity]) beta
          (Pi.single 0 1) (![.hyperplane, b] : Fin 2 → SurfaceBasisLabel X)).addPoints m) then
        RationalTerms.coefficient (RationalTerms.rename Sum.inr
          (SurfaceFirstDescendant.terms 2 beta .hyperplane (Multiset.replicate m .point +
            (Finset.univ.erase (0 : Fin 2)).val.map
              (![.hyperplane, b] : Fin 2 → SurfaceBasisLabel X)))) {hColumn X beta}
      else 0) = if b = .point ∧ m = n then 1 else 0
    have hset : (Finset.univ.erase (0 : Fin 2)).val.map
        (![.hyperplane, b] : Fin 2 → SurfaceBasisLabel X) = {b} := rfl
    rw [hset]
    cases b with
    | unit | hyperplane | exceptional i =>
      rw [if_neg]
      · simp only [reduceCtorEq, false_and, ite_false]
      · rw [pair_dimension]
        simp only [SurfaceBasisLabel.codimension]
        omega
    | point =>
      have hd : SurfaceAncestorKey.DimensionCompatible
          ((SurfaceAncestorKey.ofLabels 2 (Fin 2) (by norm_num [StableArity]) beta
            (Pi.single 0 1) (![.hyperplane, .point] : Fin 2 → SurfaceBasisLabel X)).addPoints m) ↔
          m = n := by
        rw [pair_dimension]
        simp only [SurfaceBasisLabel.codimension]
        omega
      simp only [true_and]
      by_cases hmn : m = n
      · rw [if_pos (hd.mpr hmn), if_pos hmn]
        subst m
        have hu : SurfaceBasisLabel.unit ∉
            (Multiset.replicate n .point + {.point} : Multiset (SurfaceBasisLabel X)) := by
          simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton,
            reduceCtorEq, and_false, or_self, not_false_eq_true]
        have hq :
            (SurfaceFirstDescendant.query 2 beta .hyperplane (n + 1)).DimensionCompatible := by
          rw [SurfaceQuery.dimensionCompatible_first, he]
          rfl
        rw [SurfaceFirstDescendant.terms, if_neg hu,
          if_neg (show (SurfaceBasisLabel.hyperplane : SurfaceBasisLabel X) ≠ .unit from by
            intro heq; cases heq), RationalTerms.coefficient_rename_add,
          RationalTerms.coefficient_rename_scale, RationalTerms.coefficient_rename_scale]
        simp only [SurfaceFirstDescendant.primaryCoefficient,
          Multiset.map_add, Multiset.map_replicate, Multiset.map_singleton,
          Multiset.prod_add, Multiset.prod_replicate, Multiset.prod_singleton,
          SurfaceBasisLabel.primaryFactor, one_pow, one_mul,
          SurfaceFirstDescendant.correctionCoefficient, SurfaceFirstDescendant.divisorSquare,
          Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton,
          reduceCtorEq, ite_false, ite_true, add_zero, Nat.cast_zero, mul_zero, zero_mul]
        rw [SurfaceFirstDescendant.dimensionTerms, if_pos hq,
          RationalTerms.coefficient_rename_term]
        simp only [Multiset.map_singleton, Multiset.singleton_inj]
        rw [hColumn, he, if_pos rfl]
      · rw [if_neg (fun h ↦ hmn (hd.mp h)), if_neg hmn]
  · rw [if_neg hz, if_neg (fun h ↦ hz h.1)]

/-- With the selected main factor, any rational four-flag complement receives
the entire effective remainder and a unit node, with no added points. -/
theorem common_join_eq_pair (X : SurfaceTarget) (i : Fin X.blowups)
    (beta delta : X.Curve) (n : ℕ) (he : X.effective.energy beta = n + 1)
    (x : GluingExpression 0 (Fin 4)) (d : x.CotangentDecoration)
    (l : x.DecidableLabels) :
    remainderPointCoefficient X (hColumn X beta) (coefficientVertex X (hColumn X beta))
      (⟨GetzlerGraphs.join (m := 3) (n := 1) 3 1 x
          (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity])),
        (d, ![1, 0]), (l, (inferInstance : DecidableEq (Fin 2)))⟩ :
          GluingExpression.CotangentTerm 2 (Fin 4))
      delta n ![.exceptional i, .exceptional i, .exceptional i, .hyperplane] =
    x.pointContraction X (primaryPointVertex X (hColumn X beta)) d l
      delta 0 ![.exceptional i, .exceptional i, .exceptional i, .unit] := by
  have hx : x.maxComponentGenus = 0 := Nat.eq_zero_of_le_zero x.maxComponentGenus_le
  have hd : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by
    ext j
    fin_cases j <;> rfl
  let a : Fin 4 → SurfaceBasisLabel X :=
    ![.exceptional i, .exceptional i, .exceptional i, .hyperplane]
  have hl (b : SurfaceBasisLabel X) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4)) ∘ Sum.inl)) ∘
        finSuccEquiv' 3 = ![.exceptional i, .exceptional i, .exceptional i, b] := by
    funext k
    fin_cases k <;> rfl
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4)) ∘ Sum.inr)) ∘
        finSuccEquiv' 1 = ![.hyperplane, b] := by
    funext k
    fin_cases k <;> rfl
  simp only [GetzlerGraphs.join, GluingExpression.maxComponentGenus, hx,
    max_eq_right (show (0 : ℕ) ≤ 2 by decide), remainderPointCoefficient,
    ite_true, remainderContraction, if_neg (show (0 : ℕ) ≠ 2 by decide), hd]
  have hmem : (delta, 0) ∈ X.splittings delta := by
    rw [X.splittings_eq, X.effective.mem_splittings, add_zero]
  rw [Finset.sum_eq_single_of_mem (delta, 0) hmem]
  · rw [Finset.sum_eq_single_of_mem .unit
      (Finset.mem_univ (SurfaceBasisLabel.unit : SurfaceBasisLabel X))]
    · simp only [SurfaceBasisLabel.inverseWeight, SurfaceBasisLabel.dual, one_mul]
      have hij : (0, n) ∈ Finset.HasAntidiagonal.antidiagonal n := by
        rw [Finset.HasAntidiagonal.mem_antidiagonal]
        exact zero_add n
      rw [Finset.sum_eq_single_of_mem (0, n) hij]
      · rw [GluingExpression.pointContraction, hl, hr,
          main_hyperplane_pair X beta 0 n n le_rfl he .point,
          if_pos ⟨rfl, rfl, rfl⟩]
        simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, mul_one]
      · intro ij hij hne
        have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
        have hm : ij.2 ≠ n := by
          intro hz
          apply hne
          apply Prod.ext
          · omega
          · exact hz
        rw [hr, main_hyperplane_pair X beta 0 n ij.2 (by omega) he .point,
          if_neg (fun h ↦ hm h.2.2), mul_zero, mul_zero]
    · intro b _ hb
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro ij hij
      have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      have hd : b.dual ≠ .point := by
        intro h
        apply hb
        have h' := congrArg SurfaceBasisLabel.dual h
        rw [SurfaceBasisLabel.dual_dual] at h'
        exact h'
      rw [hr, main_hyperplane_pair X beta 0 n ij.2 (by omega) he b.dual,
        if_neg (fun h ↦ hd h.2.1), mul_zero, mul_zero]
  · intro split hs hne
    apply Finset.sum_eq_zero
    intro b _
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro ij hij
    have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hsz : split.2 ≠ 0 := by
      intro hzero
      apply hne
      apply Prod.ext
      · have hsplit := (X.effective.mem_splittings split.1 split.2 delta).mp
          ((X.splittings_eq delta).symm ▸ hs)
        simpa only [hzero, add_zero] using hsplit
      · exact hzero
    rw [hr, main_hyperplane_pair X beta split.2 n ij.2 (by omega) he b.dual,
      if_neg (fun h ↦ hsz h.1), mul_zero, mul_zero]

private theorem remainderPointCoefficient_relabel {X : SurfaceTarget}
    (v : SurfacePolynomialReduction.Variable X) (terminal : SurfaceVertexValues X ℚ)
    {S T : Type} [Fintype S] [Fintype T] (z : GluingExpression.CotangentTerm 2 S)
    (e : S ≃ T) (delta : X.Curve) (n : ℕ) (a : T → SurfaceBasisLabel X) :
    remainderPointCoefficient X v terminal (z.relabel e) delta n a =
      remainderPointCoefficient X v terminal z delta n (a ∘ e) := by
  simp only [remainderPointCoefficient, GluingExpression.CotangentTerm.relabel,
    GluingExpression.maxComponentGenus, remainderContraction]

/-- Actual held term 57, including its flag transport, reduces to the complete
rational pair at an arbitrary full effective remainder. -/
theorem term57_eq_pair (X : SurfaceTarget) (i : Fin X.blowups)
    (beta delta : X.Curve) (n : ℕ) (he : X.effective.energy beta = n + 1) :
    remainderPointCoefficient X (hColumn X beta) (coefficientVertex X (hColumn X beta))
      (L24Gluing.term (57 : Fin 815)) delta n (labels X i) =
    (GetzlerGraphs.join (m := 2) (n := 2) 2 1
      (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
      (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))).pointContraction X
      (primaryPointVertex X (hColumn X beta)) (![0, 0, 0], ![0, 0, 0])
      ((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 3)))
      delta 0 ![.exceptional i, .exceptional i, .exceptional i, .unit] := by
  have ht : L24Gluing.term (57 : Fin 815) =
      L24Gluing.term95.relabel L24Gluing.flagPermutation9 := rfl
  have ha : labels X i ∘ L24Gluing.flagPermutation9 =
      ![.exceptional i, .exceptional i, .exceptional i, .hyperplane] := by
    funext k
    fin_cases k <;> rfl
  rw [ht, remainderPointCoefficient_relabel, ha]
  exact common_join_eq_pair X i beta delta n he _ _ _

/-- Actual held term 64 has the same rational pair after its distinct flag
transport; its original constructor and cotangent powers are retained. -/
theorem term64_eq_pair (X : SurfaceTarget) (i : Fin X.blowups)
    (beta delta : X.Curve) (n : ℕ) (he : X.effective.energy beta = n + 1) :
    remainderPointCoefficient X (hColumn X beta) (coefficientVertex X (hColumn X beta))
      (L24Gluing.term (64 : Fin 815)) delta n (labels X i) =
    (GetzlerGraphs.join (m := 2) (n := 2) 2 1
      (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
      (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))).pointContraction X
      (primaryPointVertex X (hColumn X beta)) (![0, 0, 0], ![0, 0, 0])
      ((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 3)))
      delta 0 ![.exceptional i, .exceptional i, .exceptional i, .unit] := by
  have ht : L24Gluing.term (64 : Fin 815) =
      L24Gluing.term95.relabel L24Gluing.flagPermutation3 := rfl
  have ha : labels X i ∘ L24Gluing.flagPermutation3 =
      ![.exceptional i, .exceptional i, .exceptional i, .hyperplane] := by
    funext k
    fin_cases k <;> rfl
  rw [ht, remainderPointCoefficient_relabel, ha]
  exact common_join_eq_pair X i beta delta n he _ _ _

private theorem term57_weight : L24CorrectionsReplay.fullClaim (57 : Fin 815) = 1/2 :=
  by decide +kernel
private theorem term64_weight : L24CorrectionsReplay.fullClaim (64 : Fin 815) = 1/2 :=
  by decide +kernel

/-- The original weight of held term 57 gives minus one half precisely at
the exceptional generator selected by the three external exceptional states. -/
theorem term57_contribution_at_generator (X : SurfaceTarget) (i j : Fin X.blowups)
    (beta : X.Curve) (hbeta : 0 < X.effective.energy beta) :
    L24CorrectionsReplay.fullClaim (57 : Fin 815) *
      remainderPointCoefficient X (hColumn X beta)
        (firstCoefficientVertex X beta .hyperplane (X.effective.energy beta))
        (L24Gluing.term (57 : Fin 815)) (X.exceptionalCurve j) (pointCount X beta)
        (labels X i) = if i = j then -1/2 else 0 := by
  rw [firstCoefficientVertex_eq]
  change L24CorrectionsReplay.fullClaim (57 : Fin 815) *
    remainderPointCoefficient X (hColumn X beta) (coefficientVertex X (hColumn X beta))
      (L24Gluing.term (57 : Fin 815)) (X.exceptionalCurve j) (pointCount X beta)
      (labels X i) = _
  rw [term57_eq_pair X i beta (X.exceptionalCurve j) (pointCount X beta)
      (by unfold pointCount; omega),
    SurfaceGenusTwoBlowupExceptionalComplement.exceptional_pair_primary_at_generator,
    term57_weight]
  split_ifs <;> norm_num

/-- The original weight of held term 64 gives the second minus one half,
and vanishes at every other exceptional generator. -/
theorem term64_contribution_at_generator (X : SurfaceTarget) (i j : Fin X.blowups)
    (beta : X.Curve) (hbeta : 0 < X.effective.energy beta) :
    L24CorrectionsReplay.fullClaim (64 : Fin 815) *
      remainderPointCoefficient X (hColumn X beta)
        (firstCoefficientVertex X beta .hyperplane (X.effective.energy beta))
        (L24Gluing.term (64 : Fin 815)) (X.exceptionalCurve j) (pointCount X beta)
        (labels X i) = if i = j then -1/2 else 0 := by
  rw [firstCoefficientVertex_eq]
  change L24CorrectionsReplay.fullClaim (64 : Fin 815) *
    remainderPointCoefficient X (hColumn X beta) (coefficientVertex X (hColumn X beta))
      (L24Gluing.term (64 : Fin 815)) (X.exceptionalCurve j) (pointCount X beta)
      (labels X i) = _
  rw [term64_eq_pair X i beta (X.exceptionalCurve j) (pointCount X beta)
      (by unfold pointCount; omega),
    SurfaceGenusTwoBlowupExceptionalComplement.exceptional_pair_primary_at_generator,
    term64_weight]
  split_ifs <;> norm_num

/-- The exact two surviving contributions have diagonal value minus one
and retain distinct exceptional classes with cross value zero. -/
theorem survivingCoefficient_at_generator (X : SurfaceTarget) (i j : Fin X.blowups)
    (beta : X.Curve) (hbeta : 0 < X.effective.energy beta) :
    SurfaceGenusTwoBlowupHVanishing.survivingCoefficient X i beta (X.exceptionalCurve j) =
      if i = j then -1 else 0 := by
  unfold SurfaceGenusTwoBlowupHVanishing.survivingCoefficient
    SurfaceGenusTwoBlowupHVanishing.survivingFrame
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    term57_contribution_at_generator X i j beta hbeta,
    term64_contribution_at_generator X i j beta hbeta]
  split_ifs <;> norm_num

/-- Binding the two contributions to the original L24 equation proves the
diagonal and cross-generator identities for every positive-energy full class. -/
theorem pointCoefficient_at_exceptional_generator (X : SurfaceTarget)
    (i j : Fin X.blowups) (beta : X.Curve) (hbeta : 0 < X.effective.energy beta) :
    L24Relation.pointCoefficient X (pointCount X beta) (beta + X.exceptionalCurve j)
      (labels X i) (hColumn X beta) = if i = j then -1 else 0 := by
  rw [SurfaceGenusTwoBlowupHVanishing.pointCoefficient_eq_surviving_of_planeDegree_zero
    X i beta (X.exceptionalCurve j) hbeta (X.planeDegree_exceptionalCurve j),
    survivingCoefficient_at_generator X i j beta hbeta]

/-- The complete shifted L24 coefficient is a uniform nonzero H pivot on
the full effective monoid at positive target energy. -/
theorem coefficient_eq_neg_one (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) (hbeta : 0 < X.effective.energy beta) :
    coefficient X i beta = -1 := by
  unfold coefficient sourceCurve
  rw [pointCoefficient_at_exceptional_generator X i i beta hbeta, if_pos rfl]

/-- The uniform pivot is the coefficient of the complete original normalized
equation, including all its constants and other variables. -/
theorem row_coefficient_eq_neg_one (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) (hbeta : 0 < X.effective.energy beta) :
    RationalTerms.coefficient (row X i beta) {hColumn X beta} = -1 := by
  rw [← coefficient_eq_full, coefficient_eq_neg_one X i beta hbeta]

end AxiomaticGW.SurfaceGenusTwoBlowupHContributions

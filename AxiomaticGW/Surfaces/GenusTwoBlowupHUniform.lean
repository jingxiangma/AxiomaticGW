/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupHPivots
public import AxiomaticGW.Surfaces.GenusTwoFirstCoefficients

/-!
# The exact exceptional-remainder form of the shifted hyperplane coefficient

The complete L24 relation has 27 nonzero terms containing a genus-two component.
Their held indices are checked in the kernel. Every other coefficient vanishes
because its graph has no genus-two component; none of its numerical constants
is evaluated or discarded from the original equation.

Fixing the requested full curve class translates the graph's splitting sums to
an explicit effective remainder. This gives a uniform 27-term formula for the
shifted hyperplane coefficient at every effective class, including class zero.
The six primary-main terms have a uniformly zero coefficient, leaving an exact
21-term expression for the same full normalized coefficient.
At positive target energy, nine one-marking first-power terms also have zero
coefficient, giving an exact twelve-term formula. The unconditional 27- and
21-term formulas retain the zero-energy request unchanged.
At positive energy it is the dimension-compatible request of `BlowupHPivots`.
The formula retains all signed marking corrections, inverse-metric factors,
rational complements and normalization terms. The uniform value minus one,
cancellation of different full-class columns at the same plane degree and
energy, decreasing support for all other variables, and reconstruction
termination remain open.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupHUniform
open SurfacePolynomialReduction SurfaceGenusTwoBlowupHPivots SurfaceGenusTwo

set_option maxRecDepth 20000

/-- Held column indices of the nonzero L24 terms with a genus-two component. -/
def genusTwoFrame : Finset (Fin 815) :=
  {51, 52, 56, 57, 59, 62, 63, 64, 66, 69, 70, 74, 76, 81, 83, 88, 93, 95, 97,
    101, 105, 109, 110, 112, 113, 119, 120}

/-- The complete held frame, without inferring graph support from a source formula. -/
theorem genusTwoFrame_checked : ∀ j : Fin 815,
    j ∈ genusTwoFrame ↔ L24CorrectionsReplay.fullClaim j ≠ 0 ∧
      (L24Gluing.term j).expression.maxComponentGenus = 2 := by decide +kernel

/-- The original 721 nonzero terms contain precisely these 27 genus-two terms. -/
theorem genusTwoFrame_card : genusTwoFrame.card = 27 := by decide +kernel

/-- The exact hyperplane coefficient after distributing only an effective remainder.
The explicit remainder also permits inspection of different exceptional columns. -/
def remainderCoefficient (X : SurfaceTarget) (i : Fin X.blowups)
    (beta delta : X.Curve) : ℚ :=
  ∑ j ∈ genusTwoFrame, L24CorrectionsReplay.fullClaim j *
    SurfaceGenusTwo.remainderPointCoefficient X (hColumn X beta)
      (SurfaceGenusTwo.firstCoefficientVertex X beta .hyperplane (X.effective.energy beta))
      (L24Gluing.term j)
      delta (pointCount X beta) (labels X i)

/-- Finite frame pruning and remainder translation preserve the existing full
normalized coefficient, including every signed additional-marking correction. -/
theorem remainderCoefficient_eq (X : SurfaceTarget) (i : Fin X.blowups)
    (beta delta : X.Curve) :
    remainderCoefficient X i beta delta =
      L24Relation.pointCoefficient X (pointCount X beta) (beta + delta)
        (labels X i) (hColumn X beta) := by
  unfold remainderCoefficient L24Relation.pointCoefficient L24Relation.cotangentRelation
  simp only [Multiset.map_map, Function.comp_def, ← Finset.sum_eq_multiset_sum]
  trans ∑ j ∈ genusTwoFrame, L24CorrectionsReplay.fullClaim j *
    SurfaceGenusTwo.pointCoefficient X (hColumn X beta) (L24Gluing.term j)
      (beta + delta) (pointCount X beta) (labels X i)
  · apply Finset.sum_congr rfl
    intro j _
    congr 1
    rw [SurfaceGenusTwo.remainderPointCoefficient_eq X (hColumn X beta)
      (SurfaceGenusTwo.firstCoefficientVertex X beta .hyperplane (X.effective.energy beta))
      (SurfaceGenusTwo.firstCoefficientVertex_eq (X := X) beta .hyperplane
        (X.effective.energy beta))]
    rfl
  · apply Finset.sum_subset
    · intro j hj
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ j, ((genusTwoFrame_checked j).mp hj).1⟩
    · intro j hj hnot
      have hne : (L24Gluing.term j).expression.maxComponentGenus ≠ 2 := by
        intro he
        exact hnot ((genusTwoFrame_checked j).mpr ⟨(Finset.mem_filter.mp hj).2, he⟩)
      rw [SurfaceGenusTwo.pointCoefficient, if_neg hne, mul_zero]

/-- The shifted request distributes exactly the chosen exceptional curve. -/
theorem coefficient_eq_remainder (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) :
    coefficient X i beta = remainderCoefficient X i beta (X.exceptionalCurve i) :=
  (remainderCoefficient_eq X i beta (X.exceptionalCurve i)).symm

/-- The compact remainder expression is a coefficient of the complete original
normalized equation, whose constants and other columns are retained. -/
theorem row_coefficient_eq_remainder (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) :
    RationalTerms.coefficient (row X i beta) {hColumn X beta} =
      remainderCoefficient X i beta (X.exceptionalCurve i) :=
  (coefficient_eq_full X i beta).symm.trans (coefficient_eq_remainder X i beta)

private theorem primary_chain_zero (X : SurfaceTarget) (beta delta : X.Curve) (n : ℕ)
    (a : Fin 4 → SurfaceBasisLabel X) (e : Equiv.Perm (Fin 4)) :
    remainderPointCoefficient X (hColumn X beta)
      (coefficientVertex X (hColumn X beta)) (L24Gluing.term120.relabel e) delta n a = 0 := by
  have hv : ∀ gamma m, Sum.inr (SurfaceQuery.points X 2 gamma m) ≠ hColumn X beta := by
    intro gamma m
    exact SurfaceFirstDescendant.query_ne_points beta gamma .hyperplane
      (X.effective.energy beta) m
  have hz : (![0] : Fin 1 → ℕ) = 0 := by
    funext s
    fin_cases s
    rfl
  simp only [GluingExpression.CotangentTerm.relabel, L24Gluing.term120,
    L24Gluing.expression50, GetzlerGraphs.join, GluingExpression.maxComponentGenus,
    Nat.zero_add, max_self, max_eq_right (show (0 : ℕ) ≤ 2 by decide),
    remainderPointCoefficient, ite_true, if_neg (show (0 : ℕ) ≠ 2 by decide),
    remainderContraction, hz,
    remainderVertex_primary_eq_zero_of_not_points (hColumn X beta) hv,
    mul_zero, zero_mul, Finset.sum_const_zero]

private theorem remainderPointCoefficient_relabel {X : SurfaceTarget}
    (v : SurfacePolynomialReduction.Variable X) (terminal : SurfaceVertexValues X ℚ)
    {S T : Type} [Fintype S] [Fintype T] (z : GluingExpression.CotangentTerm 2 S)
    (e : S ≃ T) (delta : X.Curve) (n : ℕ) (a : T → SurfaceBasisLabel X) :
    remainderPointCoefficient X v terminal (z.relabel e) delta n a =
      remainderPointCoefficient X v terminal z delta n (a ∘ e) := by
  simp only [remainderPointCoefficient, GluingExpression.CotangentTerm.relabel,
    GluingExpression.maxComponentGenus, remainderContraction]

/-- The six held genus-two terms whose main component is primary. -/
def primaryFrame : Finset (Fin 815) := {109, 110, 112, 113, 119, 120}

/-- The six actual primary-main graphs vanish in the H coefficient at every
full class, remainder and added-point count. No rational constant is evaluated. -/
theorem primaryFrame_coefficient_zero (X : SurfaceTarget) (beta delta : X.Curve) (n : ℕ)
    (a : Fin 4 → SurfaceBasisLabel X) : ∀ j ∈ primaryFrame,
    remainderPointCoefficient X (hColumn X beta)
      (coefficientVertex X (hColumn X beta)) (L24Gluing.term j) delta n a = 0 := by
  intro j hj
  simp only [primaryFrame, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show L24Gluing.term (109 : Fin 815) = L24Gluing.term120.relabel
        L24Gluing.flagPermutation9 from rfl]
    exact primary_chain_zero X beta delta n a L24Gluing.flagPermutation9
  · rw [show L24Gluing.term (110 : Fin 815) = L24Gluing.term120.relabel
        L24Gluing.flagPermutation1 from rfl]
    exact primary_chain_zero X beta delta n a L24Gluing.flagPermutation1
  · rw [show L24Gluing.term (112 : Fin 815) = L24Gluing.term120.relabel
        L24Gluing.flagPermutation3 from rfl]
    exact primary_chain_zero X beta delta n a L24Gluing.flagPermutation3
  · rw [show L24Gluing.term (113 : Fin 815) = L24Gluing.term120.relabel
        L24Gluing.flagPermutation2 from rfl]
    exact primary_chain_zero X beta delta n a L24Gluing.flagPermutation2
  · rw [show L24Gluing.term (119 : Fin 815) = L24Gluing.term120.relabel
        L24Gluing.flagPermutation7 from rfl]
    exact primary_chain_zero X beta delta n a L24Gluing.flagPermutation7
  · rw [show L24Gluing.term (120 : Fin 815) = L24Gluing.term120 from rfl]
    have h := primary_chain_zero X beta delta n a (Equiv.refl _)
    simpa only [remainderPointCoefficient_relabel, Equiv.refl_apply,
      Function.comp_def] using h
/-- The genus-two terms left after the proved primary-main vanishing. -/
def firstPsiFrame : Finset (Fin 815) := genusTwoFrame \ primaryFrame

/-- This is an exact 21-term coefficient expression, rather than sampled support. -/
theorem firstPsiFrame_card : firstPsiFrame.card = 21 := by decide +kernel

private theorem genusTwoFrame_union : genusTwoFrame = firstPsiFrame ∪ primaryFrame :=
  by decide +kernel

private theorem firstPsiFrame_disjoint : Disjoint firstPsiFrame primaryFrame :=
  by decide +kernel

/-- Only the 21 nonprimary-main terms contribute to the selected H coefficient.
Their complete point pullbacks and rational complements remain unchanged. -/
def firstPsiCoefficient (X : SurfaceTarget) (i : Fin X.blowups)
    (beta delta : X.Curve) : ℚ :=
  ∑ j ∈ firstPsiFrame, L24CorrectionsReplay.fullClaim j *
    SurfaceGenusTwo.remainderPointCoefficient X (hColumn X beta)
      (SurfaceGenusTwo.firstCoefficientVertex X beta .hyperplane (X.effective.energy beta))
      (L24Gluing.term j) delta (pointCount X beta) (labels X i)

/-- Every removed term has a proved primary-main coefficient zero. The original
relation's coefficients and graph constructions are unchanged. -/
theorem remainderCoefficient_eq_firstPsi (X : SurfaceTarget) (i : Fin X.blowups)
    (beta delta : X.Curve) :
    remainderCoefficient X i beta delta = firstPsiCoefficient X i beta delta := by
  unfold remainderCoefficient firstPsiCoefficient
  rw [genusTwoFrame_union, Finset.sum_union firstPsiFrame_disjoint]
  have hz : (∑ j ∈ primaryFrame, L24CorrectionsReplay.fullClaim j *
      SurfaceGenusTwo.remainderPointCoefficient X (hColumn X beta)
        (SurfaceGenusTwo.firstCoefficientVertex X beta .hyperplane (X.effective.energy beta))
        (L24Gluing.term j) delta (pointCount X beta) (labels X i)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [SurfaceGenusTwo.firstCoefficientVertex_eq]
    have h := congrArg (L24CorrectionsReplay.fullClaim j * ·)
      (primaryFrame_coefficient_zero X beta delta (pointCount X beta) (labels X i) j hj)
    simpa only [hColumn, mul_zero] using h
  rw [hz, add_zero]

/-- The exact 21-term formula is the selected coefficient of the full normalized
shifted L24 equation, including at zero target energy. -/
theorem row_coefficient_eq_firstPsi (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) :
    RationalTerms.coefficient (row X i beta) {hColumn X beta} =
      firstPsiCoefficient X i beta (X.exceptionalCurve i) :=
  (row_coefficient_eq_remainder X i beta).trans
    (remainderCoefficient_eq_firstPsi X i beta (X.exceptionalCurve i))

private theorem oneMarking_dimension (X : SurfaceTarget) (beta : X.Curve)
    (m : ℕ) (b : SurfaceBasisLabel X) :
    SurfaceAncestorKey.DimensionCompatible
      ((SurfaceAncestorKey.ofLabels 2 (Fin 1) (by norm_num [StableArity]) beta
        (Pi.single 0 1) (fun _ ↦ b)).addPoints m) ↔
      (m : ℤ) + b.codimension = (X.effective.energy beta : ℤ) + 1 := by
  simp only [SurfaceAncestorKey.DimensionCompatible, SurfaceAncestorKey.totalCodimension,
    SurfaceAncestorKey.addPoints, SurfaceAncestorKey.ofLabels, Multiset.map_add,
    Multiset.map_replicate, Multiset.sum_add, Multiset.sum_replicate,
    Multiset.card_add, Multiset.card_replicate, Multiset.card_map, Finset.card_val,
    Finset.card_univ, Fintype.card_fin, SurfaceTarget.c1Degree,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  change (m : ℤ) * 2 + (b.codimension + 1) =
    (X.effective.energy beta : ℤ) + 2 - 1 + ((m : ℤ) + 1) ↔ _
  omega

private theorem point_query_ne_hColumn (X : SurfaceTarget) (beta : X.Curve) (m : ℕ) :
    (Sum.inr (SurfaceFirstDescendant.query 2 beta .point m) : Variable X) ≠
      hColumn X beta := by
  intro he
  have hl := congrArg (fun q : SurfaceQuery X ↦
      q.insertions.head?.map SurfaceInsertion.label) (Sum.inr.inj he)
  simp only [SurfaceFirstDescendant.query, List.head?_cons, Option.map_some,
    Option.some.injEq] at hl
  cases hl

/-- A genus-two main component with only its node marking cannot produce the H
request if it receives fewer points than the target energy. Every effective
remainder and every node state is retained. -/
theorem remainderVertex_oneMarking_eq_zero (X : SurfaceTarget) (beta delta : X.Curve)
    (m : ℕ) (hm : m < X.effective.energy beta) (b : SurfaceBasisLabel X) :
    remainderVertex X (hColumn X beta) (coefficientVertex X (hColumn X beta)) m
      2 (Fin 1) (by norm_num [StableArity]) (Pi.single 0 1) inferInstance delta
      (fun _ ↦ b) = 0 := by
  have hv : ∀ gamma n, Sum.inr (SurfaceQuery.points X 2 gamma n) ≠ hColumn X beta :=
    fun gamma n ↦ SurfaceFirstDescendant.query_ne_points beta gamma .hyperplane
      (X.effective.energy beta) n
  rw [remainderVertex_onePsi_of_not_points (hColumn X beta) hv]
  by_cases hz : delta = 0
  · rw [if_pos hz, coefficient_residualTerms_onePsi_of_not_points (hColumn X beta) hv]
    change (if SurfaceAncestorKey.DimensionCompatible
        ((SurfaceAncestorKey.ofLabels 2 (Fin 1) (by norm_num [StableArity]) beta
          (Pi.single 0 1) (fun _ ↦ b)).addPoints m) then
        RationalTerms.coefficient (RationalTerms.rename Sum.inr
          (SurfaceFirstDescendant.terms 2 beta b (Multiset.replicate m .point +
            (Finset.univ.erase (0 : Fin 1)).val.map (fun _ ↦ b)))) {hColumn X beta}
      else 0) = 0
    have he : (Finset.univ.erase (0 : Fin 1)).val = 0 := by decide +kernel
    simp only [he, Multiset.map_zero, add_zero]
    cases b with
    | unit | hyperplane | exceptional i =>
      rw [if_neg]
      rw [oneMarking_dimension]
      simp only [SurfaceBasisLabel.codimension]
      omega
    | point =>
      split_ifs with hd
      · have hu : SurfaceBasisLabel.unit ∉
          (Multiset.replicate m .point : Multiset (SurfaceBasisLabel X)) := by
          simp only [Multiset.mem_replicate, reduceCtorEq, and_false, not_false_eq_true]
        rw [SurfaceFirstDescendant.terms, if_neg hu,
          if_neg (show (SurfaceBasisLabel.point : SurfaceBasisLabel X) ≠ .unit by
            intro heq; cases heq), RationalTerms.coefficient_rename_add,
          RationalTerms.coefficient_rename_scale, RationalTerms.coefficient_rename_scale]
        simp only [SurfaceFirstDescendant.correctionCoefficient,
          SurfaceFirstDescendant.divisorSquare, zero_mul, add_zero]
        rw [SurfaceFirstDescendant.dimensionTerms]
        split_ifs with hp
        · rw [RationalTerms.coefficient_rename_term]
          simp only [Multiset.map_singleton, Multiset.singleton_inj,
            Multiset.count_replicate, ite_true, if_neg (point_query_ne_hColumn X beta m), mul_zero]
        · simp only [RationalTerms.rename_zero, RationalTerms.coefficient_zero, mul_zero]
      · rfl
  · rw [if_neg hz]

private theorem oneMarking_chain_zero (X : SurfaceTarget) (beta delta : X.Curve)
    (x : GluingExpression 0 (Fin 5)) (d : x.CotangentDecoration)
    (l : x.DecidableLabels) (e : Equiv.Perm (Fin 4))
    (n : ℕ) (hn : n < X.effective.energy beta) (a : Fin 4 → SurfaceBasisLabel X) :
    remainderPointCoefficient X (hColumn X beta) (coefficientVertex X (hColumn X beta))
      (⟨(GetzlerGraphs.join (m := 4) (n := 0) 4 0 x
        (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel e,
        (d, ![1]), (l, (inferInstance : DecidableEq (Fin 1)))⟩ :
        GluingExpression.CotangentTerm 2 (Fin 4))
      delta n a = 0 := by
  have hd : (![1] : Fin 1 → ℕ) = Pi.single 0 1 := by
    ext s
    fin_cases s
    rfl
  have hz (m : ℕ) (hm : m < X.effective.energy beta) (epsilon : X.Curve)
      (b : Fin 1 → SurfaceBasisLabel X) :
      remainderVertex X (hColumn X beta) (coefficientVertex X (hColumn X beta)) m
        2 (Fin 1) (by norm_num [StableArity]) (Pi.single 0 1) inferInstance epsilon b = 0 := by
    have hb : b = fun _ ↦ b 0 := by
      ext s
      fin_cases s
      rfl
    rw [hb]
    exact remainderVertex_oneMarking_eq_zero X beta epsilon m hm (b 0)
  have hx : x.maxComponentGenus = 0 := Nat.eq_zero_of_le_zero x.maxComponentGenus_le
  simp only [GetzlerGraphs.join,
    GluingExpression.maxComponentGenus, hx,
    max_eq_right (show (0 : ℕ) ≤ 2 by decide), remainderPointCoefficient,
    ite_true, remainderContraction, if_neg (show (0 : ℕ) ≠ 2 by decide), hd]
  apply Finset.sum_eq_zero
  intro split _
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij hij
  have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [hz ij.2 (by omega) split.2, mul_zero, mul_zero]

/-- The nine held first-power terms with a one-marking genus-two component. -/
def oneMarkingFrame : Finset (Fin 815) := {56, 63, 70, 74, 81, 88, 97, 101, 105}

/-- These actual nine source constructors have uniformly zero H coefficient
when the available added-point count is less than the target energy. -/
theorem oneMarkingFrame_coefficient_zero (X : SurfaceTarget) (beta delta : X.Curve)
    (n : ℕ) (hn : n < X.effective.energy beta) (a : Fin 4 → SurfaceBasisLabel X) :
    ∀ j ∈ oneMarkingFrame, remainderPointCoefficient X (hColumn X beta)
      (coefficientVertex X (hColumn X beta)) (L24Gluing.term j) delta n a = 0 := by
  intro j hj
  simp only [oneMarkingFrame, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show L24Gluing.term (56 : Fin 815) = L24Gluing.term56 from rfl]
    unfold L24Gluing.term56 L24Gluing.expression14
    exact oneMarking_chain_zero X beta delta _ _ _ _ n hn a
  · rw [show L24Gluing.term (63 : Fin 815) = L24Gluing.term63 from rfl]
    unfold L24Gluing.term63 L24Gluing.expression18
    exact oneMarking_chain_zero X beta delta _ _ _ _ n hn a
  · rw [show L24Gluing.term (70 : Fin 815) = L24Gluing.term70 from rfl]
    unfold L24Gluing.term70 L24Gluing.expression22
    exact oneMarking_chain_zero X beta delta _ _ _ _ n hn a
  · rw [show L24Gluing.term (74 : Fin 815) = L24Gluing.term74 from rfl]
    unfold L24Gluing.term74 L24Gluing.expression23
    exact oneMarking_chain_zero X beta delta _ _ _ _ n hn a
  · rw [show L24Gluing.term (81 : Fin 815) = L24Gluing.term81 from rfl]
    unfold L24Gluing.term81 L24Gluing.expression26
    exact oneMarking_chain_zero X beta delta _ _ _ _ n hn a
  · rw [show L24Gluing.term (88 : Fin 815) = L24Gluing.term88 from rfl]
    unfold L24Gluing.term88 L24Gluing.expression29
    exact oneMarking_chain_zero X beta delta _ _ _ _ n hn a
  · rw [show L24Gluing.term (97 : Fin 815) = L24Gluing.term97 from rfl]
    unfold L24Gluing.term97 L24Gluing.expression33
    have h := oneMarking_chain_zero X beta delta
      (GetzlerGraphs.join (m := 2) (n := 3) 2 2
        (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
        (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
      (![0, 0, 0], ![0, 0, 0, 0])
      ((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 4)))
      (Equiv.refl _) n hn a
    simpa only [remainderPointCoefficient, GluingExpression.maxComponentGenus,
      remainderContraction, Equiv.refl_apply, Function.comp_def] using h
  · rw [show L24Gluing.term (101 : Fin 815) = L24Gluing.term101 from rfl]
    unfold L24Gluing.term101 L24Gluing.expression34
    exact oneMarking_chain_zero X beta delta _ _ _ _ n hn a
  · rw [show L24Gluing.term (105 : Fin 815) = L24Gluing.term105 from rfl]
    unfold L24Gluing.term105 L24Gluing.expression35
    have h := oneMarking_chain_zero X beta delta
      (GetzlerGraphs.join (m := 3) (n := 2) 3 1
        (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
        (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (![0, 0, 0, 0], ![0, 0, 0])
      ((inferInstance : DecidableEq (Fin 4)), (inferInstance : DecidableEq (Fin 3)))
      (Equiv.refl _) n hn a
    simpa only [remainderPointCoefficient, GluingExpression.maxComponentGenus,
      remainderContraction, Equiv.refl_apply, Function.comp_def] using h

/-- Exact size of the kernel-checked one-marking held frame. -/
theorem oneMarkingFrame_card : oneMarkingFrame.card = 9 := by decide +kernel

/-- The actual one-marking frame lies in the previously verified first-power frame. -/
theorem oneMarkingFrame_subset : oneMarkingFrame ⊆ firstPsiFrame := by decide +kernel

/-- The first-power terms left after one-marking vanishing at positive target energy. -/
def twoMarkingFrame : Finset (Fin 815) := firstPsiFrame \ oneMarkingFrame

/-- The new positive-energy formula has exactly twelve original held terms. -/
theorem twoMarkingFrame_card : twoMarkingFrame.card = 12 := by decide +kernel

private theorem firstPsiFrame_partition :
    firstPsiFrame = twoMarkingFrame ∪ oneMarkingFrame := by decide +kernel

private theorem twoMarkingFrame_disjoint :
    Disjoint twoMarkingFrame oneMarkingFrame := by decide +kernel

/-- The twelve-term expression retains the original coefficients, point pullbacks
and effective remainder. Its equality to the row requires positive target energy. -/
def twoMarkingCoefficient (X : SurfaceTarget) (i : Fin X.blowups)
    (beta delta : X.Curve) : ℚ :=
  ∑ j ∈ twoMarkingFrame, L24CorrectionsReplay.fullClaim j *
    SurfaceGenusTwo.remainderPointCoefficient X (hColumn X beta)
      (SurfaceGenusTwo.firstCoefficientVertex X beta .hyperplane (X.effective.energy beta))
      (L24Gluing.term j) delta (pointCount X beta) (labels X i)

private theorem shifted_oneMarkingFrame_coefficient_zero (X : SurfaceTarget)
    (i : Fin X.blowups) (beta delta : X.Curve) (hbeta : 0 < X.effective.energy beta) :
    ∀ j ∈ oneMarkingFrame, L24CorrectionsReplay.fullClaim j *
      remainderPointCoefficient X (hColumn X beta)
        (firstCoefficientVertex X beta .hyperplane (X.effective.energy beta))
        (L24Gluing.term j) delta (pointCount X beta) (labels X i) = 0 := by
  intro j hj
  rw [firstCoefficientVertex_eq]
  change L24CorrectionsReplay.fullClaim j *
    remainderPointCoefficient X (hColumn X beta) (coefficientVertex X (hColumn X beta))
      (L24Gluing.term j) delta (pointCount X beta) (labels X i) = 0
  rw [oneMarkingFrame_coefficient_zero X beta delta (pointCount X beta)
    (by unfold pointCount; omega) (labels X i) j hj, mul_zero]

/-- Positive target energy justifies deleting the nine proved one-marking terms
for every effective remainder; the unconditional 21-term formula is unchanged. -/
theorem firstPsiCoefficient_eq_twoMarking_of_pos (X : SurfaceTarget) (i : Fin X.blowups)
    (beta delta : X.Curve) (hbeta : 0 < X.effective.energy beta) :
    firstPsiCoefficient X i beta delta = twoMarkingCoefficient X i beta delta := by
  unfold firstPsiCoefficient twoMarkingCoefficient
  rw [firstPsiFrame_partition, Finset.sum_union twoMarkingFrame_disjoint]
  have hz : (∑ j ∈ oneMarkingFrame, L24CorrectionsReplay.fullClaim j *
      SurfaceGenusTwo.remainderPointCoefficient X (hColumn X beta)
        (SurfaceGenusTwo.firstCoefficientVertex X beta .hyperplane (X.effective.energy beta))
        (L24Gluing.term j) delta (pointCount X beta) (labels X i)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact shifted_oneMarkingFrame_coefficient_zero X i beta delta hbeta j hj
  rw [hz, add_zero]

/-- At positive target energy, the twelve-term formula is the H coefficient
of the complete original shifted normalized equation. -/
theorem row_coefficient_eq_twoMarking_of_pos (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) (hbeta : 0 < X.effective.energy beta) :
    RationalTerms.coefficient (row X i beta) {hColumn X beta} =
      twoMarkingCoefficient X i beta (X.exceptionalCurve i) :=
  (row_coefficient_eq_firstPsi X i beta).trans
    (firstPsiCoefficient_eq_twoMarking_of_pos X i beta (X.exceptionalCurve i) hbeta)

end AxiomaticGW.SurfaceGenusTwoBlowupHUniform

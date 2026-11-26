/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoFirstCoefficients
public import AxiomaticGW.Surfaces.GenusTwoCoefficientRelations
public import AxiomaticGW.Surfaces.GenusTwoBlowupOrder

/-!
# Same-class first-descendant coefficients of the BP HHH row

For every fixed surface and full effective class `beta` of positive energy,
the complete normalized BP equation with three hyperplanes and
`energy(beta) - 1` extra labelled points has H coefficient eighteen and P
coefficient minus eighteen times `planeDegree(beta)`. Its same-class
exceptional first-descendant coefficients vanish. The raw constructor weights
thus give eighteen times `H_beta - d * P_beta`, corresponding to the rescaled
P equation in Wennink, arXiv:2210.04038, Section 8.3 (page 25).

The argument follows the actual first four BP diagrams and all six marking
assignments. At zero effective remainder, the classical two-hyperplane
rational triple contributes a point node, and receives none of the added
points. The remaining genus-two first-power terms are identified using the
generic coefficient normalization, including all signed cotangent and
calibration tails on the left. The original normalized polynomial, its
primary terms, constants and other curve classes are retained.

Positive energy supplies the exact dimension condition; class-zero natural
underflow does not satisfy it. Positive plane degree is needed only for the
nonzero point pivot. Pure exceptional classes have H coefficient eighteen
and P coefficient zero. No recurrence or numerical seed is assumed here.
The companion PPrimary, PSupport and PPrimarySupport modules prove primary N
vanishing at equal plane degree and canonical dependency bounds for the full
P row. A full reconstruction recurrence remains a separate obligation.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupPCoefficients
open SurfacePolynomialReduction SurfaceGenusTwo GluingExpression

set_option maxRecDepth 20000
variable {X : SurfaceTarget}

/-- The class-zero rational HH triple pairs only with a unit node and has no extra points. -/
theorem classical_hh (n : ℕ) (b : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) 0 n
      (![.hyperplane, .hyperplane, b] : Fin 3 → _) =
      if n = 0 ∧ b = .unit then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    cases b with
    | unit =>
      simp only [SurfaceGenusZero.primaryScalar, ne_eq, not_true_eq_false, false_and,
        ite_false, Fin.sum_univ_three, Fin.prod_univ_three, Fintype.card_fin,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        SurfaceBasisLabel.codimension, Nat.cast_zero,
        SurfaceTarget.c1Degree, map_zero, SurfaceBasisLabel.value,
        SurfaceCohomology.hyperplane_mul_hyperplane, pow_zero, one_mul,
        and_self, ite_true]
      norm_num
      rfl
    | hyperplane | exceptional i | point =>
      norm_num [SurfaceGenusZero.primaryScalar, Fin.sum_univ_three, Matrix.cons_val_two,
        SurfaceBasisLabel.codimension, reduceCtorEq]
      intro he
      cases he
  · have hc : n + Fintype.card (Fin 3) ≠ 3 := by
      simp only [Fintype.card_fin]
      omega
    simp only [SurfaceGenusZero.primaryScalar, ne_eq, not_true_eq_false, false_and,
      ite_false, ite_true, if_neg hc, ite_self, hn]

/-- A class-zero primary rational component of arity four vanishes, with any extra points. -/
theorem classical_four (n : ℕ) (a : Fin 4 → SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) 0 n a = 0 := by
  have hc : n + Fintype.card (Fin 4) ≠ 3 := by simp only [Fintype.card_fin]; omega
  simp only [SurfaceGenusZero.primaryScalar, ne_eq, not_true_eq_false, false_and, ite_true,
    if_neg hc, ite_self]

/-- The full binomial point distribution on a class-zero HH triple selects its unit node. -/
theorem classical_hh_points (f : ℕ → ℚ) (n : ℕ) (b : SurfaceBasisLabel X) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) 0 ij.2
        (![.hyperplane, .hyperplane, b] : Fin 3 → _))) =
      if b = .unit then f n else 0 := by
  rw [SurfacePointPullback.sum_binomial_of_right_support f
    (fun j ↦ SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) 0 j
      (![.hyperplane, .hyperplane, b] : Fin 3 → _)) n 0 (by
        intro j hj
        rw [classical_hh, if_neg (fun h ↦ hj h.1)])]
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul,
    classical_hh, true_and, mul_ite, mul_one, mul_zero]

/-- Expand the actual genus-two/rational pair join, preserving class splits, signed node weights
and binomial marking multiplicities. -/
theorem pair_join (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ) (n : ℕ)
    (x : GluingExpression 2 (Fin 2)) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (delta : X.Curve) (a b c : SurfaceBasisLabel X) :
    let y := GetzlerGraphs.join (m := 1) (n := 2) 1 2 x
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
    remainderContraction X v main y (by exact (d, (0 : Fin 3 → ℕ)))
      (by exact (l, (inferInstance : DecidableEq (Fin 3)))) delta n ![a, b, c] =
      ∑ split ∈ X.splittings delta, ∑ t : SurfaceBasisLabel X,
        t.inverseWeight * ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          (n.choose ij.1 : ℚ) *
            (remainderContraction X v main x d l split.1 ij.1 ![a, t] *
              SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X)
                split.2 ij.2 (![b, c, t.dual] : Fin 3 → _)) := by
  dsimp only
  simp only [GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction]
  have hl (t : SurfaceBasisLabel X) :
      (Option.elim · t (((![a, b, c] : Fin 3 → _) ∘
        (finSumFinEquiv : Fin 1 ⊕ Fin 2 ≃ Fin 3)) ∘ Sum.inl)) ∘
        finSuccEquiv' 1 = ![a, t] := by
    funext i
    fin_cases i <;> rfl
  have hr (t : SurfaceBasisLabel X) :
      (Option.elim · t (((![a, b, c] : Fin 3 → _) ∘
        (finSumFinEquiv : Fin 1 ⊕ Fin 2 ≃ Fin 3)) ∘ Sum.inr)) ∘
        finSuccEquiv' 2 = ![b, c, t] := by
    funext i
    fin_cases i <;> rfl
  simp only [hl, hr, primaryPointVertex, and_self, ite_true]

/-- At zero effective remainder, an outer HH rational pair inserts a point on
the inner component. -/
theorem pair_hh_zero (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ) (n : ℕ)
    (x : GluingExpression 2 (Fin 2)) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (a : SurfaceBasisLabel X) :
    let y := GetzlerGraphs.join (m := 1) (n := 2) 1 2 x
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
    remainderContraction X v main y (by exact (d, (0 : Fin 3 → ℕ)))
      (by exact (l, (inferInstance : DecidableEq (Fin 3)))) 0 n ![a, .hyperplane, .hyperplane] =
      remainderContraction X v main x d l 0 n ![a, .point] := by
  dsimp only
  rw [pair_join, (X.splittings_eq 0).trans X.effective.splittings_zero]
  simp only [Finset.sum_singleton]
  have hsum (b : SurfaceBasisLabel X) := classical_hh_points
      (fun m ↦ remainderContraction X v main x d l 0 m ![a, b]) n b.dual
  simp only [hsum]
  rw [SurfaceBasisLabel.sum_labels]
  simp only [SurfaceBasisLabel.inverseWeight, SurfaceBasisLabel.dual,
    one_mul, reduceCtorEq, ite_false, ite_true, zero_add,
    mul_zero, Finset.sum_const_zero]

/-- The primary-main BP diagram has no nonprimary coefficient, for arbitrary
external labels, full effective remainder and added-point count. -/
theorem paper_zero (v : Variable X)
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

/-- At zero effective remainder, the BP diagram with a rational four-flag
component vanishes for every requested coefficient and external labelling. -/
theorem paper_one (v : Variable X) (n : ℕ)
    (a : Fin 3 → SurfaceBasisLabel X) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 1) 0 n a = 0 := by
  have hx : (BelorousskiPandharipande.paperCotangentTerm 1).expression.maxComponentGenus = 2 :=
    by decide +kernel
  rw [remainderPointCoefficient, if_pos hx]
  change remainderContraction X v (remainderVertex X v (coefficientVertex X v))
    (GetzlerGraphs.join (m := 0) (n := 3) 0 3
      (fundamental 2 (Fin 1) (by norm_num [StableArity]))
      (fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (![1], (0 : Fin 4 → ℕ))
    ((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 4)))
    0 n a = _
  simp only [GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction]
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 0 ⊕ Fin 3 ≃ Fin 3)) ∘ Sum.inr)) ∘
        finSuccEquiv' 3 = ![a 0, a 1, a 2, b] := by
    funext i
    fin_cases i <;> rfl
  rw [(X.splittings_eq 0).trans X.effective.splittings_zero]
  simp only [Finset.sum_singleton, hr, primaryPointVertex, and_self, ite_true]
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [classical_four (X := X)]
  simp only [mul_zero]

/-- A classical rational H-square reduces either BP cotangent diagram to
its two-flag main component, for every external main state. -/
theorem paper_pair (v : Variable X) (n : ℕ) (s : Fin 2)
    (a : SurfaceBasisLabel X) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) 0 n
        ![a, .hyperplane, .hyperplane] =
      remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
        (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0 ![a, .point] := by
  have h0 : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
  have h1 : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
  have hs : s = 0 ∨ s = 1 := by omega
  have he : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) 0 n
        ![a, .hyperplane, .hyperplane] =
      remainderContraction X v (remainderVertex X v (coefficientVertex X v))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          (fundamental 2 (Fin 2) (by norm_num [StableArity]))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        (by exact (Pi.single s 1, (0 : Fin 3 → ℕ)))
        (by exact ((inferInstance : DecidableEq (Fin 2)),
          (inferInstance : DecidableEq (Fin 3)))) 0 n ![a, .hyperplane, .hyperplane] := by
    rcases hs with rfl | rfl
    · rw [if_pos rfl, ← h0]
      rfl
    · rw [if_neg (by decide : (1 : Fin 2) ≠ 0), ← h1]
      rfl
  rw [he, pair_hh_zero]
  rfl

private theorem pair_dimension (beta : X.Curve) (n : ℕ) (s : Fin 2) :
    SurfaceAncestorKey.DimensionCompatible
      ((SurfaceAncestorKey.ofLabels 2 (Fin 2) (by norm_num [StableArity]) beta
        (Pi.single s 1) (![.hyperplane, .point] : Fin 2 → SurfaceBasisLabel X)).addPoints n) ↔
      X.effective.energy beta = n + 1 := by
  fin_cases s <;>
    simp only [SurfaceAncestorKey.DimensionCompatible, SurfaceAncestorKey.totalCodimension,
      SurfaceAncestorKey.addPoints, SurfaceAncestorKey.ofLabels, Multiset.map_add,
      Multiset.map_replicate, Multiset.sum_add, Multiset.sum_replicate,
      Multiset.card_add, Multiset.card_replicate, Multiset.card_map, Finset.card_val,
      Finset.card_univ, Fintype.card_fin, SurfaceTarget.c1Degree,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  · change (n : ℤ) * 2 + 4 =
      (X.effective.energy beta : ℤ) + 2 - 1 + ((n : ℤ) + 2) ↔ _
    omega
  · change (n : ℤ) * 2 + 4 =
      (X.effective.energy beta : ℤ) + 2 - 1 + ((n : ℤ) + 2) ↔ _
    omega

/-- The nonprimary coefficient with psi on H is exactly its full H query. -/
theorem main_h (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (n : ℕ) (he : X.effective.energy (SurfaceGenusZero.variableCurve v) = n + 1) :
    remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0
      ![.hyperplane, .point] =
      if Sum.inr (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
        .hyperplane (n + 1)) = v then 1 else 0 := by
  have hm : ((Finset.univ.erase (0 : Fin 2)).val.map
      (![.hyperplane, .point] : Fin 2 → SurfaceBasisLabel X)) = {.point} := by
    change Multiset.map (![.hyperplane, .point] : Fin 2 → SurfaceBasisLabel X) {1} = _
    rfl
  have hu : SurfaceBasisLabel.unit ∉
      (Multiset.replicate n .point + {.point} : Multiset (SurfaceBasisLabel X)) := by
    simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton,
      reduceCtorEq, and_false, or_self, not_false_eq_true]
  have hd : (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
      .hyperplane (n + 1)).DimensionCompatible := by
    rw [SurfaceQuery.dimensionCompatible_first, he]
    rfl
  rw [remainderVertex_onePsi_of_not_points v hv, if_pos rfl,
    coefficient_residualTerms_onePsi_of_not_points v hv,
    if_pos ((pair_dimension _ n 0).mpr he)]
  simp only [hm, Matrix.cons_val_zero]
  rw [SurfaceFirstDescendant.terms, if_neg hu,
    if_neg (show (SurfaceBasisLabel.hyperplane : SurfaceBasisLabel X) ≠ .unit from by
      intro heq
      cases heq)]
  rw [RationalTerms.coefficient_rename_add, RationalTerms.coefficient_rename_scale,
    RationalTerms.coefficient_rename_scale]
  simp only [SurfaceFirstDescendant.primaryCoefficient,
    Multiset.map_add, Multiset.map_replicate, Multiset.map_singleton,
    Multiset.prod_add, Multiset.prod_replicate, Multiset.prod_singleton,
    SurfaceBasisLabel.primaryFactor, one_pow, one_mul,
    SurfaceFirstDescendant.correctionCoefficient, SurfaceFirstDescendant.divisorSquare,
    Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton,
    reduceCtorEq, ite_false, ite_true, add_zero, Nat.cast_zero, mul_zero,
    zero_mul]
  rw [SurfaceFirstDescendant.dimensionTerms, if_pos hd,
    RationalTerms.coefficient_rename_term]
  simp only [Multiset.map_singleton, Multiset.singleton_inj]

/-- The nonprimary coefficient with psi on the point retains its H divisor factor. -/
theorem main_p (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (n : ℕ) (he : X.effective.energy (SurfaceGenusZero.variableCurve v) = n + 1) :
    remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single 1 1) inferInstance 0
      ![.hyperplane, .point] =
      (X.planeDegree (SurfaceGenusZero.variableCurve v) : ℚ) *
      (if Sum.inr (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
        .point n) = v then 1 else 0) := by
  have hm : ((Finset.univ.erase (1 : Fin 2)).val.map
      (![.hyperplane, .point] : Fin 2 → SurfaceBasisLabel X)) = {.hyperplane} := by
    change Multiset.map (![.hyperplane, .point] : Fin 2 → SurfaceBasisLabel X) {0} = _
    rfl
  have hu : SurfaceBasisLabel.unit ∉
      (Multiset.replicate n .point + {.hyperplane} : Multiset (SurfaceBasisLabel X)) := by
    simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton,
      reduceCtorEq, and_false, or_self, not_false_eq_true]
  have hd : (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
      .point n).DimensionCompatible := by
    rw [SurfaceQuery.dimensionCompatible_first, he]
    rfl
  rw [remainderVertex_onePsi_of_not_points v hv, if_pos rfl,
    coefficient_residualTerms_onePsi_of_not_points v hv,
    if_pos ((pair_dimension _ n 1).mpr he)]
  simp only [hm, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [SurfaceFirstDescendant.terms, if_neg hu,
    if_neg (show (SurfaceBasisLabel.point : SurfaceBasisLabel X) ≠ .unit from by
      intro heq
      cases heq)]
  rw [RationalTerms.coefficient_rename_add, RationalTerms.coefficient_rename_scale,
    RationalTerms.coefficient_rename_scale]
  simp only [SurfaceFirstDescendant.primaryCoefficient,
    Multiset.map_add, Multiset.map_replicate, Multiset.map_singleton,
    Multiset.prod_add, Multiset.prod_replicate, Multiset.prod_singleton,
    SurfaceBasisLabel.primaryFactor, one_pow, one_mul,
    SurfaceFirstDescendant.correctionCoefficient, SurfaceFirstDescendant.divisorSquare,
    Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton,
    reduceCtorEq, ite_false, ite_true, add_zero,
    zero_mul]
  rw [SurfaceFirstDescendant.dimensionTerms, if_pos hd,
    RationalTerms.coefficient_rename_term]
  simp only [Multiset.map_singleton, Multiset.singleton_inj]
  rw [← X.planeDegree_eq_divisorIntersections]
  simp only [Int.cast_natCast]

/-- The actual BP marking orbit transports arbitrary external states through
the complete remainder coefficient, preserving their permutation. -/
theorem remainder_orbit (v : Variable X) (n : ℕ)
    (delta : X.Curve) (a : Fin 3 → SurfaceBasisLabel X)
    (i : Fin 20) (e : Fin 6) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm i e) delta n a =
      remainderPointCoefficient X v (coefficientVertex X v)
        (BelorousskiPandharipande.paperCotangentTerm i) delta n
        (a ∘ BelorousskiPandharipande.labelPermutation e) := by
  simp only [BelorousskiPandharipande.orbitCotangentTerm, CotangentTerm.relabel,
    remainderPointCoefficient, GluingExpression.maxComponentGenus, remainderContraction]

private theorem hhh_permutation (e : Fin 6) :
    (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) ∘
      BelorousskiPandharipande.labelPermutation e = ![.hyperplane, .hyperplane, .hyperplane] := by
  have hh : (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) =
      fun _ ↦ .hyperplane := by
    funext i
    fin_cases i <;> rfl
  rw [hh]
  rfl

/-- The actual compressed BP constructor has precisely these same-class
first-descendant coefficients. The complete normalized row is retained;
primary calibration and cotangent tails have zero coefficient at this request.
The exact dimension condition excludes class zero and natural underflow. -/
theorem pointCoefficient_at_requested_class (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (n : ℕ) (he : X.effective.energy (SurfaceGenusZero.variableCurve v) = n + 1) :
    BelorousskiPandharipande.pointCoefficient X n (SurfaceGenusZero.variableCurve v)
      ![.hyperplane, .hyperplane, .hyperplane] v =
      18 * (if Sum.inr (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
        .hyperplane (n + 1)) = v then 1 else 0) -
      18 * (X.planeDegree (SurfaceGenusZero.variableCurve v) : ℚ) *
        (if Sum.inr (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
          .point n) = v then 1 else 0) := by
  have hterm (i : Fin 20) (e : Fin 6) :
      SurfaceGenusTwo.pointCoefficient X v (BelorousskiPandharipande.orbitCotangentTerm i e)
        (SurfaceGenusZero.variableCurve v) n ![.hyperplane, .hyperplane, .hyperplane] =
      remainderPointCoefficient X v (coefficientVertex X v)
        (BelorousskiPandharipande.paperCotangentTerm i) 0 n
          ![.hyperplane, .hyperplane, .hyperplane] := by
    have h := remainderPointCoefficient_eq X v (coefficientVertex X v) rfl
      (BelorousskiPandharipande.orbitCotangentTerm i e) 0 n
      (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
    rw [remainder_orbit, hhh_permutation] at h
    simpa only [add_zero] using h.symm
  simp only [BelorousskiPandharipande.pointCoefficient, hterm,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fin.sum_univ_four]
  change -2 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 0) 0 n
        ![.hyperplane, .hyperplane, .hyperplane]) +
    2 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 1) 0 n
        ![.hyperplane, .hyperplane, .hyperplane]) +
    3 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 2) 0 n
        ![.hyperplane, .hyperplane, .hyperplane]) +
    -3 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 3) 0 n
        ![.hyperplane, .hyperplane, .hyperplane]) = _
  rw [paper_zero v hv, paper_one]
  have h2 := paper_pair v n (0 : Fin 2) .hyperplane
  have h3 := paper_pair v n (1 : Fin 2) .hyperplane
  simp only [ite_true, if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h2 h3
  rw [h2, h3, main_h v hv n he, main_p v hv n he]
  ring

/-- Coefficient extraction is from the full normalized BP polynomial, including
its primary terms, lower-class calibration tails and rational complements. -/
theorem normalizedCoefficient_at_requested_class (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (n : ℕ) (he : X.effective.energy (SurfaceGenusZero.variableCurve v) = n + 1) :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X n
        (SurfaceGenusZero.variableCurve v) 0 (SurfaceGenusZero.pointLabels
          (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) n)) {v} =
      18 * (if Sum.inr (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
        .hyperplane (n + 1)) = v then 1 else 0) -
      18 * (X.planeDegree (SurfaceGenusZero.variableCurve v) : ℚ) *
        (if Sum.inr (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
          .point n) = v then 1 else 0) := by
  rw [← BelorousskiPandharipande.pointCoefficient_eq_full]
  exact pointCoefficient_at_requested_class v hv n he

/-- Different distinguished first-descendant labels give distinct complete
variables, even when the point counts differ. -/
theorem first_queries_ne (beta : X.Curve) (b c : SurfaceBasisLabel X)
    (n m : ℕ) (hbc : b ≠ c) :
    Sum.inr (SurfaceFirstDescendant.query 2 beta b n) ≠
      (Sum.inr (SurfaceFirstDescendant.query 2 beta c m) : Variable X) := by
  intro he
  have hl := congrArg (fun q : SurfaceQuery X ↦ q.insertions.head?.map SurfaceInsertion.label)
    (Sum.inr.inj he)
  simp only [SurfaceFirstDescendant.query, List.head?_cons, Option.map_some,
    Option.some.injEq] at hl
  exact hbc hl

/-- Positive energy is the exact additional-point condition for the HHH BP row.
No positive plane-degree premise is needed for its coefficient identities. -/
theorem pointCount_dimension (beta : X.Curve) (hbeta : 0 < X.effective.energy beta) :
    X.effective.energy beta = (X.effective.energy beta - 1) + 1 := by omega

/-- Every first-descendant state at the original full class is extracted from
the complete normalized HHH BP equation. Its possible H/P terms retain their
full queries, so exceptional divisor labels are not identified. -/
theorem first_coefficient (beta : X.Curve) (b : SurfaceBasisLabel X) (m : ℕ)
    (hbeta : 0 < X.effective.energy beta) :
    let n := X.effective.energy beta - 1
    let v : Variable X := .inr (SurfaceFirstDescendant.query 2 beta b m)
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X n beta 0
        (SurfaceGenusZero.pointLabels
          (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) n)) {v} =
      18 * (if Sum.inr (SurfaceFirstDescendant.query 2 beta .hyperplane
        (X.effective.energy beta)) = v then 1 else 0) -
      18 * (X.planeDegree beta : ℚ) *
        (if Sum.inr (SurfaceFirstDescendant.query 2 beta .point n) = v then 1 else 0) := by
  dsimp only
  have h := normalizedCoefficient_at_requested_class
    (Sum.inr (SurfaceFirstDescendant.query 2 beta b m))
    (fun gamma k ↦ SurfaceFirstDescendant.query_ne_points beta gamma b m k)
    (X.effective.energy beta - 1) (pointCount_dimension beta hbeta)
  change RationalTerms.coefficient _ {_} =
    18 * (if Sum.inr (SurfaceFirstDescendant.query 2 beta .hyperplane
      (X.effective.energy beta - 1 + 1)) = _ then 1 else 0) -
      18 * (X.planeDegree beta : ℚ) *
        (if Sum.inr (SurfaceFirstDescendant.query 2 beta .point
          (X.effective.energy beta - 1)) = _ then 1 else 0) at h
  rw [← pointCount_dimension beta hbeta] at h
  exact h

/-- The uniform hyperplane coefficient of the full BP HHH row is eighteen. -/
theorem hyperplane_coefficient (beta : X.Curve) (hbeta : 0 < X.effective.energy beta) :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X (X.effective.energy beta - 1) beta 0
        (SurfaceGenusZero.pointLabels
          (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
          (X.effective.energy beta - 1)))
      {Sum.inr (SurfaceFirstDescendant.query 2 beta .hyperplane (X.effective.energy beta))} =
      18 := by
  have hne := first_queries_ne beta .point .hyperplane (X.effective.energy beta - 1)
    (X.effective.energy beta) (by intro h; cases h)
  have h := first_coefficient beta .hyperplane (X.effective.energy beta) hbeta
  simpa only [ite_true, if_neg hne, mul_one, mul_zero, sub_zero] using h

/-- The uniform point-descendant coefficient is minus eighteen times plane
intersection degree. At exceptional classes it is zero; no division is used. -/
theorem point_coefficient (beta : X.Curve) (hbeta : 0 < X.effective.energy beta) :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X (X.effective.energy beta - 1) beta 0
        (SurfaceGenusZero.pointLabels
          (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
          (X.effective.energy beta - 1)))
      {Sum.inr (SurfaceFirstDescendant.query 2 beta .point (X.effective.energy beta - 1))} =
      -18 * (X.planeDegree beta : ℚ) := by
  have hne := first_queries_ne beta .hyperplane .point (X.effective.energy beta)
    (X.effective.energy beta - 1) (by intro h; cases h)
  have h := first_coefficient beta .point (X.effective.energy beta - 1) hbeta
  simpa only [if_neg hne, ite_true, mul_one, mul_zero, zero_sub, neg_mul] using h

/-- No exceptional first descendant at the same full class is introduced by
this BP row. Different exceptional labels and all other polynomial terms remain. -/
theorem exceptional_coefficient (beta : X.Curve) (i : Fin X.blowups)
    (hbeta : 0 < X.effective.energy beta) :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X (X.effective.energy beta - 1) beta 0
        (SurfaceGenusZero.pointLabels
          (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
          (X.effective.energy beta - 1)))
      {Sum.inr (SurfaceFirstDescendant.query 2 beta (.exceptional i) (X.effective.energy beta))} =
      0 := by
  have hneH := first_queries_ne beta .hyperplane (.exceptional i) (X.effective.energy beta)
    (X.effective.energy beta) (by intro h; cases h)
  have hneP := first_queries_ne beta .point (.exceptional i) (X.effective.energy beta - 1)
    (X.effective.energy beta) (by intro h; cases h)
  have h := first_coefficient beta (.exceptional i) (X.effective.energy beta) hbeta
  simpa only [if_neg hneH, if_neg hneP, mul_zero, sub_zero] using h

/-- At positive plane degree the proved point coefficient is nonzero.
This theorem does not assume a recurrence, seed value or geometric support. -/
theorem point_coefficient_ne_zero (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta) (hd : 0 < X.planeDegree beta) :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X (X.effective.energy beta - 1) beta 0
        (SurfaceGenusZero.pointLabels
          (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
          (X.effective.energy beta - 1)))
      {Sum.inr (SurfaceFirstDescendant.query 2 beta .point (X.effective.energy beta - 1))} ≠
      0 := by
  rw [point_coefficient beta hbeta]
  exact mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (by omega))

end AxiomaticGW.SurfaceGenusTwoBlowupPCoefficients

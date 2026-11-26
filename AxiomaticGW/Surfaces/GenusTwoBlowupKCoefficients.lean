/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupPCoefficients

/-!
# Exceptional first-descendant pivots of the complete BP row

For every full effective class `beta` of positive energy, the complete normalized
BP equation with three copies of `E_i` and `energy(beta) - 1` added points has
same-class `K_i` coefficient minus eighteen. Its other same-class exceptional
coefficients vanish, and its same-class point-descendant coefficient is eighteen
times the signed exceptional intersection of `beta`. The latter may be negative
or zero; the `K_i` pivot remains nonzero without a positive plane-degree premise.

The calculation follows the actual first four BP diagrams and all six marking
assignments. The class-zero rational `E_i/E_i` triple inserts minus the point
state, reflecting `E_i^2 = -pt`. Calibration and cotangent tails have primary
main components and retain their proved zero nonprimary coefficient. Full
normalization and every primary or different-class term remain on the left.

Together with the effective-subclass bound, the exact exceptional coefficients
prove canonical column support: a surviving canonical coefficient is the row's
own `K_i` column or strictly earlier in the order on plane degree, family rank,
and energy. Other exceptional labels at the same full class are checked
explicitly, rather than identified by their common rank or energy. Proper
subclasses decrease energy. This theorem supplies a nonzero pivot and canonical
support, but no complete reconstruction or primary-N seed-sufficiency claim.
The exceptional triple route is used in Wennink, arXiv:2210.04038, Section 8.3;
no displayed paper recurrence is assumed in this proof.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupKCoefficients
open SurfacePolynomialReduction SurfaceGenusTwo GluingExpression
open SurfaceGenusTwoBlowupPCoefficients

set_option maxRecDepth 20000
variable {X : SurfaceTarget}

/-- A class-zero rational exceptional square pairs only with a unit node, with value minus one. -/
theorem classical_ee (i : Fin X.blowups) (n : ℕ) (b : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) 0 n
      (![.exceptional i, .exceptional i, b] : Fin 3 → _) =
      if n = 0 ∧ b = .unit then -1 else 0 := by
  by_cases hn : n = 0
  · subst n
    cases b with
    | unit =>
      simp only [SurfaceGenusZero.primaryScalar, ne_eq, not_true_eq_false, false_and,
        ite_false, Fin.sum_univ_three, Fin.prod_univ_three, Fintype.card_fin,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        SurfaceBasisLabel.codimension, Nat.cast_zero,
        SurfaceTarget.c1Degree, map_zero, SurfaceBasisLabel.value,
        SurfaceCohomology.exceptional_mul_exceptional, pow_zero, one_mul,
        and_self, ite_true]
      norm_num
      rfl
    | hyperplane | exceptional j | point =>
      norm_num [SurfaceGenusZero.primaryScalar, Fin.sum_univ_three, Matrix.cons_val_two,
        SurfaceBasisLabel.codimension, reduceCtorEq]
      intro he
      cases he
  · have hc : n + Fintype.card (Fin 3) ≠ 3 := by
      simp only [Fintype.card_fin]
      omega
    simp only [SurfaceGenusZero.primaryScalar, ne_eq, not_true_eq_false, false_and,
      ite_false, ite_true, if_neg hc, ite_self, hn]

/-- The full point distribution on the classical exceptional square inserts
its negative unit pairing. -/
theorem classical_ee_points (i : Fin X.blowups) (f : ℕ → ℚ) (n : ℕ)
    (b : SurfaceBasisLabel X) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) 0 ij.2
        (![.exceptional i, .exceptional i, b] : Fin 3 → _))) =
      if b = .unit then -f n else 0 := by
  rw [SurfacePointPullback.sum_binomial_of_right_support f
    (fun j ↦ SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) 0 j
      (![.exceptional i, .exceptional i, b] : Fin 3 → _)) n 0 (by
        intro j hj
        rw [classical_ee, if_neg (fun h ↦ hj h.1)])]
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul,
    classical_ee, true_and, mul_ite, mul_neg, mul_one, mul_zero]

/-- At zero effective remainder, the outer exceptional square inserts minus the point state. -/
theorem pair_ee_zero (i : Fin X.blowups) (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ) (n : ℕ)
    (x : GluingExpression 2 (Fin 2)) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (a : SurfaceBasisLabel X) :
    let y := GetzlerGraphs.join (m := 1) (n := 2) 1 2 x
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
    remainderContraction X v main y (by exact (d, (0 : Fin 3 → ℕ)))
      (by exact (l, (inferInstance : DecidableEq (Fin 3)))) 0 n
        ![a, .exceptional i, .exceptional i] =
      -remainderContraction X v main x d l 0 n ![a, .point] := by
  dsimp only
  rw [pair_join, (X.splittings_eq 0).trans X.effective.splittings_zero]
  simp only [Finset.sum_singleton]
  have hsum (b : SurfaceBasisLabel X) := classical_ee_points i
      (fun m ↦ remainderContraction X v main x d l 0 m ![a, b]) n b.dual
  simp only [hsum]
  rw [SurfaceBasisLabel.sum_labels]
  simp only [SurfaceBasisLabel.inverseWeight, SurfaceBasisLabel.dual,
    one_mul, reduceCtorEq, ite_false, ite_true, zero_add,
    mul_zero, Finset.sum_const_zero]

private theorem pair_dimension (i : Fin X.blowups) (beta : X.Curve) (n : ℕ) (s : Fin 2) :
    SurfaceAncestorKey.DimensionCompatible
      ((SurfaceAncestorKey.ofLabels 2 (Fin 2) (by norm_num [StableArity]) beta
        (Pi.single s 1) (![(.exceptional i), .point] : Fin 2 → SurfaceBasisLabel X)).addPoints n) ↔
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

/-- The nonprimary coefficient with psi on E_i is exactly its full K_i query. -/
theorem main_k (i : Fin X.blowups) (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (n : ℕ) (he : X.effective.energy (SurfaceGenusZero.variableCurve v) = n + 1) :
    remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0
      ![(.exceptional i), .point] =
      if Sum.inr (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
        (.exceptional i) (n + 1)) = v then 1 else 0 := by
  have hm : ((Finset.univ.erase (0 : Fin 2)).val.map
      (![(.exceptional i), .point] : Fin 2 → SurfaceBasisLabel X)) = {.point} := by
    change Multiset.map (![(.exceptional i), .point] : Fin 2 → SurfaceBasisLabel X) {1} = _
    rfl
  have hu : SurfaceBasisLabel.unit ∉
      (Multiset.replicate n .point + {.point} : Multiset (SurfaceBasisLabel X)) := by
    simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton,
      reduceCtorEq, and_false, or_self, not_false_eq_true]
  have hd : (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
      (.exceptional i) (n + 1)).DimensionCompatible := by
    rw [SurfaceQuery.dimensionCompatible_first, he]
    rfl
  rw [remainderVertex_onePsi_of_not_points v hv, if_pos rfl,
    coefficient_residualTerms_onePsi_of_not_points v hv,
    if_pos ((pair_dimension i _ n 0).mpr he)]
  simp only [hm, Matrix.cons_val_zero]
  rw [SurfaceFirstDescendant.terms, if_neg hu,
    if_neg (show (SurfaceBasisLabel.exceptional i : SurfaceBasisLabel X) ≠ .unit from by
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

/-- The nonprimary point descendant retains its signed exceptional divisor factor. -/
theorem main_p (i : Fin X.blowups) (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (n : ℕ) (he : X.effective.energy (SurfaceGenusZero.variableCurve v) = n + 1) :
    remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single 1 1) inferInstance 0
      ![(.exceptional i), .point] =
      ((X.signedMultiplicity (SurfaceGenusZero.variableCurve v) i : ℤ) : ℚ) *
      (if Sum.inr (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
        .point n) = v then 1 else 0) := by
  have hm : ((Finset.univ.erase (1 : Fin 2)).val.map
      (![(.exceptional i), .point] : Fin 2 → SurfaceBasisLabel X)) = {(.exceptional i)} := by
    change Multiset.map (![(.exceptional i), .point] : Fin 2 → SurfaceBasisLabel X) {0} = _
    rfl
  have hu : SurfaceBasisLabel.unit ∉
      (Multiset.replicate n .point + {(.exceptional i)} : Multiset (SurfaceBasisLabel X)) := by
    simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton,
      reduceCtorEq, and_false, or_self, not_false_eq_true]
  have hd : (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
      .point n).DimensionCompatible := by
    rw [SurfaceQuery.dimensionCompatible_first, he]
    rfl
  rw [remainderVertex_onePsi_of_not_points v hv, if_pos rfl,
    coefficient_residualTerms_onePsi_of_not_points v hv,
    if_pos ((pair_dimension i _ n 1).mpr he)]
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
  rfl

/-- A classical rational exceptional square inserts minus the point into
either BP cotangent diagram, for every external main state. -/
theorem paper_pair (i : Fin X.blowups) (v : Variable X) (n : ℕ) (s : Fin 2)
    (a : SurfaceBasisLabel X) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) 0 n
        ![a, (.exceptional i), (.exceptional i)] =
      -remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
        (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0 ![a, .point] := by
  have h0 : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
  have h1 : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
  have hs : s = 0 ∨ s = 1 := by omega
  have he : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) 0 n
        ![a, (.exceptional i), (.exceptional i)] =
      remainderContraction X v (remainderVertex X v (coefficientVertex X v))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          (fundamental 2 (Fin 2) (by norm_num [StableArity]))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        (by exact (Pi.single s 1, (0 : Fin 3 → ℕ)))
        (by exact ((inferInstance : DecidableEq (Fin 2)),
          (inferInstance : DecidableEq (Fin 3)))) 0 n ![a, (.exceptional i), (.exceptional i)] := by
    rcases hs with rfl | rfl
    · rw [if_pos rfl, ← h0]
      rfl
    · rw [if_neg (by decide : (1 : Fin 2) ≠ 0), ← h1]
      rfl
  rw [he, pair_ee_zero]
  rfl

private theorem eee_permutation (i : Fin X.blowups) (e : Fin 6) :
    (![(.exceptional i), (.exceptional i), (.exceptional i)] : Fin 3 → SurfaceBasisLabel X) ∘
      BelorousskiPandharipande.labelPermutation e =
        ![(.exceptional i), (.exceptional i), (.exceptional i)] := by
  have hh : (![(.exceptional i), (.exceptional i), (.exceptional i)] :
      Fin 3 → SurfaceBasisLabel X) =
      fun _ ↦ (.exceptional i) := by
    funext i
    fin_cases i <;> rfl
  rw [hh]
  rfl

/-- The compressed BP constructor retains exactly its distinguished exceptional
and point first-descendant columns at the original requested full class. The
positive-energy dimension equation is explicit, and every primary tail remains
in the complete coefficient computation on the left. -/
theorem pointCoefficient_at_requested_class (i : Fin X.blowups) (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (n : ℕ) (he : X.effective.energy (SurfaceGenusZero.variableCurve v) = n + 1) :
    BelorousskiPandharipande.pointCoefficient X n (SurfaceGenusZero.variableCurve v)
      ![.exceptional i, .exceptional i, .exceptional i] v =
      -18 * (if Sum.inr (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
        (.exceptional i) (n + 1)) = v then 1 else 0) +
      18 * ((X.signedMultiplicity (SurfaceGenusZero.variableCurve v) i : ℤ) : ℚ) *
        (if Sum.inr (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
          .point n) = v then 1 else 0) := by
  have hterm (j : Fin 20) (e : Fin 6) :
      SurfaceGenusTwo.pointCoefficient X v (BelorousskiPandharipande.orbitCotangentTerm j e)
        (SurfaceGenusZero.variableCurve v) n ![.exceptional i, .exceptional i, .exceptional i] =
      remainderPointCoefficient X v (coefficientVertex X v)
        (BelorousskiPandharipande.paperCotangentTerm j) 0 n
          ![.exceptional i, .exceptional i, .exceptional i] := by
    have h := remainderPointCoefficient_eq X v (coefficientVertex X v) rfl
      (BelorousskiPandharipande.orbitCotangentTerm j e) 0 n
      (![.exceptional i, .exceptional i, .exceptional i] : Fin 3 → SurfaceBasisLabel X)
    have ho : remainderPointCoefficient X v (coefficientVertex X v)
        (BelorousskiPandharipande.orbitCotangentTerm j e) 0 n
          ![.exceptional i, .exceptional i, .exceptional i] =
        remainderPointCoefficient X v (coefficientVertex X v)
          (BelorousskiPandharipande.paperCotangentTerm j) 0 n
            ![.exceptional i, .exceptional i, .exceptional i] := by
      simp only [BelorousskiPandharipande.orbitCotangentTerm, CotangentTerm.relabel,
        remainderPointCoefficient, GluingExpression.maxComponentGenus,
        remainderContraction, eee_permutation]
    rw [ho] at h
    simpa only [add_zero] using h.symm
  simp only [BelorousskiPandharipande.pointCoefficient, hterm,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fin.sum_univ_four]
  change -2 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 0) 0 n
        ![.exceptional i, .exceptional i, .exceptional i]) +
    2 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 1) 0 n
        ![.exceptional i, .exceptional i, .exceptional i]) +
    3 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 2) 0 n
        ![.exceptional i, .exceptional i, .exceptional i]) +
    -3 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 3) 0 n
        ![.exceptional i, .exceptional i, .exceptional i]) = _
  rw [SurfaceGenusTwoBlowupPCoefficients.paper_zero v hv,
    SurfaceGenusTwoBlowupPCoefficients.paper_one]
  have h2 := paper_pair i v n (0 : Fin 2) (.exceptional i)
  have h3 := paper_pair i v n (1 : Fin 2) (.exceptional i)
  simp only [ite_true, if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h2 h3
  rw [h2, h3, main_k i v hv n he, main_p i v hv n he]
  ring

/-- Bind the exact nonprimary coefficient identity to the complete original
normalized BP polynomial, including its other classes and primary tails. -/
theorem normalizedCoefficient_at_requested_class (i : Fin X.blowups) (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (n : ℕ) (he : X.effective.energy (SurfaceGenusZero.variableCurve v) = n + 1) :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X n
        (SurfaceGenusZero.variableCurve v) 0 (SurfaceGenusZero.pointLabels
          (![.exceptional i, .exceptional i, .exceptional i] :
            Fin 3 → SurfaceBasisLabel X) n)) {v} =
      -18 * (if Sum.inr (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
        (.exceptional i) (n + 1)) = v then 1 else 0) +
      18 * ((X.signedMultiplicity (SurfaceGenusZero.variableCurve v) i : ℤ) : ℚ) *
        (if Sum.inr (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
          .point n) = v then 1 else 0) := by
  rw [← BelorousskiPandharipande.pointCoefficient_eq_full]
  exact pointCoefficient_at_requested_class i v hv n he

/-- Extract any first-descendant state at the original full class from the
complete exceptional triple row. Full queries distinguish all exceptional
labels and point counts. -/
theorem first_coefficient (i : Fin X.blowups) (beta : X.Curve) (b : SurfaceBasisLabel X) (m : ℕ)
    (hbeta : 0 < X.effective.energy beta) :
    let n := X.effective.energy beta - 1
    let v : Variable X := .inr (SurfaceFirstDescendant.query 2 beta b m)
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X n beta 0
        (SurfaceGenusZero.pointLabels
          (![.exceptional i, .exceptional i, .exceptional i] :
            Fin 3 → SurfaceBasisLabel X) n)) {v} =
      -18 * (if Sum.inr (SurfaceFirstDescendant.query 2 beta (.exceptional i)
        (X.effective.energy beta)) = v then 1 else 0) +
      18 * ((X.signedMultiplicity beta i : ℤ) : ℚ) *
        (if Sum.inr (SurfaceFirstDescendant.query 2 beta .point n) = v then 1 else 0) := by
  dsimp only
  have h := normalizedCoefficient_at_requested_class i
    (Sum.inr (SurfaceFirstDescendant.query 2 beta b m))
    (fun gamma k ↦ SurfaceFirstDescendant.query_ne_points beta gamma b m k)
    (X.effective.energy beta - 1) (pointCount_dimension beta hbeta)
  change RationalTerms.coefficient _ {_} =
    -18 * (if Sum.inr (SurfaceFirstDescendant.query 2 beta (.exceptional i)
      (X.effective.energy beta - 1 + 1)) = _ then 1 else 0) +
      18 * ((X.signedMultiplicity beta i : ℤ) : ℚ) *
        (if Sum.inr (SurfaceFirstDescendant.query 2 beta .point
          (X.effective.energy beta - 1)) = _ then 1 else 0) at h
  rw [← pointCount_dimension beta hbeta] at h
  exact h

/-- The row has coefficient minus eighteen at its own exceptional descendant,
and zero at every other same-class exceptional label. -/
theorem exceptional_coefficient (i j : Fin X.blowups) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta) :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X (X.effective.energy beta - 1)
        beta 0 (SurfaceGenusZero.pointLabels
          (![.exceptional i, .exceptional i, .exceptional i] : Fin 3 → SurfaceBasisLabel X)
          (X.effective.energy beta - 1)))
      {Sum.inr (SurfaceFirstDescendant.query 2 beta (.exceptional j)
        (X.effective.energy beta))} = if i = j then -18 else 0 := by
  have hneP := first_queries_ne beta .point (.exceptional j)
    (X.effective.energy beta - 1) (X.effective.energy beta) (by intro h; cases h)
  have h := first_coefficient i beta (.exceptional j) (X.effective.energy beta) hbeta
  by_cases hij : i = j
  · subst j
    simpa only [ite_true, if_neg hneP, mul_one, mul_zero, add_zero] using h
  · have hneK := first_queries_ne beta (.exceptional i) (.exceptional j)
      (X.effective.energy beta) (X.effective.energy beta)
      (fun h ↦ hij (SurfaceBasisLabel.exceptional.inj h))
    simpa only [if_neg hij, if_neg hneK, if_neg hneP, mul_zero, add_zero] using h

/-- The same-class point-descendant coefficient retains the signed exceptional
intersection, including negative multiplicities and the zero boundary. -/
theorem point_coefficient (i : Fin X.blowups) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta) :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X (X.effective.energy beta - 1)
        beta 0 (SurfaceGenusZero.pointLabels
          (![.exceptional i, .exceptional i, .exceptional i] : Fin 3 → SurfaceBasisLabel X)
          (X.effective.energy beta - 1)))
      {Sum.inr (SurfaceFirstDescendant.query 2 beta .point
        (X.effective.energy beta - 1))} =
      18 * ((X.signedMultiplicity beta i : ℤ) : ℚ) := by
  have hneK := first_queries_ne beta (.exceptional i) .point
    (X.effective.energy beta) (X.effective.energy beta - 1) (by intro h; cases h)
  have h := first_coefficient i beta .point (X.effective.energy beta - 1) hbeta
  simpa only [ite_true, if_neg hneK, mul_one, mul_zero, zero_add] using h

/-- Every surviving canonical coefficient is the distinguished exceptional
column itself or precedes it in the full-class order. Other exceptional labels
at the same class vanish; all different-class primary and nonprimary tails
remain on the original polynomial. -/
theorem canonical_coefficient_support (i : Fin X.blowups) (beta gamma : X.Curve)
    (family : SurfaceGenusTwoBlowupOrder.Family X)
    (hbeta : 0 < X.effective.energy beta)
    (hc : RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X (X.effective.energy beta - 1)
        beta 0 (SurfaceGenusZero.pointLabels
          (![.exceptional i, .exceptional i, .exceptional i] : Fin 3 → SurfaceBasisLabel X)
          (X.effective.energy beta - 1)))
      {Sum.inr (family.query gamma)} ≠ 0) :
    (family = .exceptional i ∧ gamma = beta) ∨
      SurfaceGenusTwoBlowupOrder.Earlier X (gamma, family) (beta, .exceptional i) := by
  have hle : gamma ≤ beta := by
    by_contra hn
    have hb := BelorousskiPandharipande.genusTwoTerms_bound X (X.effective.energy beta - 1)
      beta 0 (SurfaceGenusZero.pointLabels
        (![.exceptional i, .exceptional i, .exceptional i] : Fin 3 → SurfaceBasisLabel X)
        (X.effective.energy beta - 1))
    have hv : SurfaceGenusZero.variableCurve (Sum.inr (family.query gamma)) = gamma := by
      cases family <;> rfl
    exact hc (hb.normalized_coefficient_eq_zero_of_not_le le_rfl
      (.inr (family.query gamma)) (by rwa [hv]))
  cases family with
  | hyperplane =>
    right
    exact SurfaceGenusTwoBlowupOrder.earlier_of_rank_lt X _ _
      (hle (Fin.last X.blowups)) (show (0 : ℕ) < 3 from by decide)
  | point =>
    right
    exact SurfaceGenusTwoBlowupOrder.earlier_of_rank_lt X _ _
      (hle (Fin.last X.blowups)) (show (1 : ℕ) < 3 from by decide)
  | primary =>
    right
    exact SurfaceGenusTwoBlowupOrder.earlier_of_rank_lt X _ _
      (hle (Fin.last X.blowups)) (show (2 : ℕ) < 3 from by decide)
  | exceptional j =>
    by_cases he : gamma = beta
    · subst gamma
      by_cases hij : i = j
      · subst j
        exact Or.inl ⟨rfl, rfl⟩
      · have hz := exceptional_coefficient i j beta hbeta
        rw [if_neg hij] at hz
        exact (hc hz).elim
    · right
      have hsplit : gamma + (beta - gamma) = beta := by
        funext k
        exact Nat.add_sub_of_le (hle k)
      have hz : beta - gamma ≠ 0 := by
        intro hzero
        rw [hzero, add_zero] at hsplit
        exact he hsplit
      exact SurfaceGenusTwoBlowupOrder.earlier_of_energy_lt X _ _
        (hle (Fin.last X.blowups)) rfl (X.energy_lt_of_add_eq hsplit hz)

/-- The distinguished exceptional coefficient is uniformly minus eighteen. -/
theorem exceptional_coefficient_self (i : Fin X.blowups) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta) :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X (X.effective.energy beta - 1)
        beta 0 (SurfaceGenusZero.pointLabels
          (![.exceptional i, .exceptional i, .exceptional i] : Fin 3 → SurfaceBasisLabel X)
          (X.effective.energy beta - 1)))
      {Sum.inr (SurfaceFirstDescendant.query 2 beta (.exceptional i)
        (X.effective.energy beta))} = -18 := by
  simpa only [ite_true] using exceptional_coefficient i i beta hbeta

/-- The actual full-row exceptional pivot is nonzero at every positive-energy
full class, without any restriction on plane degree or signed multiplicity. -/
theorem exceptional_coefficient_ne_zero (i : Fin X.blowups) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta) :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X (X.effective.energy beta - 1)
        beta 0 (SurfaceGenusZero.pointLabels
          (![.exceptional i, .exceptional i, .exceptional i] : Fin 3 → SurfaceBasisLabel X)
          (X.effective.energy beta - 1)))
      {Sum.inr (SurfaceFirstDescendant.query 2 beta (.exceptional i)
        (X.effective.energy beta))} ≠ 0 := by
  rw [exceptional_coefficient_self i beta hbeta]
  norm_num

end AxiomaticGW.SurfaceGenusTwoBlowupKCoefficients

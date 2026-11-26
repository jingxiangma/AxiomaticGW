/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupPCoefficients

/-!
# The same-class primary column of the BP HHH row

The complete BP HHH row has zero coefficient at its own canonical genus-two
primary point request. The proof follows the actual four genus-two diagrams
and six marking assignments, with the complete normalizer on the left.

At zero effective remainder, a new cotangent tail carrying a point and a
nonunit old state is zero by its classical rational dimension. Positive
calibration tails cannot contribute at the original full class. Neither
argument removes primary tails at different effective classes, which remain
part of the normalized polynomial and require separate support analysis.

For a hyperplane first-power input, an additional identity cancels calibration
coefficients at the same plane degree: degree-zero tails have a zero hyperplane
input column. Calibration tails that lower plane degree are retained.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupPPrimary
open SurfacePolynomialReduction SurfaceGenusTwo GluingExpression
open SurfaceGenusTwoBlowupPCoefficients
variable {X : SurfaceTarget}

set_option maxRecDepth 20000

private theorem classical_tail_zero (n : ℕ) (b c : SurfaceBasisLabel X)
    (hc : c ≠ .unit) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) 0 n
      (Option.elim · b (fun t : Bool ↦ if t then .point else c)) = 0 := by
  have hcod : 0 < c.codimension := by
    cases c <;> first | exact (hc rfl).elim | exact Nat.zero_lt_succ _
  simp only [SurfaceBasisLabel.codimension] at hcod
  have hd : ¬((((∑ s : Option Bool,
      ((Option.elim · b (fun t : Bool ↦ if t then .point else c)) s).codimension : ℕ) : ℤ)
      + (n : ℤ)) = X.c1Degree 0 - 1 + (Fintype.card (Option Bool) : ℤ)) := by
    simp only [Fintype.sum_option, Fintype.sum_bool, Option.elim_none, Option.elim_some,
      Bool.false_eq_true, ite_true, ite_false, SurfaceBasisLabel.codimension, Fintype.card_option,
      Fintype.card_bool, map_zero]
    omega
  rw [SurfaceGenusZero.primaryScalar,
    if_neg (fun h ↦ h.1 rfl), if_neg hd]

/-- At zero remainder, the actual first-power tail carrying a nonunit old state
is zero for every terminal family, including primary requests. -/
theorem remainderContraction_onePsi_zero_of_ne_unit (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (n : ℕ) (a : S → SurfaceBasisLabel X) (hs : a s ≠ .unit) :
    let z := CotangentTerm.tail h (Pi.single s 1) s
    remainderContraction X v main z.expression z.decoration z.labels
      0 n (Option.elim · .point a) = 0 := by
  have hd : Function.update (Pi.single s 1 : S → ℕ) s
      ((Pi.single s 1 : S → ℕ) s - 1) = (0 : S → ℕ) := by
    funext t
    by_cases ht : t = s
    · subst t
      simp only [Function.update_self, Pi.single_eq_same, Nat.sub_self, Pi.zero_apply]
    · rw [Function.update_of_ne ht, Pi.single_eq_of_ne ht]
      rfl
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b (((Option.elim · SurfaceBasisLabel.point a) ∘
        PsiBoundaryExpansion.tailLabels s) ∘ Sum.inr)) =
        (Option.elim · b (fun t : Bool ↦ if t then .point else a s)) := by
    funext t
    rcases t with _ | (_ | _) <;> rfl
  have hz : (fun _ : Option Bool ↦ (0 : ℕ)) = 0 := rfl
  dsimp only
  simp only [CotangentTerm.tail, CotangentTerm.relabel, CotangentTerm.separating,
    CotangentTerm.fundamental, remainderContraction, ite_true, hd,
    primaryPointVertex_eq, GluingExpression.pointContraction,
    hz, vertex_primary_genusZero_eq, hr]
  rw [(X.splittings_eq 0).trans X.effective.splittings_zero]
  simp only [Finset.sum_singleton, classical_tail_zero _ _ _ hs,
    mul_zero, Finset.sum_const_zero]

/-- A nonunit first power receives no classical correction at zero remainder.
The full normalized terminal expression, including its calibration tails, is retained. -/
theorem remainderVertex_onePsi_zero_of_ne_unit (v : Variable X) (n : ℕ)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (a : S → SurfaceBasisLabel X) (hs : a s ≠ .unit) :
    remainderVertex X v (coefficientVertex X v) n 2 S h (Pi.single s 1)
      inferInstance 0 a =
      RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
        (residualTerms ((SurfaceAncestorKey.ofLabels 2 S h
          (SurfaceGenusZero.variableCurve v) (Pi.single s 1) a).addPoints n))) {v} := by
  induction n generalizing S with
  | zero =>
    simp only [remainderVertex, add_zero, coefficientVertex, ite_true, vertexTerms,
      SurfaceAncestorKey.addPoints_zero]
  | succ n ih =>
    rw [remainderVertex_onePsi_step,
      remainderContraction_onePsi_zero_of_ne_unit v _ S h s n a hs, sub_zero]
    rw [ih (Option S) h.option (some s) (Option.elim · .point a)
      (show (Option.elim · .point a) (some s) ≠ .unit from hs)]
    have hk : (Pi.single (some s) 1 : Option S → ℕ) =
        (Option.elim · 0 (Pi.single s 1)) := by
      funext t
      cases t with
      | none => simp only [Option.elim_none, Pi.single_eq_of_ne
          (show (none : Option S) ≠ some s from by intro he; cases he)]
      | some t =>
        by_cases ht : t = s
        · subst t
          simp only [Option.elim_some, Pi.single_eq_same]
        · simp only [Option.elim_some, Pi.single_eq_of_ne ht,
            Pi.single_eq_of_ne (fun he ↦ ht (Option.some.inj he))]
    rw [hk, SurfaceAncestorKey.addPoints_ofLabels_option_powers 2 S h
      (SurfaceGenusZero.variableCurve v) (Pi.single s 1) a n]

/-- Calibration can be omitted when extracting an input-class coefficient, including
a primary one. Other-class primary coefficients are not covered by this identity. -/
theorem coefficient_residualTerms_eq_direct_at_class (v : Variable X)
    (q : SurfaceAncestorKey X) (hg : q.genus = 2)
    (hb : SurfaceGenusZero.variableCurve v = q.beta) :
    RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
      (residualTerms q)) {v} =
      if q.DimensionCompatible then RationalTerms.coefficient (directNormalizedTerms q) {v}
      else 0 := by
  unfold residualTerms
  by_cases hd : q.DimensionCompatible
  · rw [if_pos hd, if_neg (by omega : ¬q.genus ≤ 1), if_pos hd,
      RationalTerms.coefficient_affineSubstitute_term, Multiset.map_singleton,
      Multiset.sum_singleton, one_mul,
      coefficient_normalizedTerms_eq_direct q v hb]
  · rw [if_neg hd, if_neg hd, RationalTerms.coefficient_affineSubstitute_zero]

/-- A dimension-filtered first descendant cannot equal a primary point request
at any full effective class. -/
theorem coefficient_dimensionTerms_primary_zero (beta gamma : X.Curve)
    (b : SurfaceBasisLabel X) (n m : ℕ) :
    RationalTerms.coefficient (RationalTerms.rename (Sum.inr : SurfaceQuery X → Variable X)
      (SurfaceFirstDescendant.dimensionTerms (SurfaceFirstDescendant.query 2 beta b n)))
      {Sum.inr (SurfaceQuery.points X 2 gamma m)} = 0 := by
  rw [SurfaceFirstDescendant.dimensionTerms]
  split_ifs
  · rw [RationalTerms.coefficient_rename_term]
    simp only [Multiset.map_singleton, Multiset.singleton_inj]
    exact if_neg (Ne.symm (SurfaceFirstDescendant.query_ne_points beta gamma b n m))
  · rw [RationalTerms.rename_zero, RationalTerms.coefficient_zero]

/-- With no unit reduction or divisor correction, a first-descendant normal form
has zero coefficient at every primary point request, including other classes. -/
theorem coefficient_terms_primary_zero (beta gamma : X.Curve)
    (b : SurfaceBasisLabel X) (m : Multiset (SurfaceBasisLabel X)) (k : ℕ)
    (hu : .unit ∉ m) (hb : b ≠ .unit)
    (hc : SurfaceFirstDescendant.correctionCoefficient beta b m = 0) :
    RationalTerms.coefficient (RationalTerms.rename (Sum.inr : SurfaceQuery X → Variable X)
      (SurfaceFirstDescendant.terms 2 beta b m))
      {Sum.inr (SurfaceQuery.points X 2 gamma k)} = 0 := by
  rw [SurfaceFirstDescendant.terms, if_neg hu, if_neg hb,
    RationalTerms.coefficient_rename_add, RationalTerms.coefficient_rename_scale,
    RationalTerms.coefficient_rename_scale, coefficient_dimensionTerms_primary_zero, hc]
  simp only [mul_zero, zero_mul, add_zero]

/-- Both psi positions of the actual H/point main pair have zero coefficient
at every primary point request of their full input class. -/
theorem pair_main_primary_zero (beta : X.Curve) (m n : ℕ) (s : Fin 2) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 beta m)
    remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0
      ![.hyperplane, .point] = 0 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 beta m)
  have hs : (![.hyperplane, .point] : Fin 2 → SurfaceBasisLabel X) s ≠ .unit := by
    fin_cases s <;> intro he <;> cases he
  dsimp only
  rw [remainderVertex_onePsi_zero_of_ne_unit v n (Fin 2) _ s _ hs,
    coefficient_residualTerms_eq_direct_at_class v _ rfl rfl]
  split_ifs with hd
  · change RationalTerms.coefficient (directNormalizedTerms
        ((SurfaceAncestorKey.ofLabels 2 (Fin 2) (by norm_num [StableArity]) beta
          (Pi.single s 1) ![.hyperplane, .point]).addPoints n))
        {Sum.inr (SurfaceQuery.points X 2 beta m)} = 0
    rw [directNormalizedTerms_onePsi_ofLabels 2 le_rfl (Fin 2) _ s beta
      (![.hyperplane, .point] : Fin 2 → SurfaceBasisLabel X) n]
    have h0 : ((Finset.univ.erase (0 : Fin 2)).val.map
        (![.hyperplane, .point] : Fin 2 → SurfaceBasisLabel X)) = {.point} := rfl
    have h1 : ((Finset.univ.erase (1 : Fin 2)).val.map
        (![.hyperplane, .point] : Fin 2 → SurfaceBasisLabel X)) = {.hyperplane} := rfl
    rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
    · rw [h0, Matrix.cons_val_zero]
      apply coefficient_terms_primary_zero
      · simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton,
          reduceCtorEq, and_false, or_self, not_false_eq_true]
      · intro he
        cases he
      · simp only [SurfaceFirstDescendant.correctionCoefficient,
          SurfaceFirstDescendant.divisorSquare, Multiset.count_add,
          Multiset.count_replicate, Multiset.count_singleton, reduceCtorEq,
          ite_false, zero_add, Nat.cast_zero, mul_zero, zero_mul]
    · rw [h1, Matrix.cons_val_one, Matrix.cons_val_zero]
      apply coefficient_terms_primary_zero
      · simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton,
          reduceCtorEq, and_false, or_self, not_false_eq_true]
      · intro he
        cases he
      · simp only [SurfaceFirstDescendant.correctionCoefficient,
          SurfaceFirstDescendant.divisorSquare, zero_mul]
  · rfl

private theorem paper_one (v : Variable X) (n : ℕ)
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

private theorem paper_pair (v : Variable X) (n : ℕ) (s : Fin 2)
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

private theorem classical_h_node_point (n : ℕ) (b : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) 0 n
      (![.hyperplane, b, .point] : Fin 3 → _) = 0 := by
  have hd : ¬((((∑ i : Fin 3,
      ((![.hyperplane, b, .point] : Fin 3 → SurfaceBasisLabel X) i).codimension : ℕ) : ℤ)
      + (n : ℤ)) = X.c1Degree 0 - 1 + (Fintype.card (Fin 3) : ℤ)) := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, SurfaceBasisLabel.codimension, Fintype.card_fin, map_zero]
    change ¬(((1 + b.codimension + 2 : ℕ) : ℤ) + (n : ℤ) = 0 - 1 + 3)
    omega
  rw [SurfaceGenusZero.primaryScalar, if_neg (fun h ↦ h.1 rfl), if_neg hd]

private theorem inner_h_point_zero (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ) (n : ℕ) (k : Fin 1 → ℕ) :
    remainderContraction X v main
      (GetzlerGraphs.join (m := 0) (n := 2) 0 1
        (fundamental 2 (Fin 1) (by norm_num [StableArity]))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (by exact (k, (0 : Fin 3 → ℕ)))
      (by exact ((inferInstance : DecidableEq (Fin 1)),
        (inferInstance : DecidableEq (Fin 3)))) 0 n ![.hyperplane, .point] = 0 := by
  simp only [GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction]
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b (((![.hyperplane, .point] : Fin 2 → SurfaceBasisLabel X) ∘
        (finSumFinEquiv : Fin 0 ⊕ Fin 2 ≃ Fin 2)) ∘ Sum.inr)) ∘
        finSuccEquiv' 1 = ![.hyperplane, b, .point] := by
    funext i
    fin_cases i <;> rfl
  simp only [hr, primaryPointVertex, and_self, ite_true]
  rw [(X.splittings_eq 0).trans X.effective.splittings_zero]
  simp only [Finset.sum_singleton]
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [classical_h_node_point]
  simp only [mul_zero]

private theorem paper_zero (v : Variable X) (n : ℕ) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 0) 0 n
        ![.hyperplane, .hyperplane, .hyperplane] = 0 := by
  have hz : (![0, 0, 0] : Fin 3 → ℕ) = 0 := by decide +kernel
  have he : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 0) 0 n
        ![.hyperplane, .hyperplane, .hyperplane] =
      remainderContraction X v (remainderVertex X v (coefficientVertex X v))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          (GetzlerGraphs.join (m := 0) (n := 2) 0 1
            (fundamental 2 (Fin 1) (by norm_num [StableArity]))
            (fundamental 0 (Fin 3) (by norm_num [StableArity])))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        ((![0], (0 : Fin 3 → ℕ)), (0 : Fin 3 → ℕ))
        (((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 3))),
          (inferInstance : DecidableEq (Fin 3))) 0 n
        ![.hyperplane, .hyperplane, .hyperplane] := by
    rw [remainderPointCoefficient, if_pos (by decide +kernel)]
    change remainderContraction X v (remainderVertex X v (coefficientVertex X v))
      (GetzlerGraphs.join (m := 1) (n := 2) 1 2
        (GetzlerGraphs.join (m := 0) (n := 2) 0 1
          (fundamental 2 (Fin 1) (by norm_num [StableArity]))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      ((![0], ![0, 0, 0]), ![0, 0, 0]) _ 0 n
        ![.hyperplane, .hyperplane, .hyperplane] = _
    rw [hz]
    rfl
  exact he.trans ((pair_hh_zero v (remainderVertex X v (coefficientVertex X v)) n
    (GetzlerGraphs.join (m := 0) (n := 2) 0 1
      (fundamental 2 (Fin 1) (by norm_num [StableArity]))
      (fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (![0], (0 : Fin 3 → ℕ))
    ((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 3)))
    .hyperplane).trans (inner_h_point_zero v _ n ![0]))

private theorem remainder_orbit (v : Variable X) (n : ℕ)
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

/-- The actual compressed BP row has no primary point coefficient at its own
full curve class. This algebraic vanishing holds at any marking count. -/
theorem pointCoefficient_primary_at_requested_class (beta : X.Curve) (m n : ℕ) :
    BelorousskiPandharipande.pointCoefficient X n beta
      ![.hyperplane, .hyperplane, .hyperplane]
      (.inr (SurfaceQuery.points X 2 beta m)) = 0 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 beta m)
  have hterm (i : Fin 20) (e : Fin 6) :
      SurfaceGenusTwo.pointCoefficient X v (BelorousskiPandharipande.orbitCotangentTerm i e)
        beta n ![.hyperplane, .hyperplane, .hyperplane] =
      remainderPointCoefficient X v (coefficientVertex X v)
        (BelorousskiPandharipande.paperCotangentTerm i) 0 n
          ![.hyperplane, .hyperplane, .hyperplane] := by
    have h := remainderPointCoefficient_eq X v (coefficientVertex X v) rfl
      (BelorousskiPandharipande.orbitCotangentTerm i e) 0 n
      (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
    rw [remainder_orbit, hhh_permutation] at h
    simpa only [add_zero, v, SurfaceGenusZero.variableCurve, SurfaceQuery.points] using h.symm
  change BelorousskiPandharipande.pointCoefficient X n beta
    ![.hyperplane, .hyperplane, .hyperplane] v = 0
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
        ![.hyperplane, .hyperplane, .hyperplane]) = 0
  rw [paper_zero, paper_one]
  have h2 := paper_pair v n (0 : Fin 2) .hyperplane
  have h3 := paper_pair v n (1 : Fin 2) .hyperplane
  simp only [ite_true, if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h2 h3
  rw [h2, h3, pair_main_primary_zero beta m n 0, pair_main_primary_zero beta m n 1]
  ring

/-- Exact binding to the complete normalized BP row. Its different-class
primary calibration and cotangent tails are not removed by this theorem. -/
theorem normalized_primary_at_requested_class (beta : X.Curve) (m n : ℕ) :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X n beta 0
        (SurfaceGenusZero.pointLabels
          (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) n))
      {Sum.inr (SurfaceQuery.points X 2 beta m)} = 0 := by
  rw [← BelorousskiPandharipande.pointCoefficient_eq_full]
  exact pointCoefficient_primary_at_requested_class beta m n

/-- Positive energy gives the exact BP marking condition and the zero
coefficient of the dimension-compatible canonical primary N request. -/
theorem canonical_primary_row (beta : X.Curve) (hbeta : 0 < X.effective.energy beta) :
    X.effective.energy beta = (X.effective.energy beta - 1) + 1 ∧
      RationalTerms.coefficient
        (BelorousskiPandharipande.normalizedGenusTwoTerms X (X.effective.energy beta - 1)
          beta 0 (SurfaceGenusZero.pointLabels
            (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
            (X.effective.energy beta - 1)))
        {Sum.inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))} = 0 :=
  ⟨SurfaceGenusTwoBlowupPCoefficients.pointCount_dimension beta hbeta,
    normalized_primary_at_requested_class beta _ _⟩

/-- The entire hyperplane input column of first calibration vanishes at plane
degree zero, including the zero class. Mixed and multiple exceptional classes
are included; no point invariant or geometric support assumption is used. -/
theorem firstCalibrationMatrix_hyperplane_eq_zero (gamma : X.Curve)
    (hd : X.planeDegree gamma = 0) (row : SurfaceBasisLabel X) :
    SurfaceDescendant.firstCalibrationMatrix X gamma row .hyperplane = 0 := by
  unfold SurfaceDescendant.firstCalibrationMatrix SurfaceGenusZero.primaryValue
  by_cases hz : gamma = 0
  · rw [if_pos hz]
    have hc : (((Finset.univ : Finset (Fin 2)).val.map
        (![row.dual, .hyperplane] : Fin 2 → SurfaceBasisLabel X))).card = 2 := by
      simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
    rw [SurfacePrimary.classicalValue, hc, if_neg (by decide : (2 : ℕ) ≠ 3), mul_zero]
  · rw [if_neg hz]
    have hh : (SurfaceBasisLabel.hyperplane : SurfaceBasisLabel X).primaryFactor gamma = 0 := by
      change (X.divisorIntersections gamma 0 : ℚ) = 0
      rw [← X.planeDegree_eq_divisorIntersections gamma, hd]
      rfl
    have hv : (((Finset.univ : Finset (Fin 2)).val.map
        (![row.dual, .hyperplane] : Fin 2 → SurfaceBasisLabel X)).map
        (SurfaceBasisLabel.primaryFactor gamma)).prod = 0 := by
      simp only [Multiset.map_map, Function.comp_def, ← Finset.prod_eq_multiset_prod,
        Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hh, mul_zero]
    rw [hv, zero_mul, ite_self, mul_zero]

/-- Hyperplane first-power calibration does not transfer a coefficient to a
different class of the same plane degree. Positive-degree tails still remain.
This is an identity of coefficients of the full normalizer, not a pruning rule. -/
theorem coefficient_normalizedTerms_hyperplane_same_planeDegree (q : SurfaceAncestorKey X)
    (v : Variable X) (h : 2 ≤ q.genus ∧ q.totalPsi = 1)
    (hh : (q.onePsiInsertion h.2).label = .hyperplane)
    (hd : X.planeDegree (SurfaceGenusZero.variableCurve v) = X.planeDegree q.beta) :
    RationalTerms.coefficient (normalizedTerms q) {v} =
      RationalTerms.coefficient (directNormalizedTerms q) {v} := by
  unfold normalizedTerms directNormalizedTerms
  rw [dif_pos h, dif_pos h, RationalTerms.coefficient_add]
  suffices hc : RationalTerms.coefficient
      (∑ split ∈ X.positiveTailSplittings q.beta, ∑ b : SurfaceBasisLabel X,
        RationalTerms.scale
          (-SurfaceDescendant.firstCalibrationMatrix X split.2 b
            (q.orderedLabels (q.onePsiMark h.2)))
          (canonicalPrimaryTerms (SurfaceAncestorKey.ofLabels q.genus
            (Fin q.orderedInsertions.length) q.ordered_stable split.1 0
            (Function.update q.orderedLabels (q.onePsiMark h.2) b)))) {v} = 0 by
    rw [hc, add_zero]
  rw [RationalTerms.coefficient_sum]
  apply Finset.sum_eq_zero
  intro split hs
  rw [RationalTerms.coefficient_sum]
  apply Finset.sum_eq_zero
  intro b _
  rw [RationalTerms.coefficient_scale]
  by_cases hb : SurfaceGenusZero.variableCurve v = split.1
  · have hsplit : split.1 + split.2 = q.beta := by
      have hmem := (Finset.mem_filter.mp hs).1
      rw [X.splittings_eq] at hmem
      exact (X.effective.mem_splittings _ _ _).mp hmem
    have hz : X.planeDegree split.2 = 0 := by
      have he := congrArg X.planeDegree hsplit
      rw [map_add] at he
      rw [hb] at hd
      omega
    change -(SurfaceDescendant.firstCalibrationMatrix X split.2 b
      (q.onePsiInsertion h.2).label) * _ = 0
    rw [hh, firstCalibrationMatrix_hyperplane_eq_zero split.2 hz b, neg_zero, zero_mul]
  · rw [coefficient_canonicalPrimaryTerms_eq_zero
      (SurfaceAncestorKey.ofLabels q.genus (Fin q.orderedInsertions.length) q.ordered_stable
        split.1 0 (Function.update q.orderedLabels (q.onePsiMark h.2) b)) h.1 v hb, mul_zero]

end AxiomaticGW.SurfaceGenusTwoBlowupPPrimary

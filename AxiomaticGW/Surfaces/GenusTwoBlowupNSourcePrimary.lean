/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupPPrimary
public import AxiomaticGW.Surfaces.GenusTwoBlowupNRelation
/-!
# Source-class primary vanishing in the blowup BP equations

For any three divisor basis labels, the original full normalized BP equation
has zero coefficient at every primary point request in its own full class.
This is uniform in both point counts, including class zero. No positive-energy
or sign premise is needed.

At zero effective remainder the outer rational triple forces a point node.
The primary-main chain then vanishes by its classical dimension; either
cotangent position on the divisor/point main pair has no primary correction.
The four-point rational component also vanishes. These facts cover the actual
four genus-two diagrams and all six marking assignments. The full normalizer
is retained, and positive calibration tails cannot return to the source class.

The combined N relation consequently has no source-class primary coefficient.
Its requested shifted pivot and other equal-degree dependencies require
separate proofs.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupNSourcePrimary
open SurfacePolynomialReduction SurfaceGenusTwo GluingExpression
open SurfaceGenusTwoBlowupPCoefficients SurfaceGenusTwoBlowupPPrimary
set_option maxRecDepth 20000
variable {X : SurfaceTarget}

private theorem pair_exceptional_main_primary_zero (i : Fin X.blowups)
    (beta : X.Curve) (m n : ℕ) (s : Fin 2) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 beta m)
    remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0
      ![.exceptional i, .point] = 0 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 beta m)
  have hs : (![.exceptional i, .point] : Fin 2 → SurfaceBasisLabel X) s ≠ .unit := by
    fin_cases s <;> intro he <;> cases he
  dsimp only
  rw [remainderVertex_onePsi_zero_of_ne_unit v n (Fin 2) _ s _ hs,
    coefficient_residualTerms_eq_direct_at_class v _ rfl rfl]
  split_ifs with hd
  · change RationalTerms.coefficient (directNormalizedTerms
        ((SurfaceAncestorKey.ofLabels 2 (Fin 2) (by norm_num [StableArity]) beta
          (Pi.single s 1) ![.exceptional i, .point]).addPoints n))
        {Sum.inr (SurfaceQuery.points X 2 beta m)} = 0
    rw [directNormalizedTerms_onePsi_ofLabels 2 le_rfl (Fin 2) _ s beta
      (![.exceptional i, .point] : Fin 2 → SurfaceBasisLabel X) n]
    have h0 : ((Finset.univ.erase (0 : Fin 2)).val.map
        (![.exceptional i, .point] : Fin 2 → SurfaceBasisLabel X)) = {.point} := rfl
    have h1 : ((Finset.univ.erase (1 : Fin 2)).val.map
        (![.exceptional i, .point] : Fin 2 → SurfaceBasisLabel X)) = {.exceptional i} := rfl
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

private theorem classical_divisor_node_point (a : SurfaceBasisLabel X)
    (ha : a.codimension = 1) (n : ℕ) (b : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) 0 n
      (![a, b, .point] : Fin 3 → _) = 0 := by
  have hd : ¬((((∑ i : Fin 3,
      ((![a, b, .point] : Fin 3 → SurfaceBasisLabel X) i).codimension : ℕ) : ℤ)
      + (n : ℤ)) = X.c1Degree 0 - 1 + (Fintype.card (Fin 3) : ℤ)) := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Fintype.card_fin, map_zero]
    change ¬(((a.codimension + b.codimension + 2 : ℕ) : ℤ) + (n : ℤ) = 0 - 1 + 3)
    rw [ha]
    omega
  rw [SurfaceGenusZero.primaryScalar, if_neg (fun h ↦ h.1 rfl), if_neg hd]

private theorem inner_divisor_point_zero (a : SurfaceBasisLabel X) (ha : a.codimension = 1)
    (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ) (n : ℕ) (k : Fin 1 → ℕ) :
    remainderContraction X v main
      (GetzlerGraphs.join (m := 0) (n := 2) 0 1
        (fundamental 2 (Fin 1) (by norm_num [StableArity]))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (by exact (k, (0 : Fin 3 → ℕ)))
      (by exact ((inferInstance : DecidableEq (Fin 1)),
        (inferInstance : DecidableEq (Fin 3)))) 0 n ![a, .point] = 0 := by
  simp only [GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction]
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b (((![a, .point] : Fin 2 → SurfaceBasisLabel X) ∘
        (finSumFinEquiv : Fin 0 ⊕ Fin 2 ≃ Fin 2)) ∘ Sum.inr)) ∘
        finSuccEquiv' 1 = ![a, b, .point] := by
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
  rw [classical_divisor_node_point a ha]
  simp only [mul_zero]


private theorem pair_divisor_main_primary_zero (a : SurfaceBasisLabel X) (ha : a.codimension = 1)
    (beta : X.Curve) (m n : ℕ) (s : Fin 2) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 beta m)
    remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0 ![a, .point] = 0 := by
  cases a with
  | unit => cases ha
  | hyperplane => exact pair_main_primary_zero beta m n s
  | exceptional i => exact pair_exceptional_main_primary_zero i beta m n s
  | point => cases ha

private theorem classical_divisor_pair_node_zero (a b t : SurfaceBasisLabel X)
    (ha : a.codimension = 1) (hb : b.codimension = 1) (ht : t ≠ .unit) (n : ℕ) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) 0 n
      (![a, b, t] : Fin 3 → _) = 0 := by
  have hc : 0 < t.codimension := by
    cases t <;> first | exact (ht rfl).elim | exact Nat.zero_lt_succ _
  have hd : ¬((((∑ j : Fin 3,
      ((![a, b, t] : Fin 3 → SurfaceBasisLabel X) j).codimension : ℕ) : ℤ)
      + (n : ℤ)) = X.c1Degree 0 - 1 + (Fintype.card (Fin 3) : ℤ)) := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Fintype.card_fin, map_zero]
    change ¬(((a.codimension + b.codimension + t.codimension : ℕ) : ℤ) + (n : ℤ) = 0 - 1 + 3)
    rw [ha, hb]
    omega
  rw [SurfaceGenusZero.primaryScalar, if_neg (fun h ↦ h.1 rfl), if_neg hd]

private theorem pair_join_divisors_zero (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ) (n : ℕ)
    (x : GluingExpression 2 (Fin 2)) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (a b c : SurfaceBasisLabel X) (hb : b.codimension = 1) (hc : c.codimension = 1)
    (hmain : ∀ m, remainderContraction X v main x d l 0 m ![a, .point] = 0) :
    let y := GetzlerGraphs.join (m := 1) (n := 2) 1 2 x
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
    remainderContraction X v main y (by exact (d, (0 : Fin 3 → ℕ)))
      (by exact (l, (inferInstance : DecidableEq (Fin 3)))) 0 n ![a, b, c] = 0 := by
  dsimp only
  rw [pair_join, (X.splittings_eq 0).trans X.effective.splittings_zero]
  simp only [Finset.sum_singleton]
  apply Finset.sum_eq_zero
  intro t _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  by_cases ht : t = .point
  · subst t
    rw [hmain]
    simp only [zero_mul, mul_zero]
  · have hdu : t.dual ≠ .unit := by cases t <;> first | exact (ht rfl).elim | intro h; cases h
    rw [classical_divisor_pair_node_zero b c t.dual hb hc hdu]
    simp only [mul_zero]

private theorem paper_zero_divisors (v : Variable X) (n : ℕ)
    (a b c : SurfaceBasisLabel X) (ha : a.codimension = 1)
    (hb : b.codimension = 1) (hc : c.codimension = 1) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 0) 0 n
        ![a, b, c] = 0 := by
  have hz : (![0, 0, 0] : Fin 3 → ℕ) = 0 := by decide +kernel
  have he : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 0) 0 n
        ![a, b, c] =
      remainderContraction X v (remainderVertex X v (coefficientVertex X v))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          (GetzlerGraphs.join (m := 0) (n := 2) 0 1
            (fundamental 2 (Fin 1) (by norm_num [StableArity]))
            (fundamental 0 (Fin 3) (by norm_num [StableArity])))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        ((![0], (0 : Fin 3 → ℕ)), (0 : Fin 3 → ℕ))
        (((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 3))),
          (inferInstance : DecidableEq (Fin 3))) 0 n
        ![a, b, c] := by
    rw [remainderPointCoefficient, if_pos (by decide +kernel)]
    change remainderContraction X v (remainderVertex X v (coefficientVertex X v))
      (GetzlerGraphs.join (m := 1) (n := 2) 1 2
        (GetzlerGraphs.join (m := 0) (n := 2) 0 1
          (fundamental 2 (Fin 1) (by norm_num [StableArity]))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      ((![0], ![0, 0, 0]), ![0, 0, 0]) _ 0 n
        ![a, b, c] = _
    rw [hz]
    rfl
  exact he.trans (pair_join_divisors_zero v (remainderVertex X v (coefficientVertex X v)) n
    (GetzlerGraphs.join (m := 0) (n := 2) 0 1
      (fundamental 2 (Fin 1) (by norm_num [StableArity]))
      (fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (![0], (0 : Fin 3 → ℕ))
    ((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 3)))
    a b c hb hc (fun m ↦ inner_divisor_point_zero a ha v _ m ![0]))

private theorem paper_pair_primary_divisors (beta : X.Curve) (m n : ℕ) (s : Fin 2)
    (a b c : SurfaceBasisLabel X) (ha : a.codimension = 1)
    (hb : b.codimension = 1) (hc : c.codimension = 1) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 beta m)
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) 0 n
        ![a, b, c] = 0 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 beta m)
  have h0 : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
  have h1 : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
  have hs : s = 0 ∨ s = 1 := by omega
  have he : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) 0 n
        ![a, b, c] =
      remainderContraction X v (remainderVertex X v (coefficientVertex X v))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          (fundamental 2 (Fin 2) (by norm_num [StableArity]))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        (by exact (Pi.single s 1, (0 : Fin 3 → ℕ)))
        (by exact ((inferInstance : DecidableEq (Fin 2)),
          (inferInstance : DecidableEq (Fin 3)))) 0 n ![a, b, c] := by
    rcases hs with rfl | rfl
    · rw [if_pos rfl, ← h0]
      rfl
    · rw [if_neg (by decide : (1 : Fin 2) ≠ 0), ← h1]
      rfl
  dsimp only
  rw [he]
  apply pair_join_divisors_zero v _ n _ _ _ a b c hb hc
  intro k
  change remainderVertex X v (coefficientVertex X v) k 2 (Fin 2)
    (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0 ![a, .point] = 0
  exact pair_divisor_main_primary_zero a ha beta m k s

private theorem paper_primary_divisors (beta : X.Curve) (m n : ℕ) (j : Fin 4)
    (a : Fin 3 → SurfaceBasisLabel X) (ha : ∀ t, (a t).codimension = 1) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 beta m)
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (j.castAdd 16)) 0 n a = 0 := by
  have hea : a = ![a 0, a 1, a 2] := by funext t; fin_cases t <;> rfl
  fin_cases j
  · rw [hea]
    exact paper_zero_divisors _ n (a 0) (a 1) (a 2) (ha 0) (ha 1) (ha 2)
  · exact SurfaceGenusTwoBlowupPCoefficients.paper_one _ n a
  · rw [hea]
    exact paper_pair_primary_divisors beta m n 0 (a 0) (a 1) (a 2) (ha 0) (ha 1) (ha 2)
  · rw [hea]
    exact paper_pair_primary_divisors beta m n 1 (a 0) (a 1) (a 2) (ha 0) (ha 1) (ha 2)


/-- Every primary source-class coefficient in the original four-diagram expansion vanishes. -/
theorem pointCoefficient_primary_divisors_at_class (beta : X.Curve) (m n : ℕ)
    (a : Fin 3 → SurfaceBasisLabel X) (ha : ∀ t, (a t).codimension = 1) :
    BelorousskiPandharipande.pointCoefficient X n beta a
      (.inr (SurfaceQuery.points X 2 beta m)) = 0 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 beta m)
  have hterm (j : Fin 4) (e : Fin 6) :
      SurfaceGenusTwo.pointCoefficient X v
        (BelorousskiPandharipande.orbitCotangentTerm (j.castAdd 16) e) beta n a = 0 := by
    have h := remainderPointCoefficient_eq X v (coefficientVertex X v) rfl
      (BelorousskiPandharipande.orbitCotangentTerm (j.castAdd 16) e) 0 n a
    have hz : remainderPointCoefficient X v (coefficientVertex X v)
        (BelorousskiPandharipande.orbitCotangentTerm (j.castAdd 16) e) 0 n a = 0 := by
      rw [SurfaceGenusTwoBlowupPCoefficients.remainder_orbit]
      exact paper_primary_divisors beta m n j (a ∘ BelorousskiPandharipande.labelPermutation e)
        (fun t ↦ ha _)
    simpa only [add_zero, v, SurfaceGenusZero.variableCurve, SurfaceQuery.points] using
      h.symm.trans hz
  change BelorousskiPandharipande.pointCoefficient X n beta a v = 0
  simp only [BelorousskiPandharipande.pointCoefficient, hterm,
    Finset.sum_const_zero, mul_zero]

/-- Exact coefficient binding to the complete normalized BP equation. -/
theorem normalized_primary_divisors_at_class (beta : X.Curve) (m n : ℕ)
    (a : Fin 3 → SurfaceBasisLabel X) (ha : ∀ t, (a t).codimension = 1) :
    RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.bpRow X n beta a)
      {Sum.inr (SurfaceQuery.points X 2 beta m)} = 0 := by
  rw [SurfaceGenusTwoBlowupNRelation.bpRow,
    ← BelorousskiPandharipande.pointCoefficient_eq_full]
  exact pointCoefficient_primary_divisors_at_class beta m n a ha


/-- The four-relation N equation has no primary coefficient at its shifted source class. -/
theorem row_source_primary_eq_zero (i : Fin X.blowups) (beta : X.Curve) (m : ℕ) :
    RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row X i beta)
      {Sum.inr (SurfaceQuery.points X 2 (beta + X.exceptionalCurve i) m)} = 0 := by
  simp only [SurfaceGenusTwoBlowupNRelation.row, RationalTerms.coefficient_add,
    RationalTerms.coefficient_scale]
  have hh : ∀ t : Fin 3,
      ((![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) t).codimension =
        1 := by intro t; fin_cases t <;> rfl
  have hehh : ∀ t : Fin 3,
      ((![.exceptional i, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) t).codimension =
        1 := by intro t; fin_cases t <;> rfl
  have heeh : ∀ t : Fin 3,
      ((![.exceptional i, .exceptional i, .hyperplane] :
        Fin 3 → SurfaceBasisLabel X) t).codimension = 1 := by intro t; fin_cases t <;> rfl
  have heee : ∀ t : Fin 3,
      ((![.exceptional i, .exceptional i, .exceptional i] :
        Fin 3 → SurfaceBasisLabel X) t).codimension = 1 := by intro t; fin_cases t <;> rfl
  rw [normalized_primary_divisors_at_class _ m _ _ hehh,
    normalized_primary_divisors_at_class _ m _ _ heeh,
    normalized_primary_divisors_at_class _ m _ _ heee,
    normalized_primary_divisors_at_class _ m _ _ hh]
  ring

end AxiomaticGW.SurfaceGenusTwoBlowupNSourcePrimary

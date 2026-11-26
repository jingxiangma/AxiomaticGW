/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupNCoefficients
public import AxiomaticGW.Surfaces.GenusTwoBlowupNRelation

/-!
# Foreign exceptional remainders of the shifted primary BP row

For the complete combined N relation with labels `H` and `E_i`, an energy-one
remainder `E_j` with `j ≠ i` contributes zero to every requested variable at its
original full class. In particular, equal-plane-degree primary N couplings at
another full class cancel without identifying classes by their energy.

The actual four BP diagrams vanish separately. Positive rational components
carrying `H` or `E_i` have zero divisor factor at `E_j`. Their classical triples
insert only the point state, while classical quadruples vanish. The remaining
one-psi main components have a nonunit input different from `E_j`; their complete
normalization is zero because the exceptional first-calibration matrix has only
its own exceptional input column. Cotangent tails and dimension tests are kept.

All original constants, signs, marking assignments and primary tails remain on
the left. No geometric input, numerical seed or support hypothesis is added.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupNForeignSupport
open SurfacePolynomialReduction SurfaceGenusTwo GluingExpression
open SurfaceGenusTwoBlowupNEEEPrimary SurfaceGenusTwoBlowupPPrimarySupport
open SurfaceGenusTwoBlowupNCoefficients

set_option maxRecDepth 20000

variable {X : SurfaceTarget}

/-- A wrong exceptional input has zero complete normalized coefficient at the shifted class. -/
theorem coefficient_normalizedTerms_foreign_exceptional
    (j : Fin X.blowups) (gamma : X.Curve) (q : SurfaceAncestorKey X)
    (hg : q.genus = 2) (hp : q.totalPsi = 1)
    (hb : q.beta = gamma + X.exceptionalCurve j)
    (hh : (q.onePsiInsertion hp).label ≠ .exceptional j)
    (v : Variable X) (hv : SurfaceGenusZero.variableCurve v = gamma) :
    RationalTerms.coefficient (normalizedTerms q) {v} = 0 := by
  have h : 2 ≤ q.genus ∧ q.totalPsi = 1 := ⟨by omega, hp⟩
  have hn : SurfaceGenusZero.variableCurve v ≠ q.beta := by
    rw [hv, hb]
    intro he
    have he' := congrArg X.effective.energy he
    rw [X.energy_add_exceptionalCurve] at he'
    omega
  have hd := coefficient_directNormalizedTerms_eq_zero q h.1 v hn
  unfold directNormalizedTerms at hd
  unfold normalizedTerms
  rw [dif_pos h] at hd ⊢
  rw [RationalTerms.coefficient_add, hd, zero_add, RationalTerms.coefficient_sum]
  apply Finset.sum_eq_zero
  intro split hs
  rw [RationalTerms.coefficient_sum]
  apply Finset.sum_eq_zero
  intro b _
  rw [RationalTerms.coefficient_scale]
  by_cases hs1 : split.1 = gamma
  · have hs2 : split.2 = X.exceptionalCurve j := by
      have hc : split.1 + split.2 = q.beta := by
        rw [X.positiveTailSplittings_eq, X.effective.mem_positiveTailSplittings] at hs
        exact hs.1
      rw [hs1, hb] at hc
      exact add_left_cancel hc
    change -SurfaceDescendant.firstCalibrationMatrix X split.2 b
      (q.onePsiInsertion hp).label * _ = 0
    rw [hs2, firstCalibrationMatrix_exceptional_eq]
    have hm : ¬(b = .exceptional j ∧ (q.onePsiInsertion hp).label = .exceptional j) :=
      fun h ↦ hh h.2
    simp only [SurfaceFirstCalibration.exceptionalMatrix, if_neg hm, neg_zero, zero_mul]
  · apply mul_eq_zero_of_right
    apply coefficient_canonicalPrimaryTerms_eq_zero
      (SurfaceAncestorKey.ofLabels q.genus (Fin q.orderedInsertions.length)
        q.ordered_stable split.1 0 (Function.update q.orderedLabels (q.onePsiMark hp) b)) h.1 v
    change SurfaceGenusZero.variableCurve v ≠ split.1
    rw [hv]
    exact Ne.symm hs1

/-- The original residual dimension filter preserves the wrong-column vanishing. -/
theorem coefficient_residualTerms_foreign_exceptional (j : Fin X.blowups)
    (v : Variable X) (S : Type) [Fintype S] [DecidableEq S]
    (h : StableArity 2 S) (s : S) (a : S → SurfaceBasisLabel X)
    (hh : a s ≠ .exceptional j) (n : ℕ) :
    RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
      (residualTerms ((SurfaceAncestorKey.ofLabels 2 S h
        (SurfaceGenusZero.variableCurve v + X.exceptionalCurve j)
        (Pi.single s 1) a).addPoints n))) {v} = 0 := by
  let q := (SurfaceAncestorKey.ofLabels 2 S h
    (SurfaceGenusZero.variableCurve v + X.exceptionalCurve j) (Pi.single s 1) a).addPoints n
  have hi : (SurfaceAncestorKey.ofLabels 2 S h
      (SurfaceGenusZero.variableCurve v + X.exceptionalCurve j)
      (Pi.single s 1) a).insertions =
      ⟨a s, 1⟩ ::ₘ ((Finset.univ.erase s).val.map a).map (fun c ↦ ⟨c, 0⟩) := by
    have he : (Finset.univ : Finset S).val = s ::ₘ (Finset.univ.erase s).val := by
      rw [Finset.erase_val, Multiset.cons_erase (Finset.mem_univ s)]
    change (Finset.univ.val.map fun t ↦
      (⟨a t, (Pi.single s 1 : S → ℕ) t⟩ : SurfaceInsertion X)) = _
    rw [he, Multiset.map_cons, Pi.single_eq_same, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro t ht
    have hts : t ≠ s := (Finset.mem_erase.mp ht).1
    simp only [Pi.single_eq_of_ne hts, Function.comp_apply]
  have ha : q.insertions =
      ⟨a s, 1⟩ ::ₘ (Multiset.replicate n (SurfaceBasisLabel.point : SurfaceBasisLabel X) +
        (Finset.univ.erase s).val.map a).map (fun c ↦ ⟨c, 0⟩) := by
    simp only [q, SurfaceAncestorKey.addPoints, hi, Multiset.map_add, Multiset.map_replicate,
      Multiset.add_cons]
  have hp : q.totalPsi = 1 := by
    simp only [SurfaceAncestorKey.totalPsi, ha, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_map, Function.comp_def, Multiset.map_const', Multiset.sum_replicate,
      nsmul_zero, add_zero]
  have hpsi : q.onePsiInsertion hp = ⟨a s, 1⟩ := by
    have ht := q.onePsiInsertion_mem hp
    rw [ha, Multiset.mem_cons] at ht
    rcases ht with ht | ht
    · exact ht
    · obtain ⟨c, _, he⟩ := Multiset.mem_map.mp ht
      have hz := q.onePsiInsertion_power hp
      rw [← he] at hz
      cases hz
  change RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
    (residualTerms q)) {v} = 0
  unfold residualTerms
  by_cases hdim : q.DimensionCompatible
  · rw [if_pos hdim, if_neg (show ¬q.genus ≤ 1 from Nat.not_succ_le_self 1),
      RationalTerms.coefficient_affineSubstitute_term, Multiset.map_singleton,
      Multiset.sum_singleton, one_mul]
    apply coefficient_normalizedTerms_foreign_exceptional j
      (SurfaceGenusZero.variableCurve v) q rfl hp rfl _ v rfl
    rw [hpsi]
    exact hh
  · rw [if_neg hdim, RationalTerms.coefficient_affineSubstitute_zero]

/-- Every nonunit wrong exceptional input keeps zero coefficient after the actual
cotangent pullback, including every signed primary calibration tail. -/
theorem remainderVertex_foreign_onePsi_zero (j : Fin X.blowups)
    (v : Variable X) (n : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (h : StableArity 2 S) (s : S) (a : S → SurfaceBasisLabel X)
    (hu : a s ≠ .unit) (hh : a s ≠ .exceptional j) :
    remainderVertex X v (coefficientVertex X v) n 2 S h (Pi.single s 1)
      inferInstance (X.exceptionalCurve j) a = 0 := by
  have he : remainderVertex X v (coefficientVertex X v) n 2 S h (Pi.single s 1)
      inferInstance (X.exceptionalCurve j) a =
      RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
        (residualTerms ((SurfaceAncestorKey.ofLabels 2 S h
          (SurfaceGenusZero.variableCurve v + X.exceptionalCurve j)
          (Pi.single s 1) a).addPoints n))) {v} := by
    cases hs : a s with
    | unit => exact (hu hs).elim
    | hyperplane =>
        exact remainderVertex_onePsi_of_planeDegree_zero v n S h s _
          (X.planeDegree_exceptionalCurve j) a (Or.inl hs)
    | point =>
        exact remainderVertex_onePsi_of_planeDegree_zero v n S h s _
          (X.planeDegree_exceptionalCurve j) a (Or.inr hs)
    | exceptional i =>
        exact remainderVertex_exceptionalPsi_of_planeDegree_zero i v n S h s _
          (X.planeDegree_exceptionalCurve j) a hs
  rw [he, coefficient_residualTerms_foreign_exceptional j v S h s a hh n]

private theorem exceptional_ne_zero (j : Fin X.blowups) : X.exceptionalCurve j ≠ 0 := by
  intro he
  have he' := congrArg X.effective.energy he
  rw [X.energy_exceptionalCurve, map_zero] at he'
  cases he'

private theorem foreign_scalar_zero (i j : Fin X.blowups) (hij : i ≠ j)
    (S : Type) [Fintype S] (a : S → SurfaceBasisLabel X)
    (s : S) (ha : a s = .hyperplane ∨ a s = .exceptional i) (n : ℕ) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X)
      (X.exceptionalCurve j) n a = 0 := by
  have hf : (a s).primaryFactor (X.exceptionalCurve j) = 0 := by
    rcases ha with ha | ha
    · rw [ha]
      change (X.divisorIntersections (X.exceptionalCurve j) 0 : ℚ) = 0
      rw [← X.planeDegree_eq_divisorIntersections, X.planeDegree_exceptionalCurve]
      rfl
    · rw [ha]
      cases X <;> fin_cases i <;> fin_cases j <;>
        first | exact (hij rfl).elim | rfl
  have hp : (∏ t, (a t).primaryFactor (X.exceptionalCurve j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ s) hf
  simp only [SurfaceGenusZero.primaryScalar, if_neg (exceptional_ne_zero j), hp,
    zero_mul, ite_self]

private theorem pair_ee_foreign (i j : Fin X.blowups) (hij : i ≠ j) (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ) (n : ℕ)
    (x : GluingExpression 2 (Fin 2)) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (a : SurfaceBasisLabel X) :
    let y := GetzlerGraphs.join (m := 1) (n := 2) 1 2 x
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
    remainderContraction X v main y (by exact (d, (0 : Fin 3 → ℕ)))
      (by exact (l, (inferInstance : DecidableEq (Fin 3)))) (X.exceptionalCurve j) n
        ![a, .exceptional i, .exceptional i] =
      -remainderContraction X v main x d l (X.exceptionalCurve j) n ![a, .point] := by
  dsimp only
  rw [SurfaceGenusTwoBlowupPCoefficients.pair_join,
    Finset.sum_eq_single (X.exceptionalCurve j, 0)]
  · have ht (b : SurfaceBasisLabel X) :=
      SurfaceGenusTwoBlowupKCoefficients.classical_ee_points i
        (fun m ↦ remainderContraction X v main x d l (X.exceptionalCurve j) m ![a, b])
        n b.dual
    simp only [ht]
    rw [SurfaceBasisLabel.sum_labels]
    simp only [SurfaceBasisLabel.inverseWeight, SurfaceBasisLabel.dual,
      reduceCtorEq, ite_false, ite_true, mul_zero, zero_add, add_zero, one_mul,
      Finset.sum_const_zero]
  · intro split hs hne
    have hm := splittings_exceptional X j
    rw [hm, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | he
    · apply Finset.sum_eq_zero
      intro b _
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro ij _
      rw [foreign_scalar_zero i j hij (Fin 3) _ 0 (Or.inr rfl), mul_zero, mul_zero]
    · exact (hne he).elim
  · intro hn
    exact (hn (by rw [X.splittings_eq, X.effective.mem_splittings]; exact add_zero _)).elim

private theorem classical_divisor_node_point (a : SurfaceBasisLabel X)
    (ha : a.codimension = 1) (n : ℕ) (b : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) 0 n
      (![a, b, .point] : Fin 3 → _) = 0 := by
  have hd : ¬((((∑ t : Fin 3,
      ((![a, b, .point] : Fin 3 → SurfaceBasisLabel X) t).codimension : ℕ) : ℤ)
      + (n : ℤ)) = X.c1Degree 0 - 1 + (Fintype.card (Fin 3) : ℤ)) := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Fintype.card_fin, map_zero]
    change ¬(((a.codimension + b.codimension + 2 : ℕ) : ℤ) + (n : ℤ) = 0 - 1 + 3)
    rw [ha]
    omega
  rw [SurfaceGenusZero.primaryScalar, if_neg (fun h ↦ h.1 rfl), if_neg hd]

private theorem inner_allowed_point_foreign_zero (i j : Fin X.blowups) (hij : i ≠ j)
    (a : SurfaceBasisLabel X) (ha : a = .hyperplane ∨ a = .exceptional i)
    (v : Variable X) (main : ℕ → SurfaceCotangentVertexValues X ℚ)
    (n : ℕ) (k : Fin 1 → ℕ) :
    remainderContraction X v main
      (GetzlerGraphs.join (m := 0) (n := 2) 0 1
        (fundamental 2 (Fin 1) (by norm_num [StableArity]))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (by exact (k, (0 : Fin 3 → ℕ)))
      (by exact ((inferInstance : DecidableEq (Fin 1)),
        (inferInstance : DecidableEq (Fin 3)))) (X.exceptionalCurve j) n ![a, .point] = 0 := by
  simp only [GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction]
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b (((![a, .point] : Fin 2 → SurfaceBasisLabel X) ∘
        (finSumFinEquiv : Fin 0 ⊕ Fin 2 ≃ Fin 2)) ∘ Sum.inr)) ∘
        finSuccEquiv' 1 = ![a, b, .point] := by
    funext t; fin_cases t <;> rfl
  have hac : a.codimension = 1 := by rcases ha with rfl | rfl <;> rfl
  simp only [hr, primaryPointVertex, and_self, ite_true]
  apply Finset.sum_eq_zero
  intro split hs
  rw [splittings_exceptional X j, Finset.mem_insert, Finset.mem_singleton] at hs
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rcases hs with rfl | rfl
  · rw [foreign_scalar_zero i j hij (Fin 3) _ 0 ha ij.2, mul_zero, mul_zero]
  · rw [classical_divisor_node_point a hac ij.2 b.dual, mul_zero, mul_zero]

private theorem allowed_ne_unit (i : Fin X.blowups) (a : SurfaceBasisLabel X)
    (ha : a = .hyperplane ∨ a = .exceptional i) : a ≠ .unit := by
  rcases ha with rfl | rfl <;> intro he <;> cases he

private theorem allowed_ne_foreign (i j : Fin X.blowups) (hij : i ≠ j)
    (a : SurfaceBasisLabel X) (ha : a = .hyperplane ∨ a = .exceptional i) :
    a ≠ .exceptional j := by
  rcases ha with rfl | rfl
  · intro he; cases he
  · intro he; exact hij (SurfaceBasisLabel.exceptional.inj he)

private theorem pair_allowed_foreign_zero (i j : Fin X.blowups) (hij : i ≠ j) (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ) (n : ℕ)
    (x : GluingExpression 2 (Fin 2)) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (a b c : SurfaceBasisLabel X)
    (hb : b = .hyperplane ∨ b = .exceptional i)
    (hc : c = .hyperplane ∨ c = .exceptional i)
    (hm : remainderContraction X v main x d l (X.exceptionalCurve j) n ![a, .point] = 0) :
    let y := GetzlerGraphs.join (m := 1) (n := 2) 1 2 x
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
    remainderContraction X v main y (by exact (d, (0 : Fin 3 → ℕ)))
      (by exact (l, (inferInstance : DecidableEq (Fin 3)))) (X.exceptionalCurve j) n
        ![a, b, c] = 0 := by
  rcases hb with rfl | rfl <;> rcases hc with rfl | rfl
  · exact (SurfaceGenusTwoBlowupPPrimarySupport.pair_hh_of_planeDegree_zero v main n
      x d l _ (X.planeDegree_exceptionalCurve j) a).trans hm
  · exact pair_orthogonal_of_planeDegree_zero v main n x d l _
      (X.planeDegree_exceptionalCurve j) a .hyperplane (.exceptional i)
      (SurfaceCohomology.hyperplane_mul_exceptional X.blowups i) (Or.inl rfl)
  · exact pair_orthogonal_of_planeDegree_zero v main n x d l _
      (X.planeDegree_exceptionalCurve j) a (.exceptional i) .hyperplane
      (by rw [mul_comm]; exact SurfaceCohomology.hyperplane_mul_exceptional X.blowups i)
      (Or.inr rfl)
  · exact (pair_ee_foreign i j hij v main n x d l a).trans
      (by rw [hm, neg_zero])

private theorem paper_zero_foreign_zero (i j : Fin X.blowups) (hij : i ≠ j) (v : Variable X)
    (n : ℕ) (a b c : SurfaceBasisLabel X)
    (ha : a = .hyperplane ∨ a = .exceptional i)
    (hb : b = .hyperplane ∨ b = .exceptional i)
    (hc : c = .hyperplane ∨ c = .exceptional i) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 0) (X.exceptionalCurve j) n
        ![a, b, c] = 0 := by
  have hz : (![0, 0, 0] : Fin 3 → ℕ) = 0 := by decide +kernel
  rw [remainderPointCoefficient, if_pos (by decide +kernel)]
  change remainderContraction X v (remainderVertex X v (coefficientVertex X v))
    (GetzlerGraphs.join (m := 1) (n := 2) 1 2
      (GetzlerGraphs.join (m := 0) (n := 2) 0 1
        (fundamental 2 (Fin 1) (by norm_num [StableArity]))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (fundamental 0 (Fin 3) (by norm_num [StableArity])))
    ((![0], ![0, 0, 0]), ![0, 0, 0])
    (((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 3))),
      (inferInstance : DecidableEq (Fin 3))) (X.exceptionalCurve j) n ![a, b, c] = _
  rw [hz]
  apply pair_allowed_foreign_zero i j hij v _ n _ _ _ a b c hb hc
  exact inner_allowed_point_foreign_zero i j hij a ha v _ n ![0]

private theorem paper_one_foreign_zero (i j : Fin X.blowups) (hij : i ≠ j) (v : Variable X)
    (n : ℕ) (a : Fin 3 → SurfaceBasisLabel X)
    (ha : a 0 = .hyperplane ∨ a 0 = .exceptional i) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 1) (X.exceptionalCurve j) n a = 0 := by
  have hx : (BelorousskiPandharipande.paperCotangentTerm 1).expression.maxComponentGenus = 2 :=
    by decide +kernel
  rw [remainderPointCoefficient, if_pos hx]
  change remainderContraction X v (remainderVertex X v (coefficientVertex X v))
    (GetzlerGraphs.join (m := 0) (n := 3) 0 3
      (fundamental 2 (Fin 1) (by norm_num [StableArity]))
      (fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (![1], (0 : Fin 4 → ℕ))
    ((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 4)))
    (X.exceptionalCurve j) n a = _
  simp only [GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction]
  apply Finset.sum_eq_zero
  intro split hs
  rw [splittings_exceptional X j, Finset.mem_insert, Finset.mem_singleton] at hs
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  simp only [primaryPointVertex, and_self, ite_true]
  rcases hs with rfl | rfl
  · rw [foreign_scalar_zero i j hij (Fin 4) _ 0 ha ij.2, mul_zero, mul_zero]
  · rw [SurfaceGenusTwoBlowupPCoefficients.classical_four, mul_zero, mul_zero]

private theorem main_allowed_point_foreign_zero (i j : Fin X.blowups) (hij : i ≠ j)
    (v : Variable X) (n : ℕ) (s : Fin 2) (a : SurfaceBasisLabel X)
    (ha : a = .hyperplane ∨ a = .exceptional i) :
    remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single s 1) inferInstance (X.exceptionalCurve j)
      ![a, .point] = 0 := by
  apply remainderVertex_foreign_onePsi_zero j v n (Fin 2) _ s _
  · fin_cases s
    · exact allowed_ne_unit i a ha
    · intro he; cases he
  · fin_cases s
    · exact allowed_ne_foreign i j hij a ha
    · intro he; cases he

private theorem paper_pair_foreign_zero (i j : Fin X.blowups) (hij : i ≠ j) (v : Variable X)
    (n : ℕ) (s : Fin 2) (a b c : SurfaceBasisLabel X)
    (ha : a = .hyperplane ∨ a = .exceptional i)
    (hb : b = .hyperplane ∨ b = .exceptional i)
    (hc : c = .hyperplane ∨ c = .exceptional i) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3))
      (X.exceptionalCurve j) n ![a, b, c] = 0 := by
  have h0 : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
  have h1 : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
  have he : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3))
      (X.exceptionalCurve j) n ![a, b, c] =
      remainderContraction X v (remainderVertex X v (coefficientVertex X v))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          (fundamental 2 (Fin 2) (by norm_num [StableArity]))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        (by exact (Pi.single s 1, (0 : Fin 3 → ℕ)))
        (by exact ((inferInstance : DecidableEq (Fin 2)),
          (inferInstance : DecidableEq (Fin 3)))) (X.exceptionalCurve j) n ![a, b, c] := by
    rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
    · rw [if_pos rfl, ← h0]; rfl
    · rw [if_neg (by decide : (1:Fin 2) ≠ 0), ← h1]; rfl
  rw [he]
  apply pair_allowed_foreign_zero i j hij v _ n _ _ _ a b c hb hc
  simpa only [remainderContraction, fundamental, ite_true] using
    main_allowed_point_foreign_zero i j hij v n s a ha

private theorem paper_foreign_zero (i j : Fin X.blowups) (hij : i ≠ j) (v : Variable X)
    (n : ℕ) (k : Fin 4) (a : Fin 3 → SurfaceBasisLabel X)
    (ha : ∀ t, a t = .hyperplane ∨ a t = .exceptional i) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (Fin.castAdd 16 k))
      (X.exceptionalCurve j) n a = 0 := by
  have hv : a = ![a 0, a 1, a 2] := by funext t; fin_cases t <;> rfl
  fin_cases k
  · rw [hv]
    exact paper_zero_foreign_zero i j hij v n (a 0) (a 1) (a 2) (ha 0) (ha 1) (ha 2)
  · exact paper_one_foreign_zero i j hij v n a (ha 0)
  · rw [hv]
    exact paper_pair_foreign_zero i j hij v n 0 (a 0) (a 1) (a 2) (ha 0) (ha 1) (ha 2)
  · rw [hv]
    exact paper_pair_foreign_zero i j hij v n 1 (a 0) (a 1) (a 2) (ha 0) (ha 1) (ha 2)

/-- Every actual held BP diagram and marking assignment has zero coefficient
at a foreign energy-one exceptional remainder for these divisor labels. -/
theorem pointCoefficient_foreign_zero (i j : Fin X.blowups) (hij : i ≠ j)
    (v : Variable X) (n : ℕ) (a : Fin 3 → SurfaceBasisLabel X)
    (ha : ∀ t, a t = .hyperplane ∨ a t = .exceptional i) :
    BelorousskiPandharipande.pointCoefficient X n
      (SurfaceGenusZero.variableCurve v + X.exceptionalCurve j) a v = 0 := by
  unfold BelorousskiPandharipande.pointCoefficient
  apply Finset.sum_eq_zero
  intro k _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro e _
  have he := remainderPointCoefficient_eq X v (coefficientVertex X v) rfl
    (BelorousskiPandharipande.orbitCotangentTerm (Fin.castAdd 16 k) e)
    (X.exceptionalCurve j) n a
  rw [← he, SurfaceGenusTwoBlowupPCoefficients.remainder_orbit]
  apply paper_foreign_zero i j hij v n k
  intro t
  exact ha (BelorousskiPandharipande.labelPermutation e t)

/-- The vanishing binds to the complete original normalized BP polynomial,
including every primary calibration term and the lower-genus constant. -/
theorem bpRow_foreign_coefficient_zero (i j : Fin X.blowups) (hij : i ≠ j)
    (v : Variable X) (n : ℕ) (a : Fin 3 → SurfaceBasisLabel X)
    (ha : ∀ t, a t = .hyperplane ∨ a t = .exceptional i) :
    RationalTerms.coefficient
      (SurfaceGenusTwoBlowupNRelation.bpRow X n
        (SurfaceGenusZero.variableCurve v + X.exceptionalCurve j) a) {v} = 0 := by
  unfold SurfaceGenusTwoBlowupNRelation.bpRow
  rw [← BelorousskiPandharipande.pointCoefficient_eq_full]
  exact pointCoefficient_foreign_zero i j hij v n a ha

/-- The complete combined N relation has no coefficient at a foreign exceptional
energy-one remainder, for any requested variable with its original full class. -/
theorem row_foreign_coefficient_zero (i j : Fin X.blowups) (hij : i ≠ j)
    (beta : X.Curve) (v : Variable X)
    (hs : SurfaceGenusZero.variableCurve v + X.exceptionalCurve j = beta + X.exceptionalCurve i) :
    RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row X i beta) {v} = 0 := by
  unfold SurfaceGenusTwoBlowupNRelation.row
  rw [← hs]
  have hehh := bpRow_foreign_coefficient_zero i j hij v (X.effective.energy beta)
    (![.exceptional i, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
    (by
      intro t
      fin_cases t
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact Or.inl rfl)
  have heeh := bpRow_foreign_coefficient_zero i j hij v (X.effective.energy beta)
    (![.exceptional i, .exceptional i, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
    (by
      intro t
      fin_cases t
      · exact Or.inr rfl
      · exact Or.inr rfl
      · exact Or.inl rfl)
  have heee := bpRow_foreign_coefficient_zero i j hij v (X.effective.energy beta)
    (![.exceptional i, .exceptional i, .exceptional i] : Fin 3 → SurfaceBasisLabel X)
    (by intro t; fin_cases t <;> exact Or.inr rfl)
  have hhhh := bpRow_foreign_coefficient_zero i j hij v (X.effective.energy beta)
    (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
    (by intro t; fin_cases t <;> exact Or.inl rfl)
  rw [RationalTerms.coefficient_add, RationalTerms.coefficient_add,
    RationalTerms.coefficient_add, RationalTerms.coefficient_scale,
    RationalTerms.coefficient_scale, RationalTerms.coefficient_scale,
    RationalTerms.coefficient_scale, hehh, heeh, heee, hhhh]
  ring

/-- The primary N corollary preserves the requested full curve class and every point count. -/
theorem row_foreign_primary_coefficient_zero (i j : Fin X.blowups) (hij : i ≠ j)
    (beta gamma : X.Curve)
    (hs : gamma + X.exceptionalCurve j = beta + X.exceptionalCurve i) (m : ℕ) :
    RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row X i beta)
      {Sum.inr (SurfaceQuery.points X 2 gamma m)} = 0 := by
  exact row_foreign_coefficient_zero i j hij beta
    (Sum.inr (SurfaceQuery.points X 2 gamma m)) hs


end AxiomaticGW.SurfaceGenusTwoBlowupNForeignSupport

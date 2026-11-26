/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupHUniform
public import AxiomaticGW.Surfaces.GenusTwoBlowupOrder

/-!
# Constructor-level vanishing in the shifted hyperplane coefficient

The exact twelve-term shifted-H formula contains seven chains whose genus-two
component has an external exceptional state, three forks with an outer primary
rational H/Ei triple, and two remaining chains. The seven external-state chains
vanish at every full effective remainder when the available point budget is
below the requested energy. A wrong psi state gives no H first-descendant
coefficient; two divisor states instead fail the exact dimension condition.
All primary corrections and calibration tails retain their proved zero H
coefficient.

The three forks have two genus-two node flags and no external main state. They
vanish by a different argument: their outer rational H/Ei triple has zero value
at every zero-plane-degree class, including the classical class-zero boundary.
Effective splittings of a zero-plane-degree remainder preserve that property.

Together these facts reduce the original H coefficient to held terms 57 and 64
for every positive-energy full curve class and every zero-plane-degree effective
remainder. This includes the selected exceptional shift and other exceptional
remainders. No irreducibility or restriction on signed multiplicities is used.
The two surviving contributions are not evaluated here; full other-column
support and a reconstruction recurrence are separate obligations.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupHVanishing
open SurfacePolynomialReduction SurfaceGenusTwo SurfaceGenusTwoBlowupHPivots GluingExpression
-- Unfolding the actual held 815-term dispatch requires this recursion depth.
set_option maxRecDepth 20000

private theorem h_request_ne_primary (X : SurfaceTarget) (beta gamma : X.Curve) (n : ℕ) :
    Sum.inr (SurfaceQuery.points X 2 gamma n) ≠ hColumn X beta :=
  SurfaceFirstDescendant.query_ne_points beta gamma .hyperplane (X.effective.energy beta) n

private theorem first_request_ne_h (X : SurfaceTarget) (beta gamma : X.Curve)
    (b : SurfaceBasisLabel X) (n : ℕ) (hb : b ≠ .hyperplane) :
    (Sum.inr (SurfaceFirstDescendant.query 2 gamma b n) : Variable X) ≠ hColumn X beta := by
  intro he
  have hl := congrArg (fun q : SurfaceQuery X ↦ q.insertions.head?.map SurfaceInsertion.label)
    (Sum.inr.inj he)
  simp only [SurfaceFirstDescendant.query, List.head?_cons, Option.map_some,
    Option.some.injEq] at hl
  exact hb hl

private theorem primaryTerms_h_zero (X : SurfaceTarget) (beta gamma : X.Curve)
    (m : Multiset (SurfaceBasisLabel X)) :
    RationalTerms.coefficient (RationalTerms.rename Sum.inr
      (SurfaceFirstDescendant.primaryTerms 2 gamma m)) {hColumn X beta} = 0 := by
  rw [SurfaceFirstDescendant.primaryTerms, RationalTerms.coefficient_rename_scale,
    SurfaceFirstDescendant.dimensionTerms]
  split_ifs with hd
  · rw [RationalTerms.coefficient_rename_term]
    simp only [Multiset.map_singleton, Multiset.singleton_inj,
      if_neg (h_request_ne_primary X beta gamma _), mul_zero]
  · simp only [RationalTerms.rename_zero, RationalTerms.coefficient_zero, mul_zero]

private theorem firstTerms_wrong_label (X : SurfaceTarget) (beta gamma : X.Curve)
    (b : SurfaceBasisLabel X) (hb : b ≠ .hyperplane)
    (m : Multiset (SurfaceBasisLabel X)) :
    RationalTerms.coefficient (RationalTerms.rename Sum.inr
      (SurfaceFirstDescendant.terms 2 gamma b m)) {hColumn X beta} = 0 := by
  rw [SurfaceFirstDescendant.terms]
  split_ifs with hu hbunit
  · exact primaryTerms_h_zero X beta gamma _
  · rw [RationalTerms.coefficient_rename_scale, primaryTerms_h_zero, mul_zero]
  · rw [RationalTerms.coefficient_rename_add, RationalTerms.coefficient_rename_scale,
      RationalTerms.coefficient_rename_scale]
    have hd (q : SurfaceQuery X) (hne : Sum.inr q ≠ hColumn X beta) :
        RationalTerms.coefficient (RationalTerms.rename Sum.inr
          (SurfaceFirstDescendant.dimensionTerms q)) {hColumn X beta} = 0 := by
      rw [SurfaceFirstDescendant.dimensionTerms]
      split_ifs with hq
      · rw [RationalTerms.coefficient_rename_term]
        simp only [Multiset.map_singleton, Multiset.singleton_inj, if_neg hne]
      · simp only [RationalTerms.rename_zero, RationalTerms.coefficient_zero]
    rw [hd _ (first_request_ne_h X beta gamma b _ hb),
      hd _ (h_request_ne_primary X beta gamma _), mul_zero, mul_zero, add_zero]

/-- A main first descendant at a state other than H cannot contribute to the H
request. String/divisor corrections are primary, and all calibration tails
retain the proved zero nonprimary coefficient. -/
theorem remainderVertex_wrong_label_eq_zero (X : SurfaceTarget) (beta delta : X.Curve)
    (n : ℕ) (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (a : S → SurfaceBasisLabel X) (ha : a s ≠ .hyperplane) :
    remainderVertex X (hColumn X beta) (coefficientVertex X (hColumn X beta)) n
      2 S h (Pi.single s 1) inferInstance delta a = 0 := by
  have hv := h_request_ne_primary X beta
  rw [remainderVertex_onePsi_of_not_points (hColumn X beta) hv]
  split_ifs with hz
  · rw [coefficient_residualTerms_onePsi_of_not_points (hColumn X beta) hv]
    split_ifs with hd
    · exact firstTerms_wrong_label X beta beta (a s) ha _
    · rfl
  · rfl

private theorem twoDivisors_dimension (X : SurfaceTarget) (beta : X.Curve)
    (n : ℕ) (s : Fin 2) (a : Fin 2 → SurfaceBasisLabel X)
    (ha0 : (a 0).codimension = 1) (ha1 : (a 1).codimension = 1) :
    SurfaceAncestorKey.DimensionCompatible
      ((SurfaceAncestorKey.ofLabels 2 (Fin 2) (by norm_num [StableArity]) beta
        (Pi.single s 1) a).addPoints n) ↔ n = X.effective.energy beta := by
  fin_cases s <;>
    simp only [SurfaceAncestorKey.DimensionCompatible, SurfaceAncestorKey.totalCodimension,
      SurfaceAncestorKey.addPoints, SurfaceAncestorKey.ofLabels, Multiset.map_add,
      Multiset.map_replicate, Multiset.sum_add, Multiset.sum_replicate,
      Multiset.card_add, Multiset.card_replicate, Multiset.card_map, Finset.card_val,
      Finset.card_univ, Fintype.card_fin, SurfaceTarget.c1Degree,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  · change (n : ℤ) * 2 + ((a 0).codimension + 1 + (a 1).codimension : ℕ) =
      (X.effective.energy beta : ℤ) + 2 - 1 + ((n : ℤ) + 2) ↔ _
    rw [ha0, ha1]
    omega
  · change (n : ℤ) * 2 + ((a 0).codimension + ((a 1).codimension + 1) : ℕ) =
      (X.effective.energy beta : ℤ) + 2 - 1 + ((n : ℤ) + 2) ↔ _
    rw [ha0, ha1]
    omega

/-- With two divisor states on the main component, the exact dimension check
requires the full target energy in points. A smaller budget cannot contribute,
regardless of which of its two flags carries psi or of the effective remainder. -/
theorem remainderVertex_twoDivisors_eq_zero (X : SurfaceTarget) (beta delta : X.Curve)
    (n : ℕ) (hn : n < X.effective.energy beta) (s : Fin 2)
    (a : Fin 2 → SurfaceBasisLabel X) (ha0 : (a 0).codimension = 1)
    (ha1 : (a 1).codimension = 1) :
    remainderVertex X (hColumn X beta) (coefficientVertex X (hColumn X beta)) n
      2 (Fin 2) (by norm_num [StableArity]) (Pi.single s 1) inferInstance delta a = 0 := by
  have hv := h_request_ne_primary X beta
  rw [remainderVertex_onePsi_of_not_points (hColumn X beta) hv]
  split_ifs with hz
  · rw [coefficient_residualTerms_onePsi_of_not_points (hColumn X beta) hv, if_neg]
    intro hd
    have he := (twoDivisors_dimension X beta n s a ha0 ha1).mp hd
    omega
  · rfl

/-- An exceptional external state on a two-flag main component forces zero H
coefficient for every node state and either psi flag, at the available budget. -/
theorem remainderVertex_exceptional_pair_eq_zero (X : SurfaceTarget) (beta delta : X.Curve)
    (n : ℕ) (hn : n < X.effective.energy beta) (i : Fin X.blowups)
    (s : Fin 2) (b : SurfaceBasisLabel X) :
    remainderVertex X (hColumn X beta) (coefficientVertex X (hColumn X beta)) n
      2 (Fin 2) (by norm_num [StableArity]) (Pi.single s 1) inferInstance delta
      ![.exceptional i, b] = 0 := by
  by_cases hb : b = .hyperplane
  · subst b
    exact remainderVertex_twoDivisors_eq_zero X beta delta n hn s _ rfl rfl
  · apply remainderVertex_wrong_label_eq_zero X beta delta n (Fin 2) _ s _
    fin_cases s
    · intro he
      cases he
    · exact hb

private theorem external_chain_zero (X : SurfaceTarget) (beta delta : X.Curve)
    (x : GluingExpression 0 (Fin 4)) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (e : Equiv.Perm (Fin 4)) (s : Fin 2) (n : ℕ) (hn : n < X.effective.energy beta)
    (i : Fin X.blowups) (a : Fin 4 → SurfaceBasisLabel X)
    (ha : a (e 3) = .exceptional i) :
    remainderPointCoefficient X (hColumn X beta) (coefficientVertex X (hColumn X beta))
      (⟨(GetzlerGraphs.join (m := 3) (n := 1) 3 1 x
        (fundamental 2 (Fin 2) (by norm_num [StableArity]))).relabel e,
        (d, Pi.single s 1), (l, (inferInstance : DecidableEq (Fin 2)))⟩ :
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
  rw [hr, ha, remainderVertex_exceptional_pair_eq_zero X beta split.2 ij.2 (by omega)
    i s b.dual, mul_zero, mul_zero]

/-- The seven chain constructors whose two-flag genus-two component has an
exceptional external marking. The three two-node fork constructors are distinct. -/
def externalExceptionalFrame : Finset (Fin 815) := {51, 59, 66, 76, 83, 93, 95}

/-- Every original external-exceptional chain has zero H coefficient at any
full effective remainder and any added-point budget below the target energy. -/
theorem externalExceptionalFrame_coefficient_zero (X : SurfaceTarget)
    (beta delta : X.Curve) (n : ℕ) (hn : n < X.effective.energy beta)
    (i : Fin X.blowups) : ∀ j ∈ externalExceptionalFrame,
    remainderPointCoefficient X (hColumn X beta) (coefficientVertex X (hColumn X beta))
      (L24Gluing.term j) delta n (labels X i) = 0 := by
  have h0 : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
  have h1 : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
  intro j hj
  simp only [externalExceptionalFrame, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show L24Gluing.term (51 : Fin 815) = L24Gluing.term51 from rfl]
    unfold L24Gluing.term51 L24Gluing.expression12
    rw [h1]
    exact external_chain_zero X beta delta _ _ _ _ 1 n hn i (labels X i) rfl
  · rw [show L24Gluing.term (59 : Fin 815) = L24Gluing.term59 from rfl]
    unfold L24Gluing.term59 L24Gluing.expression16
    rw [h0]
    exact external_chain_zero X beta delta _ _ _ _ 0 n hn i (labels X i) rfl
  · rw [show L24Gluing.term (66 : Fin 815) = L24Gluing.term66 from rfl]
    unfold L24Gluing.term66 L24Gluing.expression20
    rw [h0]
    exact external_chain_zero X beta delta _ _ _ _ 0 n hn i (labels X i) rfl
  · rw [show L24Gluing.term (76 : Fin 815) = L24Gluing.term76 from rfl]
    unfold L24Gluing.term76 L24Gluing.expression24
    rw [h1]
    exact external_chain_zero X beta delta _ _ _ _ 1 n hn i (labels X i) rfl
  · rw [show L24Gluing.term (83 : Fin 815) = L24Gluing.term83 from rfl]
    unfold L24Gluing.term83 L24Gluing.expression27
    rw [h1]
    exact external_chain_zero X beta delta _ _ _ _ 1 n hn i (labels X i) rfl
  · rw [show L24Gluing.term (93 : Fin 815) = L24Gluing.term93 from rfl]
    unfold L24Gluing.term93 L24Gluing.expression31
    rw [h0]
    exact external_chain_zero X beta delta _ _ _ _ 0 n hn i (labels X i) rfl
  · rw [show L24Gluing.term (95 : Fin 815) = L24Gluing.term95 from rfl]
    unfold L24Gluing.term95 L24Gluing.expression32
    rw [h0]
    have h := external_chain_zero X beta delta
      (GetzlerGraphs.join (m := 2) (n := 2) 2 1
        (fundamental 0 (Fin 3) (by norm_num [StableArity]))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (![0, 0, 0], ![0, 0, 0])
      ((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 3)))
      (Equiv.refl _) 0 n hn i (labels X i) rfl
    simpa only [remainderPointCoefficient, GluingExpression.maxComponentGenus,
      remainderContraction, Equiv.refl_apply, Function.comp_def] using h



/-- A primary rational triple carrying H and Ei is zero at every full class
with plane degree zero, including the classical class-zero boundary. -/
theorem primaryScalar_hyperplane_exceptional_eq_zero (X : SurfaceTarget)
    (i : Fin X.blowups) (f : X.Curve → ℚ) (gamma : X.Curve) (hd : X.planeDegree gamma = 0) (n : ℕ)
    (b : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X f gamma n
      (![.hyperplane, .exceptional i, b] : Fin 3 → _) = 0 := by
  by_cases hz : gamma = 0
  · subst gamma
    have hv : (∏ j : Fin 3,
        ((![.hyperplane, .exceptional i, b] : Fin 3 → SurfaceBasisLabel X) j).value) = 0 := by
      simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, SurfaceBasisLabel.value]
      rw [SurfaceCohomology.hyperplane_mul_exceptional, zero_mul]
    simp only [SurfaceGenusZero.primaryScalar, ne_eq, not_true_eq_false,
      false_and, ite_true, hv, mul_zero, map_zero, ite_self]
  · have hh : (SurfaceBasisLabel.hyperplane : SurfaceBasisLabel X).primaryFactor gamma = 0 := by
      change (X.divisorIntersections gamma 0 : ℚ) = 0
      rw [← X.planeDegree_eq_divisorIntersections gamma, hd]
      rfl
    unfold SurfaceGenusZero.primaryScalar
    split_ifs with hvalue hdim
    · rfl
    · rw [Fin.prod_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        hh, zero_mul]
    · rfl

private theorem outer_fork_zero (X : SurfaceTarget) (beta delta : X.Curve)
    (hd : X.planeDegree delta = 0) (x : GluingExpression 2 (Fin 3))
    (d : x.CotangentDecoration) (l : x.DecidableLabels) (hx : x.maxComponentGenus = 2)
    (e : Equiv.Perm (Fin 4)) (n : ℕ) (i : Fin X.blowups)
    (a : Fin 4 → SurfaceBasisLabel X) (ha0 : a (e 0) = .hyperplane)
    (ha1 : a (e 1) = .exceptional i) :
    remainderPointCoefficient X (hColumn X beta) (coefficientVertex X (hColumn X beta))
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

/-- The three two-node fork constructors have a separate outer rational H/Ei triple. -/
def rationalHyperplaneExceptionalFrame : Finset (Fin 815) := {52, 62, 69}

/-- Each actual fork vanishes whenever the full distributed remainder has plane
degree zero. Every ordered splitting and every added-point allocation remains. -/
theorem rationalHyperplaneExceptionalFrame_coefficient_zero (X : SurfaceTarget)
    (beta delta : X.Curve) (hd : X.planeDegree delta = 0) (n : ℕ)
    (i : Fin X.blowups) : ∀ j ∈ rationalHyperplaneExceptionalFrame,
    remainderPointCoefficient X (hColumn X beta) (coefficientVertex X (hColumn X beta))
      (L24Gluing.term j) delta n (labels X i) = 0 := by
  intro j hj
  simp only [rationalHyperplaneExceptionalFrame, Finset.mem_insert,
    Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  · rw [show L24Gluing.term (52 : Fin 815) = L24Gluing.term52 from rfl]
    unfold L24Gluing.term52 L24Gluing.expression13
    have h := outer_fork_zero X beta delta hd
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
    exact outer_fork_zero X beta delta hd _ _ _
      (by simp only [GetzlerGraphs.join, GluingExpression.maxComponentGenus,
        max_eq_right (show (0 : ℕ) ≤ 2 by decide)])
      _ n i (labels X i) rfl rfl
  · rw [show L24Gluing.term (69 : Fin 815) = L24Gluing.term69 from rfl]
    unfold L24Gluing.term69 L24Gluing.expression21
    exact outer_fork_zero X beta delta hd _ _ _
      (by simp only [GetzlerGraphs.join, GluingExpression.maxComponentGenus,
        max_eq_right (show (0 : ℕ) ≤ 2 by decide)])
      _ n i (labels X i) rfl rfl



/-- The ten actual source terms proved zero by the two different mechanisms. -/
def vanishingFrame : Finset (Fin 815) :=
  externalExceptionalFrame ∪ rationalHyperplaneExceptionalFrame

/-- Exact size of the ten held terms removed from the twelve-term frame. -/
theorem vanishingFrame_card : vanishingFrame.card = 10 := by decide +kernel

/-- Zero coefficients are proved from actual constructors for all full classes,
zero-plane-degree remainders and point budgets below the requested energy. -/
theorem vanishingFrame_coefficient_zero (X : SurfaceTarget) (beta delta : X.Curve)
    (hd : X.planeDegree delta = 0) (n : ℕ) (hn : n < X.effective.energy beta)
    (i : Fin X.blowups) : ∀ j ∈ vanishingFrame,
    remainderPointCoefficient X (hColumn X beta) (coefficientVertex X (hColumn X beta))
      (L24Gluing.term j) delta n (labels X i) = 0 := by
  intro j hj
  rcases Finset.mem_union.mp hj with hj | hj
  · exact externalExceptionalFrame_coefficient_zero X beta delta n hn i j hj
  · exact rationalHyperplaneExceptionalFrame_coefficient_zero X beta delta hd n i j hj

/-- At the physical positive-energy marking count, all ten actual shifted terms
vanish. The class-zero request is excluded by this explicit premise. -/
theorem shifted_vanishingFrame_coefficient_zero (X : SurfaceTarget)
    (i : Fin X.blowups) (beta : X.Curve) (hbeta : 0 < X.effective.energy beta) :
    ∀ j ∈ vanishingFrame,
    remainderPointCoefficient X (hColumn X beta)
      (firstCoefficientVertex X beta .hyperplane (X.effective.energy beta))
      (L24Gluing.term j) (X.exceptionalCurve i) (pointCount X beta) (labels X i) = 0 := by
  intro j hj
  rw [firstCoefficientVertex_eq]
  exact vanishingFrame_coefficient_zero X beta (X.exceptionalCurve i)
    (X.planeDegree_exceptionalCurve i) (pointCount X beta) (by unfold pointCount; omega)
    i j hj

/-- The two original held terms left after constructor-level vanishing. -/
def survivingFrame : Finset (Fin 815) := {57, 64}

private theorem twoMarkingFrame_partition :
    SurfaceGenusTwoBlowupHUniform.twoMarkingFrame = survivingFrame ∪ vanishingFrame :=
  by decide +kernel

private theorem survivingFrame_disjoint : Disjoint survivingFrame vanishingFrame :=
  by decide +kernel

/-- The last two contributions retain their original relation weights, all point
pullbacks, inverse-metric states and full effective remainder. -/
def survivingCoefficient (X : SurfaceTarget) (i : Fin X.blowups)
    (beta delta : X.Curve) : ℚ :=
  ∑ j ∈ survivingFrame, L24CorrectionsReplay.fullClaim j *
    remainderPointCoefficient X (hColumn X beta)
      (firstCoefficientVertex X beta .hyperplane (X.effective.energy beta))
      (L24Gluing.term j) delta (pointCount X beta) (labels X i)

/-- The twelve-term coefficient is exactly the two surviving contributions at
positive target energy and any zero-plane-degree effective remainder. -/
theorem twoMarkingCoefficient_eq_surviving (X : SurfaceTarget) (i : Fin X.blowups)
    (beta delta : X.Curve) (hbeta : 0 < X.effective.energy beta)
    (hd : X.planeDegree delta = 0) :
    SurfaceGenusTwoBlowupHUniform.twoMarkingCoefficient X i beta delta =
      survivingCoefficient X i beta delta := by
  unfold SurfaceGenusTwoBlowupHUniform.twoMarkingCoefficient survivingCoefficient
  rw [twoMarkingFrame_partition, Finset.sum_union survivingFrame_disjoint]
  have hz : (∑ j ∈ vanishingFrame, L24CorrectionsReplay.fullClaim j *
      remainderPointCoefficient X (hColumn X beta)
        (firstCoefficientVertex X beta .hyperplane (X.effective.energy beta))
        (L24Gluing.term j) delta (pointCount X beta) (labels X i)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [firstCoefficientVertex_eq]
    change L24CorrectionsReplay.fullClaim j *
      remainderPointCoefficient X (hColumn X beta) (coefficientVertex X (hColumn X beta))
        (L24Gluing.term j) delta (pointCount X beta) (labels X i) = 0
    rw [vanishingFrame_coefficient_zero X beta delta hd (pointCount X beta)
      (by unfold pointCount; omega) i j hj, mul_zero]
  rw [hz, add_zero]

/-- The two-term expression remains the requested coefficient of the original
L24 point equation at any zero-plane-degree full effective remainder. -/
theorem pointCoefficient_eq_surviving_of_planeDegree_zero (X : SurfaceTarget)
    (i : Fin X.blowups) (beta delta : X.Curve) (hbeta : 0 < X.effective.energy beta)
    (hd : X.planeDegree delta = 0) :
    L24Relation.pointCoefficient X (pointCount X beta) (beta + delta)
      (labels X i) (hColumn X beta) = survivingCoefficient X i beta delta := by
  calc
    _ = SurfaceGenusTwoBlowupHUniform.remainderCoefficient X i beta delta :=
      (SurfaceGenusTwoBlowupHUniform.remainderCoefficient_eq X i beta delta).symm
    _ = SurfaceGenusTwoBlowupHUniform.firstPsiCoefficient X i beta delta :=
      SurfaceGenusTwoBlowupHUniform.remainderCoefficient_eq_firstPsi X i beta delta
    _ = SurfaceGenusTwoBlowupHUniform.twoMarkingCoefficient X i beta delta :=
      SurfaceGenusTwoBlowupHUniform.firstPsiCoefficient_eq_twoMarking_of_pos
        X i beta delta hbeta
    _ = survivingCoefficient X i beta delta :=
      twoMarkingCoefficient_eq_surviving X i beta delta hbeta hd

/-- At positive target energy, the actual full shifted normalized row has only
the two contributions 57 and 64 in its requested H coefficient. -/
theorem row_coefficient_eq_surviving_of_pos (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) (hbeta : 0 < X.effective.energy beta) :
    RationalTerms.coefficient (row X i beta) {hColumn X beta} =
      survivingCoefficient X i beta (X.exceptionalCurve i) :=
  (SurfaceGenusTwoBlowupHUniform.row_coefficient_eq_twoMarking_of_pos X i beta hbeta).trans
    (twoMarkingCoefficient_eq_surviving X i beta (X.exceptionalCurve i) hbeta
      (X.planeDegree_exceptionalCurve i))

end AxiomaticGW.SurfaceGenusTwoBlowupHVanishing

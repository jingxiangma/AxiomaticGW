/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroExceptionalPoints
public import AxiomaticGW.Surfaces.GenusTwoBlowupPSupport

/-!
# Primary and canonical support of the complete BP HHH row

Every primary coefficient at the same plane degree is zero in the original
normalized BP HHH row. The proof retains each original graph, marking
assignment, calibration term and signed point-cotangent tail. At exceptional
remainders, point-containing rational tails vanish by the existing genus-zero
reconstruction, while hyperplane-containing tails vanish by their divisor
factor or classical dimension.

In a positive-energy canonical P row, primary and exceptional columns can
survive only at smaller plane degree, and every other canonical column is
earlier in the proved plane-degree/sector/energy order. The theorem
allows its own P column and retains all lower-plane primary tails; it supplies
neither a pivot assumption nor a reconstruction recurrence.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupPPrimarySupport
open SurfacePolynomialReduction SurfaceGenusTwo GluingExpression
open SurfaceGenusTwoBlowupPCoefficients SurfaceGenusTwoBlowupPPrimary
open SurfaceGenusTwoBlowupPSupport
variable {X : SurfaceTarget}

set_option maxRecDepth 20000

/-- The entire point-input first-calibration column vanishes at plane degree
zero, including class zero, with the existing exceptional generator seed retained. -/
theorem firstCalibrationMatrix_point_eq_zero (gamma : X.Curve)
    (hd : X.planeDegree gamma = 0) (row : SurfaceBasisLabel X) :
    SurfaceDescendant.firstCalibrationMatrix X gamma row .point = 0 := by
  unfold SurfaceDescendant.firstCalibrationMatrix SurfaceGenusZero.primaryValue
  by_cases hz : gamma = 0
  · rw [if_pos hz]
    have hc : (((Finset.univ : Finset (Fin 2)).val.map
        (![row.dual, .point] : Fin 2 → SurfaceBasisLabel X))).card = 2 := by
      simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
    rw [SurfacePrimary.classicalValue, hc, if_neg (by decide : (2 : ℕ) ≠ 3), mul_zero]
  · rw [if_neg hz]
    by_cases he : 2 ≤ X.effective.energy gamma
    · rw [SurfaceGenusZero.pointValue_eq_zero_of_hyperplane_zero_of_energy_ge_two X gamma
        ((X.planeDegree_eq_zero_iff_divisorIntersections_eq_zero gamma).mp hd) he]
      simp only [mul_zero, ite_self]
    · have hp : (SurfaceBasisLabel.point : SurfaceBasisLabel X) ∈
          ((Finset.univ : Finset (Fin 2)).val.map
            (![row.dual, .point] : Fin 2 → SurfaceBasisLabel X)) := by
        apply Multiset.mem_map.mpr
        exact ⟨1, (by simpa only [Finset.mem_val] using Finset.mem_univ (1 : Fin 2)), rfl⟩
      have hc := Multiset.count_pos.mpr hp
      rw [if_neg (by omega), mul_zero]

/-- Point-input calibration has no same-plane coefficient transfer. The full
normalizer remains on the left and all lower-plane tails are retained. -/
theorem coefficient_normalizedTerms_point_same_planeDegree (q : SurfaceAncestorKey X)
    (v : Variable X) (h : 2 ≤ q.genus ∧ q.totalPsi = 1)
    (hh : (q.onePsiInsertion h.2).label = .point)
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
    rw [hh, firstCalibrationMatrix_point_eq_zero split.2 hz b, neg_zero, zero_mul]
  · rw [coefficient_canonicalPrimaryTerms_eq_zero
      (SurfaceAncestorKey.ofLabels q.genus (Fin q.orderedInsertions.length) q.ordered_stable
        split.1 0 (Function.update q.orderedLabels (q.onePsiMark h.2) b)) h.1 v hb, mul_zero]

private theorem coefficient_normalizedTerms_of_onePsi_same_planeDegree
    (q : SurfaceAncestorKey X) (hg : 2 ≤ q.genus) (b : SurfaceBasisLabel X)
    (m : Multiset (SurfaceBasisLabel X))
    (hi : q.insertions = ⟨b, 1⟩ ::ₘ m.map (fun c ↦ ⟨c, 0⟩))
    (hb : b = .hyperplane ∨ b = .point) (v : Variable X)
    (hd : X.planeDegree (SurfaceGenusZero.variableCurve v) = X.planeDegree q.beta) :
    RationalTerms.coefficient (normalizedTerms q) {v} =
      RationalTerms.coefficient (directNormalizedTerms q) {v} := by
  have hp : q.totalPsi = 1 := by
    simp only [SurfaceAncestorKey.totalPsi, hi, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_map, Function.comp_def, Multiset.map_const', Multiset.sum_replicate,
      nsmul_zero, add_zero]
  have hh : q.onePsiInsertion hp = ⟨b, 1⟩ := by
    have ht := q.onePsiInsertion_mem hp
    rw [hi, Multiset.mem_cons] at ht
    rcases ht with ht | ht
    · exact ht
    · obtain ⟨c, _, he⟩ := Multiset.mem_map.mp ht
      have hz := q.onePsiInsertion_power hp
      rw [← he] at hz
      cases hz
  rcases hb with hb | hb
  · apply coefficient_normalizedTerms_hyperplane_same_planeDegree q v ⟨hg, hp⟩ _ hd
    rw [hh]
    exact hb
  · apply coefficient_normalizedTerms_point_same_planeDegree q v ⟨hg, hp⟩ _ hd
    rw [hh]
    exact hb

/-- A one-psi H/point terminal at equal plane degree keeps its direct coefficient
after the original residual dimension filter and full calibration substitution. -/
theorem coefficient_residualTerms_onePsi_same_planeDegree (v : Variable X)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (beta : X.Curve) (a : S → SurfaceBasisLabel X)
    (hs : a s = .hyperplane ∨ a s = .point)
    (hd : X.planeDegree (SurfaceGenusZero.variableCurve v) = X.planeDegree beta) (n : ℕ) :
    let q := (SurfaceAncestorKey.ofLabels 2 S h beta (Pi.single s 1) a).addPoints n
    RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
      (residualTerms q)) {v} =
      if q.DimensionCompatible then RationalTerms.coefficient (directNormalizedTerms q) {v}
      else 0 := by
  have hi : (SurfaceAncestorKey.ofLabels 2 S h beta (Pi.single s 1) a).insertions =
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
  have ha : ((SurfaceAncestorKey.ofLabels 2 S h beta (Pi.single s 1) a).addPoints n).insertions =
      ⟨a s, 1⟩ ::ₘ (Multiset.replicate n (SurfaceBasisLabel.point : SurfaceBasisLabel X) +
        (Finset.univ.erase s).val.map a).map (fun c ↦ ⟨c, 0⟩) := by
    simp only [SurfaceAncestorKey.addPoints, hi, Multiset.map_add, Multiset.map_replicate,
      Multiset.add_cons]
  dsimp only
  unfold residualTerms
  by_cases hdim :
      ((SurfaceAncestorKey.ofLabels 2 S h beta (Pi.single s 1) a).addPoints n).DimensionCompatible
  · rw [if_pos hdim, if_neg (show ¬((SurfaceAncestorKey.ofLabels 2 S h beta
        (Pi.single s 1) a).addPoints n).genus ≤ 1 from Nat.not_succ_le_self 1),
      RationalTerms.coefficient_affineSubstitute_term, Multiset.map_singleton,
      Multiset.sum_singleton, one_mul, if_pos hdim]
    apply coefficient_normalizedTerms_of_onePsi_same_planeDegree _ le_rfl (a s) _ ha hs v hd
  · rw [if_neg hdim, if_neg hdim, RationalTerms.coefficient_affineSubstitute_zero]

private theorem primaryScalar_hyperplane_point_tail_eq_zero (X : SurfaceTarget) (beta : X.Curve)
    (hd : X.planeDegree beta = 0) (b : SurfaceBasisLabel X) (n : ℕ) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) beta n
      (Option.elim · b (fun t : Bool ↦ if t then .point else .hyperplane)) = 0 := by
  by_cases hz : beta = 0
  · subst beta
    have hdim : ¬((((∑ s : Option Bool,
        ((Option.elim · b (fun t : Bool ↦ if t then
          (SurfaceBasisLabel.point : SurfaceBasisLabel X) else .hyperplane))
          s).codimension : ℕ) : ℤ)
        + (n : ℤ)) = X.c1Degree 0 - 1 + (Fintype.card (Option Bool) : ℤ)) := by
      simp only [Fintype.sum_option, Fintype.sum_bool, Option.elim_none, Option.elim_some,
        Bool.false_eq_true, ite_true, ite_false, SurfaceBasisLabel.codimension,
        Fintype.card_option, Fintype.card_bool, map_zero]
      change ¬(((b.codimension + (2 + 1) : ℕ) : ℤ) + (n : ℤ) = 0 - 1 + (2 + 1))
      omega
    rw [SurfaceGenusZero.primaryScalar, if_neg (fun h ↦ h.1 rfl), if_neg hdim]
  · exact primaryScalar_hyperplane_eq_zero _ beta hz hd (Option Bool) _ (some false) rfl n


/-- The actual signed one-psi correction vanishes at a plane-zero effective
remainder for an old H or point state, for every terminal callback. -/
theorem remainderContraction_onePsi_eq_zero_of_planeDegree_zero (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (delta : X.Curve) (hd : X.planeDegree delta = 0)
    (n : ℕ) (a : S → SurfaceBasisLabel X)
    (hs : a s = .hyperplane ∨ a s = .point) :
    let z := CotangentTerm.tail h (Pi.single s 1) s
    remainderContraction X v main z.expression z.decoration z.labels
      delta n (Option.elim · .point a) = 0 := by
  have hp : Function.update (Pi.single s 1 : S → ℕ) s
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
    CotangentTerm.fundamental, remainderContraction, ite_true, hp,
    primaryPointVertex_eq, GluingExpression.pointContraction,
    hz, vertex_primary_genusZero_eq, hr]
  apply Finset.sum_eq_zero
  intro split hsplit
  have ha : split.1 + split.2 = delta := by
    rw [X.splittings_eq] at hsplit
    exact (X.effective.mem_splittings _ _ _).mp hsplit
  have ht : X.planeDegree split.2 = 0 := by
    have he := congrArg X.planeDegree ha
    rw [map_add, hd] at he
    omega
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  have hv : SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) split.2 ij.2
      (Option.elim · b.dual (fun t : Bool ↦ if t then .point else a s)) = 0 := by
    rcases hs with hs | hs
    · rw [hs]
      exact primaryScalar_hyperplane_point_tail_eq_zero X split.2 ht b.dual ij.2
    · rw [hs]
      have hh : (fun t : Bool ↦ if t then (SurfaceBasisLabel.point : SurfaceBasisLabel X)
          else .point) = fun _ : Bool ↦ .point := by
        funext t
        cases t <;> rfl
      rw [hh]
      exact SurfaceGenusZero.primaryScalar_point_point_tail_eq_zero X split.2
        ((X.planeDegree_eq_zero_iff_divisorIntersections_eq_zero split.2).mp ht) b.dual ij.2
  rw [hv, mul_zero, mul_zero]

/-- At plane-zero remainders, H/point cotangent pullback keeps its complete
normalized terminal expression. This equality preserves its dimension test. -/
theorem remainderVertex_onePsi_of_planeDegree_zero (v : Variable X) (n : ℕ)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (delta : X.Curve) (hd : X.planeDegree delta = 0)
    (a : S → SurfaceBasisLabel X) (hs : a s = .hyperplane ∨ a s = .point) :
    remainderVertex X v (coefficientVertex X v) n 2 S h (Pi.single s 1)
      inferInstance delta a =
      RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
        (residualTerms ((SurfaceAncestorKey.ofLabels 2 S h
          (SurfaceGenusZero.variableCurve v + delta) (Pi.single s 1) a).addPoints n))) {v} := by
  induction n generalizing S with
  | zero =>
    simp only [remainderVertex, coefficientVertex, ite_true, vertexTerms,
      SurfaceAncestorKey.addPoints_zero]
  | succ n ih =>
    rw [remainderVertex_onePsi_step,
      remainderContraction_onePsi_eq_zero_of_planeDegree_zero v _ S h s delta hd n a hs,
      sub_zero]
    rw [ih (Option S) h.option (some s) (Option.elim · .point a)
      (show (Option.elim · .point a) (some s) = .hyperplane ∨
        (Option.elim · .point a) (some s) = .point from hs)]
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
      (SurfaceGenusZero.variableCurve v + delta) (Pi.single s 1) a n]

/-- At a plane-zero effective remainder, neither actual H/point psi position
contributes to any primary point request of the fixed main class. -/
theorem pair_main_primary_zero_of_planeDegree_zero (gamma : X.Curve) (m : ℕ)
    (delta : X.Curve) (hd : X.planeDegree delta = 0) (n : ℕ) (s : Fin 2) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 gamma m)
    remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single s 1) inferInstance delta
      ![.hyperplane, .point] = 0 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 gamma m)
  have hs : (![.hyperplane, .point] : Fin 2 → SurfaceBasisLabel X) s = .hyperplane ∨
      (![.hyperplane, .point] : Fin 2 → SurfaceBasisLabel X) s = .point := by
    fin_cases s
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hg : X.planeDegree (SurfaceGenusZero.variableCurve v) =
      X.planeDegree (SurfaceGenusZero.variableCurve v + delta) := by
    rw [map_add, hd, add_zero]
  dsimp only
  rw [remainderVertex_onePsi_of_planeDegree_zero v n (Fin 2) _ s delta hd _ hs,
    coefficient_residualTerms_onePsi_same_planeDegree v (Fin 2) _ s _ _ hs hg n]
  split_ifs with hdim
  · rw [directNormalizedTerms_onePsi_ofLabels 2 le_rfl (Fin 2) _ s
      (SurfaceGenusZero.variableCurve v + delta)
      (![.hyperplane, .point] : Fin 2 → SurfaceBasisLabel X) n]
    have h0 : ((Finset.univ.erase (0 : Fin 2)).val.map
        (![.hyperplane, .point] : Fin 2 → SurfaceBasisLabel X)) = {.point} := rfl
    have h1 : ((Finset.univ.erase (1 : Fin 2)).val.map
        (![.hyperplane, .point] : Fin 2 → SurfaceBasisLabel X)) = {.hyperplane} := rfl
    rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
    · rw [h0, Matrix.cons_val_zero]
      apply SurfaceGenusTwoBlowupPPrimary.coefficient_terms_primary_zero
      · simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton,
          reduceCtorEq, and_false, or_self, not_false_eq_true]
      · intro he
        cases he
      · simp only [SurfaceFirstDescendant.correctionCoefficient,
          SurfaceFirstDescendant.divisorSquare, Multiset.count_add,
          Multiset.count_replicate, Multiset.count_singleton, reduceCtorEq,
          ite_false, zero_add, Nat.cast_zero, mul_zero, zero_mul]
    · rw [h1, Matrix.cons_val_one, Matrix.cons_val_zero]
      apply SurfaceGenusTwoBlowupPPrimary.coefficient_terms_primary_zero
      · simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton,
          reduceCtorEq, and_false, or_self, not_false_eq_true]
      · intro he
        cases he
      · simp only [SurfaceFirstDescendant.correctionCoefficient,
          SurfaceFirstDescendant.divisorSquare, zero_mul]
  · rfl

private theorem splitting_add {delta : X.Curve} {split : X.Curve × X.Curve}
    (hs : split ∈ X.splittings delta) : split.1 + split.2 = delta := by
  rw [X.splittings_eq] at hs
  exact (X.effective.mem_splittings _ _ _).mp hs

private theorem splitting_planeDegree_right {delta : X.Curve}
    (hd : X.planeDegree delta = 0) {split : X.Curve × X.Curve}
    (hs : split ∈ X.splittings delta) : X.planeDegree split.2 = 0 := by
  have he := congrArg X.planeDegree (splitting_add hs)
  rw [map_add, hd] at he
  omega

/-- A plane-zero outer HH rational pair has exactly its classical unit-node
contribution. Positive exceptional rational classes vanish by the H divisor factor. -/
theorem pair_hh_of_planeDegree_zero (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ) (n : ℕ)
    (x : GluingExpression 2 (Fin 2)) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (delta : X.Curve) (hd : X.planeDegree delta = 0) (a : SurfaceBasisLabel X) :
    let y := GetzlerGraphs.join (m := 1) (n := 2) 1 2 x
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
    remainderContraction X v main y (by exact (d, (0 : Fin 3 → ℕ)))
      (by exact (l, (inferInstance : DecidableEq (Fin 3)))) delta n
      ![a, .hyperplane, .hyperplane] =
      remainderContraction X v main x d l delta n ![a, .point] := by
  dsimp only
  rw [pair_join]
  rw [Finset.sum_eq_single (delta, 0)]
  · have hsum (b : SurfaceBasisLabel X) := classical_hh_points
      (fun m ↦ remainderContraction X v main x d l delta m ![a, b]) n b.dual
    simp only [hsum]
    rw [SurfaceBasisLabel.sum_labels]
    simp only [SurfaceBasisLabel.inverseWeight, SurfaceBasisLabel.dual,
      one_mul, reduceCtorEq, ite_false, ite_true, zero_add,
      mul_zero, Finset.sum_const_zero]
  · intro split hs hne
    have hz : split.2 ≠ 0 := by
      intro he
      have ha := splitting_add hs
      rw [he, add_zero] at ha
      exact hne (Prod.ext ha he)
    apply Finset.sum_eq_zero
    intro b _
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro ij _
    rw [primaryScalar_hyperplane_eq_zero _ split.2 hz
      (splitting_planeDegree_right hd hs) (Fin 3) _ 0 rfl ij.2,
      mul_zero, mul_zero]
  · intro hnot
    apply (hnot _).elim
    rw [X.splittings_eq]
    exact (X.effective.mem_splittings _ _ _).mpr (add_zero _)

private theorem primaryScalar_h_node_point_zero (gamma : X.Curve)
    (hd : X.planeDegree gamma = 0) (n : ℕ) (b : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) gamma n
      (![.hyperplane, b, .point] : Fin 3 → _) = 0 := by
  by_cases hz : gamma = 0
  · subst gamma
    have hdim : ¬((((∑ i : Fin 3,
        ((![.hyperplane, b, .point] : Fin 3 → SurfaceBasisLabel X) i).codimension : ℕ) : ℤ)
        + (n : ℤ)) = X.c1Degree 0 - 1 + (Fintype.card (Fin 3) : ℤ)) := by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, SurfaceBasisLabel.codimension, Fintype.card_fin, map_zero]
      change ¬(((1 + b.codimension + 2 : ℕ) : ℤ) + (n : ℤ) = 0 - 1 + 3)
      omega
    rw [SurfaceGenusZero.primaryScalar, if_neg (fun h ↦ h.1 rfl), if_neg hdim]
  · exact primaryScalar_hyperplane_eq_zero _ gamma hz hd (Fin 3) _ 0 rfl n

private theorem inner_h_point_zero (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ) (delta : X.Curve)
    (hd : X.planeDegree delta = 0) (n : ℕ) (k : Fin 1 → ℕ) :
    remainderContraction X v main
      (GetzlerGraphs.join (m := 0) (n := 2) 0 1
        (fundamental 2 (Fin 1) (by norm_num [StableArity]))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (by exact (k, (0 : Fin 3 → ℕ)))
      (by exact ((inferInstance : DecidableEq (Fin 1)),
        (inferInstance : DecidableEq (Fin 3)))) delta n ![.hyperplane, .point] = 0 := by
  simp only [GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction]
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b (((![.hyperplane, .point] : Fin 2 → SurfaceBasisLabel X) ∘
        (finSumFinEquiv : Fin 0 ⊕ Fin 2 ≃ Fin 2)) ∘ Sum.inr)) ∘
        finSuccEquiv' 1 = ![.hyperplane, b, .point] := by
    funext i
    fin_cases i <;> rfl
  simp only [hr, primaryPointVertex, and_self, ite_true]
  apply Finset.sum_eq_zero
  intro split hs
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [primaryScalar_h_node_point_zero split.2
    (splitting_planeDegree_right hd hs) ij.2 b.dual, mul_zero, mul_zero]

private theorem paper_zero (v : Variable X) (delta : X.Curve)
    (hd : X.planeDegree delta = 0) (n : ℕ) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 0) delta n
        ![.hyperplane, .hyperplane, .hyperplane] = 0 := by
  have hz : (![0, 0, 0] : Fin 3 → ℕ) = 0 := by decide +kernel
  have he : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 0) delta n
        ![.hyperplane, .hyperplane, .hyperplane] =
      remainderContraction X v (remainderVertex X v (coefficientVertex X v))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          (GetzlerGraphs.join (m := 0) (n := 2) 0 1
            (fundamental 2 (Fin 1) (by norm_num [StableArity]))
            (fundamental 0 (Fin 3) (by norm_num [StableArity])))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        ((![0], (0 : Fin 3 → ℕ)), (0 : Fin 3 → ℕ))
        (((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 3))),
          (inferInstance : DecidableEq (Fin 3))) delta n
        ![.hyperplane, .hyperplane, .hyperplane] := by
    rw [remainderPointCoefficient, if_pos (by decide +kernel)]
    change remainderContraction X v (remainderVertex X v (coefficientVertex X v))
      (GetzlerGraphs.join (m := 1) (n := 2) 1 2
        (GetzlerGraphs.join (m := 0) (n := 2) 0 1
          (fundamental 2 (Fin 1) (by norm_num [StableArity]))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      ((![0], ![0, 0, 0]), ![0, 0, 0]) _ delta n
        ![.hyperplane, .hyperplane, .hyperplane] = _
    rw [hz]
    rfl
  exact he.trans ((pair_hh_of_planeDegree_zero v
    (remainderVertex X v (coefficientVertex X v)) n
    (GetzlerGraphs.join (m := 0) (n := 2) 0 1
      (fundamental 2 (Fin 1) (by norm_num [StableArity]))
      (fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (![0], (0 : Fin 3 → ℕ))
    ((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 3)))
    delta hd .hyperplane).trans (inner_h_point_zero v _ delta hd n ![0]))

private theorem paper_one (v : Variable X) (delta : X.Curve)
    (hd : X.planeDegree delta = 0) (n : ℕ) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 1) delta n
        ![.hyperplane, .hyperplane, .hyperplane] = 0 := by
  have hx : (BelorousskiPandharipande.paperCotangentTerm 1).expression.maxComponentGenus = 2 :=
    by decide +kernel
  rw [remainderPointCoefficient, if_pos hx]
  change remainderContraction X v (remainderVertex X v (coefficientVertex X v))
    (GetzlerGraphs.join (m := 0) (n := 3) 0 3
      (fundamental 2 (Fin 1) (by norm_num [StableArity]))
      (fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (![1], (0 : Fin 4 → ℕ))
    ((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 4)))
    delta n ![.hyperplane, .hyperplane, .hyperplane] = _
  simp only [GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction]
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b
        (((![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) ∘
          (finSumFinEquiv : Fin 0 ⊕ Fin 3 ≃ Fin 3)) ∘ Sum.inr)) ∘
        finSuccEquiv' 3 = ![.hyperplane, .hyperplane, .hyperplane, b] := by
    funext i
    fin_cases i <;> rfl
  simp only [hr, primaryPointVertex, and_self, ite_true]
  apply Finset.sum_eq_zero
  intro split hs
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  by_cases hz : split.2 = 0
  · rw [hz, classical_four]
    simp only [mul_zero]
  · rw [primaryScalar_hyperplane_eq_zero _ split.2 hz
      (splitting_planeDegree_right hd hs) (Fin 4) _ 0 rfl ij.2]
    simp only [mul_zero]

private theorem paper_pair (gamma : X.Curve) (m : ℕ) (delta : X.Curve)
    (hd : X.planeDegree delta = 0) (n : ℕ) (s : Fin 2) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 gamma m)
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![.hyperplane, .hyperplane, .hyperplane] = 0 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 gamma m)
  have h0 : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
  have h1 : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
  have he : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![.hyperplane, .hyperplane, .hyperplane] =
      remainderContraction X v (remainderVertex X v (coefficientVertex X v))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          (fundamental 2 (Fin 2) (by norm_num [StableArity]))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        (by exact (Pi.single s 1, (0 : Fin 3 → ℕ)))
        (by exact ((inferInstance : DecidableEq (Fin 2)),
          (inferInstance : DecidableEq (Fin 3)))) delta n
        ![.hyperplane, .hyperplane, .hyperplane] := by
    rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
    · rw [if_pos rfl, ← h0]
      rfl
    · rw [if_neg (by decide : (1 : Fin 2) ≠ 0), ← h1]
      rfl
  dsimp only
  rw [he, pair_hh_of_planeDegree_zero v _ n _ _ _ delta hd .hyperplane,
    remainderContraction, if_pos rfl]
  exact pair_main_primary_zero_of_planeDegree_zero gamma m delta hd n s

/-- The compressed actual BP HHH row has no primary coefficient at a
plane-zero effective remainder, including zero and mixed exceptional classes. -/
theorem pointCoefficient_primary_eq_zero_of_planeDegree_zero (gamma : X.Curve) (m : ℕ)
    (delta : X.Curve) (hd : X.planeDegree delta = 0) (n : ℕ) :
    BelorousskiPandharipande.pointCoefficient X n (gamma + delta)
      ![.hyperplane, .hyperplane, .hyperplane]
      (.inr (SurfaceQuery.points X 2 gamma m)) = 0 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 gamma m)
  have hterm (i : Fin 20) (e : Fin 6) :
      SurfaceGenusTwo.pointCoefficient X v (BelorousskiPandharipande.orbitCotangentTerm i e)
        (gamma + delta) n ![.hyperplane, .hyperplane, .hyperplane] =
      remainderPointCoefficient X v (coefficientVertex X v)
        (BelorousskiPandharipande.paperCotangentTerm i) delta n
        ![.hyperplane, .hyperplane, .hyperplane] := by
    have h := remainderPointCoefficient_eq X v (coefficientVertex X v) rfl
      (BelorousskiPandharipande.orbitCotangentTerm i e) delta n
      (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
    rw [SurfaceGenusTwoBlowupPSupport.remainder_orbit] at h
    exact h.symm
  change BelorousskiPandharipande.pointCoefficient X n (gamma + delta)
    ![.hyperplane, .hyperplane, .hyperplane] v = 0
  simp only [BelorousskiPandharipande.pointCoefficient, hterm,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fin.sum_univ_four]
  change -2 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 0) delta n
        ![.hyperplane, .hyperplane, .hyperplane]) +
    2 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 1) delta n
        ![.hyperplane, .hyperplane, .hyperplane]) +
    3 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 2) delta n
        ![.hyperplane, .hyperplane, .hyperplane]) +
    -3 * (6 * remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 3) delta n
        ![.hyperplane, .hyperplane, .hyperplane]) = 0
  have h2 := paper_pair gamma m delta hd n (0 : Fin 2)
  have h3 := paper_pair gamma m delta hd n (1 : Fin 2)
  simp only [ite_true, if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h2 h3
  rw [paper_zero v delta hd n, paper_one v delta hd n, h2, h3]
  ring

/-- Every same-plane primary column of the complete original normalized BP HHH
row is zero, including its own full class and incomparable effective classes.
No dimension or effective-subclass hypothesis prunes the row. -/
theorem primary_coefficient_eq_zero_of_same_planeDegree (beta gamma : X.Curve)
    (hd : X.planeDegree gamma = X.planeDegree beta) (m n : ℕ) :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X n beta 0
        (SurfaceGenusZero.pointLabels
          (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) n))
      {Sum.inr (SurfaceQuery.points X 2 gamma m)} = 0 := by
  by_cases hle : gamma ≤ beta
  · have hsplit : gamma + (beta - gamma) = beta := by
      funext i
      exact Nat.add_sub_of_le (hle i)
    have hzero : X.planeDegree (beta - gamma) = 0 := by
      have he := congrArg X.planeDegree hsplit
      rw [map_add] at he
      omega
    rw [← BelorousskiPandharipande.pointCoefficient_eq_full, ← hsplit]
    exact pointCoefficient_primary_eq_zero_of_planeDegree_zero gamma m _ hzero n
  · exact SurfaceGenusTwo.TermsBound.normalized_coefficient_eq_zero_of_not_le
      (BelorousskiPandharipande.genusTwoTerms_bound X n beta 0
        (SurfaceGenusZero.pointLabels
          (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) n))
      le_rfl (.inr (SurfaceQuery.points X 2 gamma m)) hle

/-- Any primary coefficient surviving in the complete BP HHH row strictly
lowers plane degree. Every lower-plane calibration and cotangent tail is retained. -/
theorem primary_coefficient_support (beta gamma : X.Curve) (m n : ℕ)
    (hc : RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X n beta 0
        (SurfaceGenusZero.pointLabels
          (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) n))
      {Sum.inr (SurfaceQuery.points X 2 gamma m)} ≠ 0) :
    X.planeDegree gamma < X.planeDegree beta := by
  have hle : gamma ≤ beta := by
    by_contra hn
    exact hc (SurfaceGenusTwo.TermsBound.normalized_coefficient_eq_zero_of_not_le
      (BelorousskiPandharipande.genusTwoTerms_bound X n beta 0
        (SurfaceGenusZero.pointLabels
          (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) n))
      le_rfl (.inr (SurfaceQuery.points X 2 gamma m)) hn)
  have hdle : X.planeDegree gamma ≤ X.planeDegree beta := hle (Fin.last X.blowups)
  by_contra hn
  have hd : X.planeDegree gamma = X.planeDegree beta := by omega
  exact hc (primary_coefficient_eq_zero_of_same_planeDegree beta gamma hd m n)

/-- Primary columns at equal or higher plane degree are absent from the full
BP HHH row. The original marking counts and normalization are unchanged. -/
theorem primary_coefficient_eq_zero_of_planeDegree_ge (beta gamma : X.Curve)
    (hd : X.planeDegree beta ≤ X.planeDegree gamma) (m n : ℕ) :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X n beta 0
        (SurfaceGenusZero.pointLabels
          (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) n))
      {Sum.inr (SurfaceQuery.points X 2 gamma m)} = 0 := by
  by_contra hc
  have ht := primary_coefficient_support beta gamma m n hc
  omega

/-- Actual canonical column support of the positive-energy P row: its own P
column is the only non-earlier canonical column. This is a collected-coefficient
support theorem, not a reconstruction recurrence or a claim about nonzero pivots. -/
theorem canonical_coefficient_support (beta gamma : X.Curve)
    (family : SurfaceGenusTwoBlowupOrder.Family X)
    (hbeta : 0 < X.effective.energy beta)
    (hc : RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X (X.effective.energy beta - 1)
        beta 0 (SurfaceGenusZero.pointLabels
          (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
          (X.effective.energy beta - 1)))
      {Sum.inr (family.query gamma)} ≠ 0) :
    (family = .point ∧ gamma = beta) ∨
      SurfaceGenusTwoBlowupOrder.Earlier X (gamma, family) (beta, .point) := by
  have hle : gamma ≤ beta := by
    by_contra hn
    have hb := BelorousskiPandharipande.genusTwoTerms_bound X (X.effective.energy beta - 1)
      beta 0 (SurfaceGenusZero.pointLabels
        (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
        (X.effective.energy beta - 1))
    have hv : SurfaceGenusZero.variableCurve (Sum.inr (family.query gamma)) = gamma := by
      cases family <;> rfl
    exact hc (hb.normalized_coefficient_eq_zero_of_not_le le_rfl
      (.inr (family.query gamma)) (by rwa [hv]))
  cases family with
  | hyperplane =>
    right
    exact SurfaceGenusTwoBlowupOrder.earlier_of_rank_lt X _ _
      (hle (Fin.last X.blowups)) (Nat.zero_lt_succ 0)
  | point =>
    by_cases he : gamma = beta
    · exact Or.inl ⟨rfl, he⟩
    · right
      have hsplit : gamma + (beta - gamma) = beta := by
        funext i
        exact Nat.add_sub_of_le (hle i)
      have hz : beta - gamma ≠ 0 := by
        intro hzero
        rw [hzero, add_zero] at hsplit
        exact he hsplit
      exact SurfaceGenusTwoBlowupOrder.earlier_of_effective_subclass X .point hsplit hz
  | primary =>
    right
    exact SurfaceGenusTwoBlowupOrder.earlier_of_planeDegree_lt X _ _
      (primary_coefficient_support beta gamma _ _ hc)
  | exceptional i =>
    right
    exact SurfaceGenusTwoBlowupOrder.earlier_of_planeDegree_lt X _ _
      (SurfaceGenusTwoBlowupPSupport.exceptional_coefficient_support beta gamma i hbeta hc)

end AxiomaticGW.SurfaceGenusTwoBlowupPPrimarySupport

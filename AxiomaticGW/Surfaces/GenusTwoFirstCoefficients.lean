/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.OnePsiSupport
public import AxiomaticGW.Surfaces.GenusTwoRemainder
public import AxiomaticGW.Coefficients.RenamedCoefficient

/-!
# First-descendant coefficients on the fixed surfaces

Calibration tails of a single ancestor psi have primary main components. They
cannot contribute to a requested first descendant, even at a smaller effective
class. This coefficient statement retains the full normalization polynomial:
it does not assert the plane-specific cancellation of all calibration tails.

The resulting component shortcut and signed point-pullback identities preserve
every full curve class, state, dimension condition and rational complement.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceFirstDescendant
variable {X : SurfaceTarget}

/-- A positive first power distinguishes its full query from every primary point query. -/
theorem query_ne_points (beta gamma : X.Curve) (b : SurfaceBasisLabel X) (n m : ℕ) :
    Sum.inr (SurfaceQuery.points X 2 gamma m) ≠
      (Sum.inr (query 2 beta b n) : SurfacePolynomialReduction.Variable X) := by
  intro he
  have hi : (⟨b, 1⟩ : SurfaceInsertion X) ∈ (SurfaceQuery.points X 2 gamma m).insertions := by
    rw [Sum.inr.inj he]
    exact List.mem_cons_self
  obtain ⟨_, hp⟩ := List.mem_replicate.mp hi
  have hz := congrArg SurfaceInsertion.psi hp
  norm_num only at hz

end AxiomaticGW.SurfaceFirstDescendant

namespace AxiomaticGW.SurfacePolynomialReduction
variable {X : SurfaceTarget}

/-- Identifying the unique first-power insertion removes dependence on the
internal ordering, for direct normalization on every fixed surface. -/
theorem directNormalizedTerms_of_onePsi (q : SurfaceAncestorKey X)
    (hg : 2 ≤ q.genus) (b : SurfaceBasisLabel X)
    (m : Multiset (SurfaceBasisLabel X))
    (hi : q.insertions = ⟨b, 1⟩ ::ₘ m.map (fun c ↦ ⟨c, 0⟩)) :
    directNormalizedTerms q = RationalTerms.rename Sum.inr
      (SurfaceFirstDescendant.terms q.genus q.beta b m) := by
  have hp : q.totalPsi = 1 := by
    simp only [SurfaceAncestorKey.totalPsi, hi, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_map, Function.comp_def, Multiset.map_const', Multiset.sum_replicate,
      nsmul_zero, add_zero]
  have hb : q.onePsiInsertion hp = ⟨b, 1⟩ := by
    have ht := q.onePsiInsertion_mem hp
    rw [hi, Multiset.mem_cons] at ht
    rcases ht with ht | ht
    · exact ht
    · obtain ⟨c, _, he⟩ := Multiset.mem_map.mp ht
      have hz := q.onePsiInsertion_power hp
      rw [← he] at hz
      cases hz
  rw [directNormalizedTerms, dif_pos ⟨hg, hp⟩]
  simp only [SurfaceAncestorKey.onePsiPrimaries, hb, hi, Multiset.erase_cons_head,
    Multiset.map_map, Function.comp_def, Multiset.map_id']

/-- Added primary points preserve the specified descendant and every original label. -/
theorem directNormalizedTerms_onePsi_addPoints (q : SurfaceAncestorKey X)
    (hg : 2 ≤ q.genus) (b : SurfaceBasisLabel X)
    (m : Multiset (SurfaceBasisLabel X))
    (hi : q.insertions = ⟨b, 1⟩ ::ₘ m.map (fun c ↦ ⟨c, 0⟩)) (n : ℕ) :
    directNormalizedTerms (q.addPoints n) = RationalTerms.rename Sum.inr
      (SurfaceFirstDescendant.terms q.genus q.beta b (Multiset.replicate n .point + m)) := by
  apply directNormalizedTerms_of_onePsi (q.addPoints n) hg b _
  simp only [SurfaceAncestorKey.addPoints, hi, Multiset.map_add, Multiset.map_replicate,
    Multiset.add_cons]

/-- A specified first-power marking gives direct canonical terms without inspecting
the sort; all other label multiplicities and the full class are retained. -/
theorem directNormalizedTerms_onePsi_ofLabels (g : ℕ) (hg : 2 ≤ g)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity g S) (s : S)
    (beta : X.Curve) (a : S → SurfaceBasisLabel X) (n : ℕ) :
    directNormalizedTerms
      ((SurfaceAncestorKey.ofLabels g S h beta (Pi.single s 1) a).addPoints n) =
      RationalTerms.rename Sum.inr (SurfaceFirstDescendant.terms g beta (a s)
        (Multiset.replicate n .point + (Finset.univ.erase s).val.map a)) := by
  apply directNormalizedTerms_onePsi_addPoints _ hg (a s) _
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

/-- A canonical primary component has no coefficient at a nonprimary request. -/
theorem coefficient_canonicalPrimaryTerms_eq_zero_of_not_points
    (q : SurfaceAncestorKey X) (hg : q.genus = 2) (hp : q.IsPrimary)
    (v : Variable X) (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v) :
    RationalTerms.coefficient (canonicalPrimaryTerms q) {v} = 0 := by
  rw [canonicalPrimaryTerms, if_pos ⟨by omega, hp⟩, hg,
    SurfaceFirstDescendant.primaryTerms, RationalTerms.coefficient_rename_scale]
  unfold SurfaceFirstDescendant.dimensionTerms
  split_ifs with hd
  · rw [RationalTerms.coefficient_rename_term]
    simp only [Multiset.map_singleton, Multiset.singleton_inj, if_neg (hv _ _), mul_zero]
  · simp only [RationalTerms.rename_zero, RationalTerms.coefficient_zero, mul_zero]

/-- Calibration tails cannot contribute to a nonprimary genus-two coefficient,
including requests at smaller energy than the original component. -/
theorem coefficient_normalizedTerms_eq_direct_of_not_points
    (q : SurfaceAncestorKey X) (hg : q.genus = 2)
    (v : Variable X) (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v) :
    RationalTerms.coefficient (normalizedTerms q) {v} =
      RationalTerms.coefficient (directNormalizedTerms q) {v} := by
  unfold normalizedTerms directNormalizedTerms
  split_ifs with h
  · rw [RationalTerms.coefficient_add]
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
    intro split _
    rw [RationalTerms.coefficient_sum]
    apply Finset.sum_eq_zero
    intro b _
    let r := SurfaceAncestorKey.ofLabels q.genus (Fin q.orderedInsertions.length)
      q.ordered_stable split.1 0 (Function.update q.orderedLabels (q.onePsiMark h.2) b)
    have hr : r.genus = 2 := hg
    have hp : r.IsPrimary := by
      intro t ht
      change t ∈ (Finset.univ : Finset (Fin q.orderedInsertions.length)).val.map
        (fun j ↦ ⟨Function.update q.orderedLabels (q.onePsiMark h.2) b j, 0⟩) at ht
      obtain ⟨s, _, rfl⟩ := Multiset.mem_map.mp ht
      rfl
    rw [RationalTerms.coefficient_scale,
      coefficient_canonicalPrimaryTerms_eq_zero_of_not_points r hr hp v hv, mul_zero]
  · rfl

end AxiomaticGW.SurfacePolynomialReduction

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction GluingExpression
open SurfaceGenusZero (variableCurve)
variable {X : SurfaceTarget}

/-- Partial reconstruction and full normalization preserve the direct coefficient
of any nonprimary request at genus two. -/
theorem coefficient_residualTerms_eq_direct_of_not_points (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (q : SurfaceAncestorKey X) (hg : q.genus = 2) :
    RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
      (residualTerms q)) {v} =
      if q.DimensionCompatible then RationalTerms.coefficient (directNormalizedTerms q) {v}
      else 0 := by
  unfold residualTerms
  by_cases hd : q.DimensionCompatible
  · rw [if_pos hd, if_neg (by omega : ¬q.genus ≤ 1), if_pos hd,
      RationalTerms.coefficient_affineSubstitute_term, Multiset.map_singleton,
      Multiset.sum_singleton, one_mul,
      coefficient_normalizedTerms_eq_direct_of_not_points q hg v hv]
  · rw [if_neg hd, if_neg hd, RationalTerms.coefficient_affineSubstitute_zero]

/-- The terminal first-power coefficient exposes the canonical descendant terms,
while keeping its dimension check and the complete normalizer on the left. -/
theorem coefficient_residualTerms_onePsi_of_not_points (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (beta : X.Curve) (a : S → SurfaceBasisLabel X) (n : ℕ) :
    let q := (SurfaceAncestorKey.ofLabels 2 S h beta (Pi.single s 1) a).addPoints n
    RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
      (residualTerms q)) {v} =
      if q.DimensionCompatible then
        RationalTerms.coefficient (RationalTerms.rename Sum.inr
          (SurfaceFirstDescendant.terms 2 beta (a s)
            (Multiset.replicate n .point + (Finset.univ.erase s).val.map a))) {v}
      else 0 := by
  dsimp only
  rw [coefficient_residualTerms_eq_direct_of_not_points v hv _ rfl,
    directNormalizedTerms_onePsi_ofLabels 2 le_rfl S h s beta a n]

/-- Primary terms cannot contribute to a nonprimary request on any fixed surface. -/
theorem coefficient_residualTerms_primary_eq_zero_of_not_points (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (q : SurfaceAncestorKey X) (hg : q.genus = 2) (hp : q.IsPrimary) :
    RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
      (residualTerms q)) {v} = 0 := by
  rw [coefficient_residualTerms_eq_direct_of_not_points v hv q hg]
  split_ifs with hd
  · have hn : ¬(2 ≤ q.genus ∧ q.totalPsi = 1) := by
      rw [q.totalPsi_eq_zero_iff.mpr hp]
      exact fun h ↦ Nat.zero_ne_one h.2
    rw [directNormalizedTerms, dif_neg hn,
      coefficient_canonicalPrimaryTerms_eq_zero_of_not_points q hg hp v hv]
  · rfl

/-- Reject a different full component class before normalizing a requested first
descendant. Other genera retain the original reconstructed constant. -/
def firstCoefficientVertex (X : SurfaceTarget) (beta : X.Curve)
    (b : SurfaceBasisLabel X) (n : ℕ) : SurfaceVertexValues X ℚ :=
  let v : Variable X := .inr (SurfaceFirstDescendant.query 2 beta b n)
  fun g S _ h gamma k a ↦
    if g = 2 then
      if beta = gamma then
        let q := SurfaceAncestorKey.ofLabels g S h gamma k a
        if q.DimensionCompatible then RationalTerms.coefficient (directNormalizedTerms q) {v}
        else 0
      else 0
    else RationalTerms.coefficient (vertexTerms X g S h gamma k a) 0

/-- First-descendant class pruning equals the complete original component
coefficient for every class, label and point count. -/
theorem firstCoefficientVertex_eq (beta : X.Curve) (b : SurfaceBasisLabel X) (n : ℕ) :
    firstCoefficientVertex X beta b n =
      coefficientVertex X (.inr (SurfaceFirstDescendant.query 2 beta b n)) := by
  let v : Variable X := .inr (SurfaceFirstDescendant.query 2 beta b n)
  have hv : ∀ gamma m, Sum.inr (SurfaceQuery.points X 2 gamma m) ≠ v :=
    fun gamma m ↦ SurfaceFirstDescendant.query_ne_points beta gamma b n m
  funext g S _ h gamma k a
  unfold firstCoefficientVertex coefficientVertex
  by_cases hg : g = 2
  · subst g
    rw [if_pos rfl, if_pos rfl]
    let q := SurfaceAncestorKey.ofLabels 2 S h gamma k a
    change (if beta = gamma then
        if q.DimensionCompatible then RationalTerms.coefficient (directNormalizedTerms q) {v}
        else 0
      else 0) = RationalTerms.coefficient
        (RationalTerms.affineSubstitute normalizedTerms (residualTerms q)) {v}
    rw [coefficient_residualTerms_eq_direct_of_not_points v hv q rfl]
    split_ifs with hb hd
    · rfl
    · rfl
    · exact (coefficient_directNormalizedTerms_eq_zero q le_rfl v hb).symm
    · rfl
  · rw [if_neg hg, if_neg hg]

/-- A nonprimary genus-two coefficient vanishes at every different full class. -/
theorem coefficientVertex_genusTwo_eq_zero_of_class_ne_of_not_points (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (S : Type) [Fintype S] (h : StableArity 2 S) (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) (hb : variableCurve v ≠ beta) :
    coefficientVertex X v 2 S h beta k a = 0 := by
  rw [coefficientVertex, if_pos rfl, vertexTerms,
    coefficient_residualTerms_eq_direct_of_not_points v hv _ rfl]
  split_ifs with hd
  · exact coefficient_directNormalizedTerms_eq_zero _ le_rfl v hb
  · rfl

/-- Without further point pullbacks, the main component consumes no effective
remainder in a nonprimary coefficient. Rational complements are retained. -/
theorem remainderVertex_zero_of_not_points (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (S : Type) [Fintype S] (h : StableArity 2 S) (d : S → ℕ) (l : DecidableEq S)
    (delta : X.Curve) (a : S → SurfaceBasisLabel X) :
    remainderVertex X v (coefficientVertex X v) 0 2 S h d l delta a =
      if delta = 0 then coefficientVertex X v 2 S h (variableCurve v) d a else 0 := by
  rw [remainderVertex]
  dsimp only
  by_cases hz : delta = 0
  · rw [hz, add_zero, if_pos rfl]
  · rw [if_neg hz]
    apply coefficientVertex_genusTwo_eq_zero_of_class_ne_of_not_points v hv
    intro he
    apply hz
    apply add_left_cancel (a := variableCurve v)
    exact he.symm.trans (add_zero _).symm

/-- All primary main components vanish in a nonprimary coefficient, after any
number of point pullbacks and at every effective remainder. -/
theorem remainderVertex_primary_eq_zero_of_not_points (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (n : ℕ) (S : Type) [Fintype S] (h : StableArity 2 S) (l : DecidableEq S)
    (delta : X.Curve) (a : S → SurfaceBasisLabel X) :
    remainderVertex X v (coefficientVertex X v) n 2 S h 0 l delta a = 0 := by
  rw [remainderVertex_eq X v _ rfl, vertex_primary_genusTwo_eq]
  apply coefficient_residualTerms_primary_eq_zero_of_not_points v hv _ rfl
  intro t ht
  rcases Multiset.mem_add.mp ht with ht | ht
  · exact congrArg SurfaceInsertion.psi (Multiset.mem_replicate.mp ht).2
  · obtain ⟨s, _, rfl⟩ := Multiset.mem_map.mp ht
    rfl

/-- The actual first-power tail has a primary main component, so its coefficient
at a nonprimary request is zero, independently of every rational-tail value. -/
theorem remainderContraction_onePsi_tail_eq_zero_of_not_points (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (delta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) :
    let z := CotangentTerm.tail h (Pi.single s 1) s
    remainderContraction X v (remainderVertex X v (coefficientVertex X v))
      z.expression z.decoration z.labels delta n (Option.elim · .point a) = 0 := by
  have hd : Function.update (Pi.single s 1 : S → ℕ) s
      ((Pi.single s 1 : S → ℕ) s - 1) = (0 : S → ℕ) := by
    funext t
    by_cases ht : t = s
    · subst t
      simp only [Function.update_self, Pi.single_eq_same, Nat.sub_self, Pi.zero_apply]
    · rw [Function.update_of_ne ht, Pi.single_eq_of_ne ht]
      rfl
  dsimp only
  simp only [CotangentTerm.tail, CotangentTerm.relabel, CotangentTerm.separating,
    CotangentTerm.fundamental, remainderContraction, ite_true, hd,
    remainderVertex_primary_eq_zero_of_not_points v hv, zero_mul, mul_zero,
    Finset.sum_const_zero]

/-- One primary point preserves the old first power and subtracts its actual
rational tail, with all class splits and signs unchanged on every surface. -/
theorem remainderVertex_onePsi_step (v : Variable X)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (n : ℕ) (a : S → SurfaceBasisLabel X) (delta : X.Curve) :
    let main := remainderVertex X v (coefficientVertex X v)
    let z := CotangentTerm.tail h (Pi.single s 1) s
    main (n + 1) 2 S h (Pi.single s 1) inferInstance delta a =
      main n 2 (Option S) h.option (Pi.single (some s) 1) inferInstance delta
        (Option.elim · .point a) -
      remainderContraction X v main z.expression z.decoration z.labels
        delta n (Option.elim · .point a) := by
  let main := remainderVertex X v (coefficientVertex X v)
  let z := CotangentTerm.tail h (Pi.single s 1) s
  have ht := (remainderContraction_eq X v main z.expression le_rfl rfl
    z.decoration z.labels delta n (Option.elim · .point a)
    (fun m _ T _ hT k lT epsilon b ↦
      remainderVertex_eq X v _ rfl m T hT k lT epsilon b)).symm
  have hf : Finset.univ.filter (fun t ↦ (Pi.single s 1 : S → ℕ) t ≠ 0) = {s} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases ht : t = s
    · subst t
      simp only [Pi.single_eq_same]
      decide
    · simp only [Pi.single_eq_of_ne ht, ne_eq, not_true_eq_false, ht]
  have hk : (fun t : Option S ↦ t.elim 0 (Pi.single s 1)) = Pi.single (some s) 1 := by
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
  dsimp only
  rw [remainderVertex_eq X v _ rfl, SurfacePointPullback.vertex_succ]
  simp only [GluingExpression.addCotangentMarking, hf, Finset.singleton_val,
    Multiset.map_add, Multiset.map_singleton, Multiset.sum_add, Multiset.sum_singleton,
    Int.cast_one, Int.cast_neg, one_mul, neg_one_mul]
  rw [← sub_eq_add_neg]
  change SurfacePointPullback.vertex X (coefficientVertex X v) n 2 (Option S)
    h.option (fun t ↦ t.elim 0 (Pi.single s 1)) inferInstance
      (variableCurve v + delta) (Option.elim · .point a) -
    z.expression.pointContraction X (SurfacePointPullback.vertex X
      (coefficientVertex X v)) z.decoration z.labels
      (variableCurve v + delta) n (Option.elim · .point a) = _
  rw [hk, ht, ← remainderVertex_eq X v _ rfl]

/-- A first power creates only primary tail corrections, which cannot contribute
to a nonprimary request. The remaining main query consumes no remainder. -/
theorem remainderVertex_onePsi_of_not_points (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (n : ℕ) (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (delta : X.Curve) (a : S → SurfaceBasisLabel X) :
    remainderVertex X v (coefficientVertex X v) n 2 S h (Pi.single s 1)
      inferInstance delta a =
      if delta = 0 then
        RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
          (residualTerms ((SurfaceAncestorKey.ofLabels 2 S h (variableCurve v)
            (Pi.single s 1) a).addPoints n))) {v}
      else 0 := by
  induction n generalizing S with
  | zero =>
    rw [remainderVertex_zero_of_not_points v hv]
    simp only [SurfaceAncestorKey.addPoints_zero, coefficientVertex, ite_true, vertexTerms]
  | succ n ih =>
    rw [remainderVertex_onePsi_step,
      remainderContraction_onePsi_tail_eq_zero_of_not_points v hv, sub_zero]
    rw [ih (Option S) h.option (some s) (Option.elim · .point a)]
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
      (variableCurve v) (Pi.single s 1) a n]

end AxiomaticGW.SurfaceGenusTwo

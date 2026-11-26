/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.DecoratedTermDegree
public import AxiomaticGW.Tautological.GenusTwoPsiForgetful

/-!
# The leading term in arbitrary marked genus-two psi relations

Adding markings to a fundamental cotangent monomial leaves one fundamental
term with coefficient one. Every other term has a boundary edge, including
the signed tails created from the leading term itself. This isolates the
square and product relations for recursive surface evaluation without
discarding their forgetful corrections.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo
open GluingExpression

/-- Original powers extended by zero at each newly added marking. -/
def markedPowers {S : Type} (d : S → ℕ) : (n : ℕ) → ExtraMarkings n S → ℕ
  | 0 => d
  | n + 1 => fun s ↦ s.elim 0 (markedPowers d n)

theorem sum_markedPowers {S : Type} [Fintype S] (d : S → ℕ) (n : ℕ) :
    (∑ s, markedPowers d n s) = ∑ s, d s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [markedPowers, Fintype.sum_option, Option.elim_none, Option.elim_some, zero_add, ih]

theorem markedPowers_oldLabel {S : Type} (d : S → ℕ) (n : ℕ) (s : S) :
    markedPowers d n (ExtraMarkings.oldLabel n s) = d s := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- The unchanged smooth component with the original powers and additional labels. -/
def markedFundamental {g : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (h : StableArity g S) (d : S → ℕ) (n : ℕ) : CotangentTerm g (ExtraMarkings n S) :=
  letI := ExtraMarkings.decidableEq S n
  .fundamental g (ExtraMarkings n S) (h.extraMarkings n) (markedPowers d n)

/-- All signed tails in the pullback of the leading monomial. Repeated
placements remain distinct summands with their original integer weights. -/
def fundamentalCorrections {g : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (h : StableArity g S) (d : S → ℕ) :
    (n : ℕ) → Multiset (ℤ × CotangentTerm g (ExtraMarkings n S))
  | 0 => 0
  | n + 1 =>
      letI := ExtraMarkings.decidableEq S n
      (Finset.univ.filter (fun s ↦ markedPowers d n s ≠ 0)).val.map
        (fun s ↦ (-1, CotangentTerm.tail (h.extraMarkings n) (markedPowers d n) s)) +
      (fundamentalCorrections h d n).bind fun t ↦
        t.2.addMarking.map fun w ↦ (t.1 * w.1, w.2)

/-- Exact decomposition of the existing pullback algorithm; the leading
coefficient is one for every number of added markings. -/
theorem fundamental_addMarkings {g : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (h : StableArity g S) (d : S → ℕ) (n : ℕ) :
    (CotangentTerm.fundamental g S h d).addMarkings n =
      {(1, markedFundamental h d n)} + fundamentalCorrections h d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [CotangentTerm.addMarkings, ih, Multiset.add_bind, Multiset.singleton_bind]
    simp only [one_mul, Multiset.map_id', fundamentalCorrections]
    change ({(1, markedFundamental h d (n + 1))} + _) + _ = _
    exact add_assoc _ _ _

/-- No correction can be another smooth leading term: a new tail has an
edge, and the existing signed pullback never removes an edge. -/
theorem fundamentalCorrections_edge_pos {g : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (h : StableArity g S) (d : S → ℕ) (n : ℕ)
    (t : ℤ × CotangentTerm g (ExtraMarkings n S)) (ht : t ∈ fundamentalCorrections h d n) :
    0 < (t.2.expression.decoratedGraph t.2.decoration).graph.edgeCount := by
  induction n with
  | zero => exact (Multiset.notMem_zero _ ht).elim
  | succ n ih =>
    letI := ExtraMarkings.decidableEq S n
    rcases Multiset.mem_add.mp ht with ht | ht
    · obtain ⟨s, _, rfl⟩ := Multiset.mem_map.mp ht
      exact Nat.zero_lt_one
    · obtain ⟨z, hz, ht⟩ := Multiset.mem_bind.mp ht
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp ht
      exact (ih z hz).trans_le (z.2.expression.addCotangentMarking_edgeCount_le
        z.2.decoration z.2.labels w hw)

/-- Boundary part of the full pulled relation, including the corrections
created from its smooth term. The supplied boundary coefficients stay signed. -/
def psiBoundary {S : Type} [Fintype S] [DecidableEq S]
    (h : StableArity 2 S) (d : S → ℕ) (b : CotangentCombination 2 S) (n : ℕ) :
    CotangentCombination 2 (ExtraMarkings n S) :=
  (fundamentalCorrections h d n).map (fun t ↦ ((t.1 : ℚ), t.2)) + b.pullback n

/-- Equality in the actual expression syntax, before strata quotients,
geometric realization or numerical evaluation. -/
theorem pullback_eq_leading_add_boundary {S : Type} [Fintype S] [DecidableEq S]
    (h : StableArity 2 S) (d : S → ℕ) (b : CotangentCombination 2 S) (n : ℕ) :
    ({(1, CotangentTerm.fundamental 2 S h d)} + b).pullback n =
      {(1, markedFundamental h d n)} + psiBoundary h d b n := by
  simp only [CotangentCombination.pullback, Multiset.add_bind, Multiset.singleton_bind,
    one_mul, fundamental_addMarkings, Multiset.map_add, Multiset.map_singleton,
    Int.cast_one, psiBoundary, add_assoc]

/-- Every term of the isolated boundary still occurs in the complete
original pullback, with its coefficient and construction unchanged. -/
theorem psiBoundary_mem_pullback {S : Type} [Fintype S] [DecidableEq S]
    (h : StableArity 2 S) (d : S → ℕ) (b : CotangentCombination 2 S) (n : ℕ)
    (t : ℚ × CotangentTerm 2 (ExtraMarkings n S)) (ht : t ∈ psiBoundary h d b n) :
    t ∈ ({(1, CotangentTerm.fundamental 2 S h d)} + b).pullback n := by
  rw [pullback_eq_leading_add_boundary]
  exact Multiset.mem_add.mpr (Or.inr ht)

/-- Genuine source boundary terms and leading-term corrections all retain
at least one edge, independently of cancellation between coefficients. -/
theorem psiBoundary_edge_pos {S : Type} [Fintype S] [DecidableEq S]
    (h : StableArity 2 S) (d : S → ℕ) (b : CotangentCombination 2 S)
    (hb : ∀ t ∈ b, 0 < (t.2.expression.decoratedGraph t.2.decoration).graph.edgeCount)
    (n : ℕ) (t : ℚ × CotangentTerm 2 (ExtraMarkings n S))
    (ht : t ∈ psiBoundary h d b n) :
    0 < (t.2.expression.decoratedGraph t.2.decoration).graph.edgeCount := by
  rcases Multiset.mem_add.mp ht with ht | ht
  · obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp ht
    exact fundamentalCorrections_edge_pos h d n z hz
  · obtain ⟨z, hz, w, hw, rfl⟩ := (CotangentCombination.mem_pullback b n t).mp ht
    exact (hb z hz).trans_le (z.2.addMarkings_edgeCount_le n w hw)

/-- Solve for the leading term by negating the full signed boundary. Only
genus-zero/one components are evaluated; genus-two dependencies stay explicit. -/
def boundaryReductionTerms {S : Type} [Fintype S] (X : SurfaceTarget)
    (b : CotangentCombination 2 S) (beta : X.Curve) (k : S → ℕ)
    (a : S → SurfaceBasisLabel X) : RationalTerms (SurfaceAncestorKey X) :=
  b.bind fun t ↦ RationalTerms.scale (-t.1)
    (t.2.expression.surfaceDecoratedTerms X (vertexTerms X) t.2.decoration beta k a)

/-- Every residual monomial is affine in genus two and preserves the full
effective curve-class remainder, before any coefficient collection. -/
theorem boundaryReductionTerms_bound {S : Type} [Fintype S] (X : SurfaceTarget)
    (b : CotangentCombination 2 S) (beta : X.Curve) (k : S → ℕ)
    (a : S → SurfaceBasisLabel X) :
    TermsBound 2 beta (boundaryReductionTerms X b beta k a) := by
  apply termsBound_bind
  intro t _
  exact termsBound_scale (termsBound_decorated t.2.expression t.2.decoration beta k a) (-t.1)

/-- The two removed psi powers pay for codimension two. A boundary edge
forces every residual genus-two dependency to have strictly smaller psi degree. -/
theorem boundaryReductionTerms_dependency {S : Type} [Fintype S] (X : SurfaceTarget)
    (b : CotangentCombination 2 S)
    (hb : ∀ t ∈ b, (t.2.expression.decoratedGraph t.2.decoration).codimension = 2 ∧
      0 < (t.2.expression.decoratedGraph t.2.decoration).graph.edgeCount)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X)
    {t : ℚ × Multiset (SurfaceAncestorKey X)}
    (ht : t ∈ boundaryReductionTerms X b beta k a)
    (q : SurfaceAncestorKey X) (hq : q ∈ t.2) :
    q.genus = 2 ∧ q.DimensionCompatible ∧ q.totalPsi < 2 + ∑ s, k s ∧
      (q.beta = beta ∨ X.effective.energy q.beta < X.effective.energy beta) := by
  have hdata := (boundaryReductionTerms_bound X b beta k a t ht).dependency q hq
  obtain ⟨z, hz, ht⟩ := Multiset.mem_bind.mp ht
  obtain ⟨_, w, hw, rfl⟩ := RationalTerms.mem_scale.mp ht
  have he := decoratedTerms_psi_bound z.2.expression z.2.decoration beta k a hw q hq
  obtain ⟨hc, hedge⟩ := hb z hz
  exact ⟨hdata.1, hdata.2.1, by omega, hdata.2.2⟩

/-- Evaluating the residual polynomial is the negative of the complete
geometric boundary contraction, with all labels and node powers retained. -/
theorem eval_boundaryReductionTerms {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {I : StableCurveIntegration C} (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    (hzero : ∀ q : SurfaceAncestorKey X, q.genus = 0 →
      SurfaceGenusZero.ancestorValue X q = q.eval Omega P I)
    (hone : ∀ q : SurfaceAncestorKey X, q.genus = 1 →
      SurfaceGenusOne.ancestorValue X q = q.eval Omega P I)
    {S : Type} [Fintype S] (b : CotangentCombination 2 S) (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    RationalTerms.eval (SurfaceAncestorKey.eval Omega P I)
      (boundaryReductionTerms X b beta k a) =
      -b.gwContraction Omega P I beta k (fun s ↦ (a s).value) := by
  have hbind {σ : Type 1} (s : Multiset σ)
      (f : σ → RationalTerms (SurfaceAncestorKey X)) :
      RationalTerms.eval (SurfaceAncestorKey.eval Omega P I) (s.bind f) =
        (s.map fun i ↦ RationalTerms.eval (SurfaceAncestorKey.eval Omega P I) (f i)).sum := by
    simp only [RationalTerms.eval, Multiset.map_bind, Multiset.sum_bind]
  simp only [boundaryReductionTerms, hbind, RationalTerms.eval_scale,
    Algebra.algebraMap_self_apply, eval_decoratedTerms P T hzero hone,
    CotangentCombination.gwContraction, Rat.smul_def, Rat.cast_id, neg_mul,
    ← Multiset.sum_map_neg]

end AxiomaticGW.SurfaceGenusTwo

namespace AxiomaticGW.GenusTwoPsiSquare
open GluingExpression SurfaceGenusTwo

/-- The ten signed source boundary terms in the original square relation. -/
def signedBoundary : CotangentCombination 2 (Fin 1) :=
  Finset.univ.val.map fun i ↦ (-boundary (boundaryIndex i), boundaryCotangentTerm i)

/-- All original boundary placements and the leading square's signed tails. -/
def boundaryRemainder (n : ℕ) : CotangentCombination 2 (ExtraMarkings n (Fin 1)) :=
  psiBoundary stableArity (fun _ : Fin 1 ↦ 2) signedBoundary n

/-- The original relation has exactly one smooth leading square at every arity. -/
theorem pullback_eq_leading_add_boundary (n : ℕ) :
    cotangentRelation.pullback n =
      {(1, markedFundamental stableArity (fun _ : Fin 1 ↦ 2) n)} + boundaryRemainder n :=
  SurfaceGenusTwo.pullback_eq_leading_add_boundary stableArity _ signedBoundary n

/-- Every other term has an edge and retains codimension two. -/
theorem boundaryRemainder_bounds (n : ℕ)
    (t : ℚ × CotangentTerm 2 (ExtraMarkings n (Fin 1))) (ht : t ∈ boundaryRemainder n) :
    (t.2.expression.decoratedGraph t.2.decoration).codimension = 2 ∧
      0 < (t.2.expression.decoratedGraph t.2.decoration).graph.edgeCount := by
  constructor
  · apply pulled_term_codimension n t
    rw [pullback_eq_leading_add_boundary]
    exact Multiset.mem_add.mpr (Or.inr ht)
  · apply psiBoundary_edge_pos stableArity _ signedBoundary _ n t ht
    intro z hz
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hz
    have he : ∀ i : Fin 10,
        0 < ((boundaryCotangentTerm i).expression.decoratedGraph
          (boundaryCotangentTerm i).decoration).graph.edgeCount := by decide +kernel
    exact he i

end AxiomaticGW.GenusTwoPsiSquare

namespace AxiomaticGW.GenusTwoPsiProduct
open GluingExpression SurfaceGenusTwo

/-- The twenty-five signed source boundary terms in the original product relation. -/
def signedBoundary : CotangentCombination 2 (Fin 2) :=
  Finset.univ.val.map fun i ↦ (-boundary (boundaryIndex i), boundaryCotangentTerm i)

/-- All original boundary placements and the leading product's signed tails. -/
def boundaryRemainder (n : ℕ) : CotangentCombination 2 (ExtraMarkings n (Fin 2)) :=
  psiBoundary stableArity (fun _ : Fin 2 ↦ 1) signedBoundary n

/-- The original relation has exactly one smooth leading product at every arity. -/
theorem pullback_eq_leading_add_boundary (n : ℕ) :
    cotangentRelation.pullback n =
      {(1, markedFundamental stableArity (fun _ : Fin 2 ↦ 1) n)} + boundaryRemainder n :=
  SurfaceGenusTwo.pullback_eq_leading_add_boundary stableArity _ signedBoundary n

/-- This includes the genus-two rational-tail term and all of its corrections. -/
theorem boundaryRemainder_bounds (n : ℕ)
    (t : ℚ × CotangentTerm 2 (ExtraMarkings n (Fin 2))) (ht : t ∈ boundaryRemainder n) :
    (t.2.expression.decoratedGraph t.2.decoration).codimension = 2 ∧
      0 < (t.2.expression.decoratedGraph t.2.decoration).graph.edgeCount := by
  constructor
  · apply pulled_term_codimension n t
    rw [pullback_eq_leading_add_boundary]
    exact Multiset.mem_add.mpr (Or.inr ht)
  · apply psiBoundary_edge_pos stableArity _ signedBoundary _ n t ht
    intro z hz
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hz
    have he : ∀ i : Fin 25,
        0 < ((boundaryCotangentTerm i).expression.decoratedGraph
          (boundaryCotangentTerm i).decoration).graph.edgeCount := by decide +kernel
    exact he i

end AxiomaticGW.GenusTwoPsiProduct

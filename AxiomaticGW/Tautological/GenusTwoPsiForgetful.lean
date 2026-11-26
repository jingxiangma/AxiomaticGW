/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.CotangentCombination
public import AxiomaticGW.Tautological.GenusTwoPsiGluing
public import AxiomaticGW.Tautological.GenusTwoPsiProductGluing
public import AxiomaticGW.Tautological.DecoratedGluingMarkingBounds

/-!
# The complete genus-two psi relations with additional markings

The original square and product relations are bundled as explicit signed
cotangent combinations. Universal-curve pullback retains every component
placement and rational-tail correction, including corrections at node flags.
The class equation follows from the original generators and primitive laws.
No new higher-arity 3-spin vanishing or numerical seed is assumed.
-/

@[expose] public section

namespace AxiomaticGW
open GluingExpression RelationCertificate PsiBoundaryExpansion
universe u
attribute [local instance] strataRealizationModule

namespace GenusTwoPsiSquare

/-- The leading monomial retains its old labels before any markings are added. -/
def leadingCotangentTerm : CotangentTerm 2 (Fin 1) :=
  .fundamental 2 (Fin 1) stableArity (fun _ ↦ 2)

/-- The computational decisions of the original boundary components. -/
def boundaryLabelDecisions (i : Fin 10) : (boundaryTerm i).1.DecidableLabels :=
  match i with
  | ⟨0, _⟩ => by
    dsimp [boundaryTerm, separatingExpression, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨1, _⟩ => by
    dsimp [boundaryTerm, separatingExpression, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨2, _⟩ => by
    dsimp [boundaryTerm, chainExpression, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨3, _⟩ => by
    dsimp [boundaryTerm, separatingExpression, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨4, _⟩ => by
    dsimp [boundaryTerm, loopExpression, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    exact inferInstance
  | ⟨5, _⟩ => by
    dsimp [boundaryTerm, loopExpression, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    exact inferInstance
  | ⟨6, _⟩ => by
    dsimp [boundaryTerm, parallelExpression, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨7, _⟩ => by
    dsimp [boundaryTerm, loopBridgeMarkedEllipticExpression, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨8, _⟩ => by
    dsimp [boundaryTerm, loopBridgeMarkedRationalExpression, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨9, _⟩ => by
    dsimp [boundaryTerm, twoLoopsExpression, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    exact inferInstance
  | ⟨j + 10, h⟩ => False.elim (by omega)

/-- The held boundary construction, with executable finite label decisions. -/
def boundaryCotangentTerm (i : Fin 10) : CotangentTerm 2 (Fin 1) :=
  ⟨(boundaryTerm i).1, (boundaryTerm i).2, boundaryLabelDecisions i⟩

/-- Coefficient one on the leading term, minus the complete original boundary. -/
def cotangentRelation : CotangentCombination 2 (Fin 1) :=
  {(1, leadingCotangentTerm)} + Finset.univ.val.map
    (fun i ↦ (-boundary (boundaryIndex i), boundaryCotangentTerm i))

/-- Bundling changes neither the requested class nor its raw coefficients. -/
theorem cotangentRelation_strata : cotangentRelation.strata = interpret columns requested := by
  rw [interpret_request, interpret_boundary]
  simp only [cotangentRelation, CotangentCombination.strata, Multiset.map_add,
    Multiset.sum_add, Multiset.map_singleton, Multiset.sum_singleton,
    one_smul, Multiset.map_map, Function.comp_def, neg_smul,
    ← Finset.sum_eq_multiset_sum, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  congr 1
  rw [psi_square_column]
  congr 1
  change (GluingExpression.fundamental 2 (Fin 1) stableArity).decoratedStratum _ = _
  rw [GluingExpression.decoratedStratum_fundamental]
  apply congrArg (TautologicalStratum.addLegPsi _)
  funext i
  fin_cases i
  rfl

/-- Every original signed summand has the relation degree. -/
theorem cotangentRelation_codimension : ∀ t ∈ cotangentRelation,
    (t.2.expression.decoratedGraph t.2.decoration).codimension = 2 := by
  decide +kernel

/-- Markings preserve degree even when they create correction edges. -/
theorem pulled_term_codimension (n : ℕ) (t : ℚ × CotangentTerm 2 (ExtraMarkings n (Fin 1)))
    (ht : t ∈ cotangentRelation.pullback n) :
    (t.2.expression.decoratedGraph t.2.decoration).codimension = 2 := by
  obtain ⟨z, hz, hw⟩ := Multiset.mem_bind.mp ht
  obtain ⟨w, hplacement, rfl⟩ := Multiset.mem_map.mp hw
  exact ((z.2.addMarkings_bounds n w hplacement).1).trans (cotangentRelation_codimension z hz)

/-- Source validity is the unchanged finite certificate, before any pullback. -/
theorem cotangentRelation_vanishes {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} (p : Exchange) (hp : AcceptsExchange p)
    (A : StrataRealization C 2 (Fin 1))
    (hrows : ∀ i : Fin 7, A.map (interpret columns (rows i)) = 0) :
    A.map cotangentRelation.strata = 0 := by
  rw [cotangentRelation_strata, interpret_request, map_sub]
  exact sub_eq_zero.mpr (evaluated_relation p.presentation hp.1 A.map hrows)

/-- Arbitrary additional markings use only the original rows and primitive pullback laws. -/
theorem realized_relation_with_markings {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (p : Exchange) (hp : AcceptsExchange p)
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (K : PsiForgetFormula P) (hK : TailCompatible K F N)
    (H : TailForgetCompatible C) (G : GluingForgetfulCompatibility F N)
    (hrows : ∀ i : Fin 7, (A 2 (Fin 1)).map (interpret columns (rows i)) = 0)
    (n : ℕ) (hin : ∀ t ∈ cotangentRelation,
      t.2.expression.Compatible A F N ∧ t.2.expression.CotangentCompatible A P)
    (hout : ∀ t ∈ cotangentRelation, ∀ z ∈ t.2.addMarkings n,
      z.2.expression.Compatible A F N ∧ z.2.expression.CotangentCompatible A P) :
    (A 2 (ExtraMarkings n (Fin 1))).map (cotangentRelation.pullback n).strata = 0 :=
  CotangentCombination.pullback_vanishes A F N P K hK H G cotangentRelation stableArity n
    hin hout (cotangentRelation_vanishes p hp (A 2 (Fin 1)) hrows)

/-- The boundary rows are derived from their original component sources;
no higher-arity source relation is an extra hypothesis. -/
theorem realized_relation_with_markings_from_generators
    {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (p : Exchange) (hp : AcceptsExchange p)
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (K : PsiForgetFormula P) (hK : TailCompatible K F N)
    (H : TailForgetCompatible C) (G : GluingForgetfulCompatibility F N)
    (hEL : (A 1 (Fin 1)).RelabelCompatible (A 1 (Option (Fin 0)))
      GenusOnePsi.stableArity ellipticSourceStable (finSuccEquiv 0))
    (hLB : (A 1 (Option (Fin 0))).SeparatingCompatible (A 1 (Option (Fin 1)))
      (A 2 (Fin 0 ⊕ Fin 1)) F ellipticSourceStable ellipticMarkedStable)
    (hUA : (A 2 (Fin 0 ⊕ Fin 1)).RelabelCompatible (A 2 (Fin 1))
      separatingStable stableArity (Equiv.emptySum (Fin 0) (Fin 1)))
    (hinterior : ∀ i : Fin 6, (A 2 (Fin 1)).map (interpret columns (rows i.castSucc)) = 0)
    (hsource : (A 1 (Fin 1)).map
      (interpret GenusOnePsi.columns (GenusOnePsi.rows 0)) = 0)
    (n : ℕ) (hin : ∀ t ∈ cotangentRelation,
      t.2.expression.Compatible A F N ∧ t.2.expression.CotangentCompatible A P)
    (hout : ∀ t ∈ cotangentRelation, ∀ z ∈ t.2.addMarkings n,
      z.2.expression.Compatible A F N ∧ z.2.expression.CotangentCompatible A P) :
    (A 2 (ExtraMarkings n (Fin 1))).map (cotangentRelation.pullback n).strata = 0 :=
  realized_relation_with_markings p hp A F N P K hK H G
    (Fin.lastCases
      (elliptic_row_vanishes (A 1 (Fin 1)) (A 1 (Option (Fin 0))) (A 1 (Option (Fin 1)))
        (A 2 (Fin 0 ⊕ Fin 1)) (A 2 (Fin 1)) F hEL hLB hUA hsource) hinterior) n hin hout

/-- The complete pulled relation pairs with arbitrary full classes and ancestor powers. -/
theorem gw_relation_with_markings {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (p : Exchange) (hp : AcceptsExchange p)
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (K : PsiForgetFormula P) (hK : TailCompatible K F N)
    (H : TailForgetCompatible C) (G : GluingForgetfulCompatibility F N)
    (hrows : ∀ i : Fin 7, (A 2 (Fin 1)).map (interpret columns (rows i)) = 0)
    (n : ℕ) (hin : ∀ t ∈ cotangentRelation,
      t.2.expression.Compatible A F N ∧ t.2.expression.CotangentCompatible A P)
    (hout : ∀ t ∈ cotangentRelation, ∀ z ∈ t.2.addMarkings n,
      z.2.expression.Compatible A F N ∧ z.2.expression.CotangentCompatible A P)
    (beta : B) (k : ExtraMarkings n (Fin 1) → ℕ)
    (a : ExtraMarkings n (Fin 1) → V) :
    (cotangentRelation.pullback n).gwContraction Omega P I beta k a = 0 := by
  apply CotangentCombination.gwContraction_eq_zero A F N Omega P
    (cotangentRelation.pullback n) (stableArity.extraMarkings n) _
    (realized_relation_with_markings p hp A F N P K hK H G hrows n hin hout)
  intro t ht
  obtain ⟨z, hz, hm⟩ := Multiset.mem_bind.mp ht
  obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hm
  exact hout z hz w hw

end GenusTwoPsiSquare

namespace GenusTwoPsiProduct

/-- The leading monomial retains its old labels before any markings are added. -/
def leadingCotangentTerm : CotangentTerm 2 (Fin 2) :=
  .fundamental 2 (Fin 2) stableArity (fun _ ↦ 1)

/-- The computational decisions of the original boundary components. -/
def boundaryLabelDecisions (i : Fin 25) : (boundaryTerm i).1.DecidableLabels :=
  match i with
  | ⟨0, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression0, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨1, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression1, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨2, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression2, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨3, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression3, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨4, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression4, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨5, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression5, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨6, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression6, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨7, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression7, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨8, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression8, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨9, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression9, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨10, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression10, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨11, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression11, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨12, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression12, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨13, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression13, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    exact inferInstance
  | ⟨14, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression14, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    exact inferInstance
  | ⟨15, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression15, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    exact inferInstance
  | ⟨16, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression16, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨17, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression17, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨18, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression18, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨19, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression19, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨20, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression20, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨21, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression21, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨22, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression22, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨23, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression23, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    repeat' first | exact inferInstance | constructor
  | ⟨24, _⟩ => by
    dsimp [boundaryTerm, boundaryExpression24, GetzlerGraphs.join,
      GetzlerGraphs.close, DecidableLabels]
    exact inferInstance
  | ⟨j + 25, h⟩ => False.elim (by omega)

/-- The held boundary construction, with executable finite label decisions. -/
def boundaryCotangentTerm (i : Fin 25) : CotangentTerm 2 (Fin 2) :=
  ⟨(boundaryTerm i).1, (boundaryTerm i).2, boundaryLabelDecisions i⟩

/-- Coefficient one on the leading term, minus the complete original boundary. -/
def cotangentRelation : CotangentCombination 2 (Fin 2) :=
  {(1, leadingCotangentTerm)} + Finset.univ.val.map
    (fun i ↦ (-boundary (boundaryIndex i), boundaryCotangentTerm i))

/-- Bundling changes neither the requested class nor its raw coefficients. -/
theorem cotangentRelation_strata : cotangentRelation.strata = interpret columns requested := by
  rw [interpret_request, interpret_boundary]
  simp only [cotangentRelation, CotangentCombination.strata, Multiset.map_add,
    Multiset.sum_add, Multiset.map_singleton, Multiset.sum_singleton,
    one_smul, Multiset.map_map, Function.comp_def, neg_smul,
    ← Finset.sum_eq_multiset_sum, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  congr 1
  rw [psi_product_column]
  rfl

/-- Every original signed summand has the relation degree. -/
theorem cotangentRelation_codimension : ∀ t ∈ cotangentRelation,
    (t.2.expression.decoratedGraph t.2.decoration).codimension = 2 := by
  decide +kernel

/-- Markings preserve degree even when they create correction edges. -/
theorem pulled_term_codimension (n : ℕ) (t : ℚ × CotangentTerm 2 (ExtraMarkings n (Fin 2)))
    (ht : t ∈ cotangentRelation.pullback n) :
    (t.2.expression.decoratedGraph t.2.decoration).codimension = 2 := by
  obtain ⟨z, hz, hw⟩ := Multiset.mem_bind.mp ht
  obtain ⟨w, hplacement, rfl⟩ := Multiset.mem_map.mp hw
  exact ((z.2.addMarkings_bounds n w hplacement).1).trans (cotangentRelation_codimension z hz)

/-- Source validity is the unchanged finite certificate, before any pullback. -/
theorem cotangentRelation_vanishes {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} (p : Exchange) (hp : AcceptsExchange p)
    (A : StrataRealization C 2 (Fin 2))
    (hrows : ∀ i : Fin 13, A.map (interpret columns (rows i)) = 0) :
    A.map cotangentRelation.strata = 0 := by
  rw [cotangentRelation_strata, interpret_request, map_sub]
  exact sub_eq_zero.mpr (evaluated_relation p hp A.map hrows)

/-- Arbitrary additional markings use only the original rows and primitive pullback laws. -/
theorem realized_relation_with_markings {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (p : Exchange) (hp : AcceptsExchange p)
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (K : PsiForgetFormula P) (hK : TailCompatible K F N)
    (H : TailForgetCompatible C) (G : GluingForgetfulCompatibility F N)
    (hrows : ∀ i : Fin 13, (A 2 (Fin 2)).map (interpret columns (rows i)) = 0)
    (n : ℕ) (hin : ∀ t ∈ cotangentRelation,
      t.2.expression.Compatible A F N ∧ t.2.expression.CotangentCompatible A P)
    (hout : ∀ t ∈ cotangentRelation, ∀ z ∈ t.2.addMarkings n,
      z.2.expression.Compatible A F N ∧ z.2.expression.CotangentCompatible A P) :
    (A 2 (ExtraMarkings n (Fin 2))).map (cotangentRelation.pullback n).strata = 0 :=
  CotangentCombination.pullback_vanishes A F N P K hK H G cotangentRelation stableArity n
    hin hout (cotangentRelation_vanishes p hp (A 2 (Fin 2)) hrows)

/-- The boundary rows are derived from their original component sources;
no higher-arity source relation is an extra hypothesis. -/
theorem realized_relation_with_markings_from_generators
    {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (p : Exchange) (hp : AcceptsExchange p)
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (K : PsiForgetFormula P) (hK : TailCompatible K F N)
    (H : TailForgetCompatible C) (G : GluingForgetfulCompatibility F N)
    (hc : ∀ b, SourceCompatible A F b)
    (hsource : ∀ b, (A (BelorousskiPandharipande.sourceGenus (sourceFamily b))
      (Fin (BelorousskiPandharipande.sourceArity (sourceFamily b)))).map
        (BelorousskiPandharipande.sourceExpression (sourceIndex b)) = 0)
    (hinterior : ∀ i : Fin 10,
      (A 2 (Fin 2)).map (interpret columns (rows (i.castLE (by decide)))) = 0)
    (n : ℕ) (hin : ∀ t ∈ cotangentRelation,
      t.2.expression.Compatible A F N ∧ t.2.expression.CotangentCompatible A P)
    (hout : ∀ t ∈ cotangentRelation, ∀ z ∈ t.2.addMarkings n,
      z.2.expression.Compatible A F N ∧ z.2.expression.CotangentCompatible A P) :
    (A 2 (ExtraMarkings n (Fin 2))).map (cotangentRelation.pullback n).strata = 0 :=
  realized_relation_with_markings p hp A F N P K hK H G
    (rows_vanish_from_generators A F hc hsource hinterior) n hin hout

/-- The complete pulled relation pairs with arbitrary full classes and ancestor powers. -/
theorem gw_relation_with_markings {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (p : Exchange) (hp : AcceptsExchange p)
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (K : PsiForgetFormula P) (hK : TailCompatible K F N)
    (H : TailForgetCompatible C) (G : GluingForgetfulCompatibility F N)
    (hrows : ∀ i : Fin 13, (A 2 (Fin 2)).map (interpret columns (rows i)) = 0)
    (n : ℕ) (hin : ∀ t ∈ cotangentRelation,
      t.2.expression.Compatible A F N ∧ t.2.expression.CotangentCompatible A P)
    (hout : ∀ t ∈ cotangentRelation, ∀ z ∈ t.2.addMarkings n,
      z.2.expression.Compatible A F N ∧ z.2.expression.CotangentCompatible A P)
    (beta : B) (k : ExtraMarkings n (Fin 2) → ℕ)
    (a : ExtraMarkings n (Fin 2) → V) :
    (cotangentRelation.pullback n).gwContraction Omega P I beta k a = 0 := by
  apply CotangentCombination.gwContraction_eq_zero A F N Omega P
    (cotangentRelation.pullback n) (stableArity.extraMarkings n) _
    (realized_relation_with_markings p hp A F N P K hK H G hrows n hin hout)
  intro t ht
  obtain ⟨z, hz, hm⟩ := Multiset.mem_bind.mp ht
  obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hm
  exact hout z hz w hw

end GenusTwoPsiProduct

end AxiomaticGW

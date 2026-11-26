/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoNormalizedBP
public import AxiomaticGW.Surfaces.GenusTwoNormalizedL24
public import AxiomaticGW.Surfaces.GenusTwoBlowupRecursion

/-!
# Geometric input route to genus-two blowup reconstruction

The BP and L24 polynomial equation families are derived from the existing
original source rows and explicit realization, gluing, cotangent and marking
compatibilities. In particular, the square and product pullbacks and the
rational psi relations used by L24 are consequences rather than new inputs.

For either fixed blowup target, the terminating H/P/N/K table therefore agrees
with actual canonical descendant evaluations from these inputs, exceptional
point evaluation support and the finite divisor seeds. No primary genus-two
seed, pivot coefficient or numerical recurrence is assumed. Constructing the
geometric objects and proving their named compatibilities remains separate.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwoBlowupReconstruction
open BelorousskiPandharipande RelationCertificate PsiBoundaryExpansion
attribute [local instance] strataRealizationModule

/-- The complete normalized BP and primary L24 equations follow from original
source relations and the named geometric compatibility inputs. -/
theorem equation_families_from_geometry {X : SurfaceTarget}
    {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A)
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (J : GluingForgetfulCompatibility F N)
    (hWsource : ∀ i, (WDVV.expression i).Compatible Z F N)
    (hboundary : WDVV.BoundaryClassesEqual F)
    (pW : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hpW : WDVV.AcceptsExchange pW)
    (hGsource : ∀ i, (GetzlerGraphs.expression i).Compatible Z F N)
    (GG : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (Z 1 (Fin 4)).map (GetzlerGraphs.cycle x) = GG.cycle x)
    (pG : RelationCertificate.Presentation 1 (Fin 4) 1 33)
    (hpG : GetzlerGraphs.AcceptsExchange pG)
    (K : PsiForgetFormula P) (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (pPsi : RelationCertificate.Presentation 1 (Fin 1) 2 3)
    (hpPsi : GenusOnePsi.AcceptsExchange pPsi)
    (hpsi : (Z 1 (Fin 1)).LegPsiCompatible P GenusOnePsi.stableArity)
    (hfund : (Z 1 (Fin 1)).map (StrataModule.basis
      (TautologicalStratum.fundamental 1 (Fin 1) GenusOnePsi.stableArity)) = 1)
    (hrows : ∀ i, (Z 1 (Fin 1)).map
      (RelationCertificate.interpret GenusOnePsi.columns (GenusOnePsi.rows i)) = 0)
    (hloop : GenusOnePsi.loopExpression.Compatible Z F N)
    (hzeroTerms : ∀ n t, t ∈ PsiBoundaryExpansion.genusZeroTerms 0 n → t.2.Compatible Z F N)
    (honeTerms : ∀ n t, t ∈ PsiBoundaryExpansion.genusOneTerms n → t.2.Compatible Z F N)
    (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
    (hEzero : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
    (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed X).query.eval U = -1 / 8)
    (hE : ∀ i, (SurfaceSeed.genusOneExceptional i : SurfaceSeed X).query.eval U = -1 / 24)
    (hWoutput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible Z F N)
    (hGoutput : ∀ n i z, z ∈ (GetzlerGraphs.expression i).addMarkings n → z.Compatible Z F N)
    (HF : TailForgetCompatible C)
    (pB : Exchange) (hpB : AcceptsExchange pB)
    (hlB : ∀ e, (Z 2 (Fin 3)).RelabelCompatible (Z 2 (Fin 3))
      stableArity stableArity (labelPermutation e))
    (hcB : ∀ b, SourceMapCompatible Z F b)
    (hinterior : ∀ i : Fin 4, (Z 2 (Fin 3)).map
      (interpret columns (unsymmetrizedRows (Fin.castAdd 16 i))) = 0)
    (hsource : ∀ i, (Z (sourceGenus (sourceFamily i)) (Fin (sourceArity (sourceFamily i)))).map
      (sourceExpression i) = 0)
    (hglue : ∀ i e, (orbitTerm i e).1.Compatible Z F N)
    (hcotangent : ∀ i e, (orbitTerm i e).1.CotangentCompatible Z P)
    {V : StableMapIntersection U} {St : StableMapStabilization V}
    (RT : RationalTailIntersection V St P)
    (houtB : ∀ n i e t, t ∈ (orbitCotangentTerm i e).addMarkings n →
      t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
    (pS : GenusTwoPsiSquare.Exchange) (hpS : GenusTwoPsiSquare.AcceptsExchange pS)
    (hSEL : (Z 1 (Fin 1)).RelabelCompatible (Z 1 (Option (Fin 0)))
      GenusOnePsi.stableArity GenusTwoPsiSquare.ellipticSourceStable (finSuccEquiv 0))
    (hSLB : (Z 1 (Option (Fin 0))).SeparatingCompatible (Z 1 (Option (Fin 1)))
      (Z 2 (Fin 0 ⊕ Fin 1)) F GenusTwoPsiSquare.ellipticSourceStable
      GenusTwoPsiSquare.ellipticMarkedStable)
    (hSUA : (Z 2 (Fin 0 ⊕ Fin 1)).RelabelCompatible (Z 2 (Fin 1))
      GenusTwoPsiSquare.separatingStable GenusTwoPsiSquare.stableArity
      (Equiv.emptySum (Fin 0) (Fin 1)))
    (hSrows : ∀ j : Fin 6, (Z 2 (Fin 1)).map
      (interpret GenusTwoPsiSquare.columns (GenusTwoPsiSquare.rows j.castSucc)) = 0)
    (hinS : ∀ t ∈ GenusTwoPsiSquare.cotangentRelation,
      t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
    (houtS : ∀ r : Fin 2, ∀ t ∈ GenusTwoPsiSquare.cotangentRelation,
      ∀ z ∈ t.2.addMarkings (r.val + 1),
      z.2.expression.Compatible Z F N ∧ z.2.expression.CotangentCompatible Z P)
    (hlS : ∀ r : Fin 2, (Z 2 (ExtraMarkings (r.val + 1) (Fin 1))).RelabelCompatible
      (Z 2 (Fin (1 + (r.val + 1))))
      (GenusTwoPsiSquare.stableArity.extraMarkings (r.val + 1))
      ((StableArity.equiv (ExtraMarkings.finEquiv (r.val + 1) 1)).mp
        (GenusTwoPsiSquare.stableArity.extraMarkings (r.val + 1)))
      (ExtraMarkings.finEquiv (r.val + 1) 1))
    (pP : GenusTwoPsiProduct.Exchange) (hpP : GenusTwoPsiProduct.AcceptsExchange pP)
    (hcP : ∀ b, GenusTwoPsiProduct.SourceCompatible Z F b)
    (hProws : ∀ j : Fin 10, (Z 2 (Fin 2)).map
      (interpret GenusTwoPsiProduct.columns (GenusTwoPsiProduct.rows (j.castLE (by decide)))) = 0)
    (hinP : ∀ t ∈ GenusTwoPsiProduct.cotangentRelation,
      t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
    (houtP : ∀ t ∈ GenusTwoPsiProduct.cotangentRelation, ∀ z ∈ t.2.addMarkings 1,
      z.2.expression.Compatible Z F N ∧ z.2.expression.CotangentCompatible Z P)
    (hlP : (Z 2 (ExtraMarkings 1 (Fin 2))).RelabelCompatible (Z 2 (Fin 3))
      (GenusTwoPsiProduct.stableArity.extraMarkings 1)
      ((StableArity.equiv (ExtraMarkings.finEquiv 1 2)).mp
        (GenusTwoPsiProduct.stableArity.extraMarkings 1)) (ExtraMarkings.finEquiv 1 2))
    (hRpsi : ∀ r : Fin 2, (Z 0 (ExtraMarkings (r.val + 1) (Fin 3))).LegPsiCompatible P
      (StableArity.zero_fin_three.extraMarkings (r.val + 1)))
    (hRfund : ∀ r : Fin 2, (Z 0 (ExtraMarkings (r.val + 1) (Fin 3))).map (StrataModule.basis
      (TautologicalStratum.fundamental 0 _
        (StableArity.zero_fin_three.extraMarkings (r.val + 1)))) = 1)
    (hRlabels : ∀ r : Fin 2, (Z 0 (ExtraMarkings (r.val + 1) (Fin 3))).RelabelCompatible
      (Z 0 (Fin (3 + (r.val + 1)))) (StableArity.zero_fin_three.extraMarkings (r.val + 1))
      ((StableArity.equiv (ExtraMarkings.finEquiv (r.val + 1) 3)).mp
        (StableArity.zero_fin_three.extraMarkings (r.val + 1)))
      (ExtraMarkings.finEquiv (r.val + 1) 3))
    (hlL : (Z 2 (ExtraMarkings 1 (Fin 3))).RelabelCompatible (Z 2 (Fin 4))
      (BelorousskiPandharipande.stableArity.extraMarkings 1) L24Symmetry.stableArity
      L24Initial.labels)
    (hpL : (Z 2 (Fin 4)).LegPsiCompatible P L24Symmetry.stableArity)
    (hsL : ∀ p, (Z 2 (Fin 4)).RelabelCompatible (Z 2 (Fin 4))
      L24Symmetry.stableArity L24Symmetry.stableArity (L24Symmetry.labels p))
    (hhigh : L24HighPsi.Compatible Z F P)
    (hrational : L24RationalPsi.Compatible Z F P)
    (hwdvv : L24WDVV.Compatible Z F P)
    (htermsL : ∀ t ∈ L24Relation.cotangentRelation,
      t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
    (haddedL : ∀ n t, t ∈ L24Relation.cotangentRelation → ∀ z ∈ t.2.addMarkings n,
      z.2.expression.Compatible Z F N ∧ z.2.expression.CotangentCompatible Z P) :
    (∀ n beta a, RationalTerms.eval (SurfacePolynomialReduction.variableEval U P)
      (SurfaceGenusTwoBlowupNRelation.bpRow X n beta a) = 0) ∧
    (∀ n beta (a : Fin 4 → SurfaceBasisLabel X),
      RationalTerms.eval (SurfacePolynomialReduction.variableEval U P)
        (L24Relation.normalizedGenusTwoTerms X n beta 0
          (SurfaceGenusZero.pointLabels a n)) = 0) := by
  have hbp : (Z 2 (Fin 3)).map paperRelation = 0 :=
    realized_relation_from_generators Z F pB hpB hlB hcB hinterior hsource
  have hsquare (r : Fin 2) :
      (Z 2 (ExtraMarkings (r.val + 1) (Fin 1))).map
        (GenusTwoPsiSquare.cotangentRelation.pullback (r.val + 1)).strata = 0 :=
    GenusTwoPsiSquare.realized_relation_with_markings_from_generators pS hpS Z F N P K hK
      HF J hSEL hSLB hSUA hSrows (hrows 0) (r.val + 1) hinS (houtS r)
  have hs2 : (Z 2 (Fin 2)).map GenusTwoPsiPullbacks.squareTwo.strata = 0 := by
    rw [GenusTwoPsiPullbacks.squareTwo, CotangentCombination.strata_relabel]
    have hrel := StrataRealization.map_relabel _ _ _ _ _ (hlS 0)
      (GenusTwoPsiSquare.cotangentRelation.pullback 1).strata
    apply hrel.trans
    exact (congrArg (C.rename 2 _ _ _ _ _) (hsquare 0)).trans (map_zero _)
  have hs3 : (Z 2 (Fin 3)).map GenusTwoPsiPullbacks.squareThree.strata = 0 := by
    rw [GenusTwoPsiPullbacks.squareThree, CotangentCombination.strata_relabel]
    have hrel := StrataRealization.map_relabel _ _ _ _ _ (hlS 1)
      (GenusTwoPsiSquare.cotangentRelation.pullback 2).strata
    apply hrel.trans
    exact (congrArg (C.rename 2 _ _ _ _ _) (hsquare 1)).trans (map_zero _)
  have hPsource (b : Fin 3) :
      (Z (sourceGenus (GenusTwoPsiProduct.sourceFamily b))
        (Fin (sourceArity (GenusTwoPsiProduct.sourceFamily b)))).map
        (sourceExpression (GenusTwoPsiProduct.sourceIndex b)) = 0 :=
    hsource (GenusTwoPsiProduct.sourceIndex b)
  have hp2 : (Z 2 (Fin 2)).map GenusTwoPsiProduct.cotangentRelation.strata = 0 :=
    GenusTwoPsiProduct.cotangentRelation_vanishes pP hpP (Z 2 (Fin 2))
      (GenusTwoPsiProduct.rows_vanish_from_generators Z F hcP hPsource hProws)
  have hproduct : (Z 2 (ExtraMarkings 1 (Fin 2))).map
      (GenusTwoPsiProduct.cotangentRelation.pullback 1).strata = 0 :=
    GenusTwoPsiProduct.realized_relation_with_markings_from_generators pP hpP Z F N P K hK
      HF J hcP hPsource hProws 1 hinP houtP
  have hp3 : (Z 2 (Fin 3)).map GenusTwoPsiPullbacks.productThree.strata = 0 := by
    rw [GenusTwoPsiPullbacks.productThree, CotangentCombination.strata_relabel,
      StrataRealization.map_relabel _ _ _ _ _ hlP, hproduct, map_zero]
  have hr (r : Fin 2) : (Z 0 (Fin (3 + (r.val + 1)))).map
      (interpret (RationalPsiRelation.columns (r.val + 1))
        (RationalPsiRelation.coordinates (r.val + 1))) = 0 :=
    RationalPsiRelation.realized_coordinates Z P K F N J hK (r.val + 1)
      (hRpsi r) (hRfund r) (hzeroTerms (r.val + 1)) (hRlabels r)
  have hinL : ∀ t ∈ L24Initial.bp, t.2.expression.Compatible Z F N ∧
      t.2.expression.CotangentCompatible Z P := by
    intro t ht
    simp only [L24Initial.bp, Multiset.mem_bind, Multiset.mem_map] at ht
    obtain ⟨j, _, e, _, rfl⟩ := ht
    exact ⟨hglue j e, hcotangent j e⟩
  have houtL : ∀ t ∈ L24Initial.bp, ∀ z ∈ t.2.addMarkings 1,
      z.2.expression.Compatible Z F N ∧ z.2.expression.CotangentCompatible Z P := by
    intro t ht z hz
    simp only [L24Initial.bp, Multiset.mem_bind, Multiset.mem_map] at ht
    obtain ⟨j, _, e, _, rfl⟩ := ht
    exact houtB 1 j e z hz
  constructor
  · intro n beta a
    exact BelorousskiPandharipande.eval_normalizedGenusTwoTerms_eq_zero U P T laws H hpair
      Z F N J hWsource hboundary pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi
      hfund hrows hloop hzeroTerms honeTerms hline hEzero hH hE hWoutput hGoutput HF pB hpB
      hlB hcB hinterior hsource hglue hcotangent RT n (houtB n) beta 0
      (SurfaceGenusZero.pointLabels a n)
  · intro n beta a
    exact L24Relation.eval_normalizedGenusTwoTerms_eq_zero U P T laws H hpair Z F N J
      hWsource hboundary pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows
      hloop hzeroTerms honeTerms hline hEzero hH hE hWoutput hGoutput HF hbp hinL houtL
      hlL hpL hsL hhigh hs2 hs3 hp2 hp3 hrational (hr 0) (hr 1) hwdvv RT n htermsL
      (haddedL n) beta 0 (SurfaceGenusZero.pointLabels a n)

/-- The terminating full-class H/P/N/K table evaluates the actual canonical query
from original source and geometric inputs. The initial primary value is derived
from the original BP equation, rather than supplied as a separate seed. -/
theorem values_eq_eval_from_geometry {X : SurfaceTarget}
    {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A)
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (J : GluingForgetfulCompatibility F N)
    (hWsource : ∀ i, (WDVV.expression i).Compatible Z F N)
    (hboundary : WDVV.BoundaryClassesEqual F)
    (pW : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hpW : WDVV.AcceptsExchange pW)
    (hGsource : ∀ i, (GetzlerGraphs.expression i).Compatible Z F N)
    (GG : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (Z 1 (Fin 4)).map (GetzlerGraphs.cycle x) = GG.cycle x)
    (pG : RelationCertificate.Presentation 1 (Fin 4) 1 33)
    (hpG : GetzlerGraphs.AcceptsExchange pG)
    (K : PsiForgetFormula P) (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (pPsi : RelationCertificate.Presentation 1 (Fin 1) 2 3)
    (hpPsi : GenusOnePsi.AcceptsExchange pPsi)
    (hpsi : (Z 1 (Fin 1)).LegPsiCompatible P GenusOnePsi.stableArity)
    (hfund : (Z 1 (Fin 1)).map (StrataModule.basis
      (TautologicalStratum.fundamental 1 (Fin 1) GenusOnePsi.stableArity)) = 1)
    (hrows : ∀ i, (Z 1 (Fin 1)).map
      (RelationCertificate.interpret GenusOnePsi.columns (GenusOnePsi.rows i)) = 0)
    (hloop : GenusOnePsi.loopExpression.Compatible Z F N)
    (hzeroTerms : ∀ n t, t ∈ PsiBoundaryExpansion.genusZeroTerms 0 n → t.2.Compatible Z F N)
    (honeTerms : ∀ n t, t ∈ PsiBoundaryExpansion.genusOneTerms n → t.2.Compatible Z F N)
    (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
    (hEzero : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
    (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed X).query.eval U = -1 / 8)
    (hE : ∀ i, (SurfaceSeed.genusOneExceptional i : SurfaceSeed X).query.eval U = -1 / 24)
    (hWoutput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible Z F N)
    (hGoutput : ∀ n i z, z ∈ (GetzlerGraphs.expression i).addMarkings n → z.Compatible Z F N)
    (HF : TailForgetCompatible C)
    (pB : Exchange) (hpB : AcceptsExchange pB)
    (hlB : ∀ e, (Z 2 (Fin 3)).RelabelCompatible (Z 2 (Fin 3))
      stableArity stableArity (labelPermutation e))
    (hcB : ∀ b, SourceMapCompatible Z F b)
    (hinterior : ∀ i : Fin 4, (Z 2 (Fin 3)).map
      (interpret columns (unsymmetrizedRows (Fin.castAdd 16 i))) = 0)
    (hsource : ∀ i, (Z (sourceGenus (sourceFamily i)) (Fin (sourceArity (sourceFamily i)))).map
      (sourceExpression i) = 0)
    (hglue : ∀ i e, (orbitTerm i e).1.Compatible Z F N)
    (hcotangent : ∀ i e, (orbitTerm i e).1.CotangentCompatible Z P)
    {V : StableMapIntersection U} {St : StableMapStabilization V}
    (RT : RationalTailIntersection V St P)
    (houtB : ∀ n i e t, t ∈ (orbitCotangentTerm i e).addMarkings n →
      t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
    (pS : GenusTwoPsiSquare.Exchange) (hpS : GenusTwoPsiSquare.AcceptsExchange pS)
    (hSEL : (Z 1 (Fin 1)).RelabelCompatible (Z 1 (Option (Fin 0)))
      GenusOnePsi.stableArity GenusTwoPsiSquare.ellipticSourceStable (finSuccEquiv 0))
    (hSLB : (Z 1 (Option (Fin 0))).SeparatingCompatible (Z 1 (Option (Fin 1)))
      (Z 2 (Fin 0 ⊕ Fin 1)) F GenusTwoPsiSquare.ellipticSourceStable
      GenusTwoPsiSquare.ellipticMarkedStable)
    (hSUA : (Z 2 (Fin 0 ⊕ Fin 1)).RelabelCompatible (Z 2 (Fin 1))
      GenusTwoPsiSquare.separatingStable GenusTwoPsiSquare.stableArity
      (Equiv.emptySum (Fin 0) (Fin 1)))
    (hSrows : ∀ j : Fin 6, (Z 2 (Fin 1)).map
      (interpret GenusTwoPsiSquare.columns (GenusTwoPsiSquare.rows j.castSucc)) = 0)
    (hinS : ∀ t ∈ GenusTwoPsiSquare.cotangentRelation,
      t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
    (houtS : ∀ r : Fin 2, ∀ t ∈ GenusTwoPsiSquare.cotangentRelation,
      ∀ z ∈ t.2.addMarkings (r.val + 1),
      z.2.expression.Compatible Z F N ∧ z.2.expression.CotangentCompatible Z P)
    (hlS : ∀ r : Fin 2, (Z 2 (ExtraMarkings (r.val + 1) (Fin 1))).RelabelCompatible
      (Z 2 (Fin (1 + (r.val + 1))))
      (GenusTwoPsiSquare.stableArity.extraMarkings (r.val + 1))
      ((StableArity.equiv (ExtraMarkings.finEquiv (r.val + 1) 1)).mp
        (GenusTwoPsiSquare.stableArity.extraMarkings (r.val + 1)))
      (ExtraMarkings.finEquiv (r.val + 1) 1))
    (pP : GenusTwoPsiProduct.Exchange) (hpP : GenusTwoPsiProduct.AcceptsExchange pP)
    (hcP : ∀ b, GenusTwoPsiProduct.SourceCompatible Z F b)
    (hProws : ∀ j : Fin 10, (Z 2 (Fin 2)).map
      (interpret GenusTwoPsiProduct.columns (GenusTwoPsiProduct.rows (j.castLE (by decide)))) = 0)
    (hinP : ∀ t ∈ GenusTwoPsiProduct.cotangentRelation,
      t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
    (houtP : ∀ t ∈ GenusTwoPsiProduct.cotangentRelation, ∀ z ∈ t.2.addMarkings 1,
      z.2.expression.Compatible Z F N ∧ z.2.expression.CotangentCompatible Z P)
    (hlP : (Z 2 (ExtraMarkings 1 (Fin 2))).RelabelCompatible (Z 2 (Fin 3))
      (GenusTwoPsiProduct.stableArity.extraMarkings 1)
      ((StableArity.equiv (ExtraMarkings.finEquiv 1 2)).mp
        (GenusTwoPsiProduct.stableArity.extraMarkings 1)) (ExtraMarkings.finEquiv 1 2))
    (hRpsi : ∀ r : Fin 2, (Z 0 (ExtraMarkings (r.val + 1) (Fin 3))).LegPsiCompatible P
      (StableArity.zero_fin_three.extraMarkings (r.val + 1)))
    (hRfund : ∀ r : Fin 2, (Z 0 (ExtraMarkings (r.val + 1) (Fin 3))).map (StrataModule.basis
      (TautologicalStratum.fundamental 0 _
        (StableArity.zero_fin_three.extraMarkings (r.val + 1)))) = 1)
    (hRlabels : ∀ r : Fin 2, (Z 0 (ExtraMarkings (r.val + 1) (Fin 3))).RelabelCompatible
      (Z 0 (Fin (3 + (r.val + 1)))) (StableArity.zero_fin_three.extraMarkings (r.val + 1))
      ((StableArity.equiv (ExtraMarkings.finEquiv (r.val + 1) 3)).mp
        (StableArity.zero_fin_three.extraMarkings (r.val + 1)))
      (ExtraMarkings.finEquiv (r.val + 1) 3))
    (hlL : (Z 2 (ExtraMarkings 1 (Fin 3))).RelabelCompatible (Z 2 (Fin 4))
      (BelorousskiPandharipande.stableArity.extraMarkings 1) L24Symmetry.stableArity
      L24Initial.labels)
    (hpL : (Z 2 (Fin 4)).LegPsiCompatible P L24Symmetry.stableArity)
    (hsL : ∀ p, (Z 2 (Fin 4)).RelabelCompatible (Z 2 (Fin 4))
      L24Symmetry.stableArity L24Symmetry.stableArity (L24Symmetry.labels p))
    (hhigh : L24HighPsi.Compatible Z F P)
    (hrational : L24RationalPsi.Compatible Z F P)
    (hwdvv : L24WDVV.Compatible Z F P)
    (htermsL : ∀ t ∈ L24Relation.cotangentRelation,
      t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
    (haddedL : ∀ n t, t ∈ L24Relation.cotangentRelation → ∀ z ∈ t.2.addMarkings n,
      z.2.expression.Compatible Z F N ∧ z.2.expression.CotangentCompatible Z P)
    (i : Fin X.blowups) (hV : ExceptionalPointSupport V)
    (hHtwo : (SurfaceSeed.genusTwoHyperplane : SurfaceSeed X).query.eval U = -1 / 960)
    (hEtwo : ∀ j, (SurfaceSeed.genusTwoExceptional j : SurfaceSeed X).query.eval U =
      -1 / 2880)
    (s : SurfaceGenusTwoBlowupOrder.State X) :
    SurfaceGenusTwoBlowupRecursion.values i s = (s.2.query s.1).eval U := by
  obtain ⟨hBP, hL⟩ := equation_families_from_geometry U P T laws H hpair Z F N J
    hWsource hboundary pW hpW hGsource GG hcycle pG hpG K hK
      pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms hline hEzero hH hE hWoutput
      hGoutput HF pB hpB hlB hcB hinterior hsource hglue hcotangent RT houtB pS hpS hSEL
      hSLB hSUA hSrows hinS houtS hlS pP hpP hcP hProws hinP houtP hlP hRpsi hRfund
      hRlabels hlL hpL hsL hhigh hrational hwdvv htermsL haddedL
  exact SurfaceGenusTwoBlowupRecursion.values_eq_eval_of_original_equations i U P T V hV
    hHtwo hEtwo hBP hL s

end AxiomaticGW.SurfaceGenusTwoBlowupReconstruction

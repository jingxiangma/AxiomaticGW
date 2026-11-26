/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupDescendantReconstruction

/-! Consumers of primitive geometric soundness at arbitrary descendant power. -/

set_option linter.privateModule false

@[expose] public section
namespace AxiomaticGWTest.SurfaceGenusTwoBlowupDescendantReconstruction
open AxiomaticGW BelorousskiPandharipande RelationCertificate PsiBoundaryExpansion
open SurfaceGenusTwoBlowupDescendantReconstruction
attribute [local instance] strataRealizationModule

variable {X : SurfaceTarget}
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
    (V : StableMapIntersection U) {St : StableMapStabilization V}
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
    (houtS : ∀ n t, t ∈ GenusTwoPsiSquare.cotangentRelation →
      ∀ z ∈ t.2.addMarkings n,
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
      (interpret GenusTwoPsiProduct.columns (GenusTwoPsiProduct.rows (Fin.castAdd 3 j))) = 0)
    (hinP : ∀ t ∈ GenusTwoPsiProduct.cotangentRelation,
      t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
    (houtP : ∀ n t, t ∈ GenusTwoPsiProduct.cotangentRelation →
      ∀ z ∈ t.2.addMarkings n,
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
    (hV : ExceptionalPointSupport V)
    (hHtwo : (SurfaceSeed.genusTwoHyperplane : SurfaceSeed X).query.eval U = -1 / 960)
    (hEtwo : ∀ j, (SurfaceSeed.genusTwoExceptional j : SurfaceSeed X).query.eval U =
      -1 / 2880)

include U P T laws H hpair Z F N J hWsource hboundary pW hpW hGsource GG hcycle pG hpG K hK
  pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms hline hEzero hH hE hWoutput
  hGoutput HF pB hpB hlB hcB hinterior hsource hglue hcotangent V RT houtB pS hpS hSEL
  hSLB hSUA hSrows hinS houtS hlS pP hpP hcP hProws hinP houtP hlP hRpsi hRfund
  hRlabels hlL hpL hsL hhigh hrational hwdvv htermsL haddedL hV hHtwo hEtwo


/-- Every genus-two query returns its evaluation, with repeated ordered labels and
arbitrary powers allowed by the final primitive geometric API. -/
theorem query_returns_evaluation (i : Fin X.blowups) (q : SurfaceQuery X)
    (hg : q.genus = 2) :
    SurfaceGenusTwoBlowupDescendants.queryValue? i q = some (q.eval U) := by
  have hq := queryValue?_eq_checkedEval_from_geometry U P T laws H hpair Z F N J
    hWsource hboundary pW hpW hGsource GG hcycle pG hpG K hK
      pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms hline hEzero hH hE hWoutput
      hGoutput HF pB hpB hlB hcB hinterior hsource hglue hcotangent V RT houtB pS hpS hSEL
      hSLB hSUA hSrows hinS houtS hlS pP hpP hcP hProws hinP houtP hlP hRpsi hRfund
      hRlabels hlL hpL hsL hhigh hrational hwdvv htermsL haddedL
    hV hHtwo hEtwo i q hg
  have hd : q.GeometricDomain := Or.inr (by simp only [StableArity, hg]; omega)
  exact hq.trans (SurfaceQuery.checkedEval_of_geometricDomain U q hd)

/-- The public arbitrary-state theorem accepts high powers and cohomology sums,
including an exceptional contribution, without reducing the consumer to basis-only states. -/
theorem mixed_pair_states (i : Fin X.blowups) (beta : X.Curve) :
    SurfaceGenusTwoBlowupDescendants.stateValue i (Fin 2) beta ![7, 4]
      ![3 • (SurfaceBasisLabel.unit : SurfaceBasisLabel X).value + SurfaceBasisLabel.point.value,
        SurfaceBasisLabel.hyperplane.value - 2 • (SurfaceBasisLabel.exceptional i).value] =
      U.invariant 2 (Fin 2) beta ![7, 4]
        ![3 • (SurfaceBasisLabel.unit : SurfaceBasisLabel X).value + SurfaceBasisLabel.point.value,
          SurfaceBasisLabel.hyperplane.value - 2 • (SurfaceBasisLabel.exceptional i).value] := by
  exact stateValue_from_geometry U P T laws H hpair Z F N J
    hWsource hboundary pW hpW hGsource GG hcycle pG hpG K hK
      pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms hline hEzero hH hE hWoutput
      hGoutput HF pB hpB hlB hcB hinterior hsource hglue hcotangent V RT houtB pS hpS hSEL
      hSLB hSUA hSrows hinS houtS hlS pP hpP hcP hProws hinP houtP hlP hRpsi hRfund
      hRlabels hlL hpL hsL hhigh hrational hwdvv htermsL haddedL
    hV hHtwo hEtwo i (Fin 2) beta ![7, 4] _

/-- Either exceptional shift computes the same ordered descendant request from
primitive geometry; no agreement of recursive tables is supplied as a premise. -/
theorem query_shift_independent (i j : Fin X.blowups) (q : SurfaceQuery X)
    (hg : q.genus = 2) :
    SurfaceGenusTwoBlowupDescendants.queryValue? i q =
      SurfaceGenusTwoBlowupDescendants.queryValue? j q := by
  have hi := queryValue?_eq_checkedEval_from_geometry U P T laws H hpair Z F N J
    hWsource hboundary pW hpW hGsource GG hcycle pG hpG K hK
      pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms hline hEzero hH hE hWoutput
      hGoutput HF pB hpB hlB hcB hinterior hsource hglue hcotangent V RT houtB pS hpS hSEL
      hSLB hSUA hSrows hinS houtS hlS pP hpP hcP hProws hinP houtP hlP hRpsi hRfund
      hRlabels hlL hpL hsL hhigh hrational hwdvv htermsL haddedL
    hV hHtwo hEtwo i q hg
  have hj := queryValue?_eq_checkedEval_from_geometry U P T laws H hpair Z F N J
    hWsource hboundary pW hpW hGsource GG hcycle pG hpG K hK
      pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms hline hEzero hH hE hWoutput
      hGoutput HF pB hpB hlB hcB hinterior hsource hglue hcotangent V RT houtB pS hpS hSEL
      hSLB hSUA hSrows hinS houtS hlS pP hpP hcP hProws hinP houtP hlP hRpsi hRfund
      hRlabels hlL hpL hsL hhigh hrational hwdvv htermsL haddedL
    hV hHtwo hEtwo j q hg
  exact hi.trans hj.symm

end AxiomaticGWTest.SurfaceGenusTwoBlowupDescendantReconstruction

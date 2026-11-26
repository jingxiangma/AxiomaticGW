/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupReconstruction

/-! Consumer regressions for the original-source geometric reconstruction API. -/

set_option linter.privateModule false

@[expose] public section
namespace AxiomaticGWTest.SurfaceGenusTwoBlowupReconstruction
open AxiomaticGW BelorousskiPandharipande RelationCertificate PsiBoundaryExpansion
open SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupReconstruction
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
    (hV : ExceptionalPointSupport V)
    (hHtwo : (SurfaceSeed.genusTwoHyperplane : SurfaceSeed X).query.eval U = -1 / 960)
    (hEtwo : ∀ j, (SurfaceSeed.genusTwoExceptional j : SurfaceSeed X).query.eval U =
      -1 / 2880)


include U P T laws H hpair Z F N J hWsource hboundary pW hpW hGsource GG hcycle pG hpG K hK pPsi
  hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms hline hEzero hH hE hWoutput hGoutput HF pB hpB
  hlB hcB hinterior hsource hglue hcotangent RT houtB pS hpS hSEL hSLB hSUA hSrows hinS houtS hlS pP
  hpP hcP hProws hinP houtP hlP hRpsi hRfund hRlabels hlL hpL hsL hhigh hrational hwdvv htermsL
  haddedL hV hHtwo hEtwo

/-- Choosing either exceptional shift yields the same full-class table under the
same original geometric inputs. No equality of recurrence steps is assumed. -/
theorem exceptional_choice_independent (i j : Fin X.blowups) (s : State X) :
    SurfaceGenusTwoBlowupRecursion.values i s =
      SurfaceGenusTwoBlowupRecursion.values j s := by
  have hi := values_eq_eval_from_geometry U P T laws H hpair Z F N J
      hWsource hboundary pW hpW hGsource GG hcycle pG hpG K hK
      pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms hline hEzero hH hE hWoutput
      hGoutput HF pB hpB hlB hcB hinterior hsource hglue hcotangent RT houtB pS hpS hSEL
      hSLB hSUA hSrows hinS houtS hlS pP hpP hcP hProws hinP houtP hlP hRpsi hRfund
      hRlabels hlL hpL hsL hhigh hrational hwdvv htermsL haddedL
      i hV hHtwo hEtwo s
  have hj := values_eq_eval_from_geometry U P T laws H hpair Z F N J
      hWsource hboundary pW hpW hGsource GG hcycle pG hpG K hK
      pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms hline hEzero hH hE hWoutput
      hGoutput HF pB hpB hlB hcB hinterior hsource hglue hcotangent RT houtB pS hpS hSEL
      hSLB hSUA hSrows hinS houtS hlS pP hpP hcP hProws hinP houtP hlP hRpsi hRfund
      hRlabels hlL hpL hsL hhigh hrational hwdvv htermsL haddedL
      j hV hHtwo hEtwo s
  exact hi.trans hj.symm

/-- The class-zero primary value follows from the divisor seeds and original
geometric relations; the consumer requires no primary seed. -/
theorem zero_primary_from_divisor_seeds (i : Fin X.blowups) :
    (Family.primary.query (0 : X.Curve)).eval U = 0 := by
  have hs := values_eq_eval_from_geometry U P T laws H hpair Z F N J
      hWsource hboundary pW hpW hGsource GG hcycle pG hpG K hK
      pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms hline hEzero hH hE hWoutput
      hGoutput HF pB hpB hlB hcB hinterior hsource hglue hcotangent RT houtB pS hpS hSEL
      hSLB hSUA hSrows hinS houtS hlS pP hpP hcP hProws hinP houtP hlP hRpsi hRfund
      hRlabels hlL hpL hsL hhigh hrational hwdvv htermsL haddedL
      i hV hHtwo hEtwo (0, .primary)
  rw [SurfaceGenusTwoBlowupRecursion.values_boundary i (0, .primary) (map_zero _)] at hs
  exact hs.symm.trans (SurfaceGenusTwoBlowupBoundary.value_zero .primary)

/-- Every nonzero full class of plane degree zero has zero canonical evaluation,
including reducible exceptional sums; no irreducibility premise is introduced. -/
theorem exceptional_boundary_from_geometry (i : Fin X.blowups)
    (beta : X.Curve) (hb : beta ≠ 0) (hd : X.planeDegree beta = 0) (family : Family X) :
    (family.query beta).eval U = 0 := by
  have hs := values_eq_eval_from_geometry U P T laws H hpair Z F N J
      hWsource hboundary pW hpW hGsource GG hcycle pG hpG K hK
      pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms hline hEzero hH hE hWoutput
      hGoutput HF pB hpB hlB hcB hinterior hsource hglue hcotangent RT houtB pS hpS hSEL
      hSLB hSUA hSrows hinS houtS hlS pP hpP hcP hProws hinP houtP hlP hRpsi hRfund
      hRlabels hlL hpL hsL hhigh hrational hwdvv htermsL haddedL
      i hV hHtwo hEtwo (beta, family)
  rw [SurfaceGenusTwoBlowupRecursion.values_boundary i (beta, family) hd,
    SurfaceGenusTwoBlowupBoundary.value_of_ne_zero beta hb family] at hs
  exact hs.symm

end AxiomaticGWTest.SurfaceGenusTwoBlowupReconstruction

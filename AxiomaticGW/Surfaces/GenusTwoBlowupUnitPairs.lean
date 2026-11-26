/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoUnitPairReduction
public import AxiomaticGW.Surfaces.GenusTwoDivisorPairReduction

/-! # Two-marked unit and divisor reductions from the original blowup equations

The string, dilaton and divisor equations identify the finite query with one or two
calibrated singletons. The original reconstruction hypotheses supply their geometric values.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwoBlowupDescendants
open RelationCertificate PsiBoundaryExpansion SurfaceGenusTwo
variable {X : SurfaceTarget}
attribute [local instance] strataRealizationModule

/-- Arithmetic evidence for a specific ordered request and rational value.  The four
constructors record which proved geometric identification the final replay uses. -/
inductive CheckedDescendant (i : Fin X.blowups) (q : SurfaceQuery X) (v : ℚ) : Prop where
  | mixed (h : queryValue? i q = some v)
  | unitPair (h : unitPairValue? i q = some v)
  | divisorPair (h : divisorPairValue? i q = some v)
  | exceptionalPoint (h : exceptionalPointQueryValue? q = some v)

variable
    (i : Fin X.blowups)
  {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups)
      X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (T : SurfaceTheoryIdentification X Omega)
    (laws : DescendantStringDilatonLaws M I)
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
    (hEzero : ∀ j, (SurfaceSeed.exceptional j : SurfaceSeed X).query.eval U = 1)
    (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed X).query.eval U =
      -1 / 8)
    (hEone : ∀ j, (SurfaceSeed.genusOneExceptional j : SurfaceSeed X).query.eval U =
      -1 / 24)
    (hWoutput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible Z F N)
    (hGoutput : ∀ n i z, z ∈ (GetzlerGraphs.expression i).addMarkings n → z.Compatible Z F N)
    (HF : TailForgetCompatible C)
    (V : StableMapIntersection U) (hV : ExceptionalPointSupport V)
    {St : StableMapStabilization V} (RT : RationalTailIntersection V St P)
    (hHtwo : (SurfaceSeed.genusTwoHyperplane : SurfaceSeed X).query.eval U = -1 / 960)
    (hEtwo : ∀ j, (SurfaceSeed.genusTwoExceptional j : SurfaceSeed X).query.eval U =
      -1 / 2880)
    (hBP : ∀ n beta a, RationalTerms.eval (SurfacePolynomialReduction.variableEval U P)
      (SurfaceGenusTwoBlowupNRelation.bpRow X n beta a) = 0)
    (hL : ∀ n beta (a : Fin 4 → SurfaceBasisLabel X),
      RationalTerms.eval (SurfacePolynomialReduction.variableEval U P)
        (L24Relation.normalizedGenusTwoTerms X n beta 0
          (SurfaceGenusZero.pointLabels a n)) = 0)

include i U P T laws H hpair Z F N J hWsource hboundary
  pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms
  honeTerms hline hEzero hH hEone hWoutput hGoutput HF V hV RT hHtwo hEtwo hBP hL

variable
  (pS : GenusTwoPsiSquare.Exchange) (hpS : GenusTwoPsiSquare.AcceptsExchange pS)
  (hELS : (Z 1 (Fin 1)).RelabelCompatible (Z 1 (Option (Fin 0)))
    GenusOnePsi.stableArity GenusTwoPsiSquare.ellipticSourceStable (finSuccEquiv 0))
  (hLBS : (Z 1 (Option (Fin 0))).SeparatingCompatible (Z 1 (Option (Fin 1)))
    (Z 2 (Fin 0 ⊕ Fin 1)) F GenusTwoPsiSquare.ellipticSourceStable
      GenusTwoPsiSquare.ellipticMarkedStable)
  (hUAS : (Z 2 (Fin 0 ⊕ Fin 1)).RelabelCompatible (Z 2 (Fin 1))
    GenusTwoPsiSquare.separatingStable GenusTwoPsiSquare.stableArity
      (Equiv.emptySum (Fin 0) (Fin 1)))
  (hinteriorS : ∀ i : Fin 6, (Z 2 (Fin 1)).map
    (interpret GenusTwoPsiSquare.columns (GenusTwoPsiSquare.rows i.castSucc)) = 0)
  (hinS : ∀ t ∈ GenusTwoPsiSquare.cotangentRelation,
    t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
  (houtS : ∀ n t, t ∈ GenusTwoPsiSquare.cotangentRelation → ∀ z ∈ t.2.addMarkings n,
    z.2.expression.Compatible Z F N ∧ z.2.expression.CotangentCompatible Z P)
  (pP : GenusTwoPsiProduct.Exchange) (hpP : GenusTwoPsiProduct.AcceptsExchange pP)
  (hcP : ∀ b, GenusTwoPsiProduct.SourceCompatible Z F b)
  (hsourceP : ∀ b,
    (Z (BelorousskiPandharipande.sourceGenus (GenusTwoPsiProduct.sourceFamily b))
      (Fin (BelorousskiPandharipande.sourceArity (GenusTwoPsiProduct.sourceFamily b)))).map
        (BelorousskiPandharipande.sourceExpression (GenusTwoPsiProduct.sourceIndex b)) = 0)
  (hinteriorP : ∀ i : Fin 10, (Z 2 (Fin 2)).map
    (interpret GenusTwoPsiProduct.columns
      (GenusTwoPsiProduct.rows (Fin.castAdd 3 i))) = 0)
  (hinP : ∀ t ∈ GenusTwoPsiProduct.cotangentRelation,
    t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
  (houtP : ∀ n t, t ∈ GenusTwoPsiProduct.cotangentRelation → ∀ z ∈ t.2.addMarkings n,
    z.2.expression.Compatible Z F N ∧ z.2.expression.CotangentCompatible Z P)

include pS hpS hELS hLBS hUAS hinteriorS hinS houtS pP hpP hcP hsourceP
  hinteriorP hinP houtP

/-- At every recognized two-marked query the original finite blowup algorithm agrees with
the string/dilaton singleton computation under its original geometric reconstruction hypotheses. -/
theorem queryValue?_unitPair_from_original_equations (q : SurfaceQuery X) {claimed : ℚ}
    (hc : unitPairValue? i q = some claimed) : queryValue? i q = some claimed := by
  obtain ⟨rule, s, h⟩ := exists_reduction_of_unitPairValue? i q hc
  exact (unitPairValue?_eq_of_identification U T.unit_eq laws i
    (queryValue?_eq_checkedEval_from_original_equations i U P T laws H hpair Z F N J hWsource
      hboundary pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop
      hzeroTerms honeTerms hline hEzero hH hEone hWoutput hGoutput HF V hV RT hHtwo hEtwo
      hBP hL pS hpS hELS hLBS hUAS hinteriorS hinS houtS pP hpP hcP hsourceP hinteriorP
      hinP houtP) q h).trans hc

/-- Accepted two-marked units give the actual ordered geometric descendant under the
original reconstruction hypotheses, including the named string and dilaton laws. -/
theorem unitPairValue?_checkedEval_from_original_equations (q : SurfaceQuery X) {claimed : ℚ}
    (hc : unitPairValue? i q = some claimed) : q.checkedEval U = some claimed := by
  obtain ⟨rule, s, h⟩ := exists_reduction_of_unitPairValue? i q hc
  obtain ⟨last, hq⟩ := unitPairReduction?_sound q h
  have hg : q.genus = 2 := congrArg SurfaceQuery.genus hq
  have hid := queryValue?_eq_checkedEval_from_original_equations i U P T laws H hpair Z F N J
      hWsource
      hboundary pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop
      hzeroTerms honeTerms hline hEzero hH hEone hWoutput hGoutput HF V hV RT hHtwo hEtwo
      hBP hL pS hpS hELS hLBS hUAS hinteriorS hinS houtS pP hpP hcP hsourceP hinteriorP
      hinP houtP
  exact (hid q hg).symm.trans
    ((unitPairValue?_eq_of_identification U T.unit_eq laws i hid q h).trans hc)

/-- The divisor reduction gives both the original finite query and its geometric descendant
from the original reconstruction data. The cup action is the derived surface cup product. -/
theorem divisorPair_from_original_equations (q : SurfaceQuery X) {claimed : ℚ}
    (hc : divisorPairValue? i q = some claimed) :
    queryValue? i q = some claimed ∧ q.checkedEval U = some claimed := by
  have hid := queryValue?_eq_checkedEval_from_original_equations i U P T laws H hpair Z F N J
      hWsource
      hboundary pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop
      hzeroTerms honeTerms hline hEzero hH hEone hWoutput hGoutput HF V hV RT hHtwo hEtwo
      hBP hL pS hpS hELS hLBS hUAS hinteriorS hinS houtS pP hpP hcP hsourceP hinteriorP
      hinP houtP
  have hs (beta : X.Curve) (s : SurfaceInsertion X) :
      queryValue? i ⟨2, beta, [s]⟩ = some (SurfaceQuery.eval U ⟨2, beta, [s]⟩) := by
    rw [hid _ rfl, SurfaceQuery.checkedEval_of_geometricDomain U _ (Or.inr (by
      change StableArity 2 (Fin 1); simp only [StableArity, Fintype.card_fin]; decide))]
  obtain ⟨hg, hv⟩ := divisorPair_checkedEval_of_identification U T laws H hpair _ hs q hc
  exact ⟨(hid q hg).trans hv, hv⟩

/-- Every certified route gives the same original reconstruction and actual geometric
evaluation under the existing relation, stable-map, and seed hypotheses. -/
theorem CheckedDescendant.from_original_equations (q : SurfaceQuery X) (hg : q.genus = 2)
    {v : ℚ} (hc : CheckedDescendant i q v) :
    queryValue? i q = some v ∧ q.checkedEval U = some v := by
  have hid := queryValue?_eq_checkedEval_from_original_equations i U P T laws H hpair Z F N J
    hWsource hboundary pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop
    hzeroTerms honeTerms hline hEzero hH hEone hWoutput hGoutput HF V hV RT hHtwo hEtwo
    hBP hL pS hpS hELS hLBS hUAS hinteriorS hinS houtS pP hpP hcP hsourceP hinteriorP hinP houtP
  suffices hv : q.checkedEval U = some v from ⟨(hid q hg).trans hv, hv⟩
  cases hc with
  | mixed h => exact (hid q hg).symm.trans h
  | unitPair h =>
    obtain ⟨_, _, hr⟩ := exists_reduction_of_unitPairValue? i q h
    exact (hid q hg).symm.trans
      ((unitPairValue?_eq_of_identification U T.unit_eq laws i hid q hr).trans h)
  | divisorPair h =>
    exact (divisorPair_from_original_equations i U P T laws H hpair Z F N J hWsource hboundary
      pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms
      honeTerms hline hEzero hH hEone hWoutput hGoutput HF V hV RT hHtwo hEtwo hBP hL pS
      hpS hELS hLBS hUAS hinteriorS hinS houtS pP hpP hcP hsourceP hinteriorP hinP houtP q h).2
  | exceptionalPoint h => exact exceptionalPointQueryValue?_sound V hV q v h

end AxiomaticGW.SurfaceGenusTwoBlowupDescendants

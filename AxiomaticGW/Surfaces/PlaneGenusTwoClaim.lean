/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneGenusTwoCertificate
public import AxiomaticGW.Surfaces.PlaneGenusTwoReconstruction

/-!
# Geometric interpretation of accepted plane genus-two queries

The certificate checks its whole requested query and exact answer. Its final
interpretation uses the original BP reconstruction theorem, its named geometric
inputs and the same three numerical seeds. It adds no recurrence hypothesis.
All canonical queries have stable genus-two arity, including degree zero.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open RelationCertificate PsiBoundaryExpansion SurfacePolynomialReduction

/-- Genus two makes every canonical marking count geometrically admissible. -/
theorem planeCanonicalQueries_geometricDomain (d : ℕ) (j : Fin 3) :
    (planeCanonicalQueries d j).GeometricDomain := by
  right
  have hg : (planeCanonicalQueries d j).genus = 2 := by
    fin_cases j <;> rfl
  unfold StableArity
  rw [hg]
  omega

attribute [local instance] strataRealizationModule

/-- An accepted full claim gives the requested geometric invariant under the
original class-level inputs and finite seeds, with no supplied invariant family. -/
theorem planeCheckCanonicalClaim_checkedEval_from_geometry
    {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology SurfaceTarget.plane.blowups)
      SurfaceTarget.plane.Curve SurfaceTarget.plane.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (T : SurfaceTheoryIdentification SurfaceTarget.plane Omega)
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
    (hline : (SurfaceSeed.line : SurfaceSeed SurfaceTarget.plane).query.eval U = 1)
    (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed SurfaceTarget.plane).query.eval U =
      -1 / 8)
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
    (hout : ∀ n i e t, t ∈ (orbitCotangentTerm i e).addMarkings n →
      t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
    (hHtwo : (SurfaceSeed.genusTwoHyperplane : SurfaceSeed SurfaceTarget.plane).query.eval U =
      -1 / 960)
    (bound : ℕ) (values : ℕ → Fin 3 → ℚ)
    (query : SurfaceQuery .plane) (claimed : ℚ)
    (hcheck : planeCheckCanonicalClaim bound values query claimed = true) :
    query.checkedEval U = some claimed := by
  obtain ⟨d, _, j, rfl, hvalue⟩ :=
    planeCheckCanonicalClaim_sound bound values query claimed hcheck
  rw [SurfaceQuery.checkedEval_of_geometricDomain U _
    (planeCanonicalQueries_geometricDomain d j)]
  have he := planeCanonicalValues_from_geometry U P T laws H hpair Z F N J hWsource hboundary
    pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms
    honeTerms hline hH hWoutput hGoutput HF pB hpB hlB hcB hinterior hsource
    hglue hcotangent RT hout hHtwo d
  rw [congrFun he j, hvalue]

end AxiomaticGW.BelorousskiPandharipande

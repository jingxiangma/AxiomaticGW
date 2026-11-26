/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneGenusTwoRecursion

/-!
# Plane canonical genus-two reconstruction from finite seeds

The original BP equations determine the initial primary entry and all
positive-degree triples. The only additional genus-two numerical input is
the previously declared degree-zero H seed. Lower-genus constants use the
existing finite-seed algorithms. No initial primary value, ancestor family,
solved recurrence or extra geometric hypothesis is supplied.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open RelationCertificate PsiBoundaryExpansion SurfacePolynomialReduction

attribute [local instance] strataRealizationModule

/-- All three canonical plane families equal the terminating executable
algorithm under the original named geometric inputs and three finite seeds:
the line value, the degree-zero genus-one H value and genus-two H value. -/
theorem planeCanonicalValues_from_geometry
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
    (d : ℕ) : (fun j ↦ (planeCanonicalQueries d j).eval U) = planeCanonicalValues d := by
  have he (n : ℕ) (beta : SurfaceTarget.plane.Curve)
      (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel .plane) :
      RationalTerms.eval (variableEval U P)
        (normalizedGenusTwoTerms .plane n beta 0 a) = 0 :=
    eval_normalizedGenusTwoTerms_eq_zero U P T laws H hpair Z F N J hWsource hboundary
      pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms
      honeTerms hline (fun i ↦ Fin.elim0 i) hH (fun i ↦ Fin.elim0 i)
      hWoutput hGoutput HF pB hpB hlB hcB hinterior hsource
      hglue hcotangent RT n (hout n) beta 0 a
  have heq (b : ℕ) (i : Fin 3) :
      RationalTerms.eval (variableEval U P) (planeShiftedTerms b i) = 0 := by
    fin_cases i
    · exact he (3 * b + 1) ![b + 1]
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .point] (3 * b + 1))
    · exact he (3 * b) ![b + 1]
        (SurfaceGenusZero.pointLabels ![.hyperplane, .point, .point] (3 * b))
    · exact he (3 * b - 1) ![b + 1]
        (SurfaceGenusZero.pointLabels ![.point, .point, .point] (3 * b - 1))
  have hHtwo' : variableEval U P (Sum.inr (planeCanonicalQueries 0 1)) = -1 / 960 := by
    change (SurfaceFirstDescendant.query 2 ![0] .hyperplane 0).eval U = -1 / 960
    rw [show (![0] : SurfaceTarget.plane.Curve) = 0 from by decide +kernel]
    exact hHtwo
  have hPtwo' : variableEval U P (Sum.inr (planeCanonicalQueries 0 2)) = 0 :=
    SurfaceQuery.eval_eq_zero_of_dimension_incompatible U T
      (planeCanonicalQueries 0 2) (by decide +kernel)
  have hinitial := planeCanonicalInitial_eq_of_equation (variableEval U P)
    (heq 0 1) hHtwo' hPtwo'
  exact eq_planeCanonicalValues_of_equations (variableEval U P)
    (fun j ↦ congrFun hinitial j) (fun b _ ↦ heq b) d

end AxiomaticGW.BelorousskiPandharipande

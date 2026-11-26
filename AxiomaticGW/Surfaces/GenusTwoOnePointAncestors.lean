/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusOneAncestors
public import AxiomaticGW.Surfaces.DecoratedGluingEvaluation
public import AxiomaticGW.Tautological.GenusTwoPsiGluing

/-!
# Genus-two one-point ancestors of cotangent power at least two

The checked psi-square relation reduces these ancestors to ten node-decorated
contractions. Their components have genus at most one and use the already
proved finite-seed evaluators. No genus-two invariant or recurrence is supplied
as a numerical input. This does not cover genus-two primary/first-descendant
sectors, additional markings, or stable-map descendants.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo
open GenusTwoPsiSquare RelationCertificate

/-- Existing lower-genus reconstruction on the terminal component markings.
The contraction below consults this dispatch only in genera zero and one. -/
def lowerVertex (X : SurfaceTarget) : SurfaceVertexValues X ℚ :=
  fun g S _ h beta k a ↦ SurfaceGenusOne.componentValue X
    (SurfaceGenusOne.ancestorValue X) (SurfaceAncestorKey.ofLabels g S h beta k a)

/-- Exact one-marked ancestor with power `2 + k` at any full effective class. -/
def onePointAncestorValue (X : SurfaceTarget) (beta : X.Curve) (k : ℕ)
    (a : SurfaceBasisLabel X) : ℚ :=
  ∑ i, boundary (boundaryIndex i) *
    (boundaryTerm i).1.surfaceDecoratedEval X (lowerVertex X) (boundaryTerm i).2
      beta (Pi.single 0 k) (fun _ ↦ a)

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {I : StableCurveIntegration C}

/-- The terminal dispatcher is the actual ancestor family in its proved genus range. -/
theorem lowerVertex_eq (P : PsiClasses C)
    (hzero : ∀ q : SurfaceAncestorKey X, q.genus = 0 →
      SurfaceGenusZero.ancestorValue X q = q.eval Omega P I)
    (hone : ∀ q : SurfaceAncestorKey X, q.genus = 1 →
      SurfaceGenusOne.ancestorValue X q = q.eval Omega P I)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) (hg : g ≤ 1) :
    lowerVertex X g S h beta k a = Omega.surfaceVertexValues P I g S h beta k a := by
  let q := SurfaceAncestorKey.ofLabels g S h beta k a
  have hq : q.genus = g := rfl
  have he : SurfaceGenusOne.componentValue X (SurfaceGenusOne.ancestorValue X) q =
      q.eval Omega P I := by
    by_cases hz : q.genus = 0
    · rw [SurfaceGenusOne.componentValue, if_pos hz]
      exact hzero q hz
    · rw [SurfaceGenusOne.componentValue, if_neg hz]
      exact hone q (by omega)
  exact he.trans (SurfaceAncestorKey.eval_ofLabels Omega P I g S h beta k a)

attribute [local instance] strataRealizationModule

/-- The new contraction uses only the identified lower-genus families.
The final theorem below closes these identifications using their existing proofs. -/
theorem onePointAncestorValue_eq_of_identifications
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (hpair : Omega.pairing = (SurfaceCohomology.frobenius X.blowups).pairing)
    (p : Exchange) (hp : AcceptsExchange p)
    (hpsi : (Z 2 (Fin 1)).LegPsiCompatible P stableArity)
    (hfund : (Z 2 (Fin 1)).map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) stableArity)) = 1)
    (hrows : ∀ i, (Z 2 (Fin 1)).map (interpret columns (rows i)) = 0)
    (hglue : ∀ i, (boundaryTerm i).1.Compatible Z F N)
    (hcotangent : ∀ i, (boundaryTerm i).1.CotangentCompatible Z P)
    (hzero : ∀ q : SurfaceAncestorKey X, q.genus = 0 →
      SurfaceGenusZero.ancestorValue X q = q.eval Omega P I)
    (hone : ∀ q : SurfaceAncestorKey X, q.genus = 1 →
      SurfaceGenusOne.ancestorValue X q = q.eval Omega P I)
    (beta : X.Curve) (k : ℕ) (a : SurfaceBasisLabel X) :
    onePointAncestorValue X beta k a =
      Omega.ancestorInvariant P I 2 (Fin 1) stableArity beta (Pi.single 0 (2 + k))
        (fun _ ↦ a.value) := by
  rw [gwAncestor_reduction Z F N Omega P p hp hpsi hfund hrows hglue hcotangent]
  unfold onePointAncestorValue
  apply Finset.sum_congr rfl
  intro i _
  rw [(boundaryTerm i).1.surfaceDecoratedEval_congr_of_genus X (lowerVertex X)
    (Omega.surfaceVertexValues P I) (boundaryTerm i).2 beta (Pi.single 0 k) (fun _ ↦ a)
    (fun g S _ h beta k a hg ↦ lowerVertex_eq P hzero hone g S h beta k a
      (hg.trans (boundaryTerm_genus i)))]
  rw [(boundaryTerm i).1.surfaceDecoratedEval_eq_gwDecoratedAncestorContraction
    Omega P I hpair]
  rfl

/-- One-point genus-two ancestors of power at least two are determined by the
original finite low-genus seeds, accepted relations and named geometric laws.
The seventh genus-two row and all lower-genus numerical values are derived. -/
theorem onePointAncestorValue_eq {C : StableCurveCohomology ℚ}
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
    (pTwo : Exchange) (hpTwo : AcceptsExchange pTwo)
    (hTwoPsi : (Z 2 (Fin 1)).LegPsiCompatible P stableArity)
    (hTwoFund : (Z 2 (Fin 1)).map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) stableArity)) = 1)
    (hTwoRows : ∀ i : Fin 6, (Z 2 (Fin 1)).map (interpret columns (rows i.castSucc)) = 0)
    (hEL : (Z 1 (Fin 1)).RelabelCompatible (Z 1 (Option (Fin 0)))
      GenusOnePsi.stableArity ellipticSourceStable (finSuccEquiv 0))
    (hLB : (Z 1 (Option (Fin 0))).SeparatingCompatible (Z 1 (Option (Fin 1)))
      (Z 2 (Fin 0 ⊕ Fin 1)) F ellipticSourceStable ellipticMarkedStable)
    (hUA : (Z 2 (Fin 0 ⊕ Fin 1)).RelabelCompatible (Z 2 (Fin 1))
      separatingStable stableArity (Equiv.emptySum (Fin 0) (Fin 1)))
    (hglue : ∀ i, (boundaryTerm i).1.Compatible Z F N)
    (hcotangent : ∀ i, (boundaryTerm i).1.CotangentCompatible Z P)
    (beta : X.Curve) (k : ℕ) (a : SurfaceBasisLabel X) :
    onePointAncestorValue X beta k a =
      Omega.ancestorInvariant P I 2 (Fin 1) stableArity beta (Pi.single 0 (2 + k))
        (fun _ ↦ a.value) := by
  have hTwoAll : ∀ i, (Z 2 (Fin 1)).map (interpret columns (rows i)) = 0 :=
    Fin.lastCases (elliptic_row_vanishes (Z 1 (Fin 1)) (Z 1 (Option (Fin 0)))
      (Z 1 (Option (Fin 1))) (Z 2 (Fin 0 ⊕ Fin 1)) (Z 2 (Fin 1)) F
      hEL hLB hUA (hrows 0)) hTwoRows
  exact onePointAncestorValue_eq_of_identifications Z F N P T.pairing_eq pTwo hpTwo
    hTwoPsi hTwoFund hTwoAll hglue hcotangent
    (SurfaceGenusZero.ancestorValue_eq_eval U T laws H hpair Z F N J hWsource hboundary pW hpW
      P K hK hzeroTerms hline hEzero hWoutput)
    (SurfaceGenusOne.ancestorValue_eq_eval U P T laws H hpair Z F N J hWsource hboundary pW hpW
      hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms
      hline hEzero hH hE hWoutput hGoutput) beta k a

end AxiomaticGW.SurfaceGenusTwo

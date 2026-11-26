/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoOnePointAncestors
public import AxiomaticGW.GW.Descendants.DegreeZeroComparison

/-!
# Degree-zero genus-two one-point descendant certificates

The existing one-point ancestor algorithm is interpreted as a stable-map
descendant in class zero using the proved absence of positive rational tails.
The query interface retains the target, genus, full class, state and power.
It supports one marking with cotangent power at least two. Other sectors
remain the responsibility of the general surface reconstruction algorithms.
The final soundness theorem uses the original low-genus seeds and geometric
relations; no genus-two value is an additional numerical input.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo
open GenusTwoPsiSquare RelationCertificate

/-- Evaluate the degree-zero one-point sector with at least two cotangent powers.
Unsupported genus, curve class, arity or powers return `none`. -/
def degreeZeroOnePointQueryValue? {X : SurfaceTarget} (q : SurfaceQuery X) : Option ℚ :=
  match q.insertions with
  | [a] => if q.genus = 2 ∧ q.beta = 0 ∧ 2 ≤ a.psi then
      some (onePointAncestorValue X 0 (a.psi - 2) a.label)
    else none
  | _ => none

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- Intermediate interpretation using an identified ancestor algorithm.
The final theorem below supplies this identification from the original inputs. -/
theorem degreeZeroOnePointQueryValue?_sound_of_identification
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    {G : StableMapIntersection U} {St : StableMapStabilization G}
    (RT : RationalTailIntersection G St P)
    (hancestor : ∀ k a, onePointAncestorValue X 0 k a =
      Omega.ancestorInvariant P I 2 (Fin 1) stableArity 0 (Pi.single 0 (2 + k))
        (fun _ ↦ a.value))
    (q : SurfaceQuery X) (claimed : ℚ)
    (hvalue : degreeZeroOnePointQueryValue? q = some claimed) :
    q.checkedEval U = some claimed := by
  rcases q with ⟨g, beta, marks⟩
  cases marks with
  | nil => cases hvalue
  | cons a marks =>
    cases marks with
    | cons b marks => cases hvalue
    | nil =>
      simp only [degreeZeroOnePointQueryValue?] at hvalue
      split_ifs at hvalue with h
      · rcases h with ⟨rfl, rfl, hpower⟩
        have hv := Option.some.inj hvalue
        rw [SurfaceQuery.checkedEval_of_geometricDomain U _ (Or.inr stableArity)]
        apply congrArg some
        simp only [SurfaceQuery.eval, List.length_singleton, List.get_eq_getElem,
          List.getElem_singleton]
        rw [U.invariant_of_stable 2 (Fin 1) stableArity,
          RT.invariant_zero_class 2 (Fin 1) stableArity]
        have hp : (fun _ : Fin 1 ↦ a.psi) = Pi.single 0 (2 + (a.psi - 2)) := by
          funext i
          rw [Subsingleton.elim i (0 : Fin 1), Pi.single_eq_same]
          omega
        rw [hp, ← hancestor]
        exact hv

attribute [local instance] strataRealizationModule

/-- Accepted degree-zero one-point descendant claims follow from the original
low-genus seeds, relation generators and primitive cotangent geometry.
No genus-two numerical seed or free ancestor family is assumed. -/
theorem degreeZeroOnePointQueryValue?_sound {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    {G : StableMapIntersection U} {St : StableMapStabilization G}
    (RT : RationalTailIntersection G St P)
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
    (q : SurfaceQuery X) (claimed : ℚ)
    (hvalue : degreeZeroOnePointQueryValue? q = some claimed) :
    q.checkedEval U = some claimed := by
  apply degreeZeroOnePointQueryValue?_sound_of_identification U P RT
    (fun k a ↦ onePointAncestorValue_eq U P T laws H hpair Z F N J
      hWsource hboundary pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi
      hpsi hfund hrows hloop hzeroTerms honeTerms hline hEzero hH hE hWoutput hGoutput
      pTwo hpTwo hTwoPsi hTwoFund hTwoRows hEL hLB hUA hglue hcotangent 0 k a)
    q claimed hvalue

end AxiomaticGW.SurfaceGenusTwo

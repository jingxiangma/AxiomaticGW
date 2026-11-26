/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.GKM.Fixtures.GenusTwoDegreeZeroReplay
import AxiomaticGW.Tautological.Fixtures.GenusTwoPsiSquareReplay
import AxiomaticGW.Tautological.Fixtures.GenusOnePsiReplay
import AxiomaticGWTest.Tautological.GetzlerReplay
import AxiomaticGWTest.Tautological.WDVVReplay

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusTwoDegreeZeroDescendants
open AxiomaticGW SurfaceGenusTwo GenusTwoPsiSquare RelationCertificate

-- Actual incoming GKM values are kernel checked on all three fixed targets.
example : degreeZeroOnePointQueryValue? (X := .plane) ⟨2, ![0], [⟨.unit, 2⟩]⟩ =
    some (7/640) := GKM.GenusTwoDegreeZeroReplay.Plane.accepted 0
example : degreeZeroOnePointQueryValue? (X := .hirzebruchOne) ⟨2, ![0,0], [⟨.unit, 2⟩]⟩ =
    some (7/720) := GKM.GenusTwoDegreeZeroReplay.OneBlowup.accepted 0
example : degreeZeroOnePointQueryValue? (X := .blowupTwo) ⟨2, ![0,0,0], [⟨.unit, 2⟩]⟩ =
    some (49/5760) := GKM.GenusTwoDegreeZeroReplay.TwoBlowups.accepted 0

-- The partial evaluator rejects unsupported sectors without inventing zero values.
example : degreeZeroOnePointQueryValue? (X := .plane) ⟨1, ![0], [⟨.unit, 2⟩]⟩ = none := by
  decide +kernel
example : degreeZeroOnePointQueryValue? (X := .hirzebruchOne)
    ⟨2, ![1,0], [⟨.unit, 2⟩]⟩ = none := by decide +kernel
example : degreeZeroOnePointQueryValue? (X := .blowupTwo)
    ⟨2, ![0,1,0], [⟨.unit, 2⟩]⟩ = none := by decide +kernel
example : degreeZeroOnePointQueryValue? (X := .plane) ⟨2, ![0], [⟨.hyperplane, 1⟩]⟩ = none := by
  decide +kernel
example : degreeZeroOnePointQueryValue? (X := .plane) ⟨2, ![0], []⟩ = none := by decide +kernel
example : degreeZeroOnePointQueryValue? (X := .plane)
    ⟨2, ![0], [⟨.unit, 2⟩, ⟨.unit, 0⟩]⟩ = none := by decide +kernel

section Mixed
variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  {U : UnstableDescendantConventions M I} {G : StableMapIntersection U}
  {St : StableMapStabilization G} {P : PsiClasses C}
  (RT : RationalTailIntersection G St P)

-- Distinct marked powers add componentwise without exchanging the states.
example (h : StableArity 0 (Fin 3)) (a : Fin 3 → SurfaceCohomology X.blowups) :
    M.mixedInvariant P I 0 (Fin 3) h 0 ![2,0,1] ![1,4,0] a =
      Omega.ancestorInvariant P I 0 (Fin 3) h 0 ![3,4,1] a := by
  have hp : (![2,0,1] : Fin 3 → ℕ) + ![1,4,0] = ![3,4,1] := by
    funext i
    fin_cases i <;> rfl
  simpa only [hp] using RT.mixedInvariant_zero_class 0 (Fin 3) h ![2,0,1] ![1,4,0] a

-- Empty markings are allowed in the stable genus-two degree-zero sector.
example (h : StableArity 2 (Fin 0)) (a : Fin 0 → SurfaceCohomology X.blowups) :
    M.invariant I 2 (Fin 0) h 0 0 a = Omega.ancestorInvariant P I 2 (Fin 0) h 0 0 a :=
  RT.invariant_zero_class 2 (Fin 0) h 0 a
end Mixed

attribute [local instance] strataRealizationModule

-- The final consumer uses all four actual relation presentations and no genus-two seed.
example {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
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
    (hGsource : ∀ i, (GetzlerGraphs.expression i).Compatible Z F N)
    (GG : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (Z 1 (Fin 4)).map (GetzlerGraphs.cycle x) = GG.cycle x)
    (K : PsiForgetFormula P) (hK : PsiBoundaryExpansion.TailCompatible K F N)
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
    q.checkedEval U = some claimed :=
  degreeZeroOnePointQueryValue?_sound U P RT T laws H hpair Z F N J hWsource hboundary
    WDVVReplay.presentation WDVVReplay.accepted hGsource GG hcycle
    GetzlerReplay.presentation GetzlerReplay.accepted K hK
    GenusOnePsiReplay.presentation GenusOnePsiReplay.accepted hpsi hfund hrows hloop
    hzeroTerms honeTerms hline hEzero hH hE hWoutput hGoutput
    GenusTwoPsiSquareReplay.exchange GenusTwoPsiSquareReplay.accepted hTwoPsi hTwoFund
    hTwoRows hEL hLB hUA hglue hcotangent q claimed hvalue

end AxiomaticGWTest.Surfaces.GenusTwoDegreeZeroDescendants

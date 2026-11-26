/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.GenusTwoOnePointAncestors
import AxiomaticGW.Surfaces.GenusOneBenchmarks
import AxiomaticGW.Tautological.Fixtures.GenusTwoPsiSquareReplay
import AxiomaticGW.Tautological.Fixtures.GenusOnePsiReplay
import AxiomaticGWTest.Tautological.GetzlerReplay
import AxiomaticGWTest.Tautological.WDVVReplay

set_option linter.privateModule false
-- Keep the larger numerical kernel reductions from competing for memory.
set_option Elab.async false

namespace AxiomaticGWTest.Surfaces.GenusTwoOnePointAncestors
open AxiomaticGW SurfaceGenusTwo GenusTwoPsiSquare RelationCertificate

-- The stored node decoration is on the selected separating branch, not the external marking.
example : let t := boundaryTerm 1
    (t.1.decoratedGraph t.2).halfEdgePsiPower ⟨0, by decide +kernel⟩ 1 = 1 ∧
    (t.1.decoratedGraph t.2).halfEdgePsiPower ⟨0, by decide +kernel⟩ 0 = 0 ∧
    (t.1.decoratedGraph t.2).legPsiPower 0 = 0 := by decide +kernel

-- Closing a loop transports each of its two original marked cotangent powers separately.
example : let t := boundaryTerm 4
    (t.1.decoratedGraph t.2).halfEdgePsiPower ⟨0, by decide +kernel⟩ 0 = 1 ∧
    (t.1.decoratedGraph t.2).halfEdgePsiPower ⟨0, by decide +kernel⟩ 1 = 0 := by decide +kernel

-- The new layer preserves the old numerical evaluator, for arbitrary components and powers.
example {A : Type} [CommRing A] [Algebra ℚ A] (X : SurfaceTarget)
    (v : SurfaceVertexValues X A) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    x.surfaceDecoratedEval X v x.zeroDecoration beta k a = x.surfaceEval X v beta k a :=
  x.surfaceDecoratedEval_zeroDecoration X v beta k a

-- Original component powers add to external powers; neither overwrites the other.
example (X : SurfaceTarget) (v : SurfaceVertexValues X ℚ) (beta : X.Curve)
    (a : Fin 2 → SurfaceBasisLabel X) :
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])).surfaceDecoratedEval
      X v ![1, 2] beta ![3, 4] a = v 1 (Fin 2) (by norm_num [StableArity]) beta ![4, 6] a := by
  have h : (![3, 4] : Fin 2 → ℕ) + ![1, 2] = ![4, 6] := by
    funext i
    fin_cases i <;> rfl
  simp only [GluingExpression.surfaceDecoratedEval, h]

-- Degree-zero constants are reconstructed, not supplied as genus-two seeds.
example : onePointAncestorValue .plane ![0] 0 .unit = 7/640 := by decide +kernel
example : onePointAncestorValue .hirzebruchOne ![0,0] 0 .unit = 7/720 := by decide +kernel
example : onePointAncestorValue .blowupTwo ![0,0,0] 0 .unit = 49/5760 := by decide +kernel

-- These are stable-curve ancestors; positive-degree stable-map descendants are separate.
example : onePointAncestorValue .plane ![1] 1 .point = -9/640 := by decide +kernel
example : onePointAncestorValue .plane ![1] 2 .hyperplane = 1/128 := by decide +kernel
example : onePointAncestorValue .plane ![1] 3 .unit = 0 := by decide +kernel
example : onePointAncestorValue .hirzebruchOne ![1,0] 0 (.exceptional 0) = -13/2880 := by
  decide +kernel
example : onePointAncestorValue .hirzebruchOne ![1,0] 1 .unit = 1/240 := by decide +kernel

section DoubleCover

-- Reuse the checked primary table instead of recomputing its Getzler equations.
private theorem ellipticCached (beta : SurfaceTarget.hirzebruchOne.Curve) :
    SurfaceGenusOne.pointValue .hirzebruchOne beta =
      if SurfaceTarget.hirzebruchOne.effective.energy beta ≤ 12
      then GenusOneF1Table.values beta else SurfaceGenusOne.pointValue .hirzebruchOne beta := by
  split_ifs with h
  · exact (SurfaceGenusOne.pointBenchmarkValues_eq .hirzebruchOne beta h).symm
  · rfl

attribute [local cbv_eval] ellipticCached

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
-- Normalize ten decorated contractions while reusing the certified primary values.
set_option cbv.maxSteps 4000000 in
example : onePointAncestorValue .hirzebruchOne ![2,0] 0 .point = 0 := by cbv

end DoubleCover

-- Distinct exceptional states/classes are retained despite equal anticanonical energy.
example : onePointAncestorValue .blowupTwo ![1,0,0] 0 (.exceptional 0) = -13/2880 := by
  decide +kernel
example : onePointAncestorValue .blowupTwo ![1,0,0] 0 (.exceptional 1) = 0 := by decide +kernel

attribute [local instance] strataRealizationModule

-- The final consumer uses all four actual exported relation presentations.
example {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
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
    (beta : X.Curve) (k : ℕ) (a : SurfaceBasisLabel X) :
    onePointAncestorValue X beta k a =
      Omega.ancestorInvariant P I 2 (Fin 1) stableArity beta (Pi.single 0 (2 + k))
        (fun _ ↦ a.value) :=
  onePointAncestorValue_eq U P T laws H hpair Z F N J hWsource hboundary
    WDVVReplay.presentation WDVVReplay.accepted hGsource GG hcycle
    GetzlerReplay.presentation GetzlerReplay.accepted K hK
    GenusOnePsiReplay.presentation GenusOnePsiReplay.accepted hpsi hfund hrows hloop
    hzeroTerms honeTerms hline hEzero hH hE hWoutput hGoutput
    GenusTwoPsiSquareReplay.exchange GenusTwoPsiSquareReplay.accepted hTwoPsi hTwoFund
    hTwoRows hEL hLB hUA hglue hcotangent beta k a

end AxiomaticGWTest.Surfaces.GenusTwoOnePointAncestors

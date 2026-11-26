/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.GenusOneDescendants
import AxiomaticGW.Tautological.Fixtures.GenusOnePsiReplay
import AxiomaticGWTest.Tautological.GetzlerReplay
import AxiomaticGWTest.Tautological.WDVVReplay

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusOneDescendants
open AxiomaticGW SurfaceGenusOne

/-- The raw loop gives the target-dependent Euler characteristic contribution. -/
example : queryValue? (X := .plane) ⟨1,0,[⟨.unit,1⟩]⟩ = some (1/8) ∧
    queryValue? (X := .hirzebruchOne) ⟨1,0,[⟨.unit,1⟩]⟩ = some (1/6) ∧
    queryValue? (X := .blowupTwo) ⟨1,0,[⟨.unit,1⟩]⟩ = some (5/24) := by
  decide +kernel

/-- Marking multiplicity changes the elliptic dilaton factor. -/
example : queryValue? (X := .plane) ⟨1,0,[⟨.unit,1⟩,⟨.unit,1⟩]⟩ = some (1/8) ∧
    queryValue? (X := .plane) ⟨1,0,[⟨.unit,1⟩,⟨.unit,1⟩,⟨.unit,1⟩]⟩ = some (1/4) := by
  decide +kernel

/-- Sorting transports powers with states; a negative divisor value survives. -/
example : queryValue? (X := .hirzebruchOne) ⟨1,0,[⟨.unit,1⟩,⟨.exceptional 0,0⟩]⟩ =
      some (-1/24) ∧
    queryValue? (X := .hirzebruchOne) ⟨1,0,[⟨.exceptional 0,0⟩,⟨.unit,1⟩]⟩ =
      some (-1/24) := by
  decide +kernel

/-- A nonzero stable-map descendant is not its stable-curve ancestor. -/
example : ancestorValue .plane (SurfaceAncestorKey.ofLabels 1 (Fin 1)
      (by norm_num [StableArity]) ![1] ![3] ![.hyperplane]) = 0 ∧
    queryValue? (X := .plane) ⟨1,![1],[⟨.hyperplane,3⟩]⟩ = some (1/8) := by
  decide +kernel

/-- The full effective class matters even when anticanonical energy agrees. -/
example : queryValue? (X := .blowupTwo) ⟨1,![1,0,0],[⟨.exceptional 0,1⟩]⟩ = some (1/12) ∧
    queryValue? (X := .blowupTwo) ⟨1,![0,1,0],[⟨.exceptional 0,1⟩]⟩ = some 0 := by
  decide +kernel

/-- Multiple covers can have nonintegral negative descendants. -/
example : queryValue? (X := .hirzebruchOne) ⟨1,![2,0],[⟨.exceptional 0,2⟩]⟩ =
    some (-1/16) := by decide +kernel

/-- Divisor stabilization accepts positive-degree empty markings. -/
example : queryValue? (X := .plane) ⟨1,![1],[]⟩ = some 0 ∧
    queryValue? (X := .blowupTwo) ⟨1,![0,0,1],[]⟩ = some 0 := by decide +kernel

/-- Auxiliary empty degree zero and an unsupported genus cannot masquerade as values. -/
example : queryValue? (X := .plane) ⟨1,0,[]⟩ = none ∧
    queryValue? (X := .plane) ⟨2,![1],[]⟩ = none := by decide +kernel

/-- Arbitrary-state expansion retains both exceptional coordinates. -/
example : stableStateValue .blowupTwo (Fin 1) (by norm_num [StableArity]) ![1,0,0] ![1]
    (fun _ ↦ (SurfaceBasisLabel.exceptional 0).value +
      (SurfaceBasisLabel.exceptional 1).value) = 1/12 := by decide +kernel

/-- An already sufficient recursion bound does not affect any elliptic answer. -/
example {X : SurfaceTarget} (q : SurfaceAncestorKey X) (hg : q.genus = 1) (extra : ℕ) :
    ancestorValueFuel X (q.totalPsi + extra) q = ancestorValue X q :=
  ancestorValueFuel_stable _ _ q hg (Nat.le_add_right _ _) le_rfl

/-- The public query theorem consumes all three actual exported presentations.
Only the named geometric inputs and the four finite seed families remain. -/
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
  {G : StableMapIntersection U} {St : StableMapStabilization G}
  (Tail : RationalTailIntersection G St P)
    (q : SurfaceQuery X) (hg : q.genus = 1) :
    queryValue? q = q.checkedEval U :=
  queryValue?_eq_checkedEval U P T laws H hpair Z F N J hWsource hboundary
    WDVVReplay.presentation WDVVReplay.accepted hGsource GG hcycle
    GetzlerReplay.presentation GetzlerReplay.accepted K hK
    GenusOnePsiReplay.presentation GenusOnePsiReplay.accepted hpsi hfund hrows hloop
    hzeroTerms honeTerms hline hEzero hH hE hWoutput hGoutput Tail q hg

end AxiomaticGWTest.Surfaces.GenusOneDescendants

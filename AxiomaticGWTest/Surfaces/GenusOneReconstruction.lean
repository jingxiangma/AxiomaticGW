/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.GenusOneReconstruction
import AxiomaticGWTest.Tautological.GetzlerReplay
import AxiomaticGWTest.Tautological.WDVVReplay

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusOneReconstruction

open AxiomaticGW SurfaceGenusOne SurfaceLowGenus

/-- The coefficient theorem has no fixed energy or marking bound. -/
example (X : SurfaceTarget) (beta : X.Curve) (he : 2 ≤ X.effective.energy beta) :
    RationalTerms.coefficient (reconstructionTerms X beta) {pointVariable X 1 beta} = -9 :=
  GetzlerGraphs.primaryTerms_reconstruction_coefficient X beta he

/-- The uniform family covers a full class at the benchmark's upper bound. -/
example : reconstructionCoefficient .blowupTwo ![3, 4, 5] = -9 :=
  reconstructionCoefficient_eq .blowupTwo ![3, 4, 5] (by decide +kernel)

/-- Another energy-twelve class retains its own original curve coordinates. -/
example : reconstructionCoefficient .hirzebruchOne ![2, 5] = -9 :=
  reconstructionCoefficient_eq .hirzebruchOne ![2, 5] (by decide +kernel)

/-- Equal energy cannot supply an elliptic variable from another full class. -/
example : RationalTerms.coefficient (reconstructionTerms .blowupTwo ![2, 0, 0])
    {pointVariable .blowupTwo 1 ![0, 2, 0]} = 0 :=
  (pointTerms_getzler .blowupTwo 0 ![2, 0, 0] _).coefficient_eq_zero_of_curve_ne _
    (by decide +kernel)

/-- The actual 2L equation has a nonzero genus-zero term at the original energy. -/
example : RationalTerms.coefficient (reconstructionTerms .blowupTwo ![0, 0, 2])
    {pointVariable .blowupTwo 0 ![0, 0, 2]} = -5 := by
  have h := SurfaceStrictLineGetzler.hyperplane_accepted
    {pointVariable .blowupTwo 0 ![0, 0, 2]}
    (Finset.mem_union_right _ (by decide +kernel))
  exact h.trans (by decide +kernel)

/-- Filtering the elliptic pivot retains a genus-zero singleton of the same class. -/
example : lowerTerms .blowupTwo ![0, 0, 2]
    (RationalTerms.term (-5) {pointVariable .blowupTwo 0 ![0, 0, 2]} +
      RationalTerms.term (-9) {pointVariable .blowupTwo 1 ![0, 0, 2]}) =
    RationalTerms.term (-5) {pointVariable .blowupTwo 0 ![0, 0, 2]} := by
  decide +kernel

/-- A graph of genus one cannot contain two elliptic component variables. -/
example : RationalTerms.coefficient (reconstructionTerms .blowupTwo ![1, 1, 0])
    ({pointVariable .blowupTwo 1 ![1, 0, 0], pointVariable .blowupTwo 1 ![0, 1, 0]}) = 0 :=
  (pointTerms_getzler .blowupTwo 0 ![1, 1, 0] _).coefficient_eq_zero_of_genus_lt _
    (by decide +kernel)

set_option maxRecDepth 65536 in
/-- Removing a required point marking destroys the pivot by dimension. -/
example : GetzlerGraphs.pointMarkedCoefficient .plane 0 ![1]
    (GetzlerGraphs.reconstructionLabels .plane) = 0 := by
  decide +kernel

set_option maxRecDepth 65536 in
/-- The class-zero request cannot be treated as a positive-class pivot. -/
example : GetzlerGraphs.pointMarkedCoefficient .plane 0 0
    (GetzlerGraphs.reconstructionLabels .plane) = 0 := by
  decide +kernel

/-- All three positive energy-one generators have the established initial value. -/
example : pointValue .blowupTwo ![1, 0, 0] = 0 ∧
    pointValue .blowupTwo ![0, 1, 0] = 0 ∧ pointValue .blowupTwo ![0, 0, 1] = 0 :=
  ⟨pointValue_initial _ _ (by decide +kernel),
    pointValue_initial _ _ (by decide +kernel), pointValue_initial _ _ (by decide +kernel)⟩

set_option maxHeartbeats 0 in
-- Direct kernel evaluation expands the full marked graph equation and recursive calls.
set_option maxRecDepth 65536 in
/-- The recursive branch evaluates the original marked plane-line equation. -/
example : pointValue .plane ![1] = 0 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Direct kernel evaluation expands all original class splits and signed contractions.
set_option maxRecDepth 65536 in
/-- Reconstruction also evaluates a noninitial full class on F₁. -/
example : pointValue .hirzebruchOne ![0, 1] = 0 := by
  decide +kernel

/-- Degree-zero elliptic divisors retain both signs and the distinct normalizations. -/
example : primaryValue .hirzebruchOne 0 {.hyperplane} = -1 / 8 ∧
    primaryValue .hirzebruchOne 0 {.exceptional 0} = -1 / 24 := by
  decide +kernel

/-- A value for the empty zero-class convention does not make it geometric. -/
example : pointValue .plane 0 = 0 ∧
    ¬(SurfaceQuery.points .plane 1 0 0).GeometricDomain := by
  constructor
  · exact pointValue_initial _ _ (by decide +kernel)
  · decide +kernel

/-- The actual Sage-exported presentations and the existing finite seed inventory
interpret every primary genus-one request, without an extra numerical oracle. -/
example {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S) (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hWsource : ∀ i, (WDVV.expression i).Compatible A F N)
    (hboundary : WDVV.BoundaryClassesEqual F)
    (hGsource : ∀ i, (GetzlerGraphs.expression i).Compatible A F N)
    (G : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (A 1 (Fin 4)).map (GetzlerGraphs.cycle x) = G.cycle x)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
    (S : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible Adiv) (hseeds : SurfaceSeed.SeedValues U)
    (hWoutput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible A F N)
    (hGoutput : ∀ n i z, z ∈ (GetzlerGraphs.expression i).addMarkings n → z.Compatible A F N)
    (beta : X.Curve) (m : Multiset (SurfaceBasisLabel X)) :
    primaryValue X beta m = SurfacePrimary.eval U 1 beta m :=
  primaryValue_eq_eval A I F N H hWsource hboundary WDVVReplay.presentation WDVVReplay.accepted
    hGsource G hcycle GetzlerReplay.presentation GetzlerReplay.accepted Omega P T U S Hdiv hpair
    (hseeds .line) (fun i ↦ hseeds (.exceptional i))
    (hseeds .genusOneHyperplane) (fun i ↦ hseeds (.genusOneExceptional i))
    hWoutput hGoutput beta m

end AxiomaticGWTest.Surfaces.GenusOneReconstruction

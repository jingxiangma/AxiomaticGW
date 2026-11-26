/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.GenusOneBenchmarks
import AxiomaticGWTest.Tautological.GetzlerReplay
import AxiomaticGWTest.Tautological.WDVVReplay

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusOneCertificate

open AxiomaticGW SurfaceGenusOne

/-- A published plane anchor is recovered by the original evaluator. -/
example : pointValue .plane ![3] = 1 ∧ pointValue .plane ![4] = 225 := by
  rw [← pointBenchmarkValues_eq .plane ![3] (by decide +kernel),
    ← pointBenchmarkValues_eq .plane ![4] (by decide +kernel)]
  decide +kernel

/-- The F₁ class (2,5) is 5H−3E, with twelve point insertions. -/
example : pointValue .hirzebruchOne ![2, 5] = 240 := by
  rw [← pointBenchmarkValues_eq .hirzebruchOne ![2, 5] (by decide +kernel)]
  decide +kernel

/-- Both exceptional multiplicities are retained in the published blowup anchor. -/
example : pointValue .blowupTwo ![2, 3, 5] = 20 := by
  rw [← pointBenchmarkValues_eq .blowupTwo ![2, 3, 5] (by decide +kernel)]
  decide +kernel

/-- Classes with equal energy can have different elliptic point invariants. -/
example : pointValue .blowupTwo ![3, 4, 5] = 13775 ∧
    pointValue .blowupTwo ![12, 0, 0] = 0 := by
  rw [← pointBenchmarkValues_eq .blowupTwo ![3, 4, 5] (by decide +kernel),
    ← pointBenchmarkValues_eq .blowupTwo ![12, 0, 0] (by decide +kernel)]
  decide +kernel

/-- Coverage cannot omit the auxiliary zero row, even though its answer vanishes. -/
example : checkEnumeratedValues .plane 0 [] (fun _ ↦ 0) (fun _ ↦ 0) = false := by
  decide +kernel

/-- Coverage cannot replace a complete list by a larger energy bound. -/
example : checkEnumeratedValues .plane 0 [![0], ![1]]
    (fun _ ↦ 0) (fun _ ↦ 0) = false := by decide +kernel

/-- The rational input is itself checked; matching elliptic zeros do not excuse a wrong seed. -/
example : checkBoundedValues .plane 3
    (fun beta ↦ if beta = ![1] then 2 else 0) (fun _ ↦ 0) = false := by
  decide +kernel

/-- The elliptic initial sector cannot be altered by candidate data. -/
example : checkValue .blowupTwo GenusZeroBl2Table.values
    (fun _ ↦ 1) ![0, 0, 1] = false := by decide +kernel

/-- The leading elliptic candidate is removed before replay of a noninitial equation. -/
example : checkValue .plane GenusZeroPlaneTable.values
    (fun beta ↦ if beta = ![1] then 1 else 0) ![1] = false := by
  decide +kernel

/-- A rational dependency at the original energy must survive the elliptic guard. -/
example : scalarReconstructionStep .blowupTwo ![0, 0, 2]
    (fun beta ↦ if beta = ![0, 0, 2] then 1 else 0) (fun _ ↦ 0) = -5 / 9 := by
  decide +kernel

/-- Candidate zeros preserve the classical signed exceptional pairing. -/
example : primaryScalar .hirzebruchOne (fun _ ↦ 0) (fun _ ↦ 0) 0 0 0
    (![.unit, .exceptional 0, .exceptional 0] : Fin 3 → SurfaceBasisLabel .hirzebruchOne) = -1 := by
  decide +kernel

/-- The elliptic degree-zero divisor constants are not candidate table entries. -/
example : primaryScalar .hirzebruchOne (fun _ ↦ 0) (fun _ ↦ 0) 1 0 0
    (![.hyperplane] : Fin 1 → SurfaceBasisLabel .hirzebruchOne) = -1 / 8 ∧
    primaryScalar .hirzebruchOne (fun _ ↦ 0) (fun _ ↦ 0) 1 0 0
    (![.exceptional 0] : Fin 1 → SurfaceBasisLabel .hirzebruchOne) = -1 / 24 := by
  decide +kernel

/-- Adding a point to a constant elliptic divisor query gives zero by dimension. -/
example : primaryScalar .plane (fun _ ↦ 0) (fun _ ↦ 0) 1 0 1
    (![.hyperplane] : Fin 1 → SurfaceBasisLabel .plane) = 0 := by decide +kernel

/-- Negative required point counts are not silently truncated into allowed zero counts. -/
example : requiredPoints .plane GetzlerGraphs.delta22Expression 0
    (GetzlerGraphs.reconstructionLabels .plane) = -2 ∧
    dimensionPrunedEval .plane (fun _ ↦ 1) (fun _ ↦ 1)
      GetzlerGraphs.delta22Expression (by decide +kernel) 0 0
      (GetzlerGraphs.reconstructionLabels .plane) = 0 := by
  decide +kernel

/-- A parallel-edge graph counts both nodes when checking the required points. -/
example : requiredPoints .plane GetzlerGraphs.deltaBetaExpression ![1]
    (GetzlerGraphs.reconstructionLabels .plane) = 1 ∧
    dimensionPrunedEval .plane (fun _ ↦ 1) (fun _ ↦ 1)
      GetzlerGraphs.deltaBetaExpression (by decide +kernel) ![1] 0
      (GetzlerGraphs.reconstructionLabels .plane) = 0 := by
  decide +kernel

/-- A held claim rejects a value belonging to another class of the same energy. -/
example : checkPointClaim .blowupTwo 12 GenusZeroBl2Table.values
    GenusOneBl2Table.values ![12, 0, 0] 13775 = false := by decide +kernel

/-- A changed claimed value cannot reuse an accepted table. -/
example : checkPointClaim .plane 12 GenusZeroPlaneTable.values
    GenusOnePlaneTable.values ![4] 226 = false := by decide +kernel

/-- A smaller held bound cannot silently inherit a larger table's answers. -/
example : checkPointClaim .plane 9 GenusZeroPlaneTable.values
    GenusOnePlaneTable.values ![4] 225 = false := by decide +kernel

/-- The geometric lookup excludes the auxiliary empty request and unverified energies. -/
example : pointBenchmark? .plane 0 = none ∧ pointBenchmark? .plane ![5] = none := by
  decide +kernel

/-- Even correct degree-zero auxiliary data do not certify a geometric point query. -/
example : checkPointClaim .plane 12 GenusZeroPlaneTable.values
    GenusOnePlaneTable.values 0 0 = false := by decide +kernel

/-- The actual Sage-exported presentations interpret every covered positive-class
elliptic value under the original geometric inputs and unchanged finite seeds. -/
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
    (beta : X.Curve) (hbeta : beta ≠ 0) (hbound : X.effective.energy beta ≤ 12) :
    (SurfaceQuery.points X 1 beta (X.effective.energy beta)).checkedEval U =
      some (pointBenchmarkValues X beta) :=
  pointBenchmark_checkedEval A I F N H hWsource hboundary
    WDVVReplay.presentation WDVVReplay.accepted
    hGsource G hcycle GetzlerReplay.presentation GetzlerReplay.accepted Omega P T U S Hdiv hpair
    (hseeds .line) (fun i ↦ hseeds (.exceptional i))
    (hseeds .genusOneHyperplane) (fun i ↦ hseeds (.genusOneExceptional i))
    hWoutput hGoutput beta hbeta hbound

end AxiomaticGWTest.Surfaces.GenusOneCertificate

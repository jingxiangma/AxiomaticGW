/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.GenusZeroBenchmarks
import AxiomaticGWTest.Tautological.WDVVReplay

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusZeroCertificate

open AxiomaticGW SurfaceGenusZero

/-- An already replayed table discharges later held claims without rechecking every row. -/
private theorem quartic_claim : checkPointClaim .plane 12 GenusZeroPlaneTable.values ![4] 620 =
    true := by
  rw [checkPointClaim, GenusZeroPlaneTable.accepted, Bool.and_true]
  decide +kernel

/-- A positive exceptional class remains geometric even with no markings. -/
example : checkPointClaim .hirzebruchOne 1
    (fun beta ↦ if beta = ![1, 0] then 1 else 0) ![1, 0] 1 = true := by
  decide +kernel

/-- Coverage rejects omission of even an auxiliary zero-valued class. -/
example : checkEnumeratedValues .plane 3 [![1]] GenusZeroPlaneTable.values = false := by
  decide +kernel

/-- A class beyond the held bound cannot be hidden in the explicit request list. -/
example : checkEnumeratedValues .plane 3 [![0], ![1], ![2]]
    GenusZeroPlaneTable.values = false := by decide +kernel

/-- A changed seed cannot be smuggled in as an intermediate value. -/
example : checkBoundedValues .plane 3
    (fun beta ↦ if beta = ![1] then 2 else GenusZeroPlaneTable.values beta) = false := by
  decide +kernel

/-- The leading value is checked against lower classes, not against itself. -/
example : checkValue .plane
    (fun beta ↦ if beta = ![4] then 621 else GenusZeroPlaneTable.values beta) ![4] = false := by
  decide +kernel

/-- An omitted nonzero row fails its original compact equation. -/
example : checkValue .plane
    (fun beta ↦ if beta = ![3] then 0 else GenusZeroPlaneTable.values beta) ![3] = false := by
  decide +kernel

/-- Auxiliary zero-class values must also satisfy their stated convention. -/
example : checkBoundedValues .plane 0 (fun _ ↦ 1) = false := by decide +kernel

/-- The same accepted table cannot certify a different claimed answer. -/
example : checkPointClaim .plane 12 GenusZeroPlaneTable.values ![4] 621 = false := by
  decide +kernel

/-- A smaller held bound cannot silently inherit the larger table's claims. -/
example : checkPointClaim .plane 9 GenusZeroPlaneTable.values ![4] 620 = false := by
  decide +kernel

/-- Correct auxiliary data do not make the empty zero-class request geometric. -/
example : checkPointClaim .plane 12 GenusZeroPlaneTable.values 0 0 = false := by
  decide +kernel

/-- The F₁ class (2,5) is 5H−3E and has eleven point insertions. -/
example : pointValue .hirzebruchOne ![2, 5] = 640 := by
  rw [← pointBenchmarkValues_eq .hirzebruchOne ![2, 5] (by decide +kernel)]
  decide +kernel

/-- The two-point blowup retains both exceptional multiplicities in 5H−2E₁−E₂. -/
example : pointValue .blowupTwo ![3, 4, 5] = 18132 := by
  rw [← pointBenchmarkValues_eq .blowupTwo ![3, 4, 5] (by decide +kernel)]
  decide +kernel

/-- Equal anticanonical energy does not identify the underlying invariants. -/
example : pointValue .blowupTwo ![3, 3, 3] = 12 ∧
    pointValue .blowupTwo ![9, 0, 0] = 0 := by
  rw [← pointBenchmarkValues_eq .blowupTwo ![3, 3, 3] (by decide +kernel),
    ← pointBenchmarkValues_eq .blowupTwo ![9, 0, 0] (by decide +kernel)]
  decide +kernel

/-- A correct number for another same-energy class cannot certify this held request. -/
example : checkPointClaim .blowupTwo 12 GenusZeroBl2Table.values ![9, 0, 0] 12 = false := by
  decide +kernel

/-- The public lookup does not present unsupported or auxiliary values as geometric answers. -/
example : pointBenchmark? .plane 0 = none ∧ pointBenchmark? .plane ![5] = none := by
  decide +kernel

/-- Candidate zeros never suppress the classical negative exceptional pairing. -/
example : primaryScalar .hirzebruchOne (fun _ ↦ 0) 0 0
    (![.unit, .exceptional 0, .exceptional 0] : Fin 3 → SurfaceBasisLabel .hirzebruchOne) = -1 := by
  decide +kernel

/-- A valid finite claim yields the original invariant through the checked-query API. -/
example {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S) (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (WDVV.expression i).Compatible A F N)
    (hboundary : WDVV.BoundaryClassesEqual F)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology SurfaceTarget.plane.blowups)
      SurfaceTarget.plane.Curve SurfaceTarget.plane.effective C)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification .plane Omega)
    {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
    (S : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible Adiv)
    (hline : (SurfaceSeed.line : SurfaceSeed .plane).query.eval U = 1)
    (houtput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible A F N) :
    (SurfaceQuery.points .plane 0 ![4] 11).checkedEval U = some 620 :=
  checkPointClaim_checkedEval A I F N H hsource hboundary
    WDVVReplay.presentation WDVVReplay.accepted Omega P T U S Hdiv hpair
    hline (fun i ↦ Fin.elim0 i) houtput 12 GenusZeroPlaneTable.values ![4] 620 quartic_claim

/-- The actual Sage-exported relation and existing geometric inputs interpret a blowup benchmark. -/
example {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S) (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (WDVV.expression i).Compatible A F N)
    (hboundary : WDVV.BoundaryClassesEqual F)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology SurfaceTarget.blowupTwo.blowups)
      SurfaceTarget.blowupTwo.Curve SurfaceTarget.blowupTwo.effective C)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification .blowupTwo Omega)
    {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
    (S : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible Adiv)
    (hline : (SurfaceSeed.line : SurfaceSeed .blowupTwo).query.eval U = 1)
    (hE : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed .blowupTwo).query.eval U = 1)
    (houtput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible A F N) :
    (SurfaceQuery.points .blowupTwo 0 ![3, 4, 5] 11).checkedEval U = some 18132 :=
  pointBenchmark_checkedEval A I F N H hsource hboundary
    WDVVReplay.presentation WDVVReplay.accepted Omega P T U S Hdiv hpair
    hline hE houtput ![3, 4, 5] (by decide +kernel) (by decide +kernel)

end AxiomaticGWTest.Surfaces.GenusZeroCertificate

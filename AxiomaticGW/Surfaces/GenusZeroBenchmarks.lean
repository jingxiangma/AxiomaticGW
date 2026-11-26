/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.GenusZeroPlaneTable
public import AxiomaticGW.Surfaces.Fixtures.GenusZeroF1Table
public import AxiomaticGW.Surfaces.Fixtures.GenusZeroBl2Table

/-!
# The fixed genus-zero point benchmarks through energy twelve

Every full effective class in the bound is covered, including zero answers.
The three zero-class empty requests retain their auxiliary value and are
excluded from the geometric checked-query theorem. Interpretation uses the
existing original WDVV certificate, geometric laws and finite genus-zero seeds.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusZero

/-- Exact saved values for the three fixed targets; only energy at most twelve is certified. -/
def pointBenchmarkValues : (X : SurfaceTarget) → X.Curve → ℚ
  | .plane => GenusZeroPlaneTable.values
  | .hirzebruchOne => GenusZeroF1Table.values
  | .blowupTwo => GenusZeroBl2Table.values

/-- Every initial value and every selected WDVV equation in the fixed bound is checked. -/
theorem pointBenchmarkValues_checked (X : SurfaceTarget) :
    checkBoundedValues X 12 (pointBenchmarkValues X) = true := by
  cases X
  · exact GenusZeroPlaneTable.accepted
  · exact GenusZeroF1Table.accepted
  · exact GenusZeroBl2Table.accepted

/-- The finite candidates equal the original well-founded evaluator throughout the bound. -/
theorem pointBenchmarkValues_eq (X : SurfaceTarget) (beta : X.Curve)
    (hbound : X.effective.energy beta ≤ 12) :
    pointBenchmarkValues X beta = pointValue X beta :=
  checkBoundedValues_sound X 12 (pointBenchmarkValues X) (pointBenchmarkValues_checked X)
    beta hbound

/-- A bounded lookup returns no answer for an auxiliary zero-class or unsupported request. -/
def pointBenchmark? (X : SurfaceTarget) (beta : X.Curve) : Option ℚ :=
  if beta ≠ 0 ∧ X.effective.energy beta ≤ 12 then some (pointBenchmarkValues X beta) else none

/-- Every returned answer is bound to its positive full class and the proved evaluator. -/
theorem pointBenchmark?_sound (X : SurfaceTarget) (beta : X.Curve) (claimed : ℚ)
    (h : pointBenchmark? X beta = some claimed) :
    beta ≠ 0 ∧ X.effective.energy beta ≤ 12 ∧ pointValue X beta = claimed := by
  unfold pointBenchmark? at h
  split_ifs at h with hb
  exact ⟨hb.1, hb.2, (pointBenchmarkValues_eq X beta hb.2).symm.trans (Option.some.inj h)⟩

/-- A covered positive-class benchmark is an actual checked query under the
named geometric inputs. -/
theorem pointBenchmark_checkedEval
    {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (WDVV.expression i).Compatible A F N)
    (hboundary : WDVV.BoundaryClassesEqual F)
    (p : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hp : WDVV.AcceptsExchange p)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
    (S : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible Adiv)
    (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
    (hE : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
    (houtput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible A F N)
    (beta : X.Curve) (hbeta : beta ≠ 0) (hbound : X.effective.energy beta ≤ 12) :
    (SurfaceQuery.points X 0 beta (X.effective.energy beta - 1)).checkedEval U =
      some (pointBenchmarkValues X beta) := by
  apply checkPointClaim_checkedEval A I F N H hsource hboundary p hp Omega P T U S Hdiv hpair
    hline hE houtput 12 (pointBenchmarkValues X) beta (pointBenchmarkValues X beta)
  rw [checkPointClaim, pointBenchmarkValues_checked, Bool.and_true, decide_eq_true_eq]
  exact ⟨hbeta, hbound, rfl⟩

end AxiomaticGW.SurfaceGenusZero

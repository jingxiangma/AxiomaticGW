/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.GenusOnePlaneTable
public import AxiomaticGW.Surfaces.Fixtures.GenusOneF1Table
public import AxiomaticGW.Surfaces.Fixtures.GenusOneBl2Table
public import AxiomaticGW.Surfaces.GenusZeroBenchmarks

/-!
# The fixed genus-one point benchmarks through energy twelve

Both genera are checked throughout the complete full-class bound. The three
zero-class empty requests are auxiliary and excluded from the geometric
lookup. Numerical interpretation retains the original WDVV/Getzler
presentations, named geometric laws and unchanged finite seed inventory.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusOne

/-- Exact saved elliptic values; only energy at most twelve is certified. -/
def pointBenchmarkValues : (X : SurfaceTarget) → X.Curve → ℚ
  | .plane => GenusOnePlaneTable.values
  | .hirzebruchOne => GenusOneF1Table.values
  | .blowupTwo => GenusOneBl2Table.values

/-- Every initial value and selected equation in both genera is checked. -/
theorem pointBenchmarkValues_checked (X : SurfaceTarget) :
    checkBoundedValues X 12 (SurfaceGenusZero.pointBenchmarkValues X)
      (pointBenchmarkValues X) = true := by
  cases X
  · exact GenusOnePlaneTable.accepted
  · exact GenusOneF1Table.accepted
  · exact GenusOneBl2Table.accepted

/-- Every covered candidate equals the original well-founded elliptic evaluator. -/
theorem pointBenchmarkValues_eq (X : SurfaceTarget) (beta : X.Curve)
    (hbound : X.effective.energy beta ≤ 12) :
    pointBenchmarkValues X beta = pointValue X beta :=
  checkBoundedValues_sound X 12 (SurfaceGenusZero.pointBenchmarkValues X)
    (pointBenchmarkValues X) (pointBenchmarkValues_checked X) beta hbound

/-- Return no answer for an auxiliary zero-class or unsupported request. -/
def pointBenchmark? (X : SurfaceTarget) (beta : X.Curve) : Option ℚ :=
  if beta ≠ 0 ∧ X.effective.energy beta ≤ 12 then some (pointBenchmarkValues X beta) else none

/-- Every returned answer is bound to its positive full class and the proved evaluator. -/
theorem pointBenchmark?_sound (X : SurfaceTarget) (beta : X.Curve) (claimed : ℚ)
    (h : pointBenchmark? X beta = some claimed) :
    beta ≠ 0 ∧ X.effective.energy beta ≤ 12 ∧ pointValue X beta = claimed := by
  unfold pointBenchmark? at h
  split_ifs at h with hb
  exact ⟨hb.1, hb.2, (pointBenchmarkValues_eq X beta hb.2).symm.trans (Option.some.inj h)⟩

/-- A covered positive-class benchmark is a checked query under the original geometric inputs. -/
theorem pointBenchmark_checkedEval
    {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hWsource : ∀ i, (WDVV.expression i).Compatible A F N)
    (hboundary : WDVV.BoundaryClassesEqual F)
    (pW : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hpW : WDVV.AcceptsExchange pW)
    (hGsource : ∀ i, (GetzlerGraphs.expression i).Compatible A F N)
    (G : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (A 1 (Fin 4)).map (GetzlerGraphs.cycle x) = G.cycle x)
    (pG : RelationCertificate.Presentation 1 (Fin 4) 1 33)
    (hpG : GetzlerGraphs.AcceptsExchange pG)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
    (S : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible Adiv)
    (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
    (hEzero : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
    (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed X).query.eval U = -1 / 8)
    (hE : ∀ i, (SurfaceSeed.genusOneExceptional i : SurfaceSeed X).query.eval U = -1 / 24)
    (hWoutput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible A F N)
    (hGoutput : ∀ n i z, z ∈ (GetzlerGraphs.expression i).addMarkings n → z.Compatible A F N)
    (beta : X.Curve) (hbeta : beta ≠ 0) (hbound : X.effective.energy beta ≤ 12) :
    (SurfaceQuery.points X 1 beta (X.effective.energy beta)).checkedEval U =
      some (pointBenchmarkValues X beta) := by
  apply checkPointClaim_checkedEval A I F N H hWsource hboundary pW hpW hGsource G hcycle pG hpG
    Omega P T U S Hdiv hpair hline hEzero hH hE hWoutput hGoutput 12
    (SurfaceGenusZero.pointBenchmarkValues X) (pointBenchmarkValues X) beta
    (pointBenchmarkValues X beta)
  rw [checkPointClaim, pointBenchmarkValues_checked, Bool.and_true, decide_eq_true_eq]
  exact ⟨hbeta, hbound, rfl⟩

end AxiomaticGW.SurfaceGenusOne

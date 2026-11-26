/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.GenusZeroReconstruction
import AxiomaticGW.Surfaces.GenusZeroTable
import AxiomaticGWTest.Tautological.WDVVReplay

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusZeroReconstruction

open AxiomaticGW SurfaceGenusZero

/-- The auxiliary zero-point value is kept separate from the classical cubic. -/
example : pointValue .plane 0 = 0 ∧
    primaryValue .plane 0 {.unit, .hyperplane, .hyperplane} = 1 := by decide +kernel

/-- The original line seed remains an initial value on each target. -/
example : pointValue .plane SurfaceTarget.plane.lineCurve = 1 ∧
    pointValue .hirzebruchOne SurfaceTarget.hirzebruchOne.lineCurve = 1 ∧
    pointValue .blowupTwo SurfaceTarget.blowupTwo.lineCurve = 1 := by decide +kernel

/-- The conic is computed by the recursion, not inserted into its initial table. -/
example : ¬IsInitial .plane ![2] ∧ pointValue .plane ![2] = 1 := by decide +kernel

/-- A new numerical deduction from the proved WDVV recursion. -/
private theorem cubic_computation : pointValue .plane ![3] = 12 := by decide +kernel

/-- F₁ retains its unmarked exceptional seed and derived one-point ruling. -/
example : pointValue .hirzebruchOne ![1, 0] = 1 ∧
    pointValue .hirzebruchOne ![0, 1] = 1 := by decide +kernel

/-- Double and triple exceptional classes follow different branches and both vanish. -/
example : pointValue .hirzebruchOne ![2, 0] = 0 ∧
    pointValue .hirzebruchOne ![3, 0] = 0 := by decide +kernel

/-- A multiple ruling and a class with an extra exceptional component vanish. -/
example : pointValue .hirzebruchOne ![0, 2] = 0 ∧
    pointValue .hirzebruchOne ![2, 1] = 0 := by decide +kernel

/-- Full coordinates distinguish a conic from equal-energy multiple exceptional classes. -/
example : pointValue .hirzebruchOne ![2, 2] = 1 ∧
    pointValue .hirzebruchOne ![6, 0] = 0 := by decide +kernel

/-- The strict line and both distinct rulings have the derived initial value one. -/
example : pointValue .blowupTwo ![0, 0, 1] = 1 ∧
    pointValue .blowupTwo ![1, 0, 1] = 1 ∧
    pointValue .blowupTwo ![0, 1, 1] = 1 := by decide +kernel

/-- Every double-generator and the disjoint exceptional sum vanish. -/
example : pointValue .blowupTwo ![2, 0, 0] = 0 ∧
    pointValue .blowupTwo ![0, 2, 0] = 0 ∧
    pointValue .blowupTwo ![0, 0, 2] = 0 ∧
    pointValue .blowupTwo ![1, 1, 0] = 0 := by decide +kernel

/-- The energy-three exceptional-coordinate and strict-line branches are executable. -/
example : pointValue .blowupTwo ![0, 3, 0] = 0 ∧
    pointValue .blowupTwo ![0, 0, 3] = 0 := by decide +kernel

/-- Equal energy alone cannot replace the full class of the requested invariant. -/
example : pointValue .blowupTwo ![1, 1, 2] = 1 ∧
    pointValue .blowupTwo ![2, 0, 2] = 0 := by decide +kernel

/-- A wrong number of points is rejected by the primary dimension reduction. -/
example : primaryValue .plane ![1] {.point} = 0 := by decide +kernel

/-- A positive-class primary unit insertion vanishes even at the expected point count. -/
example : primaryValue .plane ![1] {.unit, .point, .point} = 0 := by decide +kernel

/-- Divisor factors retain their degree and exceptional self-intersection sign. -/
example : primaryValue .plane ![2] (.hyperplane ::ₘ Multiset.replicate 5 .point) = 2 ∧
    primaryValue .hirzebruchOne ![1, 0] {.exceptional 0} = -1 := by decide +kernel

/-- Leading coefficients retain the uniform unit value and the energy-three sign. -/
example : reconstructionCoefficient .blowupTwo ![0, 3, 0] = -3 ∧
    reconstructionCoefficient .hirzebruchOne ![4, 0] = 1 := by decide +kernel

/-- A table can answer any class inside its bound and preserves full coordinates. -/
example : tableLookup (pointTable .blowupTwo 4) ![1, 1, 2] = 1 ∧
    tableLookup (pointTable .blowupTwo 4) ![2, 0, 2] = 0 := by decide +kernel

/-- The cached primary interface retains exceptional signs and degree-zero normalization. -/
example : cachedPrimaryValue .hirzebruchOne ![1, 0] {.exceptional 0} = -1 ∧
    cachedPrimaryValue .plane 0 {.unit, .hyperplane, .hyperplane} = 1 := by decide +kernel

/-- The table equality theorem certifies the point computation at any larger bound. -/
example : tableLookup (pointTable .plane 9) ![3] = 12 := by
  rw [tableLookup_pointTable .plane 9 ![3] (by decide +kernel), cubic_computation]

/-- Public soundness turns the cubic computation into an actual invariant value.
Only the plane line seed and original WDVV certificate are supplied. -/
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
    (SurfaceQuery.points .plane 0 ![3] 8).eval U = 12 := by
  have h := pointValue_eq_eval A I F N H hsource hboundary
    WDVVReplay.presentation WDVVReplay.accepted Omega P T U S Hdiv hpair
    hline (fun i ↦ Fin.elim0 i) houtput ![3]
  rw [cubic_computation] at h
  exact h.symm

end AxiomaticGWTest.Surfaces.GenusZeroReconstruction

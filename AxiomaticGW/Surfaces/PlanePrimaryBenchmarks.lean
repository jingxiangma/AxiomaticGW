/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroReconstruction
public import AxiomaticGW.Surfaces.Fixtures.PlaneQuartic

/-!
# Primary genus-zero plane benchmarks through energy twelve

The expected values 1, 1, 12, 620 are independently recorded in Kontsevich--Manin,
section 5.2. The frozen query/source manifest is
`environments/plane-primary-genus-zero-benchmarks.json`.
Kernel computation proves agreement with the reconstructed values. The geometric
consumer retains the original relation and compatibility hypotheses and only the
line seed; no conic, cubic, or quartic value is supplied as an assumption.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusZero

/-- The four requests exhaust the positive plane classes in the required energy bound. -/
theorem plane_primary_benchmark_coverage (beta : SurfaceTarget.plane.Curve)
    (hbeta : beta ≠ 0) (henergy : SurfaceTarget.plane.effective.energy beta ≤ 12) :
    ∃ d : Fin 4, beta = ![d.val + 1] := by
  have hchecked : ∀ b ∈ SurfaceTarget.plane.bounded 12,
      b ≠ 0 → ∃ d : Fin 4, b = ![d.val + 1] := by decide +kernel
  apply hchecked beta _ hbeta
  rw [SurfaceTarget.bounded_eq, SurfaceTarget.plane.effective.mem_bounded]
  exact henergy

/-- Every positive plane class through anticanonical energy twelve. -/
theorem plane_primary_values (d : Fin 4) :
    cachedPointValue .plane ![d.val + 1] = (![1, 1, 12, 620] : Fin 4 → ℚ) d := by
  fin_cases d <;> decide +kernel

/-- The fixed numerical suite computes the supplied theory's actual point invariants. -/
theorem plane_primary_benchmark_eq_eval {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S) (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (WDVV.expression i).Compatible A F N)
    (hboundary : WDVV.BoundaryClassesEqual F)
    (p : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hp : WDVV.AcceptsExchange p)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology SurfaceTarget.plane.blowups)
      SurfaceTarget.plane.Curve SurfaceTarget.plane.effective C)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification .plane Omega)
    {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
    (S : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible Adiv)
    (hline : (SurfaceSeed.line : SurfaceSeed .plane).query.eval U = 1)
    (houtput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible A F N)
    (d : Fin 4) :
    (SurfaceQuery.points .plane 0 ![d.val + 1] (3 * (d.val + 1) - 1)).eval U =
      (![1, 1, 12, 620] : Fin 4 → ℚ) d := by
  have h := cachedPointValue_eq_eval A I F N H hsource hboundary p hp
    Omega P T U S Hdiv hpair hline (fun i ↦ Fin.elim0 i) houtput ![d.val + 1]
  rw [plane_primary_values d] at h
  have he : SurfaceTarget.plane.effective.energy ![d.val + 1] = 3 * (d.val + 1) := by
    fin_cases d <;> decide +kernel
  simpa only [he] using h.symm

end AxiomaticGW.SurfaceGenusZero

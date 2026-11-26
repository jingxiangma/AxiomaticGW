/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.WDVV
public import Mathlib.Tactic.Linarith

/-!
# The plane conic invariant from WDVV with two additional markings

The four original states are H,H,pt,pt and both added states are points.
The full class is 2H. Exact graph expansion gives N₀(2H;5)−N₀(H;2)²=0,
so the existing line seed implies the five-point conic value is one.
-/

@[expose] public section

namespace AxiomaticGW.SurfacePlaneGenusZero

open SurfacePolynomialReduction

/-- Both ordered additional markings are retained as point insertions. -/
def conicLabels : ExtraMarkings 2 (Fin 4) → SurfaceBasisLabel .plane :=
  fun s ↦ Option.elim s .point
    (fun t ↦ Option.elim t .point ![.hyperplane, .hyperplane, .point, .point])

/-- The candidate keeps the repeated line variable as a square. -/
def conicTerms : RationalTerms (Variable .plane) :=
  RationalTerms.term 1 {.inr (SurfaceQuery.points .plane 0 ![2] 5)} +
  RationalTerms.term (-1)
    (↑([.inr (SurfaceQuery.points .plane 0 ![1] 2),
      .inr (SurfaceQuery.points .plane 0 ![1] 2)] : List (Variable .plane)) :
      Multiset (Variable .plane))

/-- The complete expansion includes all placements of the two extra markings. -/
theorem conic_accepted : RationalTerms.Equivalent
    (WDVV.primaryTerms .plane 2 ![2] 0 conicLabels) conicTerms := by
  decide +kernel

/-- The genus-zero plane conic through five points is determined by the line seed. -/
theorem conic {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (I : StableCurveIntegration C)
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
    (houtput : ∀ i z, z ∈ (WDVV.expression i).addMarkings 2 → z.Compatible A F N)
    (p : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hp : WDVV.AcceptsExchange p) :
    (SurfaceQuery.points .plane 0 ![2] 5).eval U = 1 := by
  have h := WDVV.exchange_checkedPrimaryTerms_eq_zero A I F N H hsource hboundary
    Omega P T U S Hdiv hpair 2 houtput ![2] 0 conicLabels conicTerms conic_accepted p hp
  change (SurfaceQuery.points .plane 0 SurfaceTarget.plane.lineCurve 2).eval U = 1 at hline
  rw [show SurfaceTarget.plane.lineCurve = ![1] from by decide +kernel] at hline
  simp only [conicTerms, RationalTerms.eval_add, RationalTerms.eval_term,
    Multiset.map_coe, Multiset.prod_coe, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, Multiset.map_singleton, Multiset.prod_singleton,
    Algebra.algebraMap_self_apply, variableEval, hline, one_mul, mul_one] at h
  linarith

end AxiomaticGW.SurfacePlaneGenusZero

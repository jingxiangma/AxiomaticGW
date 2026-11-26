/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.DegreeZeroPolynomial
import AxiomaticGWTest.Tautological.GetzlerReplay

/-!
# Degree-zero primary reduction regressions

Finite value checks and generic consumers retain signs, exceptional values,
unbounded multiplicities, and the distinction between ancestors and descendants.
-/

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.DegreeZero

open AxiomaticGW SurfacePolynomialReduction

/-- The classical metric gives both ordered extreme-degree pairings. -/
example : SurfacePrimary.classicalValue (X := .plane) {.unit, .unit, .point} = 1 ∧
    SurfacePrimary.classicalValue (X := .plane) {.unit, .hyperplane, .hyperplane} = 1 :=
  by decide +kernel

/-- Exceptional self-intersections are negative; distinct exceptions pair to zero. -/
example : SurfacePrimary.classicalValue (X := .blowupTwo) {.unit, .exceptional 0,
      .exceptional 0} = -1 ∧
    SurfacePrimary.classicalValue (X := .blowupTwo) {.unit, .exceptional 0,
      .exceptional 1} = 0 := by decide +kernel

/-- Extra primary units do not create nonzero higher-arity classical invariants. -/
example : SurfacePrimary.classicalValue (X := .plane)
    {.unit, .unit, .hyperplane, .hyperplane, .point} = 0 := by decide +kernel

/-- The finite elliptic divisor seeds retain their distinct negative values. -/
example : SurfacePrimary.genusOneZeroValue (X := .hirzebruchOne) {.hyperplane} = -1 / 8 ∧
    SurfacePrimary.genusOneZeroValue (X := .hirzebruchOne) {.exceptional 0} = -1 / 24 :=
  by decide +kernel

/-- Primary elliptic divisors cannot be repeated at degree zero. -/
example : SurfacePrimary.genusOneZeroValue (X := .blowupTwo)
    {.hyperplane, .exceptional 0, .exceptional 1} = 0 := by decide +kernel

/-- Nonzero powers retain their ancestor semantics. -/
example : degreeZeroValue? (.inl (SurfaceAncestorKey.ofLabels (X := .plane) 1 (Fin 1)
    (by norm_num [StableArity]) 0 (fun _ ↦ 1) (fun _ ↦ .unit))) = none := by decide +kernel

/-- A proved zero is distinguished from an inapplicable reduction rule. -/
example : degreeZeroValue? (.inl (SurfaceAncestorKey.ofLabels (X := .plane) 1 (Fin 1)
    (by norm_num [StableArity]) 0 0 (fun _ ↦ .unit))) = some 0 := by decide +kernel

/-- Positive-class primaries are not assigned the degree-zero formula. -/
example : degreeZeroValue? (.inl (SurfaceAncestorKey.ofLabels (X := .plane) 1 (Fin 3)
    (by norm_num [StableArity]) (fun _ ↦ 1) 0 (fun _ ↦ .point))) = none := by decide +kernel

/-- The genus-two sector is not assigned a genus-one formula. -/
example : degreeZeroValue? (.inl (SurfaceAncestorKey.ofLabels (X := .plane) 2 (Fin 1)
    (by norm_num [StableArity]) 0 0 (fun _ ↦ .point))) = none := by decide +kernel

/-- Numerical query variables keep their own interpretation. -/
example : degreeZeroValue? (.inr (SurfaceQuery.points .plane 0 0 0)) = none := by decide +kernel

/-- Arbitrary multiplicities, not a bounded table, are covered by the zero-class proof. -/
example {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (T : SurfaceTheoryIdentification X Omega)
    (S : DescendantStringDilatonLaws M I) (n : ℕ) (b : SurfaceBasisLabel X) :
    SurfacePrimary.eval U 0 0 (Multiset.replicate (n + 4) b) = 0 := by
  rw [SurfacePrimary.eval_genus_zero_zero U T S]
  have hn : n + 4 ≠ 3 := by omega
  simp only [SurfacePrimary.classicalValue, Multiset.card_replicate, if_neg hn]

/-- The actual checked replay consumes only the existing finite seed package. -/
example {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (GetzlerGraphs.expression i).Compatible A F N)
    (G : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (A 1 (Fin 4)).map (GetzlerGraphs.cycle x) = G.cycle x)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
    (S : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible Adiv) (hseeds : SurfaceSeed.SeedValues U)
    (n : ℕ)
    (houtput : ∀ i z, z ∈ (GetzlerGraphs.expression i).addMarkings n → z.Compatible A F N)
    (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    MvPolynomial.aeval (variableEval U P)
      (reduceDegreeZero X (reduce X (GetzlerGraphs.surfacePolynomial n beta k a))) = 0 :=
  GetzlerGraphs.exchange_primarySurfacePolynomial_eq_zero A I F N H hsource G hcycle Omega P
    T U S Hdiv hpair (hseeds .genusOneHyperplane) (fun i ↦ hseeds (.genusOneExceptional i))
    n houtput beta k a GetzlerReplay.presentation GetzlerReplay.accepted

end AxiomaticGWTest.Surfaces.DegreeZero

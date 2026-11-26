/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.PolynomialReduction
import AxiomaticGWTest.Tautological.GetzlerReplay

/-!
# Surface primary and polynomial reduction regressions

The data tests use kernel reduction, including signed exceptional coefficients,
full curve coordinates, degree-zero exceptions, and unstable residual arities.
The final theorem consumes the unchanged actual Getzler replay.
-/

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.PolynomialReduction

open AxiomaticGW
open SurfacePolynomialReduction

/-- Three hyperplanes are removed while both point insertions survive. -/
example : reduceVariable (SurfaceAncestorKey.ofLabels (X := .plane) 0 (Fin 5)
    (by norm_num [StableArity]) ![1] 0 ![.hyperplane, .point, .hyperplane, .point, .hyperplane]) =
    some (1, .inr (SurfaceQuery.points .plane 0 ![1] 2)) := by decide +kernel

/-- An odd number of exceptional divisors keeps the self-intersection minus.
Its zero-marking positive-degree residual is retained. -/
example : reduceVariable (SurfaceAncestorKey.ofLabels (X := .hirzebruchOne) 0 (Fin 3)
    StableArity.zero_fin_three ![1, 0] 0 (fun _ ↦ .exceptional 0)) =
    some (-1, .inr (SurfaceQuery.points .hirzebruchOne 0 ![1, 0] 0)) := by decide +kernel

/-- Both distinct exceptional coordinates contribute to the product. -/
example : reduceVariable (SurfaceAncestorKey.ofLabels (X := .blowupTwo) 0 (Fin 3)
    StableArity.zero_fin_three ![1, 1, 0] 0 ![.exceptional 0, .exceptional 1, .point]) =
    some (1, .inr (SurfaceQuery.points .blowupTwo 0 ![1, 1, 0] 1)) := by decide +kernel

/-- The same insertions at equal energy can vanish for a different full class. -/
example : reduceVariable (SurfaceAncestorKey.ofLabels (X := .blowupTwo) 0 (Fin 3)
    StableArity.zero_fin_three ![2, 0, 0] 0 ![.exceptional 0, .exceptional 1, .point]) =
    none := by decide +kernel

/-- This query passes dimension but vanishes by primary string. -/
example : reduceVariable (SurfaceAncestorKey.ofLabels (X := .plane) 0 (Fin 4)
    (by norm_num [StableArity]) ![1] 0 ![.unit, .point, .point, .point]) =
    none := by decide +kernel

/-- The hyperplane has zero intersection with the exceptional curve. -/
example : reduceVariable (SurfaceAncestorKey.ofLabels (X := .hirzebruchOne) 0 (Fin 3)
    StableArity.zero_fin_three ![1, 0] 0 (fun _ ↦ .hyperplane)) = none := by decide +kernel

/-- A nonzero power stays an ancestor, even when it passes dimension. -/
example : let q := (SurfaceAncestorKey.ofLabels (X := .plane) 1 (Fin 1)
      (by norm_num [StableArity]) ![1] (fun _ ↦ 2) (fun _ ↦ .point));
    reduceVariable q = some (1, .inl q) := by decide +kernel

/-- The exceptional degree-zero genus-one divisor is not discarded. -/
example : let q := (SurfaceAncestorKey.ofLabels (X := .plane) 1 (Fin 1)
      (by norm_num [StableArity]) 0 0 (fun _ ↦ .hyperplane));
    reduceVariable q = some (1, .inl q) := by decide +kernel

/-- The degree-zero classical cubic remains an explicit geometric input. -/
example : let q := (SurfaceAncestorKey.ofLabels (X := .plane) 0 (Fin 3)
      StableArity.zero_fin_three 0 0 ![.unit, .hyperplane, .hyperplane]);
    reduceVariable q = some (1, .inl q) := by decide +kernel

/-- Degree-zero primary terms still obey dimension vanishing. -/
example : reduceVariable (SurfaceAncestorKey.ofLabels (X := .plane) 0 (Fin 3)
    StableArity.zero_fin_three 0 0 (fun _ ↦ .hyperplane)) = none := by decide +kernel

/-- A negative primary output degree is covered by the dimension rule. -/
example : reduceVariable (SurfaceAncestorKey.ofLabels (X := .plane) 0 (Fin 3)
    StableArity.zero_fin_three ![1] 0 (fun _ ↦ .unit)) = none := by decide +kernel

/-- Primary point queries of positive degree are in the geometric domain
even with no markings and unstable source curves. -/
example : (SurfaceQuery.points .hirzebruchOne 0 ![1, 0] 0).GeometricDomain ∧
    ¬StableArity 0 (Fin 0) := by
  constructor
  · decide +kernel
  · norm_num [StableArity]

/-- Genuine invariant semantics and the original incoming certificate give
the reduced equation, at arbitrary powers, markings, and full curve class. -/
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
    (hpair : T.DivisorPairingCompatible Adiv)
    (n : ℕ)
    (houtput : ∀ i z, z ∈ (GetzlerGraphs.expression i).addMarkings n → z.Compatible A F N)
    (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    MvPolynomial.aeval (variableEval U P)
      (reduce X (GetzlerGraphs.surfacePolynomial n beta k a)) = 0 :=
  GetzlerGraphs.exchange_reducedSurfacePolynomial_eq_zero A I F N H hsource G hcycle Omega P
    T U S Hdiv hpair n houtput beta k a GetzlerReplay.presentation GetzlerReplay.accepted

end AxiomaticGWTest.Surfaces.PolynomialReduction

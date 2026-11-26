/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.AncestorPolynomial
import AxiomaticGWTest.Tautological.GetzlerReplay

/-!
# Surface graph polynomial regressions

The rational callbacks below are algebraic probes of the expansion, not
numerical surface GW models. The final example consumes the actual frozen
certificate using the supplied theory's genuine component ancestors.
-/

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.AncestorPolynomial

open AxiomaticGW

private def classicalCubic (X : SurfaceTarget) : SurfaceVertexValues X ℚ :=
  fun g S _ _ beta k a ↦
    if g = 0 ∧ beta = 0 ∧ Fintype.card S = 3 ∧ (∀ s, k s = 0) then
      SurfaceCohomology.counit X.blowups (∏ s, (a s).value)
    else 0

private def ellipticPointProbe (X : SurfaceTarget) (beta₀ : X.Curve) (n : ℕ) :
    SurfaceVertexValues X ℚ :=
  fun g S _ h beta k a ↦
    if g = 1 ∧ beta = beta₀ ∧ Fintype.card S = n ∧ (∀ s, k s = 0 ∧ a s = .point) then 1
    else classicalCubic X g S h beta k a

private def oneLoop : GluingExpression 1 (Fin 1) :=
  GetzlerGraphs.close (.fundamental 0 (Fin 3) StableArity.zero_fin_three)

/-- Both ordered unit/point terms and each exceptional minus sign are required. -/
example : (oneLoop.surfaceEval .plane (classicalCubic .plane) 0 0 (fun _ ↦ .unit),
    oneLoop.surfaceEval .hirzebruchOne (classicalCubic .hirzebruchOne) 0 0 (fun _ ↦ .unit),
    oneLoop.surfaceEval .blowupTwo (classicalCubic .blowupTwo) 0 0 (fun _ ↦ .unit)) =
    ((3 : ℚ), 4, 5) := by decide +kernel

/-- All nine ordered component assignments of E₁+E₂ survive the expansion. -/
example : GetzlerGraphs.delta22Expression.surfaceEval .blowupTwo
    (fun _ _ _ _ _ _ _ ↦ (1 : ℚ)) ![1, 1, 0] 0 (fun _ ↦ .unit) = 9 := by decide +kernel

/-- Powers follow their labels: permuting two whole insertions leaves the key unchanged. -/
example : SurfaceAncestorKey.ofLabels (X := .blowupTwo) 1 (Fin 2)
    (by norm_num [StableArity]) ![1, 0, 1]
    ![0, 2] ![.hyperplane, .point] =
    SurfaceAncestorKey.ofLabels 1 (Fin 2) (by norm_num [StableArity]) ![1, 0, 1]
      ![2, 0] ![.point, .hyperplane] := by decide +kernel

/-- Moving a power while retaining its old state label changes the component variable. -/
example : SurfaceAncestorKey.ofLabels (X := .blowupTwo) 1 (Fin 2)
    (by norm_num [StableArity]) ![1, 0, 1]
    ![0, 2] ![.hyperplane, .point] ≠
    SurfaceAncestorKey.ofLabels 1 (Fin 2) (by norm_num [StableArity]) ![1, 0, 1]
      ![2, 0] ![.hyperplane, .point] := by decide +kernel

/-- Equal-energy exceptional classes remain different variables. -/
example : SurfaceAncestorKey.ofLabels (X := .blowupTwo) 1 (Fin 1)
    (by norm_num [StableArity]) ![1, 0, 0]
    0 (fun _ ↦ .point) ≠
    SurfaceAncestorKey.ofLabels 1 (Fin 1) (by norm_num [StableArity]) ![0, 1, 0]
      0 (fun _ ↦ .point) := by decide +kernel

/-- A repeated insertion remains two markings, not one. -/
example : (SurfaceAncestorKey.ofLabels (X := .plane) 1 (Fin 2) (by norm_num [StableArity]) ![1]
    0 (fun _ ↦ .point)).insertions.count ⟨.point, 0⟩ = 2 := by decide +kernel

/-- At the energy-two class E₁+E₂, the elliptic all-point coefficient probe is -9.
The value is a graph-algebra coefficient, not the invariant of E₁+E₂. -/
example : GetzlerGraphs.surfaceEquation .blowupTwo
    (ellipticPointProbe .blowupTwo ![1, 1, 0] 2) 0 ![1, 1, 0] 0
      (fun _ ↦ .hyperplane) = -9 := by decide +kernel

/-- The genuine supplied theory, arbitrary powers/markings, and original replay
are connected to the collected polynomial. No probe is used in this theorem. -/
example {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (GetzlerGraphs.expression i).Compatible A F N)
    (G : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (A 1 (Fin 4)).map (GetzlerGraphs.cycle x) = G.cycle x)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C)
    (hp : Omega.pairing = (SurfaceCohomology.frobenius X.blowups).pairing)
    (n : ℕ)
    (houtput : ∀ i z, z ∈ (GetzlerGraphs.expression i).addMarkings n → z.Compatible A F N)
    (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    MvPolynomial.aeval (SurfaceAncestorKey.eval Omega P I)
      (GetzlerGraphs.surfacePolynomial n beta k a) = 0 :=
  GetzlerGraphs.exchange_surfacePolynomial_eq_zero A I F N H hsource G hcycle Omega P hp n
    houtput beta k a GetzlerReplay.presentation GetzlerReplay.accepted

end AxiomaticGWTest.Surfaces.AncestorPolynomial

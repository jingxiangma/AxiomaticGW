/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.Fixtures.GenusTwoBP

set_option linter.privateModule false
set_option Elab.async false

namespace AxiomaticGWTest.Surfaces.GenusTwoTerms
open AxiomaticGW SurfaceGenusTwo

-- Degree-zero elliptic constants come from the existing reconstruction algorithm.
example : residualTerms (SurfaceAncestorKey.ofLabels 1 (Fin 1)
    (by norm_num [StableArity]) (0 : SurfaceTarget.plane.Curve) 0 (fun _ ↦ .hyperplane)) =
    RationalTerms.term (-1/8) 0 := by decide +kernel

-- Dimension vanishing is applied before any higher-genus unknown is introduced.
example : residualTerms (SurfaceAncestorKey.ofLabels 2 (Fin 1)
    (by norm_num [StableArity]) (0 : SurfaceTarget.plane.Curve) 0 (fun _ ↦ .unit)) = 0 := by
  decide +kernel

private def psiDivisor : SurfaceAncestorKey .plane :=
  .ofLabels 2 (Fin 1) (by norm_num [StableArity]) 0 (fun _ ↦ 1) (fun _ ↦ .hyperplane)

-- An unresolved first cotangent power stays an ancestor variable, even at degree zero.
example : residualTerms psiDivisor = RationalTerms.term 1 {psiDivisor} := by decide +kernel

private def pointPsi (beta : SurfaceTarget.blowupTwo.Curve) : SurfaceAncestorKey .blowupTwo :=
  .ofLabels 2 (Fin 1) (by norm_num [StableArity]) beta (fun _ ↦ 1) (fun _ ↦ .point)

-- Equal anticanonical energy does not identify exceptional curve classes.
example : residualTerms (pointPsi ![1,0,0]) ≠ residualTerms (pointPsi ![0,1,0]) := by
  decide +kernel

-- A repeated genus-two variable would be quadratic and is forbidden by the proved bound.
example : ¬MonomialBound 2 (0 : SurfaceTarget.plane.Curve) {psiDivisor, psiDivisor} := by
  intro h
  have hg := h.2.1
  norm_num [psiDivisor, SurfaceAncestorKey.ofLabels] at hg

private def atInput : SurfaceAncestorKey .plane :=
  .ofLabels 2 (Fin 1) (by norm_num [StableArity]) ![1] (fun _ ↦ 3) (fun _ ↦ .point)

private def coupled : RationalTerms (SurfaceAncestorKey .plane) :=
  RationalTerms.term 2 {atInput} + RationalTerms.term (-3) {psiDivisor} + RationalTerms.term 7 0

-- Isolate all input-class terms while retaining smaller classes and the constant.
example : sameClassTerms ![1] coupled = RationalTerms.term 2 {atInput} ∧
    smallerClassTerms ![1] coupled =
      RationalTerms.term (-3) {psiDivisor} + RationalTerms.term 7 0 := by decide +kernel

-- The partition is an algebraic identity for every valuation, not a supplied recurrence.
example (v : SurfaceAncestorKey .plane → ℚ) :
    RationalTerms.eval v coupled = RationalTerms.eval v (sameClassTerms ![1] coupled) +
      RationalTerms.eval v (smallerClassTerms ![1] coupled) := eval_split_by_class v _ _

-- Node and external powers are both retained by the same executable term format.
example (X : SurfaceTarget) (beta : X.Curve) (a : Fin 2 → SurfaceBasisLabel X) :
    (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity])).surfaceDecoratedTerms
      X (vertexTerms X) ![1,2] beta ![3,4] a =
      residualTerms (SurfaceAncestorKey.ofLabels 2 (Fin 2) (by norm_num [StableArity])
        beta ![4,6] a) := by
  have h : (![3,4] : Fin 2 → ℕ) + ![1,2] = ![4,6] := by
    funext i
    fin_cases i <;> rfl
  simp only [GluingExpression.surfaceDecoratedTerms, h, vertexTerms]

-- Every BP output monomial is constant or a single dimension-compatible genus-two query.
example (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 3) → ℕ) (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X)
    (t : ℚ × Multiset (SurfaceAncestorKey X))
    (ht : t ∈ BelorousskiPandharipande.genusTwoTerms X n beta k a) :
    t.2 = 0 ∨ ∃ q, t.2 = {q} ∧ q.genus = 2 ∧ q.DimensionCompatible ∧
      ∃ delta : X.Curve, q.beta + delta = beta :=
  ((BelorousskiPandharipande.genusTwoTerms_bound X n beta k a) t ht).affine

-- The nonzero lower-genus constant in the full F₁ equation must not be dropped.
example : ¬RationalTerms.Equivalent SurfaceGenusTwoBP.exceptional
    (SurfaceGenusTwoBP.exceptional.filter (fun t ↦ t.2 ≠ 0)) := by decide +kernel

-- A nonzero relation's raw polynomial must not be replaced by the empty expression.
example : ¬RationalTerms.Equivalent SurfaceGenusTwoBP.distinctExceptional 0 := by decide +kernel

end AxiomaticGWTest.Surfaces.GenusTwoTerms

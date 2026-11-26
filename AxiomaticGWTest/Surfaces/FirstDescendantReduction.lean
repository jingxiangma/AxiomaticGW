/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.GenusTwoDerivedInitialValues

set_option linter.privateModule false
set_option Elab.async false

namespace AxiomaticGWTest.Surfaces.FirstDescendantReduction
open AxiomaticGW SurfaceFirstDescendant SurfacePolynomialReduction

-- Degree-zero point values remain actual queries; normalization does not invent a seed.
example : primaryTerms 2 (0 : SurfaceTarget.plane.Curve) {.point} =
    RationalTerms.term 1 {SurfaceQuery.points .plane 2 0 1} := by decide +kernel

-- Degree-zero primary divisors vanish at these stable arities.
example : primaryTerms 2 (0 : SurfaceTarget.plane.Curve) {.hyperplane, .point} = 0 := by
  decide +kernel

-- The string equation consumes the unique power.
example : terms 2 (0 : SurfaceTarget.plane.Curve) .point {.unit} =
    RationalTerms.term 1 {SurfaceQuery.points .plane 2 0 1} := by decide +kernel

-- Dilaton counts the remaining marking, with coefficient 2g-2+n = 3.
example : terms 2 (0 : SurfaceTarget.plane.Curve) .unit {.point} =
    RationalTerms.term 3 {SurfaceQuery.points .plane 2 0 1} := by decide +kernel

-- A second primary unit makes the string-reduced primary invariant vanish.
example : terms 2 (0 : SurfaceTarget.plane.Curve) .point {.unit, .unit} = 0 := by
  decide +kernel

-- The signed exceptional square contributes a primary point correction.
example : RationalTerms.Equivalent
    (terms 2 (![2,0] : SurfaceTarget.hirzebruchOne.Curve) (.exceptional 0)
      {.exceptional 0, .point, .point})
    (RationalTerms.term (-2) {query 2 ![2,0] (.exceptional 0) 2} +
      RationalTerms.term (-1) {SurfaceQuery.points .hirzebruchOne 2 ![2,0] 3}) := by
  decide +kernel

-- Repeated divisors have a multiplicity-two cup correction.
example : RationalTerms.Equivalent
    (terms 2 (![2,0] : SurfaceTarget.hirzebruchOne.Curve) (.exceptional 0)
      {.exceptional 0, .exceptional 0, .point, .point})
    (RationalTerms.term 4 {query 2 ![2,0] (.exceptional 0) 2} +
      RationalTerms.term 4 {SurfaceQuery.points .hirzebruchOne 2 ![2,0] 3}) := by
  decide +kernel

-- A zero divisor pairing is not divided out: its cup contribution can still survive.
example : terms 2 (0 : SurfaceTarget.plane.Curve) .hyperplane {.hyperplane} =
    RationalTerms.term 1 {SurfaceQuery.points .plane 2 0 1} := by decide +kernel

private def twiceExceptional : SurfaceAncestorKey .hirzebruchOne :=
  ⟨2, ![2,0], {⟨.exceptional 0, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩}, by decide +kernel⟩

-- This nonzero rational-tail correction distinguishes the ancestor from its descendant.
example : RationalTerms.Equivalent (normalizedTerms twiceExceptional)
    (RationalTerms.term 1 {.inr (query 2 ![2,0] (.exceptional 0) 2)} +
      RationalTerms.term (-1) {.inr (SurfaceQuery.points .hirzebruchOne 2 ![1,0] 2)}) := by
  decide +kernel

-- Omitting the nonzero correction is rejected by the same coefficient checker.
example : ¬RationalTerms.Equivalent (normalizedTerms twiceExceptional)
    (RationalTerms.term 1 {.inr (query 2 ![2,0] (.exceptional 0) 2)}) := by decide +kernel

private def mixedClass : SurfaceAncestorKey .hirzebruchOne :=
  ⟨2, ![1,1], {⟨.exceptional 0, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩},
    by decide +kernel⟩

-- At E+F the same calibration has the opposite primary intersection factor on F.
example : RationalTerms.Equivalent (normalizedTerms mixedClass)
    (RationalTerms.term 1 {.inr (query 2 ![1,1] (.exceptional 0) 3)} +
      RationalTerms.term 1 {.inr (SurfaceQuery.points .hirzebruchOne 2 ![0,1] 3)}) := by
  decide +kernel

private def higherPower : SurfaceAncestorKey .plane :=
  ⟨2, ![1], {⟨.point, 3⟩}, by decide +kernel⟩

-- The first-power normalizer makes no unproved comparison for higher powers.
example : normalizedTerms higherPower = RationalTerms.term 1 {.inl higherPower} := by
  decide +kernel

-- A checked affine substitution preserves its independent constant term.
example : RationalTerms.Equivalent
    (RationalTerms.affineSubstitute (fun n : ℕ ↦ RationalTerms.term 3 {n + 1})
      (RationalTerms.term 7 0 + RationalTerms.term 2 {0}))
    (RationalTerms.term 7 0 + RationalTerms.term 6 {1}) := by decide +kernel

-- Quadratic monomials cannot meet the substitution theorem's support hypothesis.
example : ¬(∀ t ∈ (RationalTerms.term 1 ({0,0} : Multiset ℕ)), t.2.card ≤ 1) := by
  decide +kernel

-- The general energy bound applies to every full positive-tail splitting.
example (X : SurfaceTarget) (beta : X.Curve) (s : X.Curve × X.Curve)
    (hs : s ∈ X.positiveTailSplittings beta) :
    X.effective.energy s.1 < X.effective.energy beta := normalizedTail_energy_lt X beta s hs

end AxiomaticGWTest.Surfaces.FirstDescendantReduction

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.GenusTwoNormalizedSupport

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusTwoNormalizedSupport
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwo
open SurfaceGenusZero (variableCurve)
open SurfaceLowGenus (variableGenus)
open RelationCertificate PsiBoundaryExpansion

-- Every dependency in the normalized BP remainder strictly decreases energy.
example (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 3) → ℕ) (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X)
    (t : ℚ × Multiset (Variable X))
    (ht : t ∈ normalizedSmallerClassTerms beta
      (BelorousskiPandharipande.normalizedGenusTwoTerms X n beta k a))
    (v : Variable X) (hv : v ∈ t.2) :
    variableGenus v = 2 ∧ variableDimensionCompatible v ∧
      X.effective.energy (variableCurve v) < X.effective.energy beta :=
  normalizedSmallerClassTerms_dependencies
    (BelorousskiPandharipande.normalizedGenusTwoTerms_bound X n beta k a) ht v hv

-- The complete L24 leading matrix uses exactly the original-class ancestors.
example (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (v : Variable X) (hv : variableCurve v = beta) :
    RationalTerms.coefficient (L24Relation.normalizedGenusTwoTerms X n beta k a) {v} =
      RationalTerms.coefficient (RationalTerms.affineSubstitute directNormalizedTerms
        (sameClassTerms beta (L24Relation.genusTwoTerms X n beta k a))) {v} :=
  coefficient_normalized_eq_sameClass_direct
    (L24Relation.genusTwoTerms_bound X n beta k a) v hv

private def twiceExceptional : SurfaceAncestorKey .hirzebruchOne :=
  ⟨2, ![2,0], {⟨.exceptional 0, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩}, by decide +kernel⟩

private def lowerPoint : Variable .hirzebruchOne :=
  .inr (SurfaceQuery.points .hirzebruchOne 2 ![1,0] 2)

-- Leading extraction keeps the original-class variable and excludes constants.
example : RationalTerms.Equivalent
    (normalizedSameClassTerms twiceExceptional.beta
      (RationalTerms.term 7 0 + normalizedTerms twiceExceptional))
    (directNormalizedTerms twiceExceptional) := by decide +kernel

-- The nonzero calibration correction and the independent constant stay in the remainder.
example : RationalTerms.Equivalent
    (normalizedSmallerClassTerms twiceExceptional.beta
      (RationalTerms.term 7 0 + normalizedTerms twiceExceptional))
    (RationalTerms.term 7 0 + RationalTerms.term (-1) {lowerPoint}) := by decide +kernel

-- Direct normalization is not the complete equation at a smaller curve class.
example : RationalTerms.coefficient (normalizedTerms twiceExceptional) {lowerPoint} = -1 ∧
    RationalTerms.coefficient (directNormalizedTerms twiceExceptional) {lowerPoint} = 0 := by
  decide +kernel

private def firstExceptional : SurfaceAncestorKey .blowupTwo :=
  ⟨2, ![1,0,0], {⟨.point, 0⟩, ⟨.point, 0⟩}, by decide +kernel⟩

-- Equal energy does not merge E₁ and E₂ in the leading coefficient matrix.
example : SurfaceTarget.blowupTwo.effective.energy (![1,0,0]) =
      SurfaceTarget.blowupTwo.effective.energy (![0,1,0]) ∧
    RationalTerms.coefficient (directNormalizedTerms firstExceptional)
      {.inr (SurfaceQuery.points .blowupTwo 2 ![1,0,0] 2)} = 1 ∧
    RationalTerms.coefficient (directNormalizedTerms firstExceptional)
      {.inr (SurfaceQuery.points .blowupTwo 2 ![0,1,0] 2)} = 0 := by
  decide +kernel

private def higherPower : SurfaceAncestorKey .plane :=
  ⟨2, ![1], {⟨.point, 3⟩}, by decide +kernel⟩

-- Leading extraction retains the ancestor tag at higher powers.
example : directNormalizedTerms higherPower = RationalTerms.term 1 {.inl higherPower} := by
  decide +kernel

-- At class zero, the retained degree-zero unknown is not mistaken for a constant.
example : normalizedSameClassTerms (0 : SurfaceTarget.plane.Curve)
      (RationalTerms.term 7 0 + RationalTerms.term 2
        {.inr (SurfaceQuery.points .plane 2 0 1)}) =
    RationalTerms.term 2 {.inr (SurfaceQuery.points .plane 2 0 1)} := by decide +kernel

end AxiomaticGWTest.Surfaces.GenusTwoNormalizedSupport

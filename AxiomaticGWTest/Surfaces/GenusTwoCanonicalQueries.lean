/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.GenusTwoCanonicalQueries
import AxiomaticGW.Surfaces.PlaneCanonicalSupport

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusTwoCanonicalQueries
open AxiomaticGW SurfaceGenusTwo SurfacePolynomialReduction

-- Class-zero canonical sectors exclude the dimension-incompatible point descendant.
example : (canonicalQueries .plane 0).length = 2 := by decide +kernel
example : (canonicalQueries .hirzebruchOne 0).length = 3 := by decide +kernel
example : (canonicalQueries .blowupTwo 0).length = 4 := by decide +kernel

example (X : SurfaceTarget) :
    ¬(SurfaceFirstDescendant.query 2 (0 : X.Curve) .point 0).DimensionCompatible := by
  rw [show (0 : ℕ) = X.effective.energy (0 : X.Curve) - 1 by rw [map_zero]; rfl,
    point_first_dimensionCompatible_iff]
  exact not_not_intro rfl

-- Both distinct exceptional labels occur at the same full class.
example : SurfaceFirstDescendant.query 2 ![0,1,0] (.exceptional 0) 1 ∈
    canonicalQueries .blowupTwo ![0,1,0] := by decide +kernel

example : SurfaceFirstDescendant.query 2 ![0,1,0] (.exceptional 1) 1 ∈
    canonicalQueries .blowupTwo ![0,1,0] := by decide +kernel

-- A different equal-energy full class cannot reuse a canonical query.
example : SurfaceFirstDescendant.query 2 ![1,0,0] (.exceptional 0) 1 ∉
    canonicalQueries .blowupTwo ![0,1,0] := by decide +kernel

-- Reducible effective classes remain in the domain: this is H + E on F1.
example : (canonicalQueries .hirzebruchOne ![2,1]).length = 4 := by decide +kernel

example : (SurfaceFirstDescendant.query 2
    (![2,1] : SurfaceTarget.hirzebruchOne.Curve) .hyperplane 4).DimensionCompatible := by
  apply canonicalQueries_dimensionCompatible (![2,1] : SurfaceTarget.hirzebruchOne.Curve)
  decide +kernel

-- The positive plane list preserves the existing public triple and its order.
example : canonicalQueries .plane ![1] =
    [BelorousskiPandharipande.planeCanonicalQueries 1 0,
      BelorousskiPandharipande.planeCanonicalQueries 1 1,
      BelorousskiPandharipande.planeCanonicalQueries 1 2] := by decide +kernel

-- Direct normalization retains the exact class; complete normalization keeps subclasses.
example (X : SurfaceTarget) (q : SurfaceAncestorKey X) (hg : q.genus = 2)
    (hk : q.totalPsi ≤ 1) (t : ℚ × Multiset (Variable X))
    (ht : t ∈ directNormalizedTerms q) :
    ∃ c ∈ canonicalQueries X q.beta, t.2 = {Sum.inr c} :=
  directNormalizedTerms_canonical_support q hg hk ht

example (X : SurfaceTarget) (q : SurfaceAncestorKey X) (hg : q.genus = 2)
    (hk : q.totalPsi ≤ 1) (t : ℚ × Multiset (Variable X))
    (ht : t ∈ normalizedTerms q) :
    ∃ beta : X.Curve, ∃ c ∈ canonicalQueries X beta,
      t.2 = {Sum.inr c} ∧ ∃ delta : X.Curve, beta + delta = q.beta :=
  normalizedTerms_canonical_support q hg hk ht

private def doubleExceptional : SurfaceAncestorKey .hirzebruchOne :=
  SurfaceAncestorKey.ofLabels 2 (Fin 3) (by unfold StableArity; decide +kernel) ![2,0]
    ![1,0,0] ![.exceptional 0, .point, .point]

-- A nonzero signed tail confirms that the generic support cannot stay at one class.
example : RationalTerms.coefficient (normalizedTerms doubleExceptional)
    {Sum.inr (SurfaceQuery.points .hirzebruchOne 2 ![1,0] 2)} = -1 := by
  decide +kernel

example : RationalTerms.coefficient (directNormalizedTerms doubleExceptional)
    {Sum.inr (SurfaceQuery.points .hirzebruchOne 2 ![1,0] 2)} = 0 := by
  decide +kernel

end AxiomaticGWTest.Surfaces.GenusTwoCanonicalQueries

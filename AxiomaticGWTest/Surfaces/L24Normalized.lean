/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.Fixtures.GenusTwoNormalizedL24

set_option linter.privateModule false
set_option maxRecDepth 20000

namespace AxiomaticGWTest.Surfaces.L24Normalized
open AxiomaticGW SurfacePolynomialReduction

-- The normalized certificate also applies after any choice of cache keys.
example (v : Variable .plane → ℚ) (queries : Finset (SurfaceAncestorKey .plane)) :
    RationalTerms.eval v (RationalTerms.affineSubstitute normalizedTerms
      (L24Relation.genusTwoTermsCached .plane queries 0 0 0
        ![.hyperplane, .hyperplane, .unit, .unit])) = 0 := by
  rw [L24Relation.genusTwoTermsCached_eq]
  exact SurfaceGenusTwoNormalizedL24.eval_planeZero v

-- A surviving dilaton term cannot be deleted individually before cancellation.
example : ¬RationalTerms.Equivalent
    (normalizedTerms (⟨2, 0, {⟨.unit, 1⟩, ⟨.point, 0⟩}, by decide +kernel⟩ :
      SurfaceAncestorKey .plane)) 0 := by
  decide +kernel

-- Higher powers retain the ancestor interpretation instead of being relabelled descendants.
example : normalizedTerms (⟨2, 0, {⟨.unit, 2⟩}, by decide +kernel⟩ :
      SurfaceAncestorKey .plane) =
    RationalTerms.term 1 {.inl ⟨2, 0, {⟨.unit, 2⟩}, by decide +kernel⟩} := by
  decide +kernel

end AxiomaticGWTest.Surfaces.L24Normalized

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.PlaneGenusTwoBenchmarks

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.PlaneGenusTwoBenchmarks
open AxiomaticGW SurfaceGenusTwo BelorousskiPandharipande

-- All twelve full requests are covered, with the original positive-class bound.
example (d : Fin 4) (j : Fin 3) :
    planeCanonicalBenchmark? (PlaneGenusTwoScalarTable.requests d j) =
      some (PlaneGenusTwoScalarTable.values (d.val + 1) j) := by
  rw [PlaneGenusTwoScalarTable.coverage]
  exact planeCanonicalBenchmark?_eq _ (by omega) (by omega) j

example : planeCanonicalBenchmark? (SurfaceQuery.points .plane 2 ![4] 13) = some 27 := by
  decide +kernel

example : planeCanonicalBenchmark? (planeCanonicalQueries 4 1) = some 42 := by
  decide +kernel

example : planeCanonicalBenchmark? (planeCanonicalQueries 4 2) = some (25 / 4) := by
  decide +kernel

-- A nonzero answer reaches the original reconstruction through the accepted claim.
example : planeCanonicalValues 4 2 = 25 / 4 := by
  rw [← PlaneGenusTwoScalarTable.values_eq 4 (by decide)]
  rfl

-- Zeros remain certified outputs, distinct from unsupported requests.
example : planeCanonicalBenchmark? (planeCanonicalQueries 3 0) = some 0 := by
  decide +kernel

example : planeCanonicalBenchmark? (planeCanonicalQueries 0 1) = none := by
  decide +kernel

example : planeCanonicalBenchmark? (planeCanonicalQueries 5 0) = none := by
  decide +kernel

example : planeCanonicalBenchmark? (SurfaceQuery.points .plane 1 ![4] 12) = none := by
  decide +kernel

-- The correct degree alone cannot substitute for the insertion powers and labels.
example : planeCanonicalBenchmark? ⟨2, ![4], [⟨.point, 2⟩]⟩ = none := by
  decide +kernel

example : planeCheckCanonicalClaim 4 PlaneGenusTwoScalarTable.values
    (planeCanonicalQueries 4 2) (25 / 4) = true :=
  planeCanonicalBenchmark?_sound _ _ (by decide +kernel)

end AxiomaticGWTest.Surfaces.PlaneGenusTwoBenchmarks

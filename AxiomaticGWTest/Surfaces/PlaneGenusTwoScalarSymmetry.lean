/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.PlaneGenusTwoScalarSymmetry

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.PlaneGenusTwoScalarSymmetry
open AxiomaticGW BelorousskiPandharipande SurfacePolynomialReduction

private def labels : Fin 3 → Fin 3 → SurfaceBasisLabel .plane :=
  ![![.hyperplane, .hyperplane, .point], ![.hyperplane, .point, .point],
    ![.point, .point, .point]]

private def representative : Fin 3 → Fin 6 → Fin 6 :=
  ![![0, 1, 0, 3, 1, 3], ![0, 0, 2, 2, 4, 4], ![0, 0, 0, 0, 0, 0]]

-- Every reused assignment preserves the state at every original external label.
private theorem transported (i : Fin 3) (e : Fin 6) :
    labels i ∘ labelPermutation e = labels i ∘ labelPermutation (representative i e) := by
  fin_cases i <;> fin_cases e <;> decide +kernel

-- The equality is uniform in point count, full class and all sixteen diagrams.
example (n : ℕ) (beta : SurfaceTarget.plane.Curve) (i : Fin 3) (k : Fin 16) (e : Fin 6) :
    planePointConstantPart n beta (labels i) k e =
      planePointConstantPart n beta (labels i) k (representative i e) :=
  planePointConstantPart_eq_of_labels n beta (labels i) k e _ (transported i e)

-- All signed tails and the source guard are retained, for any requested variable.
example (n source : ℕ) (v : Variable .plane) (i : Fin 3) (k : Fin 4) (e : Fin 6) :
    planePointCoefficientPart n source (labels i) v k e =
      planePointCoefficientPart n source (labels i) v k (representative i e) :=
  planePointCoefficientPart_eq_of_labels n source (labels i) v k e _ (transported i e)

-- Equal sampled values alone would not justify exchanging these HHP assignments.
example : labels 0 ∘ labelPermutation 0 ≠ labels 0 ∘ labelPermutation 1 := by decide +kernel

-- The complete six occurrences have three, three and one different state assignments.
example : ∀ i : Fin 3, (Finset.univ.image (representative i)).card = (![3,3,1] : Fin 3 → ℕ) i := by
  decide +kernel

end AxiomaticGWTest.Surfaces.PlaneGenusTwoScalarSymmetry

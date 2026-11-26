/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneGenusTwoScalarParts

/-!
# Reuse of identical BP marking assignments

Relabelling transports the actual state at each external marking. Two
assignments with equal transported states therefore have equal contributions,
at every degree and point count. The complete sums still contain all six
assignments; these lemmas permit reuse of their arithmetic proofs without
discarding occurrences or inferring equality from coincident sampled values.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open SurfaceGenusTwo SurfacePolynomialReduction GluingExpression

/-- Equal transported states give equal complete lower-genus contributions. -/
theorem planePointConstantPart_eq_of_labels (n : ℕ) (beta : SurfaceTarget.plane.Curve)
    (a : Fin 3 → SurfaceBasisLabel .plane) (k : Fin 16) (e f : Fin 6)
    (ha : a ∘ labelPermutation e = a ∘ labelPermutation f) :
    planePointConstantPart n beta a k e = planePointConstantPart n beta a k f := by
  simp only [planePointConstantPart, orbitCotangentTerm, CotangentTerm.relabel,
    SurfaceGenusOne.primaryGraphDimensionEval, ha]

/-- The same transport equality preserves the guarded, signed earlier coefficient. -/
theorem planePointCoefficientPart_eq_of_labels (n source : ℕ)
    (a : Fin 3 → SurfaceBasisLabel .plane) (v : Variable .plane) (k : Fin 4) (e f : Fin 6)
    (ha : a ∘ labelPermutation e = a ∘ labelPermutation f) :
    planePointCoefficientPart n source a v k e = planePointCoefficientPart n source a v k f := by
  simp only [planePointCoefficientPart, orbitCotangentTerm, CotangentTerm.relabel,
    GluingExpression.maxComponentGenus, planeCachedRemainderContraction, ha]

end AxiomaticGW.BelorousskiPandharipande

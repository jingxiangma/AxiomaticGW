/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.Fixtures.L24

set_option linter.privateModule false
set_option Elab.async false
-- The finite relation uses the same reduction depth as its public support theorem.
set_option maxRecDepth 20000

namespace AxiomaticGWTest.Surfaces.L24
open AxiomaticGW SurfaceGenusTwo

-- Every output is affine before coefficient collection, at arbitrary marking counts.
example (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (t : ℚ × Multiset (SurfaceAncestorKey X))
    (ht : t ∈ L24Relation.genusTwoTerms X n beta k a) :
    t.2 = 0 ∨ ∃ q, t.2 = {q} ∧ q.genus = 2 ∧ q.DimensionCompatible ∧
      ∃ delta : X.Curve, q.beta + delta = beta :=
  ((L24Relation.genusTwoTerms_bound X n beta k a) t ht).affine

-- Removing all input-class unknowns leaves a strictly decreasing recursion dependency.
example (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (t : ℚ × Multiset (SurfaceAncestorKey X))
    (ht : t ∈ smallerClassTerms beta (L24Relation.genusTwoTerms X n beta k a))
    (q : SurfaceAncestorKey X) (hq : q ∈ t.2) :
    q.genus = 2 ∧ q.DimensionCompatible ∧
      X.effective.energy q.beta < X.effective.energy beta :=
  smallerClassTerms_dependencies (L24Relation.genusTwoTerms_bound X n beta k a) t ht q hq

private def unitPsi : SurfaceAncestorKey .plane :=
  ⟨2, ![0], {⟨.unit, 1⟩, ⟨.point, 0⟩}, by decide +kernel⟩

private def point : SurfaceAncestorKey .plane :=
  ⟨2, ![0], {⟨.point, 0⟩}, by decide +kernel⟩

-- Consume the complete certificate after caching, with no coverage assumption on the cache.
example (v : SurfaceAncestorKey .plane → ℚ) (queries : Finset (SurfaceAncestorKey .plane)) :
    RationalTerms.eval v
      (L24Relation.genusTwoTermsCached .plane queries 0 0 0
        ![.hyperplane, .hyperplane, .unit, .unit]) =
      v unitPsi - 3 * v point := by
  rw [L24Relation.genusTwoTermsCached_eq]
  rw [RationalTerms.eval_eq_of_equivalent v _ _ SurfaceL24.planeZero_checked]
  simp only [SurfaceL24.planeZero, RationalTerms.eval_add, RationalTerms.eval_term,
    Algebra.algebraMap_self_apply, Multiset.map_singleton, Multiset.prod_singleton,
    one_mul, neg_mul, sub_eq_add_neg, unitPsi, point]

-- Erasing the full nonzero equation is rejected using the certificate, without re-expansion.
example : ¬RationalTerms.Equivalent
    (L24Relation.genusTwoTerms .plane 0 0 0 ![.hyperplane, .hyperplane, .unit, .unit]) 0 := by
  intro h
  have hzero := RationalTerms.eval_eq_of_equivalent (fun _ ↦ (1 : ℚ)) _ _ h
  rw [RationalTerms.eval_eq_of_equivalent _ _ _ SurfaceL24.planeZero_checked] at hzero
  norm_num [SurfaceL24.planeZero, RationalTerms.eval_add, RationalTerms.eval_term,
    RationalTerms.eval_zero] at hzero

-- Moving the cotangent power onto the point changes the requested equation.
example : ¬RationalTerms.Equivalent SurfaceL24.planeZero
    (RationalTerms.term 1 {⟨2, ![0], {⟨.unit, 0⟩, ⟨.point, 1⟩}, by decide +kernel⟩} +
      RationalTerms.term (-3) {point}) := by
  decide +kernel

end AxiomaticGWTest.Surfaces.L24

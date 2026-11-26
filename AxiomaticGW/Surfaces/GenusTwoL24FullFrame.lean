/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoL24ConstantGuard

/-!
# The guarded L24 point constant on the original 815-term frame

The existing relation stores its 721 nonzero coefficients. This identity restores
all original 815 indices by adding only terms with coefficient zero. It provides
an assembly boundary for independent certificates of the individual weighted
contractions, without changing the relation, its signs or geometric inputs.
-/

@[expose] public section

namespace AxiomaticGW.L24Relation

open scoped BigOperators

/-- Exactly the original held coefficients and decorated terms, including zero coefficients. -/
theorem pointConstantGuarded_eq_fullFrame (X : SurfaceTarget) (n : ℕ)
    (beta : X.Curve) (a : Fin 4 → SurfaceBasisLabel X) :
    pointConstantGuarded X n beta a =
      ∑ i : Fin 815, L24CorrectionsReplay.fullClaim i *
        SurfaceGenusTwo.guardedConstantPointContraction X (L24Gluing.term i) beta n a := by
  simp only [pointConstantGuarded, cotangentRelation, Multiset.map_map,
    Function.comp_def, ← Finset.sum_eq_multiset_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : L24CorrectionsReplay.fullClaim i = 0
  · simp only [h, ne_eq, not_true_eq_false, if_false, zero_mul]
  · rw [if_pos h]

end AxiomaticGW.L24Relation

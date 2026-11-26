/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.L24CotangentSupport

/-!
# Residual genus and cotangent support in actual L24 rows

Consumers exclude higher-psi ancestors before coefficient collection at every
full class and test a genuine source column attaining the two-edge bound.
-/

@[expose] public section

namespace AxiomaticGWTest.L24CotangentSupport
open AxiomaticGW GluingExpression SurfaceGenusTwo

-- Match the existing complete L24 source frame during theorem elaboration.
set_option maxRecDepth 20000

/-- No higher-psi ancestor occurs even in the uncollected complete primary row,
for arbitrary labels, markings and full effective classes on all three targets. -/
theorem higherPsi_absent_before_collection (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (q : SurfaceAncestorKey X) (hq : 2 ≤ q.totalPsi)
    (t : ℚ × Multiset (SurfaceAncestorKey X))
    (ht : t ∈ L24Relation.genusTwoTerms X n beta 0 a) : q ∉ t.2 := by
  intro hmem
  have hp := L24Relation.genusTwoTerms_primary_psi_le_one X n beta a ht q hmem
  omega

/-- One of the actual nonzero genus-two columns attains the two-edge lower bound. -/
theorem actual_two_edge_column :
    L24CorrectionsReplay.fullClaim 57 ≠ 0 ∧
      (L24Gluing.term 57).expression.maxComponentGenus = 2 ∧
      ((L24Gluing.term 57).expression.decoratedGraph
        (L24Gluing.term 57).decoration).graph.edgeCount = 2 := by
  decide +kernel

/-- The complete mixed-class blowup row retains the uniform low-psi bound;
no restriction on signs of exceptional multiplicities is supplied. -/
theorem blowupTwo_mixed_row_lowPsi (n : ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel .blowupTwo)
    {t : ℚ × Multiset (SurfaceAncestorKey .blowupTwo)}
    (ht : t ∈ L24Relation.genusTwoTerms .blowupTwo n ![4, 2, 1] 0 a)
    (q : SurfaceAncestorKey .blowupTwo) (hq : q ∈ t.2) : q.totalPsi ≤ 1 :=
  L24Relation.genusTwoTerms_primary_psi_le_one .blowupTwo n ![4, 2, 1] a ht q hq

end AxiomaticGWTest.L24CotangentSupport

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.L24Terms
public import AxiomaticGW.Surfaces.DecoratedTermDegree

/-!
# Low cotangent support in the complete primary L24 equation

Every nonzero original L24 diagram has at least two edges. Signed forgetful
pullback cannot remove those edges. Since codimension remains three, every
remaining ancestor has total psi degree at most one when external powers
are zero. The bound includes node decorations and signed rational-tail terms.

The bound applies before coefficient collection, for every full effective
class, marking count and basis labelling on each fixed surface. It retains
all original nonzero columns and signed pullback terms. It supplies no
relation-validity hypothesis, seed, pivot or reconstruction recurrence.
-/

@[expose] public section

namespace AxiomaticGW.L24Relation
open GluingExpression PsiBoundaryExpansion
set_option maxRecDepth 20000

/-- Every nonzero original L24 column has at least two boundary edges.
This checks the actual full held source, without a component-genus restriction. -/
theorem source_edgeCount_ge_two : ∀ i : Fin 815,
    L24CorrectionsReplay.fullClaim i ≠ 0 →
    2 ≤ ((L24Gluing.term i).expression.decoratedGraph
      (L24Gluing.term i).decoration).graph.edgeCount :=
  by decide +kernel

/-- Every term in the complete signed marking pullback retains at least two
original boundary edges, including terms with only lower-genus components. -/
theorem added_term_edgeCount_ge_two (n : ℕ)
    (t : ℚ × CotangentTerm 2 (ExtraMarkings n (Fin 4)))
    (ht : t ∈ cotangentRelation.pullback n) :
    2 ≤ (t.2.expression.decoratedGraph t.2.decoration).graph.edgeCount := by
  obtain ⟨z, hz, w, hw, rfl⟩ :=
    (CotangentCombination.mem_pullback cotangentRelation n t).mp ht
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hz
  have hi' : L24CorrectionsReplay.fullClaim i ≠ 0 := by
    simpa only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  have he := source_edgeCount_ge_two i hi'
  exact he.trans ((L24Gluing.term i).addMarkings_edgeCount_le n w hw)

/-- Every residual variable of the complete primary L24 equation has total psi
power at most one, including node powers and all signed added-point corrections. -/
theorem genusTwoTerms_primary_psi_le_one (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    {t : ℚ × Multiset (SurfaceAncestorKey X)} (ht : t ∈ genusTwoTerms X n beta 0 a)
    (q : SurfaceAncestorKey X) (hq : q ∈ t.2) : q.totalPsi ≤ 1 := by
  unfold genusTwoTerms surfaceTerms at ht
  obtain ⟨z, hz, ht⟩ := Multiset.mem_bind.mp ht
  obtain ⟨_, u, hu, rfl⟩ := RationalTerms.mem_scale.mp ht
  have he := SurfaceGenusTwo.decoratedTerms_psi_bound
    z.2.expression z.2.decoration beta 0 a hu q hq
  have hc := added_term_codimension n z hz
  have hedges := added_term_edgeCount_ge_two n z hz
  simp only [Pi.zero_apply, Finset.sum_const_zero, add_zero, hc] at he
  omega
end AxiomaticGW.L24Relation

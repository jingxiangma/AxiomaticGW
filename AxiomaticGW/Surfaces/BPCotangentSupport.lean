/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.BelorousskiPandharipande
public import AxiomaticGW.Surfaces.DecoratedTermDegree

/-!
# Low cotangent support in primary BP equations

Every original BP term is a boundary class of codimension two. Signed
forgetful pullback preserves codimension and never removes its boundary
edges. Therefore every residual component of a primary BP equation has
total psi power at most one, including at node markings and after arbitrarily
many added primary points.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open GluingExpression PsiBoundaryExpansion

/-- The actual twenty published diagrams each contain a boundary edge. -/
theorem paperTerm_edgeCount_pos (i : Fin 20) :
    0 < ((paperTerm i).1.decoratedGraph (paperTerm i).2).graph.edgeCount := by
  fin_cases i <;> decide +kernel

/-- Pullback can add rational tails but preserves every original boundary edge. -/
theorem added_term_edgeCount_pos (i : Fin 20) (e : Fin 6) (n : ℕ)
    (t : ℤ × CotangentTerm 2 (ExtraMarkings n (Fin 3)))
    (ht : t ∈ (orbitCotangentTerm i e).addMarkings n) :
    0 < (t.2.expression.decoratedGraph t.2.decoration).graph.edgeCount := by
  exact (paperTerm_edgeCount_pos i).trans_le
    ((orbitCotangentTerm i e).addMarkings_edgeCount_le n t ht)

/-- The full primary BP expansion has no residual higher-power ancestor,
on any of the three fixed surfaces and before coefficient collection. -/
theorem genusTwoTerms_primary_psi_le_one (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X)
    {t : ℚ × Multiset (SurfaceAncestorKey X)} (ht : t ∈ genusTwoTerms X n beta 0 a)
    (q : SurfaceAncestorKey X) (hq : q ∈ t.2) : q.totalPsi ≤ 1 := by
  unfold genusTwoTerms surfaceTerms at ht
  obtain ⟨i, _, ht⟩ := Multiset.mem_sum.mp ht
  obtain ⟨_, u, hu, rfl⟩ := RationalTerms.mem_scale.mp ht
  obtain ⟨e, _, hu⟩ := Multiset.mem_sum.mp hu
  obtain ⟨z, hz, hu⟩ := Multiset.mem_bind.mp hu
  obtain ⟨_, w, hw, rfl⟩ := RationalTerms.mem_scale.mp hu
  have he := SurfaceGenusTwo.decoratedTerms_psi_bound z.2.expression z.2.decoration
    beta 0 a hw q hq
  have hc := added_term_codimension i e n z hz
  have hp := added_term_edgeCount_pos i e n z hz
  simp only [Pi.zero_apply, Finset.sum_const_zero, add_zero, hc] at he
  omega

end AxiomaticGW.BelorousskiPandharipande

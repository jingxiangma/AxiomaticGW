/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoTerms
public import AxiomaticGW.Surfaces.GluingDegree
public import AxiomaticGW.Coefficients.TermSupport
public import AxiomaticGW.Tautological.DecoratedGluingMarkingBounds
public import AxiomaticGW.Tautological.GraphBounds

/-!
# Cotangent bounds for actual residual graph terms

Every terminal cotangent power is paid for by external powers or graph
decoration. Boundary edges consume codimension without creating cotangent
powers. Signed forgetful corrections preserve existing edges and may add a
new rational-tail edge. These bounds apply to every uncollected dependency.
-/

@[expose] public section

namespace AxiomaticGW.GluingExpression

/-- A signed one-marking pullback never removes an existing boundary edge. -/
theorem addCotangentMarking_edgeCount_le {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (z : ℤ × CotangentTerm g (Option S)) (hz : z ∈ x.addCotangentMarking d l) :
    (x.decoratedGraph d).graph.edgeCount ≤
      (z.2.expression.decoratedGraph z.2.decoration).graph.edgeCount := by
  induction x with
  | fundamental g S h => exact Nat.zero_le _
  | relabel e x ih =>
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz
    exact ih d l w hw
  | separating x y ihx ihy =>
    rcases Multiset.mem_add.mp hz with hz | hz
    · obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz
      have he := ihx d.1 l.1 w hw
      change (x.decoratedGraph d.1).graph.edgeCount +
          (y.decoratedGraph d.2).graph.edgeCount + 1 ≤
        (w.2.expression.decoratedGraph w.2.decoration).graph.edgeCount +
          (y.decoratedGraph d.2).graph.edgeCount + 1
      omega
    · obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz
      have he := ihy d.2 l.2 w hw
      change (x.decoratedGraph d.1).graph.edgeCount +
          (y.decoratedGraph d.2).graph.edgeCount + 1 ≤
        (x.decoratedGraph d.1).graph.edgeCount +
          (w.2.expression.decoratedGraph w.2.decoration).graph.edgeCount + 1
      omega
  | nonseparating x ih =>
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz
    exact Nat.add_le_add_right (ih d l w hw) 1

/-- All iterated signed pullbacks retain at least the original boundary edges. -/
theorem CotangentTerm.addMarkings_edgeCount_le {g : ℕ} {S : Type} [Fintype S]
    (x : CotangentTerm g S) (n : ℕ)
    (z : ℤ × CotangentTerm g (ExtraMarkings n S)) (hz : z ∈ x.addMarkings n) :
    (x.expression.decoratedGraph x.decoration).graph.edgeCount ≤
      (z.2.expression.decoratedGraph z.2.decoration).graph.edgeCount := by
  induction n with
  | zero =>
    rw [CotangentTerm.addMarkings, Multiset.mem_singleton] at hz
    subst z
    exact le_rfl
  | succ n ih =>
    obtain ⟨t, ht, hz⟩ := Multiset.mem_bind.mp hz
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz
    exact (ih t ht).trans (t.2.expression.addCotangentMarking_edgeCount_le
      t.2.decoration t.2.labels w hw)

end AxiomaticGW.GluingExpression

namespace AxiomaticGW.SurfaceGenusTwo
variable {X : SurfaceTarget}

private theorem residualTerms_dependency (q : SurfaceAncestorKey X)
    {t : ℚ × Multiset (SurfaceAncestorKey X)} (ht : t ∈ residualTerms q)
    (r : SurfaceAncestorKey X) (hr : r ∈ t.2) : r = q := by
  unfold residualTerms at ht
  split_ifs at ht with hd hg
  · obtain ⟨_, rfl⟩ := RationalTerms.mem_term.mp ht
    exact (Multiset.notMem_zero _ hr).elim
  · obtain ⟨_, rfl⟩ := RationalTerms.mem_term.mp ht
    exact Multiset.mem_singleton.mp hr
  · exact (Multiset.notMem_zero _ ht).elim

/-- Edges consume codimension; they cannot be used as additional psi powers
in any terminal residual invariant. -/
theorem decoratedTerms_psi_bound {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (d : x.CotangentDecoration) (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X)
    {t : ℚ × Multiset (SurfaceAncestorKey X)}
    (ht : t ∈ x.surfaceDecoratedTerms X (vertexTerms X) d beta k a)
    (q : SurfaceAncestorKey X) (hq : q ∈ t.2) :
    q.totalPsi + (x.decoratedGraph d).graph.edgeCount ≤
      (x.decoratedGraph d).codimension + ∑ s, k s := by
  induction x generalizing beta t q with
  | fundamental g S h =>
    have he := residualTerms_dependency
      (SurfaceAncestorKey.ofLabels g S h beta (k + d) a) ht q hq
    rw [he, SurfaceAncestorKey.totalPsi_ofLabels]
    simp only [GluingExpression.decoratedGraph, DecoratedStableGraph.oneVertex_codimension,
      Finsupp.sum_zero_index, zero_add, Pi.add_apply, Finset.sum_add_distrib]
    change (∑ s, k s) + (∑ s, d s) + 0 ≤ (∑ s, d s) + ∑ s, k s
    omega
  | relabel e x ih =>
    have he := ih d beta (k ∘ e) (a ∘ e) ht q hq
    rw [GluingExpression.decoratedGraph, DecoratedStableGraph.relabel_codimension]
    change q.totalPsi + (x.decoratedGraph d).graph.edgeCount ≤
      (x.decoratedGraph d).codimension + ∑ s, k s
    simpa only [Function.comp_def, e.sum_comp k] using he
  | separating x y ihx ihy =>
    obtain ⟨split, _, ht⟩ := Multiset.mem_sum.mp ht
    obtain ⟨b, _, ht⟩ := Multiset.mem_sum.mp ht
    obtain ⟨_, u, hu, rfl⟩ := RationalTerms.mem_scale.mp ht
    obtain ⟨v, hv, w, hw, rfl⟩ := RationalTerms.mem_mul.mp hu
    rw [GluingExpression.decoratedGraph, DecoratedStableGraph.separating_codimension]
    change q.totalPsi + ((x.decoratedGraph d.1).graph.edgeCount +
      (y.decoratedGraph d.2).graph.edgeCount + 1) ≤ _
    rcases Multiset.mem_add.mp hq with hq | hq
    · have he := ihx d.1 split.1 _ _ hv q hq
      have hy := (y.decoratedGraph d.2).edgeCount_le_codimension
      have hk := PsiClasses.sum_separatingLeftPowers_le k
      omega
    · have he := ihy d.2 split.2 _ _ hw q hq
      have hx := (x.decoratedGraph d.1).edgeCount_le_codimension
      have hk := PsiClasses.sum_separatingRightPowers_le k
      omega
  | nonseparating x ih =>
    obtain ⟨b, _, ht⟩ := Multiset.mem_sum.mp ht
    obtain ⟨_, u, hu, rfl⟩ := RationalTerms.mem_scale.mp ht
    have he := ih d beta _ _ hu q hq
    rw [GluingExpression.decoratedGraph, DecoratedStableGraph.nonseparating_codimension]
    change q.totalPsi + ((x.decoratedGraph d).graph.edgeCount + 1) ≤ _
    rw [PsiClasses.sum_nonseparatingPowers] at he
    omega

end AxiomaticGW.SurfaceGenusTwo

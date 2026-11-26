/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.FixedGraphSupport
public import AxiomaticGW.GKM.Fixtures.CurveReplay

/-! # Disjoint exceptional supports on the two-point blowup

On the zero-plane-degree face the pinned target leaves just two edges.
Their endpoint sets are disjoint. This obstructs connected fixed graphs prior
to any integrations, automorphism factors, markings or genus assignments.
-/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoExceptionalGraphSupport
open CurveReplay.TwoBlowups (tables)

/-- The two fixed points on the first exceptional curve are on the true side. -/
def firstExceptional : Fin 5 → Bool := ![false, true, true, false, false]

/-- Actual zero-plane-degree edges, identified by index, both endpoints and full class. -/
theorem exceptional_edges : ∀ t : Fin 5, (tables.edges t).curve 2 = 0 ↔
    (t = 2 ∧ (tables.edges t).source = 1 ∧ (tables.edges t).target = 2 ∧
      (tables.edges t).curve = ![1, 0, 0]) ∨
    (t = 4 ∧ (tables.edges t).source = 3 ∧ (tables.edges t).target = 4 ∧
      (tables.edges t).curve = ![0, 1, 0]) := by decide +kernel

private theorem edge_side : ∀ t : Fin 5, (tables.edges t).curve 2 = 0 →
    firstExceptional (tables.edges t).source = firstExceptional (tables.edges t).target ∧
    ((tables.edges t).curve 0 ≠ 0 → firstExceptional (tables.edges t).source = true) ∧
    ((tables.edges t).curve 1 ≠ 0 → firstExceptional (tables.edges t).source = false) := by
  intro t ht
  rcases (exceptional_edges t).mp ht with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide +kernel

variable {v e : ℕ} (G : FixedGraphSupport tables v e)

/-- Every connected fixed graph of plane degree zero lies on at most one exceptional axis. -/
theorem exceptional_axis (h : G.degree 2 = 0) : G.degree 0 = 0 ∨ G.degree 1 = 0 := by
  have hside := G.constant_on_face 2 h firstExceptional (fun t ht ↦ (edge_side t ht).1)
  have at_end (a : Fin e) :
      firstExceptional (G.image (G.endpoint a 0)) =
      firstExceptional (tables.edges (G.edgeIndex a)).source := by
    rcases G.incident a with ⟨ha, _⟩ | ⟨ha, _⟩
    · rw [ha]
    · rw [ha]
      exact (edge_side _ (G.edge_coordinate_zero 2 h a)).1.symm
  by_cases ha : ∃ a : Fin e, (tables.edges (G.edgeIndex a)).curve 0 ≠ 0
  · obtain ⟨a, ha⟩ := ha
    right
    apply Finset.sum_eq_zero
    intro b _
    suffices hb : (tables.edges (G.edgeIndex b)).curve 1 = 0 by rw [hb, mul_zero]
    by_contra hb
    have hfirst := (edge_side _ (G.edge_coordinate_zero 2 h a)).2.1 ha
    have hsecond := (edge_side _ (G.edge_coordinate_zero 2 h b)).2.2 hb
    have hab := hside (G.endpoint a 0) (G.endpoint b 0)
    simp only [at_end, hfirst, hsecond] at hab
    cases hab
  · left
    apply Finset.sum_eq_zero
    intro b _
    have hb : (tables.edges (G.edgeIndex b)).curve 0 = 0 := by
      by_contra hnonzero
      exact ha ⟨b, hnonzero⟩
    rw [hb, mul_zero]

/-- Exact pre-weighting support on the plane-degree-zero face, including the origin. -/
theorem exceptional_face_support_iff (a b : ℕ) :
    Nonempty (FixedGraphSupport.AtDegree tables ![a, b, 0]) ↔ a = 0 ∨ b = 0 := by
  constructor
  · rintro ⟨v, e, G, hdeg⟩
    have h₂ : G.degree 2 = 0 := congrFun hdeg 2
    have h := exceptional_axis G h₂
    simpa only [hdeg, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h
  · intro h
    cases a with
    | zero =>
      cases b with
      | zero =>
        refine ⟨1, 0, FixedGraphSupport.contractedPoint tables 0, ?_⟩
        rw [FixedGraphSupport.degree_contractedPoint]
        decide +kernel
      | succ b =>
        refine ⟨2, 1, FixedGraphSupport.singleCover tables 4 ⟨b + 1, by omega⟩ false, ?_⟩
        rw [FixedGraphSupport.degree_singleCover]
        funext k
        fin_cases k <;> change (b + 1) * _ = _ <;> simp [tables]
    | succ a =>
      have hb : b = 0 := h.resolve_left (Nat.succ_ne_zero _)
      subst b
      refine ⟨2, 1, FixedGraphSupport.singleCover tables 2 ⟨a + 1, by omega⟩ false, ?_⟩
      rw [FixedGraphSupport.degree_singleCover]
      funext k
      fin_cases k <;> change (a + 1) * _ = _ <;> simp [tables, Matrix.cons_val_two]

/-- The whole open mixed exceptional quadrant has empty connected graph support. -/
theorem mixed_isEmpty (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    IsEmpty (FixedGraphSupport.AtDegree tables ![a, b, 0]) := by
  exact ⟨fun G ↦ ((exceptional_face_support_iff a b).mp ⟨G⟩).elim ha.ne' hb.ne'⟩

/-- The particular class requested by the genus-two application has no connected graph. -/
theorem exceptional_sum_isEmpty : IsEmpty (FixedGraphSupport.AtDegree tables ![1, 1, 0]) :=
  mixed_isEmpty 1 1 (by decide) (by decide)

/-- An indexed sum of fixed-locus classes in any additive target vanishes as soon as
each summand has a connected graph of the given full mixed exceptional class. -/
theorem class_sum_zero {ι A : Type*} [AddCommMonoid A] (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (s : Finset ι) (support : ∀ i ∈ s, Nonempty (FixedGraphSupport.AtDegree tables ![a, b, 0]))
    (contribution : ι → A) :
    ∑ i ∈ s, contribution i = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  obtain ⟨G⟩ := support i hi
  exact False.elim ((mixed_isEmpty a b ha hb).false G)

end AxiomaticGW.GKM.BlowupTwoExceptionalGraphSupport

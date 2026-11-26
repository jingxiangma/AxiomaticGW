/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.F1FiberOneMarkingReplay
public import AxiomaticGW.GKM.Fixtures.F1FiberPairs
public import AxiomaticGW.Surfaces.GenusTwoFewMarkingCounts

/-! # Completeness of the one- and two-marked genus-two fiber reports on F₁ -/

@[expose] public section
namespace AxiomaticGW.GKM.F1Fiber
open SurfaceGenusTwo

/-- The pair of native reports retains the arity in its index. -/
def request : Fin 4 ⊕ Fin 64 → SurfaceQuery .hirzebruchOne :=
  Sum.elim F1FiberOneMarking.requests F1FiberPairs.requests

private theorem frame : ∀ i, (request i).genus = 2 ∧ (request i).beta = ![0, 1] ∧
    (request i).insertions.length ≤ 2 ∧ (request i).DimensionCompatible := by
  decide +kernel

/-- Ordered insertions of a native singleton or pair. -/
def shape (i : Fin 4 ⊕ Fin 64) := (request i).insertions

private theorem shapes_injective : Function.Injective shape := by
  intro i j
  exact (by decide +kernel : ∀ a b, shape a = shape b → a = b) i j

/-- The native reports contain every list allowed by the fiber's virtual dimension. -/
theorem shape_coverage : Finset.univ.image shape = dimensionShapes .hirzebruchOne 2 := by
  apply Finset.eq_of_subset_of_card_le
  · intro m hm
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hg, hb, hn, hd⟩ := frame i
    have he : SurfaceTarget.hirzebruchOne.effective.energy (request i).beta = 2 := by
      rw [hb]
      decide +kernel
    rw [← he, mem_dimensionShapes_iff _ (by omega) _]
    have hq : (⟨2, (request i).beta, shape i⟩ : SurfaceQuery .hirzebruchOne) = request i :=
      (SurfaceQuery.eq_iff _ _).mpr ⟨hg.symm, rfl, rfl⟩
    exact ⟨hn, hq.symm ▸ hd⟩
  · rw [Finset.card_image_of_injective _ shapes_injective, Finset.card_univ, card_dimensionShapes]
    decide +kernel

/-- The same ordered insertion lists apply to either curve class of energy two. -/
theorem unique_insertions {q : SurfaceQuery .hirzebruchOne} (hq : FewMarkingQuery q)
    (he : SurfaceTarget.hirzebruchOne.effective.energy q.beta = 2) :
    ∃! i, shape i = q.insertions := by
  obtain ⟨hg, _, _, hn, hd⟩ := hq
  have hq' : (⟨2, q.beta, q.insertions⟩ : SurfaceQuery .hirzebruchOne) = q :=
    (SurfaceQuery.eq_iff _ _).mpr ⟨hg.symm, rfl, rfl⟩
  have hm : q.insertions ∈ dimensionShapes .hirzebruchOne 2 := by
    rw [← he, mem_dimensionShapes_iff _ (by omega) _, hq']
    exact ⟨hn, hd⟩
  rw [← shape_coverage] at hm
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
  exact ⟨i, hi, fun j hj ↦ shapes_injective (hj.trans hi.symm)⟩

/-- Each dimension-compatible benchmark query in the fiber class has exactly one native index. -/
theorem unique_request {q : SurfaceQuery .hirzebruchOne} (hq : FewMarkingQuery q)
    (hb : q.beta = ![0, 1]) : ∃! i, request i = q := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy q.beta = 2 := by rw [hb]; decide +kernel
  obtain ⟨i, hi, hu⟩ := unique_insertions hq he
  refine ⟨i, (SurfaceQuery.eq_iff _ _).mpr
    ⟨(frame i).1.trans hq.1.symm, (frame i).2.1.trans hb.symm, hi⟩, ?_⟩
  exact fun j hj ↦ hu j (congrArg SurfaceQuery.insertions hj)

end AxiomaticGW.GKM.F1Fiber

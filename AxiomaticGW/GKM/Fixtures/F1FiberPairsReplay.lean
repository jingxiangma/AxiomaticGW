/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.F1FiberCoverage
public import AxiomaticGW.GKM.Fixtures.F1FiberMarkedPairs
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberInteriorPairs

/-! # Reconstruction and native localization of the genus-two fiber suite on F₁ -/

@[expose] public section
namespace AxiomaticGW.GKM
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants
namespace F1FiberPairs

private theorem partition_rows : ∀ i : Fin 64, (∃ j, markedIndices j = i) ∨
    (∃ j, BlowupF1FiberInteriorPairs.index j = i) := by decide +kernel

private theorem interior_binding : ∀ j : Fin 32,
    (requests (BlowupF1FiberInteriorPairs.index j), values (BlowupF1FiberInteriorPairs.index j)) =
      (BlowupF1FiberInteriorPairs.requests j, BlowupF1FiberInteriorPairs.values j) := by
  decide +kernel

/-- Each original pair is certified by a marked equation or its calibrated ancestor reduction. -/
theorem accepted (i : Fin 64) : CheckedDescendant 0 (requests i) (values i) := by
  rcases partition_rows i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact marked_accepted j
  · exact (congrArg (fun r ↦ CheckedDescendant 0 r.1 r.2) (interior_binding j)).mpr
      (.mixed (BlowupF1FiberInteriorPairs.accepted j))

end F1FiberPairs
namespace F1Fiber

/-- The ordinary value at the given arity and ordered request. -/
def value : Fin 4 ⊕ Fin 64 → ℚ := Sum.elim F1FiberOneMarking.values F1FiberPairs.values

/-- The native rational function in both torus characters. -/
noncomputable def equivariant : Fin 4 ⊕ Fin 64 → EquivariantCoefficients.Coefficient :=
  Sum.elim F1FiberOneMarking.equivariant F1FiberPairs.equivariant

/-- Every fiber request in the few-marking benchmark has a unique checked native comparison. -/
theorem unique_comparison {q : SurfaceQuery .hirzebruchOne} (hq : FewMarkingQuery q)
    (hb : q.beta = ![0, 1]) : ∃! i, request i = q ∧ CheckedDescendant 0 q (value i) ∧
      equivariant i = (value i : EquivariantCoefficients.Coefficient) ∧
      EquivariantCoefficients.Specializes (equivariant i) (value i) := by
  obtain ⟨i, rfl, hi⟩ := unique_request hq hb
  refine ⟨i, ⟨rfl, ?_⟩, fun j hj ↦ hi j hj.1⟩
  cases i with
  | inl i => exact ⟨.mixed (F1FiberOneMarking.accepted i),
      F1FiberOneMarking.equivariant_eq_ordinary i, F1FiberOneMarking.specializes i⟩
  | inr i => exact ⟨F1FiberPairs.accepted i,
      F1FiberPairs.equivariant_eq_ordinary i, F1FiberPairs.specializes i⟩

end F1Fiber
end AxiomaticGW.GKM

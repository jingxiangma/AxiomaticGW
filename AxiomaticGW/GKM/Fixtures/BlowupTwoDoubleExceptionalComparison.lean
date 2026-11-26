/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoDoubleExceptionalFewMarkings
public import AxiomaticGW.GKM.Fixtures.F1DoubleExceptionalOneMarkingReplay
public import AxiomaticGW.GKM.Fixtures.F1DoubleExceptionalPairsReplay
public import AxiomaticGW.Surfaces.GenusTwoFewMarkingCounts

/-!
# The two complete doubled exceptional GKM frames compared with F₁

Matching rows preserve genus, curve multiplicity, state labels and the order
and powers of every marking. At these dimension-matched requests the native
fractions are constant. A foreign exceptional insertion has native value zero.
The descendant reconstruction in the cross-surface comparison is on F₁.
-/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoDoubleExceptionalFewMarkings
open EquivariantCoefficients SurfaceGenusTwoBlowupDescendants

/-- Identify the exceptional divisor on the chosen axis with the exceptional divisor of F₁. -/
def projectLabel (axis : Fin 2) : SurfaceBasisLabel .blowupTwo →
    Option (SurfaceBasisLabel .hirzebruchOne)
  | .unit => some .unit
  | .hyperplane => some .hyperplane
  | .point => some .point
  | .exceptional j => if j = axis then some (.exceptional 0) else none

/-- The ordinary label comparison for the two doubled classes, preserving all marking powers. -/
def project? (q : SurfaceQuery .blowupTwo) : Option (SurfaceQuery .hirzebruchOne) := do
  let axis : Fin 2 ← if q.beta = ![2, 0, 0] then some 0
    else if q.beta = ![0, 2, 0] then some 1 else none
  let markings ← q.insertions.mapM fun a ↦ do
    let b ← projectLabel axis a.label
    return (⟨b, a.psi⟩ : SurfaceInsertion .hirzebruchOne)
  return ⟨q.genus, ![2, 0], markings⟩

/-- The checked F₁ request and value selected by a singleton or a pair index. -/
def sourceRow : Fin 4 ⊕ Fin 64 → SurfaceQuery .hirzebruchOne × ℚ
  | .inl j => (F1DoubleExceptionalOneMarking.requests j, F1DoubleExceptionalOneMarking.values j)
  | .inr j => (F1DoubleExceptionalPairs.requests j, F1DoubleExceptionalPairs.values j)

/-- All 210 target rows project to the indicated F₁ query, or have a foreign insertion. -/
theorem projection : ∀ j : Fin 210,
    project? (requests j) = (counterpart j).map (fun c ↦ (sourceRow c).1) ∧
    values j = (counterpart j).elim 0 (fun c ↦ (sourceRow c).2) := by decide +kernel

/-- Each matched native fraction equals the constant calculated by the original F₁ evaluator. -/
theorem matched (j : Fin 210) (c : Fin 4 ⊕ Fin 64) (hc : counterpart j = some c) :
    project? (requests j) = some (sourceRow c).1 ∧
    CheckedDescendant 0 (sourceRow c).1 (values j) ∧
    equivariant j = ((sourceRow c).2 : Coefficient) := by
  obtain ⟨hq, hv⟩ := projection j
  simp only [hc, Option.map_some, Option.elim_some] at hq hv
  refine ⟨hq, ?_, (equivariant_eq_ordinary j).trans (congrArg _ hv)⟩
  rw [hv]
  cases c with
  | inl k => exact .mixed (F1DoubleExceptionalOneMarking.accepted k)
  | inr k => exact F1DoubleExceptionalPairs.accepted k

/-- An unmatched native row has both a failed relabeling and a zero full equivariant function. -/
theorem unmatched (j : Fin 210) (hc : counterpart j = none) :
    project? (requests j) = none ∧ equivariant j = 0 := by
  obtain ⟨hq, hv⟩ := projection j
  simp only [hc, Option.map_none, Option.elim_none] at hq hv
  exact ⟨hq, by rw [equivariant_eq_ordinary, hv, Rat.cast_zero]⟩

/-- Position in the unit, hyperplane, exceptional divisors, point order of the native frame. -/
def labelRank : SurfaceBasisLabel .blowupTwo → ℕ
  | .unit => 0
  | .hyperplane => 1
  | .exceptional i => 2 + i.val
  | .point => 4

/-- Inverse row number on this frame. At a fixed ordered label pair, the first
cotangent power ranges from zero to five minus the two label codimensions. -/
def rowNumber (q : SurfaceQuery .blowupTwo) : ℕ :=
  (if q.beta = ![0, 2, 0] then 0 else 105) + match q.insertions with
  | [a] => labelRank a.label
  | [a, b] => 5 + (∑ l : SurfaceBasisLabel .blowupTwo, ∑ r : SurfaceBasisLabel .blowupTwo,
      if labelRank l < labelRank a.label ∨
        (labelRank l = labelRank a.label ∧ labelRank r < labelRank b.label)
      then 6 - (l.codimension + r.codimension) else 0) + a.psi
  | _ => 0

/-- The constant-time row number recovers each exact request. -/
theorem rowNumber_requests : ∀ j : Fin 210, rowNumber (requests j) = j.val := by decide +kernel

open SurfaceGenusTwo

private theorem frame : ∀ j, FewMarkingQuery (requests j) ∧
    ((requests j).beta = ![2, 0, 0] ∨ (requests j).beta = ![0, 2, 0]) := by
  unfold FewMarkingQuery
  decide +kernel

-- Elaborating membership in the two full filtered surface manifests exceeds the default depth.
set_option maxRecDepth 8192 in
/-- The native requests exhaust exactly the two fixed degree-two classes in the benchmark. -/
theorem complete : Finset.univ.image requests =
    (fewMarkingQueries .blowupTwo).filter (fun q ↦ q.beta = ![2, 0, 0]) ∪
    (fewMarkingQueries .blowupTwo).filter (fun q ↦ q.beta = ![0, 2, 0]) := by
  apply Finset.eq_of_subset_of_card_le
  · intro q h
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    have hf := frame j
    rw [hj] at hf
    simp only [Finset.mem_union, Finset.mem_filter, mem_fewMarkingQueries_iff]
    exact hf.2.elim (fun h ↦ Or.inl ⟨hf.1, h⟩) (fun h ↦ Or.inr ⟨hf.1, h⟩)
  · have inj : Function.Injective requests := fun i j h ↦ Fin.ext
        ((rowNumber_requests i).symm.trans ((congrArg rowNumber h).trans (rowNumber_requests j)))
    have bound (b : SurfaceTarget.blowupTwo.Curve)
        (he : SurfaceTarget.blowupTwo.effective.energy b = 2) :
        ((fewMarkingQueries .blowupTwo).filter (fun q ↦ q.beta = b)).card ≤ 105 := by
      rw [fewMarkingQueries_filter_class b (by omega) (by omega), he]
      apply le_trans Finset.card_image_le
      rw [card_dimensionShapes]
      decide +kernel
    rw [Finset.card_image_of_injective _ inj, Finset.card_univ, Fintype.card_fin]
    let s (b : SurfaceTarget.blowupTwo.Curve) :=
      (fewMarkingQueries .blowupTwo).filter (fun q ↦ q.beta = b)
    let left := s ![2, 0, 0]
    let right := s ![0, 2, 0]
    have hl : left.card ≤ 105 := bound ![2, 0, 0] (by decide +kernel)
    have hr : right.card ≤ 105 := bound ![0, 2, 0] (by decide +kernel)
    change (left ∪ right).card ≤ 210
    calc
      (left ∪ right).card ≤ left.card + right.card := Finset.card_union_le left right
      _ ≤ 105 + 105 := Nat.add_le_add hl hr
      _ = 210 := rfl

end AxiomaticGW.GKM.BlowupTwoDoubleExceptionalFewMarkings

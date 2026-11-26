/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoPsiSupport

/-!
# Selecting the two cotangent powers in a genus-two ancestor reduction

A query of total psi degree at least two either has a square at one marking
or positive powers at two different markings. Both selections are executable
in the existing sorted occurrence frame. State labels travel through the
same equivalence as their powers; repeated insertions remain separate labels.
-/

@[expose] public section

namespace AxiomaticGW

namespace ExtraMarkings

theorem oldLabel_injective {S : Type} (n : ℕ) : Function.Injective (oldLabel (S := S) n) := by
  induction n with
  | zero => exact Function.injective_id
  | succ n ih =>
    intro s t h
    exact ih (Option.some.inj h)

/-- Send both old product labels to the selected distinct occurrences. -/
def twoMarkingFrame (count : ℕ) (h : 2 ≤ count) (i j : Fin count) (_hij : i ≠ j) :
    ExtraMarkings (count - 2) (Fin 2) ≃ Fin count :=
  let e := markingFrame 2 count h 0 i
  e.trans (Equiv.swap (e (oldLabel (count - 2) (1 : Fin 2))) j)

theorem twoMarkingFrame_old_zero (count : ℕ) (h : 2 ≤ count) (i j : Fin count) (hij : i ≠ j) :
    twoMarkingFrame count h i j hij (oldLabel (count - 2) (0 : Fin 2)) = i := by
  let e := markingFrame 2 count h 0 i
  have he : e (oldLabel (count - 2) (0 : Fin 2)) ≠
      e (oldLabel (count - 2) (1 : Fin 2)) := by
    intro hh
    have hh' := oldLabel_injective (count - 2) (e.injective hh)
    exact (by decide : (0 : Fin 2) ≠ 1) hh'
  change Equiv.swap (e (oldLabel (count - 2) (1 : Fin 2))) j
    (e (oldLabel (count - 2) (0 : Fin 2))) = i
  rw [show e (oldLabel (count - 2) (0 : Fin 2)) = i from markingFrame_oldLabel _ _ _ _ _]
  apply Equiv.swap_apply_of_ne_of_ne _ hij
  simpa only [e, markingFrame_oldLabel] using he

theorem twoMarkingFrame_old_one (count : ℕ) (h : 2 ≤ count) (i j : Fin count) (hij : i ≠ j) :
    twoMarkingFrame count h i j hij (oldLabel (count - 2) (1 : Fin 2)) = j :=
  Equiv.swap_apply_left _ _

end ExtraMarkings

namespace SurfaceGenusTwo
variable {X : SurfaceTarget}

/-- Exactly those occurrences to which the square relation can be applied. -/
def squareMarks (q : SurfaceAncestorKey X) : Finset (Fin q.orderedInsertions.length) :=
  Finset.univ.filter fun i ↦ 2 ≤ q.orderedPowers i

/-- The first ordered occurrence whose cotangent power is at least two. -/
def squareMark (q : SurfaceAncestorKey X) (h : (squareMarks q).Nonempty) :
    Fin q.orderedInsertions.length := (squareMarks q).min' h

theorem squareMark_power (q : SurfaceAncestorKey X) (h : (squareMarks q).Nonempty) :
    2 ≤ q.orderedPowers (squareMark q h) :=
  (Finset.mem_filter.mp (Finset.min'_mem _ h)).2

theorem nonprimary_of_highPsi (q : SurfaceAncestorKey X) (hk : 1 < q.totalPsi) :
    ¬q.IsPrimary := by
  intro hp
  have hz := q.totalPsi_eq_zero_iff.mpr hp
  omega

/-- The first positive occurrence; the second will be required to differ from it. -/
def firstProductMark (q : SurfaceAncestorKey X) (hk : 1 < q.totalPsi) :
    Fin q.orderedInsertions.length := q.positiveMark (nonprimary_of_highPsi q hk)

theorem firstProductMark_pos (q : SurfaceAncestorKey X) (hk : 1 < q.totalPsi) :
    0 < q.orderedPowers (firstProductMark q hk) := q.positiveMark_pos _

/-- Positive cotangent occurrences other than the first selected product marking. -/
def otherPositiveMarks (q : SurfaceAncestorKey X) (hk : 1 < q.totalPsi) :
    Finset (Fin q.orderedInsertions.length) :=
  Finset.univ.filter fun i ↦ i ≠ firstProductMark q hk ∧ 0 < q.orderedPowers i

/-- If no individual power reaches two, total degree at least two requires
another positive occurrence. No dimension or curve-class assumption is used. -/
theorem otherPositiveMarks_nonempty (q : SurfaceAncestorKey X) (hk : 1 < q.totalPsi)
    (hs : ¬(squareMarks q).Nonempty) : (otherPositiveMarks q hk).Nonempty := by
  by_contra hn
  have hrest (i : Fin q.orderedInsertions.length) (hi : i ≠ firstProductMark q hk) :
      q.orderedPowers i = 0 := by
    by_contra hz
    apply hn
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, Nat.pos_of_ne_zero hz⟩⟩
  have hsum : q.totalPsi = q.orderedPowers (firstProductMark q hk) := by
    rw [← q.sum_orderedPowers]
    apply Finset.sum_eq_single (firstProductMark q hk)
    · intro i _ hi
      exact hrest i hi
    · intro hi
      exact (hi (Finset.mem_univ _)).elim
  have hsmall : q.orderedPowers (firstProductMark q hk) ≤ 1 := by
    by_contra hh
    apply hs
    exact ⟨firstProductMark q hk, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
  omega

/-- The first other positive occurrence when no individual cotangent power reaches two. -/
def secondProductMark (q : SurfaceAncestorKey X) (hk : 1 < q.totalPsi)
    (hs : ¬(squareMarks q).Nonempty) : Fin q.orderedInsertions.length :=
  (otherPositiveMarks q hk).min' (otherPositiveMarks_nonempty q hk hs)

theorem secondProductMark_properties (q : SurfaceAncestorKey X) (hk : 1 < q.totalPsi)
    (hs : ¬(squareMarks q).Nonempty) :
    secondProductMark q hk hs ≠ firstProductMark q hk ∧
      0 < q.orderedPowers (secondProductMark q hk hs) :=
  (Finset.mem_filter.mp (Finset.min'_mem _ (otherPositiveMarks_nonempty q hk hs))).2

theorem two_le_length (q : SurfaceAncestorKey X) (hk : 1 < q.totalPsi)
    (hs : ¬(squareMarks q).Nonempty) : 2 ≤ q.orderedInsertions.length := by
  have hne := (secondProductMark_properties q hk hs).1
  have hi := (firstProductMark q hk).isLt
  have hj := (secondProductMark q hk hs).isLt
  by_contra hh
  apply hne
  apply Fin.ext
  omega

/-- Identify the square relation's original marking with the selected query occurrence. -/
def squareFrame (q : SurfaceAncestorKey X) (hs : (squareMarks q).Nonempty) :
    ExtraMarkings (q.orderedInsertions.length - 1) (Fin 1) ≃ Fin q.orderedInsertions.length :=
  ExtraMarkings.markingFrame 1 _ (by have h := (squareMark q hs).isLt; omega) 0 (squareMark q hs)

/-- Identify the product relation's two original markings with the selected distinct occurrences. -/
def productFrame (q : SurfaceAncestorKey X) (hk : 1 < q.totalPsi)
    (hs : ¬(squareMarks q).Nonempty) :
    ExtraMarkings (q.orderedInsertions.length - 2) (Fin 2) ≃ Fin q.orderedInsertions.length :=
  ExtraMarkings.twoMarkingFrame _ (two_le_length q hk hs)
    (firstProductMark q hk) (secondProductMark q hk hs)
    (secondProductMark_properties q hk hs).1.symm

theorem squareFrame_old (q : SurfaceAncestorKey X) (hs : (squareMarks q).Nonempty) :
    squareFrame q hs (ExtraMarkings.oldLabel (q.orderedInsertions.length - 1) (0 : Fin 1)) =
      squareMark q hs := ExtraMarkings.markingFrame_oldLabel _ _ _ _ _

theorem productFrame_old_zero (q : SurfaceAncestorKey X) (hk : 1 < q.totalPsi)
    (hs : ¬(squareMarks q).Nonempty) :
    productFrame q hk hs (ExtraMarkings.oldLabel (q.orderedInsertions.length - 2) (0 : Fin 2)) =
      firstProductMark q hk := ExtraMarkings.twoMarkingFrame_old_zero _ _ _ _ _

theorem productFrame_old_one (q : SurfaceAncestorKey X) (hk : 1 < q.totalPsi)
    (hs : ¬(squareMarks q).Nonempty) :
    productFrame q hk hs (ExtraMarkings.oldLabel (q.orderedInsertions.length - 2) (1 : Fin 2)) =
      secondProductMark q hk hs := ExtraMarkings.twoMarkingFrame_old_one _ _ _ _ _

/-- Only retained original labels can carry the extended monomial. -/
theorem markedPowers_zero_or_old {S : Type} (d : S → ℕ) (n : ℕ) (t : ExtraMarkings n S) :
    markedPowers d n t = 0 ∨ ∃ s, t = ExtraMarkings.oldLabel n s := by
  induction n with
  | zero => exact Or.inr ⟨t, rfl⟩
  | succ n ih =>
    cases t with
    | none => exact Or.inl rfl
    | some t =>
      rcases ih t with hz | ⟨s, rfl⟩
      · exact Or.inl hz
      · exact Or.inr ⟨s, rfl⟩

theorem markedPowers_le_of_old {S : Type} (d : S → ℕ) (n : ℕ)
    (k : ExtraMarkings n S → ℕ)
    (hk : ∀ s, d s ≤ k (ExtraMarkings.oldLabel n s)) : markedPowers d n ≤ k := by
  intro t
  rcases markedPowers_zero_or_old d n t with hz | ⟨s, rfl⟩
  · rw [hz]
    exact Nat.zero_le _
  · rw [markedPowers_oldLabel]
    exact hk s

/-- Lower the selected square in the same frame used for state insertions. -/
def squareLowerPowers (q : SurfaceAncestorKey X) (hs : (squareMarks q).Nonempty) :
    ExtraMarkings (q.orderedInsertions.length - 1) (Fin 1) → ℕ :=
  q.orderedPowers ∘ squareFrame q hs -
    markedPowers (fun _ : Fin 1 ↦ 2) (q.orderedInsertions.length - 1)

theorem squareLowerPowers_restore (q : SurfaceAncestorKey X) (hs : (squareMarks q).Nonempty) :
    squareLowerPowers q hs + markedPowers (fun _ : Fin 1 ↦ 2) (q.orderedInsertions.length - 1) =
      q.orderedPowers ∘ squareFrame q hs := by
  have hle := markedPowers_le_of_old (fun _ : Fin 1 ↦ 2) (q.orderedInsertions.length - 1)
    (q.orderedPowers ∘ squareFrame q hs) (by
      intro s
      fin_cases s
      change 2 ≤ q.orderedPowers (squareFrame q hs
        (ExtraMarkings.oldLabel (q.orderedInsertions.length - 1) (0 : Fin 1)))
      rw [squareFrame_old]
      exact squareMark_power q hs)
  funext t
  exact Nat.sub_add_cancel (hle t)

/-- Lower the product at its two distinct selected occurrences. -/
def productLowerPowers (q : SurfaceAncestorKey X) (hk : 1 < q.totalPsi)
    (hs : ¬(squareMarks q).Nonempty) :
    ExtraMarkings (q.orderedInsertions.length - 2) (Fin 2) → ℕ :=
  q.orderedPowers ∘ productFrame q hk hs -
    markedPowers (fun _ : Fin 2 ↦ 1) (q.orderedInsertions.length - 2)

theorem productLowerPowers_restore (q : SurfaceAncestorKey X) (hk : 1 < q.totalPsi)
    (hs : ¬(squareMarks q).Nonempty) :
    productLowerPowers q hk hs + markedPowers (fun _ : Fin 2 ↦ 1)
      (q.orderedInsertions.length - 2) = q.orderedPowers ∘ productFrame q hk hs := by
  have hle := markedPowers_le_of_old (fun _ : Fin 2 ↦ 1) (q.orderedInsertions.length - 2)
    (q.orderedPowers ∘ productFrame q hk hs) (by
      intro s
      fin_cases s
      · change 1 ≤ q.orderedPowers (productFrame q hk hs
          (ExtraMarkings.oldLabel (q.orderedInsertions.length - 2) (0 : Fin 2)))
        rw [productFrame_old_zero]
        exact firstProductMark_pos q hk
      · change 1 ≤ q.orderedPowers (productFrame q hk hs
          (ExtraMarkings.oldLabel (q.orderedInsertions.length - 2) (1 : Fin 2)))
        rw [productFrame_old_one]
        exact (secondProductMark_properties q hk hs).2)
  funext t
  exact Nat.sub_add_cancel (hle t)

theorem sum_squareLowerPowers (q : SurfaceAncestorKey X) (hs : (squareMarks q).Nonempty) :
    (∑ s, squareLowerPowers q hs s) + 2 = q.totalPsi := by
  have he := congrArg (fun k ↦ ∑ s, k s) (squareLowerPowers_restore q hs)
  simpa only [Pi.add_apply, Finset.sum_add_distrib, sum_markedPowers,
    Fin.sum_univ_one, Function.comp_def, Equiv.sum_comp, q.sum_orderedPowers] using he

theorem sum_productLowerPowers (q : SurfaceAncestorKey X) (hk : 1 < q.totalPsi)
    (hs : ¬(squareMarks q).Nonempty) :
    (∑ s, productLowerPowers q hk hs s) + 2 = q.totalPsi := by
  have he := congrArg (fun k ↦ ∑ s, k s) (productLowerPowers_restore q hk hs)
  simpa only [Pi.add_apply, Finset.sum_add_distrib, sum_markedPowers,
    Fin.sum_univ_two, Nat.reduceAdd, Function.comp_def, Equiv.sum_comp,
    q.sum_orderedPowers] using he

end SurfaceGenusTwo
end AxiomaticGW

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoZeroDivisorBenchmark
public import AxiomaticGW.GKM.Fixtures.F1ZeroDivisorPairs

/-! # Localization and seed-free descendant divisor equations on F₁

The native request image is exactly the original divisor benchmark at each
positive energy through four. The complete two-character rational functions
and the marked divisor equations both give zero. The reconstruction uses the
vanishing of both coefficients in the two-term divisor equation.
-/

@[expose] public section

namespace AxiomaticGW.GKM.ZeroDivisorPairsReplay
open SurfaceGenusTwo ZeroDivisorBenchmark

/-- The fixed two-marked manifest orders the effective coordinates, labels, then powers.
Strict increase on this finite frame is sufficient to certify distinct requests. -/
def pairOrder {X : SurfaceTarget} (q : SurfaceQuery X) : ℕ :=
  (List.ofFn q.beta ++ q.insertions.map (fun m ↦ m.label.sortCode) ++
    q.insertions.map SurfaceInsertion.psi).foldl (fun v x ↦ 8 * v + x) 0

/-- The complete seed-free divisor frame retains all four positive-energy slices. -/
def suite (X : SurfaceTarget) : Finset (SurfaceQuery X) :=
  Finset.univ.biUnion (fun j : Fin 4 ↦ rows X (j.val + 1))

private theorem card_suite (X : SurfaceTarget) :
    (suite X).card = ∑ j : Fin 4, (rows X (j.val + 1)).card := by
  apply Finset.card_biUnion
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro q hi hj
  have he := ((mem_rows q _).mp hi).2.1.symm.trans ((mem_rows q _).mp hj).2.1
  exact hij (Fin.ext (Nat.add_right_cancel he))

/-- Inclusion, distinctness and the original four independent counts give exact coverage. -/
theorem coverage_of_frame {X : SurfaceTarget} {n : ℕ} (r : Fin n → SurfaceQuery X)
    (hi : Function.Injective r)
    (hf : ∀ i, FewMarkingQuery (r i) ∧ zeroDivisorPair? (r i) = some 0)
    (hc : (∑ j : Fin 4, (rows X (j.val + 1)).card) = n) :
    Finset.univ.image r = suite X := by
  apply Finset.eq_of_subset_of_card_le
  · intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨h, hz⟩ := hf i
    have hp : X.effective.energy (r i).beta ≠ 0 :=
      fun he ↦ h.2.1 ((X.effective.energy_eq_zero_iff _).mp he)
    have hb := h.2.2.1
    apply Finset.mem_biUnion.mpr
    refine ⟨⟨X.effective.energy (r i).beta - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    exact (mem_rows _ _).mpr ⟨h, by simp only; omega, hz⟩
  · rw [card_suite, hc, Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]

/-- Selecting one energy from the full native suite recovers the original divisor rows. -/
theorem coverage_at_of_suite {X : SurfaceTarget} (qset : Finset (SurfaceQuery X))
    (h : qset = suite X) (j : Fin 4) :
    qset.filter (fun q ↦ X.effective.energy q.beta = j.val + 1) = rows X (j.val + 1) := by
  rw [h]
  ext q
  constructor
  · intro hq
    obtain ⟨hm, he⟩ := Finset.mem_filter.mp hq
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨hf, _, hz⟩ := (mem_rows q _).mp hi
    exact (mem_rows q _).mpr ⟨hf, he, hz⟩
  · intro hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hq⟩,
      ((mem_rows q _).mp hq).2.1⟩

end AxiomaticGW.GKM.ZeroDivisorPairsReplay

namespace AxiomaticGW.GKM.F1ZeroDivisorPairs
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants ZeroDivisorBenchmark

/-- Every imported request has the required dimension, energy, and two vanishing divisor terms. -/
theorem frame (j : Fin 20) :
    FewMarkingQuery (requests j) ∧ zeroDivisorPair? (requests j) = some 0 :=
  (by unfold FewMarkingQuery; decide +kernel :
    ∀ i, FewMarkingQuery (requests i) ∧ zeroDivisorPair? (requests i) = some 0) j

/-- The report retains distinct full classes, insertion order, and powers. -/
theorem requests_injective : Function.Injective requests := by
  have mono : StrictMono (fun i ↦ ZeroDivisorPairsReplay.pairOrder (requests i)) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    decide +kernel
  exact fun _ _ h ↦ mono.injective (congrArg ZeroDivisorPairsReplay.pairOrder h)

theorem coverage : Finset.univ.image requests = ZeroDivisorPairsReplay.suite .hirzebruchOne := by
  apply ZeroDivisorPairsReplay.coverage_of_frame requests requests_injective frame
  simp only [card_rows.1, Fin.sum_univ_four]
  decide +kernel

theorem coverage_at (e : Fin 4) :
    (Finset.univ.image requests).filter
      (fun q ↦ SurfaceTarget.hirzebruchOne.effective.energy q.beta = e.val + 1) =
        rows .hirzebruchOne (e.val + 1) :=
  ZeroDivisorPairsReplay.coverage_at_of_suite _ coverage e

theorem values_zero (j : Fin 20) : values j = 0 := (by decide +kernel : ∀ i, values i = 0) j

/-- The full rational function agrees with zero before ordinary specialization. -/
theorem equivariant_zero (j : Fin 20) : equivariant j = 0 := by
  rw [equivariant_eq_ordinary, values_zero, Rat.cast_zero]

/-- Every original marked divisor evaluator gives exactly the incoming ordinary value. -/
theorem original (pivot : Fin SurfaceTarget.hirzebruchOne.blowups) (j : Fin 20) :
    divisorPairValue? pivot (requests j) = some (values j) := by
  rw [values_zero]
  exact zeroDivisorPair?_original pivot _ (frame j).2

/-- The native comparison has an ordered reconstruction witness at the public pivot. -/
theorem accepted (j : Fin 20) : CheckedDescendant 0 (requests j) (values j) := by
  rw [values_zero]
  exact zeroDivisorPair?_checked 0 _ (frame j).2

/-- The full field, regular specialization, and original divisor evaluator agree at this row. -/
theorem all_accepted (pivot : Fin SurfaceTarget.hirzebruchOne.blowups) (j : Fin 20) :
    equivariant j = 0 ∧ EquivariantCoefficients.Specializes (equivariant j) 0 ∧
      divisorPairValue? pivot (requests j) = some 0 :=
  ⟨equivariant_zero j, (values_zero j) ▸ specializes j, (values_zero j) ▸ original pivot j⟩

end AxiomaticGW.GKM.F1ZeroDivisorPairs

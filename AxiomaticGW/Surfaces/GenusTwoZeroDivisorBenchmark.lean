/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoZeroDivisorPairs
public import AxiomaticGW.Surfaces.GenusTwoFewMarkingDimension

/-! # Seed-independent divisor pairs in the bounded few-marking research suite -/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo.ZeroDivisorBenchmark
variable {X : SurfaceTarget}

/-- Original benchmark slice restricted to the selected ordered divisor pairs. -/
def rows (X : SurfaceTarget) (energy : ℕ) : Finset (SurfaceQuery X) :=
  (fewMarkingsAtEnergy X energy).filter (fun q ↦ zeroDivisorPair? q = some 0)

/-- Membership is precisely the original domain, exact energy and vanishing divisor test. -/
theorem mem_rows (q : SurfaceQuery X) (energy : ℕ) :
    q ∈ rows X energy ↔ FewMarkingQuery q ∧ X.effective.energy q.beta = energy ∧
      zeroDivisorPair? q = some 0 := by
  simp only [rows, Finset.mem_filter, mem_fewMarkingsAtEnergy_iff, and_assoc]

/-- Retain rows outside energy one, F₁ energy two, Bl₂ class E₁+E₂ and exceptional point support.
The predicate describes these specific comparison families at any future level of coverage. -/
def outsideFixedSlices (X : SurfaceTarget) (q : SurfaceQuery X) : Bool :=
  1 < X.effective.energy q.beta && (exceptionalPointQueryValue? q).isNone &&
    match X, q with
    | .hirzebruchOne, q => SurfaceTarget.hirzebruchOne.effective.energy q.beta != 2
    | .blowupTwo, q => q.beta != ![1, 1, 0]
    | .plane, _ => true

/-- Additional ordered divisor pairs after all four named exclusion tests. -/
def additionalRows (X : SurfaceTarget) (energy : ℕ) : Finset (SurfaceQuery X) :=
  (rows X energy).filter (fun q ↦ outsideFixedSlices X q = true)

/-- Exact membership conditions for a row in this addition. -/
theorem mem_additionalRows (q : SurfaceQuery X) (energy : ℕ) :
    q ∈ additionalRows X energy ↔ FewMarkingQuery q ∧ X.effective.energy q.beta = energy ∧
      zeroDivisorPair? q = some 0 ∧ outsideFixedSlices X q = true := by
  simp only [additionalRows, Finset.mem_filter, mem_rows, and_assoc]

/-- Count a predicate over the original full class and ordered query domains, using disjoint
class fibers and dimension shapes to retain the meaning of every counted row. -/
private theorem filtered_card (X : SurfaceTarget) (e : ℕ) (he : 0 < e) (h4 : e ≤ 4)
    (p : SurfaceQuery X → Prop) [DecidablePred p] :
    ((fewMarkingsAtEnergy X e).filter p).card =
      ∑ b ∈ (X.bounded e).filter (fun b ↦ X.effective.energy b = e),
        ((dimensionShapes X e).filter (fun m ↦ p ⟨2, b, m⟩)).card := by
  rw [fewMarkingsAtEnergy_eq_shapes X e he h4, Finset.filter_biUnion]
  simp_rw [Finset.filter_image]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro b _
    exact Finset.card_image_of_injective _ (fun _ _ h ↦ congrArg SurfaceQuery.insertions h)
  · intro b _ c _ hbc
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨_, _, heq⟩ := Finset.mem_image.mp hq'
    exact hbc (congrArg SurfaceQuery.beta heq).symm

/-- Exact numbers of distinct zero divisor pairs in the four original energy slices. -/
theorem card_rows :
    (∀ i : Fin 4, (rows .hirzebruchOne (i.val + 1)).card = ![4, 4, 8, 4] i) ∧
    (∀ i : Fin 4, (rows .blowupTwo (i.val + 1)).card = ![24, 42, 48, 66] i) := by
  constructor <;> intro i <;> rw [rows, filtered_card _ _ (by omega) (by omega)] <;>
    fin_cases i <;> decide +kernel

/-- Distinct additions relative to the named fixed slices and exceptional point support. -/
theorem card_outsideFixedSlices :
    (∀ i : Fin 4, (additionalRows .hirzebruchOne (i.val + 1)).card = ![0, 0, 6, 2] i) ∧
    (∀ i : Fin 4, (additionalRows .blowupTwo (i.val + 1)).card = ![0, 28, 36, 52] i) := by
  constructor <;> intro i <;>
    rw [additionalRows, rows, Finset.filter_filter, filtered_card _ _ (by omega) (by omega)] <;>
    fin_cases i <;> decide +kernel

/-- The union of the new ordered requests across the four permitted positive energies. -/
def additionalSuite (X : SurfaceTarget) : Finset (SurfaceQuery X) :=
  Finset.univ.biUnion (fun i : Fin 4 ↦ additionalRows X (i.val + 1))

/-- The union retains the original full request, the exclusions and the computed zero. -/
theorem mem_additionalSuite (q : SurfaceQuery X) :
    q ∈ additionalSuite X ↔ FewMarkingQuery q ∧ outsideFixedSlices X q = true ∧
      zeroDivisorPair? q = some 0 := by
  simp only [additionalSuite, Finset.mem_biUnion, Finset.mem_univ, true_and, mem_additionalRows]
  constructor
  · rintro ⟨i, hf, _, hz, hout⟩
    exact ⟨hf, hout, hz⟩
  · rintro ⟨hf, hout, hz⟩
    have hbound := hf.2.2.1
    have hpos : X.effective.energy q.beta ≠ 0 :=
      fun h ↦ hf.2.1 ((X.effective.energy_eq_zero_iff _).mp h)
    exact ⟨⟨X.effective.energy q.beta - 1, by omega⟩, hf, by simp only; omega, hz, hout⟩

private theorem card_additionalSuite_eq_sum (X : SurfaceTarget) :
    (additionalSuite X).card = ∑ i : Fin 4, (additionalRows X (i.val + 1)).card := by
  apply Finset.card_biUnion
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro q hi hj
  have he := ((mem_additionalRows q _).mp hi).2.1.symm.trans ((mem_additionalRows q _).mp hj).2.1
  exact hij (Fin.ext (Nat.add_right_cancel he))

/-- New exact query counts relative to the four exclusion families. -/
theorem card_additionalSuite :
    (additionalSuite .hirzebruchOne).card = 8 ∧ (additionalSuite .blowupTwo).card = 116 := by
  constructor
  · simp only [card_additionalSuite_eq_sum, card_outsideFixedSlices.1, Fin.sum_univ_four]
    decide +kernel
  · simp only [card_additionalSuite_eq_sum, card_outsideFixedSlices.2, Fin.sum_univ_four]
    decide +kernel

end AxiomaticGW.SurfaceGenusTwo.ZeroDivisorBenchmark

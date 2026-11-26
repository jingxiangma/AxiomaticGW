/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.F1EnergyTwoReplay
public import AxiomaticGW.GKM.Fixtures.GenusTwoEnergyOneReplay
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoExceptionalFewMarkings
public import Mathlib.Order.Fin.Basic

/-! # Distinct checked genus-two few-marking queries on the two blowup targets

The unions retain the order of the markings and full effective class. A request
proved both by reconstruction and by exceptional point support contributes once.
-/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupFewMarkingCoverage
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

/-- Verified energy-one and energy-two rows and point-supported exceptional requests on F₁. -/
def oneBlowup : Finset (SurfaceQuery .hirzebruchOne) :=
  Finset.univ.image GenusTwoEnergyOne.OneBlowup.requests ∪ Finset.univ.image F1EnergyTwo.request ∪
    Finset.univ.image GenusTwoExceptionalFewMarkings.OneBlowup.requests

/-- Indices of the exceptional point-support frame above energy one on the two-point blowup. -/
def higherSupport : Finset (Fin 514) :=
  Finset.univ.filter fun i ↦
    1 < SurfaceTarget.blowupTwo.effective.energy
      (GenusTwoExceptionalFewMarkings.TwoBlowups.requests i).beta

/-- Verified energy-one rows and higher point-supported requests on the two-point blowup. -/
def twoBlowups : Finset (SurfaceQuery .blowupTwo) :=
  Finset.univ.image GenusTwoEnergyOne.TwoBlowups.requests ∪
    higherSupport.image GenusTwoExceptionalFewMarkings.TwoBlowups.requests

/-- Number of distinct checked requests in the displayed one-point blowup union. -/
theorem card_oneBlowup : oneBlowup.card = 255 := by decide +kernel

-- The native order compares class coordinates, arity, labels and then cotangent powers.
private def orderCode (q : SurfaceQuery .blowupTwo) : ℕ :=
  let label : SurfaceBasisLabel .blowupTwo → ℕ
    | .unit => 0 | .hyperplane => 1 | .exceptional i => i.val + 2 | .point => 4
  let b := (List.ofFn q.beta).foldl (fun n k ↦ 8 * n + k) 0
  let digits := match q.insertions with
    | [a] => [0, label a.label, 0, a.psi, 0]
    | [a, c] => [1, label a.label, label c.label, a.psi, c.psi]
    | _ => []
  digits.foldl (fun n k ↦ 8 * n + k) b

/-- Number of distinct checked requests in the displayed two-point blowup union. -/
theorem card_twoBlowups : twoBlowups.card = 714 := by
  let req := GenusTwoExceptionalFewMarkings.TwoBlowups.requests
  have mono : StrictMono (fun i ↦ orderCode (req i)) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    decide +kernel
  have inj : Function.Injective req := fun _ _ h ↦ mono.injective (congrArg orderCode h)
  have disj : Disjoint (Finset.univ.image GenusTwoEnergyOne.TwoBlowups.requests)
      (higherSupport.image req) := by
    apply Finset.disjoint_left.mpr
    intro q hq hs
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
    rw [GenusTwoEnergyOne.TwoBlowups.coverage] at hq
    have hlow := ((mem_fewMarkingsAtEnergy_iff _ _).mp hq).2
    exact (Finset.mem_filter.mp hi).2.ne' hlow
  change (Finset.univ.image GenusTwoEnergyOne.TwoBlowups.requests ∪
    higherSupport.image req).card = _
  rw [Finset.card_union_of_disjoint disj, Finset.card_image_of_injective _ inj,
    Finset.card_image_of_injective _ GenusTwoEnergyOne.TwoBlowups.requests_injective,
    Finset.card_univ, Fintype.card_fin]
  decide +kernel

private theorem from_energy {X : SurfaceTarget} {ι : Type} [Fintype ι]
    {req : ι → SurfaceQuery X} {v : ι → ℚ} {i : Fin X.blowups} {e : ℕ}
    (coverage : Finset.univ.image req = fewMarkingsAtEnergy X e)
    (accepted : ∀ j, CheckedDescendant i (req j) (v j))
    {q : SurfaceQuery X} (hm : q ∈ Finset.univ.image req) :
    FewMarkingQuery q ∧ ∃ a, CheckedDescendant i q a := by
  refine ⟨((mem_fewMarkingsAtEnergy_iff q e).mp (coverage ▸ hm)).1, ?_⟩
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hm
  exact ⟨v j, accepted j⟩

private theorem from_support {X : SurfaceTarget} {ι : Type} [Fintype ι]
    {req : ι → SurfaceQuery X} {i : Fin X.blowups}
    (accepted : ∀ j, FewMarkingQuery (req j) ∧ exceptionalPointQueryValue? (req j) = some 0)
    {q : SurfaceQuery X} (hm : q ∈ Finset.univ.image req) :
    FewMarkingQuery q ∧ ∃ a, CheckedDescendant i q a := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hm
  exact ⟨(accepted j).1, 0, .exceptionalPoint (accepted j).2⟩

/-- Every counted query on F₁ has a proof at its original ordered input. -/
theorem oneBlowup_checked {q : SurfaceQuery .hirzebruchOne} (h : q ∈ oneBlowup) :
    FewMarkingQuery q ∧ ∃ a, CheckedDescendant 0 q a := by
  rcases Finset.mem_union.mp h with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact from_energy GenusTwoEnergyOne.OneBlowup.coverage GenusTwoEnergyOne.OneBlowup.accepted h
    · exact from_energy F1EnergyTwo.coverage (fun i ↦ (F1EnergyTwo.accepted i).1) h
  · exact from_support GenusTwoExceptionalFewMarkings.OneBlowup.accepted h

/-- Every counted query on the two-point blowup has a proof at its original ordered input. -/
theorem twoBlowups_checked {q : SurfaceQuery .blowupTwo} (h : q ∈ twoBlowups) :
    FewMarkingQuery q ∧ ∃ a, CheckedDescendant 0 q a := by
  rcases Finset.mem_union.mp h with h | h
  · exact from_energy GenusTwoEnergyOne.TwoBlowups.coverage GenusTwoEnergyOne.TwoBlowups.accepted h
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact ⟨(GenusTwoExceptionalFewMarkings.TwoBlowups.accepted i).1, 0,
      .exceptionalPoint (GenusTwoExceptionalFewMarkings.TwoBlowups.accepted i).2⟩

end AxiomaticGW.GKM.BlowupFewMarkingCoverage

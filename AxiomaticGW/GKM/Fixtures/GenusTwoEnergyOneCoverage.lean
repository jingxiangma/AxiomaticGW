/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.GenusTwoEnergyOneClaims
public import AxiomaticGW.Surfaces.GenusTwoFewMarkingCounts

/-! # Completeness of the energy-one genus-two localization frame

The query sets are compared with the original mathematical benchmark including
the full effective class, the order of both markings and their powers.
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoEnergyOne
open SurfaceGenusTwo

/-- The plane has no effective curve of anticanonical energy one. -/
theorem plane_empty : fewMarkingsAtEnergy .plane 1 = ∅ := by
  rw [fewMarkingsAtEnergy_eq_shapes .plane 1 (by decide) (by decide)]
  decide +kernel

private def labelIndex {X : SurfaceTarget} : SurfaceBasisLabel X → ℕ
  | .unit => 0
  | .hyperplane => 1
  | .exceptional j => j.val + 2
  | .point => X.blowups + 2

-- Count all preceding ordered labels, then locate the first cotangent power within its pair.
private def rowIndex {X : SurfaceTarget} (q : SurfaceQuery X) : ℕ :=
  let n := X.blowups + 3
  let c := fun j : ℕ ↦ if j = 0 then 0 else if j + 1 = n then 2 else 1
  let rows := fun i j ↦ 5 - (c i + c j)
  match q.insertions with
  | [a] => labelIndex a.label
  | [a,b] => n + (∑ i ∈ Finset.range (labelIndex a.label), ∑ j ∈ Finset.range n, rows i j) +
      (∑ j ∈ Finset.range (labelIndex b.label), rows (labelIndex a.label) j) + a.psi
  | _ => 0

private theorem one_inverse : ∀ i : Fin 52, rowIndex (OneBlowup.requests i) = i.val := by
  decide +kernel

private def twoIndex (q : SurfaceQuery .blowupTwo) : ℕ :=
  80 * (2 * q.beta 0 + q.beta 1) + rowIndex q

private theorem two_inverse : ∀ i : Fin 240, twoIndex (TwoBlowups.requests i) = i.val := by
  decide +kernel

private theorem covers {X : SurfaceTarget} {n : ℕ} (requests : Fin n → SurfaceQuery X)
    (inj : Function.Injective requests)
    (hm : ∀ i, FewMarkingQuery (requests i) ∧ X.effective.energy (requests i).beta = 1)
    (hc : (fewMarkingsAtEnergy X 1).card = n) :
    Finset.univ.image requests = fewMarkingsAtEnergy X 1 := by
  apply Finset.eq_of_subset_of_card_le
  · intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact (mem_fewMarkingsAtEnergy_iff _ _).mpr (hm i)
  · rw [hc, Finset.card_image_of_injective _ inj, Finset.card_univ, Fintype.card_fin]

/-- Distinct native indices on the first blowup give distinct ordered requests. -/
theorem OneBlowup.requests_injective : Function.Injective OneBlowup.requests := by
  intro i j h
  exact Fin.ext ((one_inverse i).symm.trans ((congrArg rowIndex h).trans (one_inverse j)))

/-- All 52 one-point blowup requests are present. -/
theorem OneBlowup.coverage : Finset.univ.image OneBlowup.requests =
    fewMarkingsAtEnergy .hirzebruchOne 1 := by
  apply covers _ OneBlowup.requests_injective
  · unfold FewMarkingQuery
    decide +kernel
  · rw [card_fewMarkingsAtEnergy _ _ (by decide), card_dimensionShapes]
    decide +kernel

/-- Distinct native indices on the second blowup retain the class as well as both markings. -/
theorem TwoBlowups.requests_injective : Function.Injective TwoBlowups.requests := by
  intro i j h
  exact Fin.ext ((two_inverse i).symm.trans ((congrArg twoIndex h).trans (two_inverse j)))

/-- The 240 two-point blowup requests distinguish both exceptionals and their strict line. -/
theorem TwoBlowups.coverage : Finset.univ.image TwoBlowups.requests =
    fewMarkingsAtEnergy .blowupTwo 1 := by
  apply covers _ TwoBlowups.requests_injective
  · unfold FewMarkingQuery
    decide +kernel
  · rw [card_fewMarkingsAtEnergy _ _ (by decide), card_dimensionShapes]
    decide +kernel

end AxiomaticGW.GKM.GenusTwoEnergyOne

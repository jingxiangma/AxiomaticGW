/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.F1FiberCoverage
public import AxiomaticGW.GKM.Fixtures.F1DoubleExceptionalOneMarking
public import AxiomaticGW.GKM.Fixtures.F1DoubleExceptionalPairs

/-! # Completeness of the genus-two localization frame at anticanonical energy two on F₁

The two curve classes have the same dimension-compatible ordered insertion lists.
The full class in every row distinguishes the fiber from twice the exceptional curve.
-/

@[expose] public section
namespace AxiomaticGW.GKM.F1EnergyTwo
open SurfaceGenusTwo

/-- Left indices refer to the fiber, right indices to twice the exceptional curve. -/
abbrev Row := (Fin 4 ⊕ Fin 64) ⊕ (Fin 4 ⊕ Fin 64)

/-- The original ordered request at each of the 136 native rows. -/
def request : Row → SurfaceQuery .hirzebruchOne :=
  Sum.elim F1Fiber.request
    (Sum.elim F1DoubleExceptionalOneMarking.requests F1DoubleExceptionalPairs.requests)

/-- Every incoming query is distinct, including requests with the same shape at the other class. -/
theorem requests_injective : Function.Injective request := by
  intro i j
  exact (by decide +kernel : ∀ a b : Row, request a = request b → a = b) i j

/-- The 136 incoming requests are exactly the complete mathematical energy-two slice. -/
theorem coverage : Finset.univ.image request = fewMarkingsAtEnergy .hirzebruchOne 2 := by
  apply Finset.eq_of_subset_of_card_le
  · intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    apply (mem_fewMarkingsAtEnergy_iff _ _).mpr
    have h : ∀ j, FewMarkingQuery (request j) ∧
        SurfaceTarget.hirzebruchOne.effective.energy (request j).beta = 2 := by
      unfold FewMarkingQuery
      decide +kernel
    exact h i
  · rw [Finset.card_image_of_injective _ requests_injective, Finset.card_univ,
      card_fewMarkingsAtEnergy _ _ (by decide), card_dimensionShapes]
    decide +kernel

end AxiomaticGW.GKM.F1EnergyTwo

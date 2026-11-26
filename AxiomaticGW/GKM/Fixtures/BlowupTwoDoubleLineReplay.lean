/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoEnergyTwoSingletonComparison
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineOneMarking

/-! # Original two-point-blowup reconstruction and localization in the class 2L -/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoDoubleLineReplay
open BlowupTwoPositivePlaneEnergyTwoSingletons (index)
open SurfaceGenusTwoBlowupDescendants EquivariantCoefficients

/-- The five singletons in the incoming strict-line sector. -/
abbrev requests (j : Fin 5) := BlowupTwoPositivePlaneEnergyTwoSingletons.requests (index 0 j)

/-- The ordinary constants read from those same native rows. -/
abbrev values (j : Fin 5) := BlowupTwoPositivePlaneEnergyTwoSingletons.values (index 0 j)

private theorem binding : ∀ j : Fin 5,
    let a : SurfaceBasisLabel .blowupTwo := ![.unit, .hyperplane, .exceptional 0,
      .exceptional 1, .point] j
    (requests j, values j) = (BlowupTwoDoubleLine.request a, BlowupTwoDoubleLine.value a) := by
  decide +kernel

/-- Every ordinary value has a witness from the original Bl₂ reconstruction in the same class. -/
theorem accepted (j : Fin 5) : CheckedDescendant 0 (requests j) (values j) := by
  exact (congrArg (fun p ↦ CheckedDescendant 0 p.1 p.2) (binding j)).mpr
    (BlowupTwoDoubleLine.checked _)

/-- The original reconstruction agrees with the exact two-character field and its specialization. -/
theorem certified (j : Fin 5) : CheckedDescendant 0 (requests j) (values j) ∧
    BlowupTwoPositivePlaneEnergyTwoSingletons.equivariant (index 0 j) = (values j : Coefficient) ∧
    Specializes (BlowupTwoPositivePlaneEnergyTwoSingletons.equivariant (index 0 j)) (values j) :=
  ⟨accepted j, BlowupTwoPositivePlaneEnergyTwoSingletons.equivariant_eq_ordinary _,
    BlowupTwoPositivePlaneEnergyTwoSingletons.specializes _⟩

end AxiomaticGW.GKM.BlowupTwoDoubleLineReplay

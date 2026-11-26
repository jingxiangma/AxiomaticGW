/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneLineBoundarySplitting

/-! # Regression checks for the stabilized positive-degree plane packet -/

@[expose] public section
namespace AxiomaticGWTest.GKM.PlaneLineBoundaryClass
open AxiomaticGW AxiomaticGW.GKM GKM.PlaneLineBoundaryData GKM.PlaneLineBoundaryClass
open GKM.EquivariantCoefficients

/-- The positive-degree request has a nonzero raw boundary representative of codimension one. -/
theorem nonzero_divisor : baseClass ≠ 0 ∧ (WDVV.columns 0).codimension = 1 := by
  exact ⟨Finsupp.single_ne_zero.mpr one_ne_zero, WDVV.graph_codimension 0⟩

/-- Exchanging the middle two external labels changes the labelled output graph. -/
theorem swapped_labels_rejected :
    TautologicalStratum.mk baseGraph (by decide +kernel) ≠ WDVV.columns 1 := by
  rw [base_column]
  exact fun h ↦ (by decide : (0 : Fin 3) ≠ 1) (WDVV.columns_injective h)

/-- Dropping the other branch while retaining its partner leaves a genuine equivariant pole. -/
theorem individual_pole_rejected (q : ℚ) : ¬Specializes psiLeft q := by
  change ¬Specializes (1 / y) q
  rw [one_div]
  apply not_specializes_inverse (MvPolynomial.X 1) y_ne_zero
  exact MvPolynomial.eval₂Hom_X' _ _ _

/-- Putting the unit on the other endpoint changes the labelled five-point graph. -/
theorem merged_unit_placements_rejected :
    (unitGraph 0 0).isomorphic? (unitGraph 1 0) = false := by decide +kernel

end AxiomaticGWTest.GKM.PlaneLineBoundaryClass

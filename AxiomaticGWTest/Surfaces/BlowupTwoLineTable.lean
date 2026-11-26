module

import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineTable

/-! # Regression checks for the complete energy-one grid on the two-point blowup -/

namespace AxiomaticGWTest.BlowupTwoLineTable
open AxiomaticGW SurfaceGenusTwoBlowupBoundedCertificate BlowupTwoLineTable BlowupTwoLineBP

/-- The primary and the second exceptional descendant use distinct columns at the same class. -/
example : SurfaceGenusTwoBlowupRecursion.values 0 (line, .primary) =
    SurfaceGenusTwoBlowupRecursion.values 0 (line, .exceptional 1) :=
  primary_eq_hyperplane.trans (family_eq_hyperplane (.exceptional 1)).symm

/-- Two incompatible numerical claims cannot both pass all twenty rows. -/
example : ¬ (checkTable (X := .blowupTwo) 0 1 (candidate 0) = true ∧
    checkTable (X := .blowupTwo) 0 1 (candidate 1) = true) := by
  intro ⟨hz, ho⟩
  have h := ((accepted_iff 0).mp hz).trans ((accepted_iff 1).mp ho).symm
  exact (by decide : (0 : ℚ) ≠ 1) h

end AxiomaticGWTest.BlowupTwoLineTable

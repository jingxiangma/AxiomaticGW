/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.FirstCalibration

/-!
# Incoming GKM first-calibration matrix replay

Input SHA256: e50d50dc43b8be23e15a33234503157cdc2fd293774555dc0339d0d7ee52474c
The digest is provenance only. Kernel checks bind ordinary entries to the
held surface values, full classes and fixed inverse-loop/psi indexing.
Equivariant specialization is checked separately by exact Python arithmetic.
No localization theorem, CohFT class or symplecticity is asserted.
-/

@[expose] public section

namespace AxiomaticGW.GKM.FirstCalibrationReplay

namespace Plane

/-- Actual incoming full curve coordinates. -/
def classes : Fin 1 → SurfaceTarget.Curve .plane :=
  ![![1]]

/-- The actual incoming order of homogeneous basis labels. -/
def labels : Fin 3 → SurfaceBasisLabel .plane :=
  ![.unit, .hyperplane, .point]

/-- Imported ordinary operator entries, with rows as output coordinates. -/
def entries : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ :=
  ![![![0, 0, 1],
    ![0, 0, 0],
    ![0, 0, 0]]]

/-- Imported inverse-loop powers. -/
def powers : Fin 1 → ℕ :=
  ![1]

/-- Imported powers at the retained tail marking. -/
def psiPowers : Fin 1 → ℕ :=
  ![0]

/-- Every basis state appears exactly once. -/
theorem labels_bijective : Function.Bijective labels := by decide +kernel

/-- Every positive class of energy at most three is present. -/
theorem coverage : Finset.univ.image classes =
    (SurfaceTarget.bounded .plane 3).erase 0 := by decide +kernel

/-- The incoming cotangent powers are precisely the first calibration coefficient. -/
theorem indices : ∀ i, powers i = 1 ∧ psiPowers i = 0 := by decide +kernel

/-- Every incoming entry agrees with the independently held sparse claim. -/
theorem accepted : ∀ i row col, entries i row col =
    SurfaceFirstCalibration.values .plane (classes i) (labels row) (labels col) := by
  decide +kernel

/-- Accepted incoming entries equal the proved primary reconstruction. -/
theorem reconstructed (i row col) : entries i row col =
    SurfaceDescendant.firstCalibrationMatrix .plane (classes i)
      (labels row) (labels col) := by
  rw [accepted, SurfaceFirstCalibration.values_eq]

end Plane

namespace OneBlowup

/-- Actual incoming full curve coordinates. -/
def classes : Fin 5 → SurfaceTarget.Curve .hirzebruchOne :=
  ![![0, 1],
    ![1, 0],
    ![1, 1],
    ![2, 0],
    ![3, 0]]

/-- The actual incoming order of homogeneous basis labels. -/
def labels : Fin 4 → SurfaceBasisLabel .hirzebruchOne :=
  ![.unit, .hyperplane, .exceptional 0, .point]

/-- Imported ordinary operator entries, with rows as output coordinates. -/
def entries : Fin 5 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![![![0, 1, 1, 0],
    ![0, 0, 0, 1],
    ![0, 0, 0, -1],
    ![0, 0, 0, 0]],
    ![![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, -1, 0],
    ![0, 0, 0, 0]],
    ![![0, 0, 0, 1],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]],
    ![![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]],
    ![![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]]

/-- Imported inverse-loop powers. -/
def powers : Fin 5 → ℕ :=
  ![1, 1, 1, 1, 1]

/-- Imported powers at the retained tail marking. -/
def psiPowers : Fin 5 → ℕ :=
  ![0, 0, 0, 0, 0]

/-- Every basis state appears exactly once. -/
theorem labels_bijective : Function.Bijective labels := by decide +kernel

/-- Every positive class of energy at most three is present. -/
theorem coverage : Finset.univ.image classes =
    (SurfaceTarget.bounded .hirzebruchOne 3).erase 0 := by decide +kernel

/-- The incoming cotangent powers are precisely the first calibration coefficient. -/
theorem indices : ∀ i, powers i = 1 ∧ psiPowers i = 0 := by decide +kernel

/-- Every incoming entry agrees with the independently held sparse claim. -/
theorem accepted : ∀ i row col, entries i row col =
    SurfaceFirstCalibration.values .hirzebruchOne (classes i) (labels row) (labels col) := by
  decide +kernel

/-- Accepted incoming entries equal the proved primary reconstruction. -/
theorem reconstructed (i row col) : entries i row col =
    SurfaceDescendant.firstCalibrationMatrix .hirzebruchOne (classes i)
      (labels row) (labels col) := by
  rw [accepted, SurfaceFirstCalibration.values_eq]

end OneBlowup

namespace TwoBlowups

/-- Actual incoming full curve coordinates. -/
def classes : Fin 19 → SurfaceTarget.Curve .blowupTwo :=
  ![![0, 0, 1],
    ![0, 0, 2],
    ![0, 0, 3],
    ![0, 1, 0],
    ![0, 1, 1],
    ![0, 1, 2],
    ![0, 2, 0],
    ![0, 2, 1],
    ![0, 3, 0],
    ![1, 0, 0],
    ![1, 0, 1],
    ![1, 0, 2],
    ![1, 1, 0],
    ![1, 1, 1],
    ![1, 2, 0],
    ![2, 0, 0],
    ![2, 0, 1],
    ![2, 1, 0],
    ![3, 0, 0]]

/-- The actual incoming order of homogeneous basis labels. -/
def labels : Fin 5 → SurfaceBasisLabel .blowupTwo :=
  ![.unit, .hyperplane, .exceptional 0, .exceptional 1, .point]

/-- Imported ordinary operator entries, with rows as output coordinates. -/
def entries : Fin 19 → Matrix (Fin 5) (Fin 5) ℚ :=
  ![![![0, 0, 0, 0, 0],
    ![0, 1, 1, 1, 0],
    ![0, -1, -1, -1, 0],
    ![0, -1, -1, -1, 0],
    ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0]],
    ![![0, 1, 1, 0, 0],
    ![0, 0, 0, 0, 1],
    ![0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]],
    ![![0, 1, 0, 1, 0],
    ![0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]]]

/-- Imported inverse-loop powers. -/
def powers : Fin 19 → ℕ :=
  ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

/-- Imported powers at the retained tail marking. -/
def psiPowers : Fin 19 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Every basis state appears exactly once. -/
theorem labels_bijective : Function.Bijective labels := by decide +kernel

/-- Every positive class of energy at most three is present. -/
theorem coverage : Finset.univ.image classes =
    (SurfaceTarget.bounded .blowupTwo 3).erase 0 := by decide +kernel

/-- The incoming cotangent powers are precisely the first calibration coefficient. -/
theorem indices : ∀ i, powers i = 1 ∧ psiPowers i = 0 := by decide +kernel

/-- Every incoming entry agrees with the independently held sparse claim. -/
theorem accepted : ∀ i row col, entries i row col =
    SurfaceFirstCalibration.values .blowupTwo (classes i) (labels row) (labels col) := by
  decide +kernel

/-- Accepted incoming entries equal the proved primary reconstruction. -/
theorem reconstructed (i row col) : entries i row col =
    SurfaceDescendant.firstCalibrationMatrix .blowupTwo (classes i)
      (labels row) (labels col) := by
  rw [accepted, SurfaceFirstCalibration.values_eq]

end TwoBlowups

end AxiomaticGW.GKM.FirstCalibrationReplay

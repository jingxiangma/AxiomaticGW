/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.HigherCalibration

/-!
# Native GKM higher-calibration replay

Input SHA256: 2cd61d6748927f230448f842136d26f176afc194a1c3b75b8a944367e153372a
Actual incoming matrices are checked against the derived recursion.
The digest records provenance; it is not a proof of localization geometry.
-/

@[expose] public section

namespace AxiomaticGW.GKM.HigherCalibrationReplay

namespace Plane

/-- Incoming powers and full curve coordinates. -/
def requests : Fin 6 → ℕ × SurfaceTarget.Curve .plane :=
  ![(2, ![1]),
    (3, ![1]),
    (4, ![1]),
    (5, ![1]),
    (6, ![1]),
    (4, ![2])]

/-- Incoming basis order. -/
def labels : Fin 3 → SurfaceBasisLabel .plane :=
  ![.unit, .hyperplane, .point]

/-- Actual imported ordinary matrices. -/
def entries : Fin 6 → Matrix (Fin 3) (Fin 3) ℚ :=
  ![![![0, -1, 0],
    ![0, 0, 1],
    ![0, 0, 0]],
    ![![1, 0, 0],
    ![0, -2, 0],
    ![0, 0, 1]],
    ![![0, 0, 0],
    ![3, 0, 0],
    ![0, -3, 0]],
    ![![0, 0, 0],
    ![0, 0, 0],
    ![6, 0, 0]],
    ![![0, 0, 0],
    ![0, 0, 0],
    ![0, 0, 0]],
    ![![0, 0, (1 / 2)],
    ![0, 0, 0],
    ![0, 0, 0]]]

/-- Actual incoming cotangent powers. -/
def psiPowers : Fin 6 → ℕ :=
  ![1, 2, 3, 4, 5, 3]

theorem labels_bijective : Function.Bijective labels := by decide +kernel

/-- Requests agree with the separately held benchmark suite. -/
theorem coverage : Finset.univ.image requests =
    (SurfaceHigherCalibration.requests .plane).toFinset := by decide +kernel

theorem indices : ∀ i, psiPowers i + 1 = (requests i).1 := by decide +kernel

/-- Each incoming entry is checked at its actual class and loop power. -/
theorem accepted : ∀ i row col, entries i row col =
    SurfaceDescendant.reconstructedCalibrationMatrix .plane
      (requests i).1 (requests i).2 (labels row) (labels col) := by
  decide +kernel

end Plane

namespace OneBlowup

/-- Incoming powers and full curve coordinates. -/
def requests : Fin 8 → ℕ × SurfaceTarget.Curve .hirzebruchOne :=
  ![(2, ![1, 0]),
    (3, ![1, 0]),
    (2, ![0, 1]),
    (3, ![0, 1]),
    (2, ![1, 1]),
    (3, ![1, 1]),
    (2, ![2, 0]),
    (3, ![2, 0])]

/-- Incoming basis order. -/
def labels : Fin 4 → SurfaceBasisLabel .hirzebruchOne :=
  ![.unit, .hyperplane, .exceptional 0, .point]

/-- Actual imported ordinary matrices. -/
def entries : Fin 8 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![![![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![-1, 0, 0, 0],
    ![0, 0, -1, 0]],
    ![![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![-2, 0, 0, 0]],
    ![![-1, 0, 0, 0],
    ![0, 0, 1, 0],
    ![0, 1, 0, 0],
    ![0, 0, 0, 1]],
    ![![0, 0, 0, 0],
    ![-1, 0, 0, 0],
    ![-1, 0, 0, 0],
    ![0, -1, 1, 0]],
    ![![0, -1, -1, 0],
    ![0, 0, 0, 1],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]],
    ![![0, 0, 0, 0],
    ![0, -2, -2, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 1]],
    ![![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, (1 / 2), 0],
    ![0, 0, 0, 0]],
    ![![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![(3 / 4), 0, 0, 0],
    ![0, 0, (1 / 4), 0]]]

/-- Actual incoming cotangent powers. -/
def psiPowers : Fin 8 → ℕ :=
  ![1, 2, 1, 2, 1, 2, 1, 2]

theorem labels_bijective : Function.Bijective labels := by decide +kernel

/-- Requests agree with the separately held benchmark suite. -/
theorem coverage : Finset.univ.image requests =
    (SurfaceHigherCalibration.requests .hirzebruchOne).toFinset := by decide +kernel

theorem indices : ∀ i, psiPowers i + 1 = (requests i).1 := by decide +kernel

/-- Each incoming entry is checked at its actual class and loop power. -/
theorem accepted : ∀ i row col, entries i row col =
    SurfaceDescendant.reconstructedCalibrationMatrix .hirzebruchOne
      (requests i).1 (requests i).2 (labels row) (labels col) := by
  decide +kernel

end OneBlowup

namespace TwoBlowups

/-- Incoming powers and full curve coordinates. -/
def requests : Fin 16 → ℕ × SurfaceTarget.Curve .blowupTwo :=
  ![(2, ![1, 0, 0]),
    (3, ![1, 0, 0]),
    (2, ![0, 1, 0]),
    (3, ![0, 1, 0]),
    (2, ![0, 0, 1]),
    (3, ![0, 0, 1]),
    (2, ![0, 1, 1]),
    (3, ![0, 1, 1]),
    (2, ![1, 0, 1]),
    (3, ![1, 0, 1]),
    (2, ![1, 1, 1]),
    (3, ![1, 1, 1]),
    (2, ![2, 0, 0]),
    (3, ![2, 0, 0]),
    (2, ![0, 2, 0]),
    (3, ![0, 2, 0])]

/-- Incoming basis order. -/
def labels : Fin 5 → SurfaceBasisLabel .blowupTwo :=
  ![.unit, .hyperplane, .exceptional 0, .exceptional 1, .point]

/-- Actual imported ordinary matrices. -/
def entries : Fin 16 → Matrix (Fin 5) (Fin 5) ℚ :=
  ![![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![-1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, -1, 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![-2, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![-1, 0, 0, 0, 0],
    ![0, 0, 0, -1, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![-2, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![-1, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0],
    ![0, 1, 1, 1, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![-2, 0, 0, 0, 0]],
    ![![-1, 0, 0, 0, 0],
    ![0, 0, 1, -1, 0],
    ![0, 1, 0, 1, 0],
    ![0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 1]],
    ![![0, 0, 0, 0, 0],
    ![-2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0],
    ![0, -1, 1, -1, 0]],
    ![![-1, 0, 0, 0, 0],
    ![0, 0, -1, 1, 0],
    ![0, 0, 1, 0, 0],
    ![0, 1, 1, 0, 0],
    ![0, 0, 0, 0, 1]],
    ![![0, 0, 0, 0, 0],
    ![-2, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, -1, -1, 1, 0]],
    ![![0, -1, -1, -1, 0],
    ![0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]],
    ![![-1, 0, 0, 0, 0],
    ![0, -2, -2, -2, 0],
    ![0, 0, 1, 0, 0],
    ![0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 1]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, (1 / 2), 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![(3 / 4), 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, (1 / 4), 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, (1 / 2), 0],
    ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0],
    ![(3 / 4), 0, 0, 0, 0],
    ![0, 0, 0, (1 / 4), 0]]]

/-- Actual incoming cotangent powers. -/
def psiPowers : Fin 16 → ℕ :=
  ![1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2]

theorem labels_bijective : Function.Bijective labels := by decide +kernel

/-- Requests agree with the separately held benchmark suite. -/
theorem coverage : Finset.univ.image requests =
    (SurfaceHigherCalibration.requests .blowupTwo).toFinset := by decide +kernel

theorem indices : ∀ i, psiPowers i + 1 = (requests i).1 := by decide +kernel

/-- Each incoming entry is checked at its actual class and loop power. -/
theorem accepted : ∀ i row col, entries i row col =
    SurfaceDescendant.reconstructedCalibrationMatrix .blowupTwo
      (requests i).1 (requests i).2 (labels row) (labels col) := by
  decide +kernel

end TwoBlowups

end AxiomaticGW.GKM.HigherCalibrationReplay

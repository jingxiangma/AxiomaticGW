/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoPrimaryConstantSymmetry
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CertifiedPoints
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHRequest
public import AxiomaticGW.Surfaces.GenusTwoBlowupPointCache

/-!
# Lower-genus BP constants for the first F1 fiber

The point and exceptional rows have source F. The primary row combines four
BP constants at E+F, with coefficients 3/2, −1, 1/2 and −1/3. The dimension
formula selects the point distribution at each separating node. The original
BP rational weights, full curve splittings and six marking assignments remain
in the calculation.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberBPValues
open BlowupF1CertifiedPoints BelorousskiPandharipande BlowupF1FiberHReduction

-- The six kernel evaluations run successively to bound memory.
set_option Elab.async false
set_option maxRecDepth 20000

/-- The HHH request for the point-descendant row. -/
theorem p_constant_computed :
    lowerPointConstantWithPrimary .hirzebruchOne rational elliptic
      1 ![0, 1] (fun _ ↦ .hyperplane) = 1 / 120 := by
  rw [lowerPointConstantWithPrimary_eq_six_primaryGraphSum]
  decide +kernel

/-- The EEE request for the exceptional-descendant row. -/
theorem k_constant_computed :
    lowerPointConstantWithPrimary .hirzebruchOne rational elliptic
      1 ![0, 1] (fun _ ↦ .exceptional 0) = 1 / 120 := by
  rw [lowerPointConstantWithPrimary_eq_six_primaryGraphSum]
  decide +kernel

/-- All six ordered assignments of EHH at the shifted source. -/
theorem n_ehh_constant_computed :
    lowerPointConstantWithPrimary .hirzebruchOne rational elliptic
      2 ![1, 1] ![.exceptional 0, .hyperplane, .hyperplane] = 0 := by
  rw [lowerPointConstantWithPrimary_eq_primaryGraphSum]
  decide +kernel

/-- All six ordered assignments of EEH at the shifted source. -/
theorem n_eeh_constant_computed :
    lowerPointConstantWithPrimary .hirzebruchOne rational elliptic
      2 ![1, 1] ![.exceptional 0, .exceptional 0, .hyperplane] = 0 := by
  rw [lowerPointConstantWithPrimary_eq_primaryGraphSum]
  decide +kernel

/-- The EEE request with two added points at the shifted source. -/
theorem n_eee_constant_computed :
    lowerPointConstantWithPrimary .hirzebruchOne rational elliptic
      2 ![1, 1] (fun _ ↦ .exceptional 0) = 0 := by
  rw [lowerPointConstantWithPrimary_eq_six_primaryGraphSum]
  decide +kernel

/-- The HHH request with two added points at the shifted source. -/
theorem n_hhh_constant_computed :
    lowerPointConstantWithPrimary .hirzebruchOne rational elliptic
      2 ![1, 1] (fun _ ↦ .hyperplane) = 1 / 80 := by
  rw [lowerPointConstantWithPrimary_eq_six_primaryGraphSum]
  decide +kernel

private theorem labels_h : (![.hyperplane, .hyperplane, .hyperplane] :
    Fin 3 → SurfaceBasisLabel target) = fun _ ↦ .hyperplane := by decide +kernel

private theorem labels_e : (![.exceptional 0, .exceptional 0, .exceptional 0] :
    Fin 3 → SurfaceBasisLabel target) = fun _ ↦ .exceptional 0 := by decide +kernel

private theorem energy_fiber : target.effective.energy fiber = 2 := by decide +kernel
private theorem degree_fiber : target.planeDegree fiber = 1 := by decide +kernel
private theorem source_fiber : fiber + target.exceptionalCurve 0 = ![1, 1] := by decide +kernel

/-- The point row has constant 1/120 at F. -/
theorem p_constant : SurfaceGenusTwoBlowupScalar.constant 0 (fiber, .point) = 1 / 120 := by
  rw [← SurfaceGenusTwoBlowupPointCache.constant_eq 0 (fiber, .point)
    rational elliptic rational_eq elliptic_eq]
  simp only [SurfaceGenusTwoBlowupPointCache.constant, energy_fiber, labels_h]
  exact p_constant_computed

/-- The exceptional row has constant 1/120 at F. -/
theorem k_constant : SurfaceGenusTwoBlowupScalar.constant 0 (fiber, .exceptional 0) = 1 / 120 := by
  rw [← SurfaceGenusTwoBlowupPointCache.constant_eq 0 (fiber, .exceptional 0)
    rational elliptic rational_eq elliptic_eq]
  simp only [SurfaceGenusTwoBlowupPointCache.constant, energy_fiber, labels_e]
  exact k_constant_computed

/-- The primary row at F retains the four weighted terms at the shifted source E+F. -/
theorem n_constant : SurfaceGenusTwoBlowupScalar.constant 0 (fiber, .primary) = -1 / 240 := by
  rw [← SurfaceGenusTwoBlowupPointCache.constant_eq 0 (fiber, .primary)
    rational elliptic rational_eq elliptic_eq]
  simp only [SurfaceGenusTwoBlowupPointCache.constant, energy_fiber, degree_fiber,
    source_fiber, Nat.cast_one, mul_one, labels_h, labels_e]
  rw [n_ehh_constant_computed, n_eeh_constant_computed, n_eee_constant_computed,
    n_hhh_constant_computed]
  norm_num only

end AxiomaticGW.BlowupF1FiberBPValues

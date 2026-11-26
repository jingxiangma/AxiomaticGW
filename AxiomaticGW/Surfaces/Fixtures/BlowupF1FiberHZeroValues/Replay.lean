/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.H0056
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.H0063
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.H0070
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.H0074
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.H0081
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.H0088
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.H0097
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.H0101
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.H0105
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.K0056
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.K0063
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.K0070
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.K0074
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.K0081
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.K0088
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.K0097
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.K0101
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.K0105
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroValues.StructuralZeros

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHReduction


@[expose] public section
-- Match the existing complete L24 frame elaboration depth.
set_option maxRecDepth 20000

namespace AxiomaticGW.BlowupF1FiberHZeroValues
open BlowupF1FiberHZeroCoefficients BlowupF1FiberHReduction

/-- Candidate table used only after all 27 corresponding weighted contributions are checked. -/
def hyperplaneClaim (j : Fin 815) : ℚ :=
  if j = 56 then (1 / 3 : ℚ) else
  if j = 63 then (2 / 3 : ℚ) else
  if j = 70 then (2 / 3 : ℚ) else
  if j = 74 then (4 / 3 : ℚ) else
  0

theorem hyperplane_terms (j : Fin 815)
    (hj : j ∈ SurfaceGenusTwoBlowupHUniform.genusTwoFrame) :
    weightedTerm .hyperplane j = hyperplaneClaim j := by
  simp only [SurfaceGenusTwoBlowupHUniform.genusTwoFrame, Finset.mem_insert,
    Finset.mem_singleton] at hj
  rcases hj with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact h_0051
  · exact h_0052
  · exact h_0056
  · exact h_0057
  · exact h_0059
  · exact h_0062
  · exact h_0063
  · exact h_0064
  · exact h_0066
  · exact h_0069
  · exact h_0070
  · exact h_0074
  · exact h_0076
  · exact h_0081
  · exact h_0083
  · exact h_0088
  · exact h_0093
  · exact h_0095
  · exact h_0097
  · exact h_0101
  · exact h_0105
  · exact h_0109
  · exact h_0110
  · exact h_0112
  · exact h_0113
  · exact h_0119
  · exact h_0120

/-- Complete checked coefficient, including every zero and signed term of the frame. -/
theorem hyperplane_coefficient : coefficient .hyperplane = (3 : ℚ) := by
  calc
    coefficient .hyperplane =
        ∑ j ∈ SurfaceGenusTwoBlowupHUniform.genusTwoFrame, hyperplaneClaim j := by
      apply Finset.sum_congr rfl
      exact fun j hj ↦ hyperplane_terms j hj
    _ = _ := by decide +kernel

/-- Candidate table used only after all 27 corresponding weighted contributions are checked. -/
def exceptionalClaim (j : Fin 815) : ℚ :=
  if j = 56 then (-1 / 3 : ℚ) else
  if j = 63 then (-2 / 3 : ℚ) else
  if j = 70 then (-2 / 3 : ℚ) else
  if j = 74 then (-4 / 3 : ℚ) else
  if j = 81 then (1 / 3 : ℚ) else
  if j = 88 then (1 / 3 : ℚ) else
  if j = 97 then (2 / 3 : ℚ) else
  if j = 101 then (4 / 3 : ℚ) else
  if j = 105 then (4 / 3 : ℚ) else
  0

theorem exceptional_terms (j : Fin 815)
    (hj : j ∈ SurfaceGenusTwoBlowupHUniform.genusTwoFrame) :
    weightedTerm (.exceptional 0) j = exceptionalClaim j := by
  simp only [SurfaceGenusTwoBlowupHUniform.genusTwoFrame, Finset.mem_insert,
    Finset.mem_singleton] at hj
  rcases hj with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact k_0051
  · exact k_0052
  · exact k_0056
  · exact k_0057
  · exact k_0059
  · exact k_0062
  · exact k_0063
  · exact k_0064
  · exact k_0066
  · exact k_0069
  · exact k_0070
  · exact k_0074
  · exact k_0076
  · exact k_0081
  · exact k_0083
  · exact k_0088
  · exact k_0093
  · exact k_0095
  · exact k_0097
  · exact k_0101
  · exact k_0105
  · exact k_0109
  · exact k_0110
  · exact k_0112
  · exact k_0113
  · exact k_0119
  · exact k_0120

/-- Complete checked coefficient, including every zero and signed term of the frame. -/
theorem exceptional_coefficient : coefficient (.exceptional 0) = (1 : ℚ) := by
  calc
    coefficient (.exceptional 0) =
        ∑ j ∈ SurfaceGenusTwoBlowupHUniform.genusTwoFrame, exceptionalClaim j := by
      apply Finset.sum_congr rfl
      exact fun j hj ↦ exceptional_terms j hj
    _ = _ := by decide +kernel

/-- The two numerical coefficients refer to the unchanged full shifted row. -/
theorem original_coefficients : hZeroCoefficient = 3 ∧ kZeroCoefficient = 1 := by
  constructor
  · rw [← hyperplane_eq]
    exact hyperplane_coefficient
  · rw [← exceptional_eq]
    exact exceptional_coefficient

/-- The well-founded formal F1 fiber H value follows from the original relation and boundary. -/
theorem reconstructed_fiber_h : SurfaceGenusTwoBlowupRecursion.values 0 fiberState = 0 := by
  rw [reconstructed_value, original_coefficients.1, original_coefficients.2]
  norm_num

/-- Any boundary-compatible candidate satisfying the actual original full row has this value. -/
theorem fiber_h_of_equation (candidate : SurfaceGenusTwoBlowupOrder.State target → ℚ)
    (hboundary : ∀ s, target.planeDegree s.1 = 0 → candidate s = boundary s)
    (he : RationalTerms.eval (SurfaceGenusTwoBlowupOrder.canonicalValuation candidate)
      (SurfaceGenusTwoBlowupRecursion.row 0 fiberState) = 0) : candidate fiberState = 0 := by
  rw [value_of_equation candidate hboundary he, original_coefficients.1, original_coefficients.2]
  norm_num

end AxiomaticGW.BlowupF1FiberHZeroValues

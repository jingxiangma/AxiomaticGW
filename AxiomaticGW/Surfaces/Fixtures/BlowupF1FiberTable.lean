/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberTableAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberBPConstants
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberBPCoefficientValues

/-!
# The complete genus-two F₁ canonical table through energy two

All sixteen canonical entries at 0, E, 2E and F agree with the well-founded
reconstruction. The fiber rows use the original BP and L24 equations.
Their interpretation as geometric invariants uses the corresponding equations,
finite seeds and support hypotheses of the surface reconstruction theorem.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberTable
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
open BlowupF1FiberHReduction BlowupF1FiberBPValues

-- Elaborate the full original BP and L24 row dispatch.
set_option maxRecDepth 20000

/-- The original bounded row checker accepts all sixteen canonical entries. -/
theorem accepted : SurfaceGenusTwoBlowupBoundedCertificate.checkTable 0 2 boundary = true := by
  apply BlowupF1FiberTableAssembly.checkTable_of_rows
  · rw [BlowupF1FiberTableAssembly.eval_boundary, p_constant, p_coefficients.1, p_coefficients.2]
    norm_num only
  · rw [BlowupF1FiberTableAssembly.eval_boundary, n_constant, n_coefficients.1, n_coefficients.2]
    norm_num only
  · rw [BlowupF1FiberTableAssembly.eval_boundary, k_constant, k_coefficients.1, k_coefficients.2]
    norm_num only

/-- Agreement with the reconstruction for every class and family in the finite table. -/
theorem values_eq (s : State target) (hs : target.effective.energy s.1 ≤ 2) :
    SurfaceGenusTwoBlowupRecursion.values 0 s = boundary s :=
  (SurfaceGenusTwoBlowupBoundedCertificate.checkTable_sound 0 2 boundary accepted s hs).symm

/-- Every canonical fiber query, including the primary and both divisor descendants, is zero. -/
theorem fiber_values (f : Family target) :
    SurfaceGenusTwoBlowupRecursion.values 0 (fiber, f) = 0 := by
  rw [values_eq (fiber, f) (by change target.effective.energy fiber ≤ 2; decide +kernel)]
  exact SurfaceGenusTwoBlowupBoundary.value_of_ne_zero fiber (by decide +kernel) f

end AxiomaticGW.BlowupF1FiberTable

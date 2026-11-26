/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.ScalarPointRootOrder
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1SelectedComponentsRow0123
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1SelectedComponentsRow0124

/-! # Real separating slots under left-first root evaluation -/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGWTest.ScalarPointRootOrder
open AxiomaticGW BlowupF1RootAssembly SurfaceGenusTwo
set_option maxRecDepth 65536

/-- The previous memory-heavy unit slot checks the left zero first. -/
theorem row123_unit_zero :
    separatingPart BlowupF1SelectedComponentsRow0123.cache 123 0 .unit 0 = 0 := by
  unfold separatingPart
  rw [GluingExpression.scalarPointRootSeparating_eq_leftFirst]
  decide +kernel

/-- The point-inserted left component also vanishes before the right is evaluated. -/
theorem row124_point_zero :
    separatingPart BlowupF1SelectedComponentsRow0124.cache 124 0 .point 0 = 0 := by
  unfold separatingPart
  rw [GluingExpression.scalarPointRootSeparating_eq_leftFirst]
  decide +kernel

/-- A second source shape has the same left-first dimension vanishing. -/
theorem row133_unit_zero :
    separatingPart BlowupF1SelectedComponentsRow0123.cache 133 0 .unit 0 = 0 := by
  unfold separatingPart
  rw [GluingExpression.scalarPointRootSeparating_eq_leftFirst]
  decide +kernel
/-- A nonzero hyperplane factor retains its original positive weight. -/
theorem row123_hyperplane :
    separatingPart BlowupF1SelectedComponentsRow0123.cache 123 0 .hyperplane 0 =
      (161 / 25920 : ℚ) := by
  unfold separatingPart
  rw [GluingExpression.scalarPointRootSeparating_eq_leftFirst]
  decide +kernel

/-- Exceptional pairing keeps its negative sign under the new evaluation order. -/
theorem row123_exceptional :
    separatingPart BlowupF1SelectedComponentsRow0123.cache 123 0 (.exceptional 0) 0 =
      (-161 / 77760 : ℚ) := by
  unfold separatingPart
  rw [GluingExpression.scalarPointRootSeparating_eq_leftFirst]
  decide +kernel

end AxiomaticGWTest.ScalarPointRootOrder

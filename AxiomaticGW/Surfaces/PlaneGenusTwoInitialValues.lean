/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneGenusTwoConstant
public import AxiomaticGW.Surfaces.PlaneGenusTwoRecursion

/-!
# Certified initial values for the plane genus-two recursion

Kernel replay evaluates the complete source-degree-one HPP constant using
already proved lower-genus point tables. The original BP equation then gives
the initial primary value zero from the existing H seed. No numerical value
is introduced as a new geometric assumption.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande

set_option maxRecDepth 20000 in
private theorem initialConstant_checked : planeShiftedConstantFast 0 1 = 1 / 80 := by
  decide +kernel

/-- The constant of the original complete HPP equation is exactly one eightieth. -/
theorem planeShiftedConstant_initial : planeShiftedConstant 0 1 = 1 / 80 :=
  (planeShiftedConstantFast_eq 0 1).symm.trans initialConstant_checked

/-- The original equation derives the zero primary value; it is not an extra seed. -/
theorem planeCanonicalInitial_eq : planeCanonicalInitial = ![0, -1 / 960, 0] := by
  rw [planeCanonicalInitial, planeShiftedConstant_initial]
  norm_num

/-- The terminating algorithm has this fully evaluated initial triple. -/
theorem planeCanonicalValues_initial : planeCanonicalValues 0 = ![0, -1 / 960, 0] := by
  rw [planeCanonicalValues_zero, planeCanonicalInitial_eq]

end AxiomaticGW.BelorousskiPandharipande

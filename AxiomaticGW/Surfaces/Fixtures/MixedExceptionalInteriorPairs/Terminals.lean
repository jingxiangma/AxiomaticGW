/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.Frame
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPrimitiveDivisorProduct

/-! # Lower terminal and primitive product terms in the mixed exceptional calibration

Every product below has a divisor with zero intersection against its primitive
exceptional curve. Its same-class point state also vanishes.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoMixedExceptionalInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

theorem low_values (j : Fin 10) : SurfaceGenusTwo.ancestorValue low (lowKey j) = 0 := by
  fin_cases j <;> rw [ancestorValue_low low _ rfl (by decide +kernel)] <;> decide +kernel

theorem product_values (j : Fin 6) : SurfaceGenusTwo.ancestorValue low (productKey j) = 0 := by
  let beta := productBeta j
  let a := productLabels j 0
  let b := productLabels j 1
  have he : X.effective.energy beta = 1 := by fin_cases j <;> decide +kernel
  have ha : a.codimension = 1 := by fin_cases j <;> decide +kernel
  have hb : b.codimension = 1 := by fin_cases j <;> decide +kernel
  have h := Option.some.inj ((queryValue?_firstDivisorPair 0 beta he a b ha hb).symm.trans
    (queryValue?_primitiveDivisorProduct 0 beta he a b ha hb))
  have hp : SurfaceGenusTwoBlowupRecursion.values 0 (beta, .point) = 0 := by
    rw [← BlowupTwoExceptionalPlaneZeroTable.table_eq]
    fin_cases j <;> decide +kernel
  rw [hp, mul_zero, add_zero] at h
  change ancestorValueWith boundary (productKey j) = _
  rw [ancestorValueWith_eq_of_table 0 2 boundary
    (fun s _ ↦ BlowupTwoExceptionalPlaneZeroTable.table_eq s) _ rfl (by
      change X.effective.energy beta ≤ 2
      omega)]
  refine h.trans ?_
  fin_cases j <;> decide +kernel

end AxiomaticGW.BlowupTwoMixedExceptionalInteriorPairs

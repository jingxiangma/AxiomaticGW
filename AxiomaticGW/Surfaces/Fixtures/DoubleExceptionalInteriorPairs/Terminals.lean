/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.DoubleExceptionalInteriorPairs.Transfer
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPrimitiveDivisorProduct

/-! # Low-power and first-divisor products inside double exceptional descendants

Both first-power products occur in the primitive class E. The checked primitive
divisor-product formula therefore evaluates them using its same-class point row.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1DoubleExceptionalInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

/-- Five signed low-power terms normalize to zero on the certified canonical table. -/
theorem low_values (j : Fin 5) : SurfaceGenusTwo.ancestorValue low (lowKey j) = 0 := by
  fin_cases j <;> rw [ancestorValue_low low _ rfl (by decide +kernel)] <;> decide +kernel

/-- Primitive ancestor products in the hyperplane-exceptional and exceptional-square orders. -/
def productValues : Fin 2 → ℚ := ![0, 1/144]

theorem product_values (j : Fin 2) :
    SurfaceGenusTwo.ancestorValue low (productKey j) = productValues j := by
  let a := productLabels j 0
  let b := productLabels j 1
  have he : X.effective.energy exceptional = 1 := by decide +kernel
  have ha : a.codimension = 1 := by fin_cases j <;> decide +kernel
  have hb : b.codimension = 1 := by fin_cases j <;> decide +kernel
  have h := Option.some.inj ((queryValue?_firstDivisorPair 0 exceptional he a b ha hb).symm.trans
    (queryValue?_primitiveDivisorProduct 0 exceptional he a b ha hb))
  have hp : SurfaceGenusTwoBlowupRecursion.values 0 (exceptional, .point) = 0 := by
    rw [SurfaceGenusTwoBlowupRecursion.values_boundary _ _ (by decide +kernel)]
    decide +kernel
  rw [hp, mul_zero, add_zero] at h
  change ancestorValueWith boundary (productKey j) = _
  rw [ancestorValueWith_eq_of_table 0 2 boundary
    (fun s hs ↦ (BlowupF1FiberTable.values_eq s hs).symm) _ rfl (by
      change X.effective.energy exceptional ≤ 2
      decide +kernel)]
  refine h.trans ?_
  fin_cases j <;> decide +kernel

end AxiomaticGW.BlowupF1DoubleExceptionalInteriorPairs

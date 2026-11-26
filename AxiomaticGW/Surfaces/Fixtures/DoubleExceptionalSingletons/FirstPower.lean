/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalDivisorAncestors

/-! # Checked full-degree lower-genus components of the doubled exceptional singleton square -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleExceptionalComponents
open SurfaceGenusTwoPositiveSquare SurfaceLowGenusPointCache
open GenusTwoSecondUnitPairs.TwoBlowupComponents
open BlowupTwoDoubleExceptionalDivisor (beta)

/-- Try the axis-specific checked keys only at the designated cotangent degree.
Every absent key uses precisely the certified preceding evaluator. -/
def addRows (c : CertifiedComponents X) (degree : ℕ) (rows : Fin 2 → List (Entry X)) :
    CertifiedComponents X where
  value q := if q.totalPsi = degree ∧ (q.beta = beta 0 ∨ q.beta = beta 1) then
      stageLookup c.value q (rows (if q.beta = beta 0 then 0 else 1)) else c.value q
  sound q := by
    split
    · exact stageLookup_eq c.value c.sound q _
    · exact c.sound q

namespace FirstPower
open BlowupTwoMixedExceptionalSingletonComponents.ThirdPower (components)

/-- Both first-power point entries follow from their original elliptic cotangent equation. -/
theorem point_value (i : Fin 2) :
    (0 : ℚ) = stagedValue components.value (componentKey 1 (beta i) [p₁]) := by
  fin_cases i <;> decide +kernel

/-- The first-cotangent elliptic point vertex at either doubled exceptional class. -/
def rows (i : Fin 2) : List (Entry X) :=
  [components.entry (componentKey 1 (beta i) [p₁]) 0 (point_value i)]

/-- The first layer on top of the existing degree-zero and primitive exceptional entries. -/
def backend : CertifiedComponents X := addRows components 1 rows

end FirstPower
end AxiomaticGW.BlowupTwoDoubleExceptionalComponents

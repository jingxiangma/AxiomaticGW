/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupExceptionalComplement

/-!
# Consumers of the exceptional rational complement

The complete contraction retains the negative exceptional metric and all
class splittings. A foreign exceptional divisor and class zero do not have
the selected generator's value. These are component calculations, not
assumed genus-two invariant values.
-/

@[expose] public section

namespace AxiomaticGWTest.GenusTwoBlowupExceptionalComplement
open AxiomaticGW AxiomaticGW.SurfaceGenusTwo AxiomaticGW.GluingExpression

/-- The actual two-triple rational graph used by the public component theorem. -/
def pair : GluingExpression 0 (Fin 4) :=
  GetzlerGraphs.join (m := 2) (n := 2) 2 1
    (fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (fundamental 0 (Fin 3) (by norm_num [StableArity]))

/-- Complete contraction with a fixed, arbitrary genus-two coefficient variable. -/
def value (X : SurfaceTarget) (beta : X.Curve)
    (a : Fin 4 → SurfaceBasisLabel X) : ℚ :=
  pair.pointContraction X
    (primaryPointVertex X (.inr (SurfaceQuery.points X 2 0 1)))
    (![0, 0, 0], ![0, 0, 0])
    ((inferInstance : DecidableEq (Fin 3)), (inferInstance : DecidableEq (Fin 3)))
    beta 0 a

/-- The genus-two coefficient variable is irrelevant on primary rational factors. -/
theorem hirzebruchOne_sign : value .hirzebruchOne ![1, 0]
    ![.exceptional 0, .exceptional 0, .exceptional 0, .unit] = -1 := by
  have h := SurfaceGenusTwoBlowupExceptionalComplement.exceptional_pair_primary
    .hirzebruchOne 0 (.inr (SurfaceQuery.points .hirzebruchOne 2 0 1))
  have hc : SurfaceTarget.hirzebruchOne.exceptionalCurve 0 = ![1, 0] := by decide +kernel
  rw [hc] at h
  exact h

/-- Equal-energy exceptional classes still have distinct divisor restrictions. -/
theorem foreign_exceptional_zero : value .blowupTwo ![1, 0, 0]
    ![.exceptional 0, .exceptional 0, .exceptional 1, .unit] = 0 := by
  unfold value pair
  simp only [GetzlerGraphs.join, pointContraction, primaryPointVertex,
    show (![0, 0, 0] : Fin 3 → ℕ) = 0 by ext j; fin_cases j <;> rfl,
    and_self, ite_true]
  decide +kernel

/-- Changing only the full exceptional curve class changes the contraction to zero. -/
theorem wrong_generator_zero : value .blowupTwo ![0, 1, 0]
    ![.exceptional 0, .exceptional 0, .exceptional 0, .unit] = 0 := by
  have h := SurfaceGenusTwoBlowupExceptionalComplement.exceptional_pair_primary_at_generator
    .blowupTwo 0 1 (.inr (SurfaceQuery.points .blowupTwo 2 0 1))
  have hc : SurfaceTarget.blowupTwo.exceptionalCurve 1 = ![0, 1, 0] := by decide +kernel
  rw [hc, if_neg (by decide : (0 : Fin 2) ≠ 1)] at h
  exact h

/-- The positive exceptional generator's value is not reused at class zero. -/
theorem zero_class_zero : value .blowupTwo 0
    ![.exceptional 0, .exceptional 0, .exceptional 0, .unit] = 0 := by
  unfold value pair
  simp only [GetzlerGraphs.join, pointContraction, primaryPointVertex,
    show (![0, 0, 0] : Fin 3 → ℕ) = 0 by ext j; fin_cases j <;> rfl,
    and_self, ite_true]
  decide +kernel

end AxiomaticGWTest.GenusTwoBlowupExceptionalComplement

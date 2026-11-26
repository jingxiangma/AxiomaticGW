/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoOneMarkingSquare
public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalSingletons.ThirdPower

/-! # One-marked exceptional-divisor ancestors at twice an exceptional curve on Bl₂

The ten cotangent-square contractions retain every effective-class split and every
basis state of the two-point blowup. The lower-genus component cache has a proof for
each vertex and uses the original lower-genus recursion for missing keys.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleExceptionalDivisor
open SurfaceGenusTwo GenusTwoPsiSquare SurfaceGenusTwoPositiveSquare

/-- The two doubled exceptional curves in the native E₁, E₂, L order. -/
def beta (i : Fin 2) : SurfaceTarget.blowupTwo.Curve :=
  2 • SurfaceTarget.blowupTwo.exceptionalCurve i

open BlowupTwoMixedExceptionalSingletonComponents.ThirdPower (components)

/-- One original cotangent-square contraction at the full doubled class, after removing
two powers from the external insertion. -/
def squareGraph (i : Fin 2) (a : SurfaceBasisLabel .blowupTwo) (k : ℕ) (j : Fin 10) : ℚ :=
  (boundaryTerm j).1.surfaceDecoratedEval .blowupTwo (components.vertex (fun _ ↦ 0))
    (boundaryTerm j).2 (beta i) (fun _ ↦ k) (fun _ ↦ a)

private def graphValues : Fin 10 → ℚ :=
  ![1/576, 1/576, 0, 1/288, 1/4, 1/6, 0, 1/12, 1/24, 3]

set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000 in
-- Each index uses the five-state Bl₂ inverse metric and the full three-coordinate class.
private theorem graph_values (i : Fin 2) (j : Fin 10) :
    squareGraph i (.exceptional i) 1 j = graphValues j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Scalar reconstruction from the original ten lower-genus contractions on either axis. -/
theorem ancestor_eq_sum (base : SurfaceAncestorKey .blowupTwo → ℚ) (i : Fin 2)
    (a : SurfaceBasisLabel .blowupTwo) (k : ℕ) :
    ancestorValue base (oneMarkingKey (beta i) a (k + 2)) =
      ∑ j, GenusTwoPsiSquare.boundary (boundaryIndex j) * squareGraph i a k j := by
  have hv : components.vertex (fun _ ↦ 0) = constantVertex .blowupTwo := by
    rw [CertifiedComponents.vertex_eq, component_eq, SurfaceGenusTwoPositiveDivisorPairs.vertex_eq]
    funext g S inst h b d a
    exact eval_zero_vertexTerms .blowupTwo g S h b d a
  rw [ancestorValue_oneMarking_square, oneMarkingSquareValue, ← hv]
  rfl

/-- The original genus-two ancestor evaluator with any terminal family. -/
theorem main_ancestor (base : SurfaceAncestorKey .blowupTwo → ℚ) (i : Fin 2) :
    ancestorValue base (oneMarkingKey (beta i) (.exceptional i) 3) = 29/5760 := by
  rw [show 3 = 1 + 2 by rfl, ancestor_eq_sum]
  simp only [graph_values]
  decide +kernel

end AxiomaticGW.BlowupTwoDoubleExceptionalDivisor

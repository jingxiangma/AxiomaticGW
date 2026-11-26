/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.DoubleExceptionalSingletons.SecondPower

/-! # Elliptic third-cotangent vertex replay for the two doubled exceptional axes -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleExceptionalComponents.ThirdPower
open SurfaceGenusTwoPositiveSquare SurfaceLowGenusPointCache
open GenusTwoSecondUnitPairs.TwoBlowupComponents
open BlowupTwoDoubleExceptionalDivisor (beta)
open SecondPower (second)

/-- The three marked positions carry total cotangent degree three. -/
def marks (i : Fin 2) : Fin 9 → List (SurfaceInsertion X) :=
  let d : SurfaceInsertion X := ⟨.exceptional i, 0⟩
  let f : SurfaceInsertion X := ⟨.exceptional i.rev, 0⟩
  let u₃ : SurfaceInsertion X := ⟨.unit, 3⟩
  ![[u₀,p₀,u₃], [u₀,p₁,u₂], [h₀,h₀,u₃], [h₀,h₁,u₂], [d,d,u₃],
    [d,⟨.exceptional i,1⟩,u₂], [f,f,u₃], [f,⟨.exceptional i.rev,1⟩,u₂], [p₀,u₁,u₂]]

/-- Each third-cotangent key belongs to genus one at the full doubled curve class. -/
def key (i : Fin 2) (j : Fin 9) : SurfaceAncestorKey X :=
  componentKey 1 (beta i) (marks i j) (by fin_cases i <;> fin_cases j <;> decide +kernel)

/-- The two nonzero elliptic entries differ in where the third power is placed. -/
def values : Fin 9 → ℚ := ![0, 0, 0, 0, 1/24, 1/12, 0, 0, 0]

set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000 in
-- The two elliptic loop terms use the checked first and second powers on their components.
/-- Each indexed value satisfies its original lower-genus cotangent equation. -/
theorem accepted (i : Fin 2) (j : Fin 9) :
    values j = stagedValue second.value (key i j) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Eighteen third-cotangent records, each verified by the original lower-genus recursion. -/
def rows (i : Fin 2) : List (Entry X) :=
  (List.finRange 9).map fun j ↦ second.entry (key i j) (values j) (accepted i j)

/-- Complete lower-genus evaluator with the three stages of verified vertex values. -/
def backend : CertifiedComponents X := addRows second 3 rows

end AxiomaticGW.BlowupTwoDoubleExceptionalComponents.ThirdPower

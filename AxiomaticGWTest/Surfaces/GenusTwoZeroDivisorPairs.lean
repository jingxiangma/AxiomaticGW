/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoZeroDivisorBenchmark

/-! # Positive-plane divisor annihilations and their signed-cup controls -/

@[expose] public section
namespace AxiomaticGWTest.GenusTwoZeroDivisorPairs
open AxiomaticGW SurfaceGenusTwo

/-- A positive-plane example on F₁ in the full class E+F. -/
theorem oneBlowup_mixed :
    zeroDivisorPair? (X := .hirzebruchOne) ⟨2, ![1, 1], [⟨.hyperplane, 4⟩, ⟨.exceptional 0, 0⟩]⟩ =
      some 0 := by decide +kernel

/-- The E₂ divisor cancels on E₂+L in both positions; E₁ does not. -/
theorem twoBlowups_distinct_divisors :
    let beta : SurfaceTarget.blowupTwo.Curve := ![0, 1, 1]
    zeroDivisorPair? (X := .blowupTwo)
      ⟨2, beta, [⟨.hyperplane, 3⟩, ⟨.exceptional 1, 0⟩]⟩ = some 0 ∧
    zeroDivisorPair? (X := .blowupTwo)
      ⟨2, beta, [⟨.exceptional 1, 0⟩, ⟨.hyperplane, 3⟩]⟩ = some 0 ∧
    zeroDivisorPair? (X := .blowupTwo)
      ⟨2, beta, [⟨.hyperplane, 3⟩, ⟨.exceptional 0, 0⟩]⟩ = none := by
  decide +kernel

/-- A surviving exceptional self-intersection obstructs the empty-table evaluation. -/
theorem same_divisor_cup :
    zeroDivisorPair? (X := .blowupTwo)
      ⟨2, ![0, 1, 1], [⟨.exceptional 1, 3⟩, ⟨.exceptional 1, 0⟩]⟩ = none := by decide +kernel

end AxiomaticGWTest.GenusTwoZeroDivisorPairs

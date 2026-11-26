/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.GenusTwoVertexHodgeReduction
public import Mathlib.Algebra.BigOperators.Fin

/-! # Symbolic controls for the genus-two vertex reduction -/

public section
namespace AxiomaticGWTest.GKM.GenusTwoVertexHodgeReduction
open AxiomaticGW.GKM.GenusTwoVertexHodgeReduction

/-- The empty marked list samples the λ₁λ₂ seed. -/
theorem unmarked (s : ↥seeds → ℚ) : evaluate s 1 2 (by decide) [] =
    s ⟨(1, 2, []), by decide +kernel⟩ := by
  rw [evaluate_reduced s 1 2 _ [] (by decide) (by decide) (by decide)]
  exact congrArg s (Subtype.ext (by decide +kernel))

/-- The two identical marked powers give two separate string contributions. -/
theorem repeated_string (s : ↥seeds → ℚ) : evaluate s 0 0 (by decide) [0, 3, 3] =
    2 * s ⟨(0, 0, [2, 3]), by decide +kernel⟩ := by
  rw [evaluate]
  change (∑ k : Fin 2, if 0 < [3, 3].get k then evaluate s 0 0 (by decide) (lower [3, 3] k)
    else 0) = _
  rw [Fin.sum_univ_two]
  change evaluate s 0 0 (by decide) [2, 3] + evaluate s 0 0 (by decide) [3, 2] = _
  rw [evaluate_reduced s 0 0 _ [2, 3] (by decide) (by decide) (by decide),
    evaluate_reduced s 0 0 _ [3, 2] (by decide) (by decide) (by decide), two_mul]
  exact congrArg₂ (· + ·) (congrArg s (Subtype.ext (by decide +kernel)))
    (congrArg s (Subtype.ext (by decide +kernel)))

/-- A dilaton marking with one remaining marked point multiplies the untouched seed by 3. -/
theorem dilaton (s : ↥seeds → ℚ) : evaluate s 0 0 (by decide) [4, 1] =
    3 * s ⟨(0, 0, [4]), by decide +kernel⟩ := by
  rw [evaluate]
  change 3 * evaluate s 0 0 (by decide) [4] = _
  rw [evaluate_reduced s 0 0 _ [4] (by decide) (by decide) (by decide)]
  exact congrArg (3 * ·) (congrArg s (Subtype.ext (by decide +kernel)))

/-- λ₂² already exceeds the dimension at an unmarked vertex. -/
theorem off_dimension (s : ↥seeds → ℚ) : evaluate s 2 2 (by decide) [] = 0 := by
  rw [evaluate]
  rfl

end AxiomaticGWTest.GKM.GenusTwoVertexHodgeReduction

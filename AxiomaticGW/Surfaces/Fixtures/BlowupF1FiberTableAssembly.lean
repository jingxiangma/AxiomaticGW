/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHValue

/-!
# Canonical reconstruction on F₁ through anticanonical energy two

The complete grid consists of the four canonical families at 0, E, 2E and F.
At F the boundary candidate is zero and its only nonzero earlier entries are
the two divisor descendants at class zero. The bounded support theorem applies
to the original rows, including cancellation at the shifted source of the
primary row. Three scalar identities suffice after the known hyperplane row.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberTableAssembly
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder BlowupF1FiberHReduction

-- The scalar dispatch contains the complete L24 equation.
set_option maxRecDepth 20000

/-- Count all four families, including the nominal point descendant at class zero. -/
theorem states_length :
    (SurfaceGenusTwoBlowupBoundedCertificate.states target 2).length = 16 := by
  decide +kernel

private theorem positive_plane_class (beta : target.Curve)
    (hb : target.effective.energy beta ≤ 2) (hd : 0 < target.planeDegree beta) :
    beta = fiber := by
  rw [energy_formula] at hb
  change 0 < beta 1 at hd
  funext j
  fin_cases j
  · change beta 0 = 0
    omega
  · change beta 1 = 1
    omega

private theorem masked_boundary (f : Family target) :
    SurfaceGenusTwoBlowupOrderedCertificate.earlierCandidate (fiber, f) boundary =
      boundary := by
  funext s
  unfold SurfaceGenusTwoBlowupOrderedCertificate.earlierCandidate
  by_cases he : Earlier target s (fiber, f)
  · exact if_pos he
  · rw [if_neg he]
    symm
    apply SurfaceGenusTwoBlowupBoundary.value_of_ne_zero s.1 _ s.2
    intro hz
    apply he
    have hs : s = (0, s.2) := Prod.ext hz rfl
    rw [hs]
    exact earlier_of_planeDegree_lt target _ _ (by change 0 < 1; decide +kernel)

private theorem earlier_columns (f : Family target) :
    SurfaceGenusTwoBlowupScalar.columns
      (SurfaceGenusTwoBlowupOrderedCertificate.earlierStates 2 (fiber, f) boundary) =
      {hZero, kZero} := by
  cases f with
  | hyperplane => exact earlier_boundary_columns
  | point => decide +kernel
  | primary => decide +kernel
  | exceptional j => fin_cases j; decide +kernel

/-- Evaluate a complete fiber row at the boundary candidate, retaining its constant
and both signed singleton contributions. -/
theorem eval_boundary (f : Family target) :
    RationalTerms.eval (canonicalValuation boundary)
      (SurfaceGenusTwoBlowupRecursion.row 0 (fiber, f)) =
      SurfaceGenusTwoBlowupScalar.constant 0 (fiber, f) -
        SurfaceGenusTwoBlowupScalar.singletonCoefficient 0 (fiber, f) hZero / 960 -
        SurfaceGenusTwoBlowupScalar.singletonCoefficient 0 (fiber, f) kZero / 2880 := by
  have hs : (fiber, f) ∈ SurfaceGenusTwoBlowupBoundedCertificate.states target 2 := by
    rw [SurfaceGenusTwoBlowupBoundedCertificate.mem_states]
    change target.effective.energy fiber ≤ 2
    decide +kernel
  have hr := SurfaceGenusTwoBlowupBoundedCertificate.replay_eq_row 0 2 (fiber, f)
    (canonicalValuation boundary) hs (by change 0 < 1; decide +kernel)
  have he := SurfaceGenusTwoBlowupOrderedCertificate.masked_replay_eq_earlier_sum
    0 2 (fiber, f) boundary
  rw [masked_boundary, hr, earlier_columns] at he
  have hk : hZero ∉ ({kZero} : Finset (Variable target)) := by
    simpa only [Finset.mem_singleton] using zero_columns_distinct
  simp only [Finset.sum_insert hk, Finset.sum_singleton] at he
  change RationalTerms.eval (canonicalValuation boundary)
      (SurfaceGenusTwoBlowupRecursion.row 0 (fiber, f)) =
    SurfaceGenusTwoBlowupScalar.constant 0 (fiber, f) +
      (SurfaceGenusTwoBlowupScalar.singletonCoefficient 0 (fiber, f) hZero *
        canonicalValuation boundary (.inr (Family.hyperplane.query 0)) +
       SurfaceGenusTwoBlowupScalar.singletonCoefficient 0 (fiber, f) kZero *
        canonicalValuation boundary (.inr ((Family.exceptional 0).query 0))) at he
  rw [canonicalValuation_query, canonicalValuation_query] at he
  simp only [boundary, SurfaceGenusTwoBlowupBoundary.value_zero,
    SurfaceGenusTwoBlowupBoundary.initial] at he
  rw [he]
  ring

/-- The three remaining BP row evaluations suffice for the complete sixteen-state grid. -/
theorem checkTable_of_rows
    (hP : RationalTerms.eval (canonicalValuation boundary)
      (SurfaceGenusTwoBlowupRecursion.row 0 (fiber, .point)) = 0)
    (hN : RationalTerms.eval (canonicalValuation boundary)
      (SurfaceGenusTwoBlowupRecursion.row 0 (fiber, .primary)) = 0)
    (hK : RationalTerms.eval (canonicalValuation boundary)
      (SurfaceGenusTwoBlowupRecursion.row 0 (fiber, .exceptional 0)) = 0) :
    SurfaceGenusTwoBlowupBoundedCertificate.checkTable 0 2 boundary = true := by
  rw [SurfaceGenusTwoBlowupBoundedCertificate.checkTable, List.all_eq_true]
  intro s hs
  by_cases hd : target.planeDegree s.1 = 0
  · rw [SurfaceGenusTwoBlowupBoundedCertificate.checkRow, if_pos hd]
    exact decide_eq_true rfl
  · rw [SurfaceGenusTwoBlowupBoundedCertificate.checkRow, if_neg hd]
    apply decide_eq_true
    rw [SurfaceGenusTwoBlowupBoundedCertificate.replay_eq_row 0 2 s _ hs (Nat.pos_of_ne_zero hd)]
    obtain ⟨beta, family⟩ := s
    have hb := (SurfaceGenusTwoBlowupBoundedCertificate.mem_states target 2 (beta, family)).mp hs
    have hf := positive_plane_class beta hb (Nat.pos_of_ne_zero hd)
    subst beta
    cases family with
    | hyperplane =>
      rw [BlowupF1FiberHReduction.eval_boundary,
        BlowupF1FiberHZeroValues.original_coefficients.1,
        BlowupF1FiberHZeroValues.original_coefficients.2]
      norm_num only
    | point => exact hP
    | primary => exact hN
    | exceptional j => fin_cases j; exact hK

end AxiomaticGW.BlowupF1FiberTableAssembly

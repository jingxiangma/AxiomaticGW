/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHRequest
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHConstant
public import AxiomaticGW.Surfaces.GenusTwoBlowupOrderedCertificate

/-!
# The exact remaining coefficients in the first F1 hyperplane equation

The target is F=(0,1), while the full shifted L24 source is E+F=(1,1).
The strict-order mask retains the established plane-degree-zero boundary.
The collected remainder has only classes 0 and E; after boundary evaluation,
only the exact H0 and K0 singleton coefficients can contribute. These two
coefficients are not assigned numerical values here. The resulting formula
concerns the formal reconstruction table; its geometric interpretation still
uses the existing reconstruction soundness hypotheses.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberHReduction
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder

-- Match the existing complete-row support API elaboration depth.
set_option maxRecDepth 20000

/-- The established boundary table, extended by zero at every nonzero full class. -/
def boundary (s : State target) : ℚ := SurfaceGenusTwoBlowupBoundary.value s.1 s.2

/-- In effective coordinates (E,F), anticanonical energy is a+2b. -/
theorem energy_formula (gamma : target.Curve) :
    target.effective.energy gamma = gamma 0 + 2 * gamma 1 := by
  change (∑ k : Fin 2, (![1, 2] : Fin 2 → ℕ) k * gamma k) = _
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Nat.one_mul]

/-- There is no earlier positive-plane state than the first hyperplane fiber state. -/
theorem earlier_planeDegree_zero (s : State target) (h : Earlier target s fiberState) :
    target.planeDegree s.1 = 0 := by
  rw [earlier_iff, energy_formula, energy_formula] at h
  change s.1 1 < 1 ∨ (s.1 1 = 1 ∧
    (s.2.rank < 0 ∨ (s.2.rank = 0 ∧ s.1 0 + 2 * s.1 1 < 0 + 2 * 1))) at h
  change s.1 1 = 0
  omega

/-- The original class split, together with strict order, leaves only 0 or E. -/
theorem earlier_subclass (gamma delta : target.Curve) (family : Family target)
    (he : Earlier target (gamma, family) fiberState)
    (hs : gamma + delta = fiber + target.exceptionalCurve 0) :
    gamma = 0 ∨ gamma = exceptional := by
  have h1 : gamma 1 = 0 := earlier_planeDegree_zero (gamma, family) he
  have h0 := congrFun hs 0
  change gamma 0 + delta 0 = 1 at h0
  have hg : gamma 0 = 0 ∨ gamma 0 = 1 := by omega
  rcases hg with hg | hg
  · left
    funext k
    fin_cases k
    · exact hg
    · exact h1
  · right
    funext k
    fin_cases k
    · exact hg
    · exact h1

/-- This is support of the actual collected remainder, not a proposed truncation. -/
theorem collected_remainder_support {t : ℚ × Multiset (Variable target)}
    (ht : t ∈ SurfaceGenusTwoBlowupHRow.remainder target 0 fiber) :
    t.2 = 0 ∨ ∃ gamma : target.Curve, ∃ family : Family target,
      (gamma = 0 ∨ gamma = exceptional) ∧
      family.query gamma ∈ SurfaceGenusTwo.canonicalQueries target gamma ∧
      t.2 = {Sum.inr (family.query gamma)} := by
  obtain ⟨ht, hne⟩ := Multiset.mem_filter.mp ht
  rcases L24Relation.collected_normalized_primary_canonical_support
    (SurfaceGenusTwoBlowupHPivots.pointCount target fiber)
    (SurfaceGenusTwoBlowupHPivots.sourceCurve target 0 fiber) _ ht with
    hz | ⟨gamma, c, hc, hm, delta, hd⟩
  · exact Or.inl hz
  · have ha := RationalTerms.mem_collect.mp ht
    have hcoef : RationalTerms.coefficient (SurfaceGenusTwoBlowupHPivots.row target 0 fiber)
        {Sum.inr c} ≠ 0 := by
      rw [← hm, ← ha.2.1]
      exact ha.2.2
    obtain ⟨family, hf⟩ := family_of_mem_canonicalQueries hc
    rw [← hf] at hm hcoef hc
    have hs := SurfaceGenusTwoBlowupHOtherFamilies.canonical_coefficient_support
      target 0 fiber gamma family (by decide +kernel) hcoef
    rcases hs with ⟨rfl, rfl⟩ | hs
    · exact (hne hm).elim
    · exact Or.inr ⟨gamma, family, earlier_subclass gamma delta family hs hd, hc, hm⟩

/-- Every class-zero family is strictly earlier, including the nominal dimension-incompatible P0. -/
theorem zero_earlier (family : Family target) : Earlier target (0, family) fiberState :=
  earlier_of_planeDegree_lt target _ _ (by change 0 < 1; decide +kernel)

/-- The strict-order mask of any boundary-compatible candidate is the existing boundary table.
No assumption is made about its own or later values. -/
theorem masked_eq_boundary (candidate : State target → ℚ)
    (hboundary : ∀ s, target.planeDegree s.1 = 0 → candidate s = boundary s) :
    SurfaceGenusTwoBlowupOrderedCertificate.earlierCandidate fiberState candidate = boundary := by
  funext s
  unfold SurfaceGenusTwoBlowupOrderedCertificate.earlierCandidate
  by_cases he : Earlier target s fiberState
  · rw [if_pos he]
    exact hboundary s (earlier_planeDegree_zero s he)
  · rw [if_neg he]
    symm
    apply SurfaceGenusTwoBlowupBoundary.value_of_ne_zero s.1 _ s.2
    intro hz
    apply he
    have hs : s = (0, s.2) := Prod.ext hz rfl
    rw [hs]
    exact zero_earlier s.2

/-- Only H0 and K0 are nonzero in the finite earlier boundary table.
The bound 2 is justified by the actual target energy through the bounded-row API. -/
theorem earlier_boundary_columns :
    SurfaceGenusTwoBlowupScalar.columns
      (SurfaceGenusTwoBlowupOrderedCertificate.earlierStates 2 fiberState boundary) =
      {hZero, kZero} := by
  decide +kernel

/-- Both surviving columns keep their full genus, class, descendant and divisor label. -/
theorem zero_columns_distinct : hZero ≠ kZero := by decide +kernel

/-- Exact boundary evaluation of the original complete row, with both remaining coefficients. -/
theorem eval_boundary :
    RationalTerms.eval (canonicalValuation boundary)
      (SurfaceGenusTwoBlowupRecursion.row 0 fiberState) =
      (1 / 288 : ℚ) - hZeroCoefficient / 960 - kZeroCoefficient / 2880 := by
  have hs : fiberState ∈ SurfaceGenusTwoBlowupBoundedCertificate.states target 2 := by
    rw [SurfaceGenusTwoBlowupBoundedCertificate.mem_states]
    decide +kernel
  have hr := SurfaceGenusTwoBlowupBoundedCertificate.replay_eq_row 0 2 fiberState
    (canonicalValuation boundary) hs (by decide +kernel)
  have he := SurfaceGenusTwoBlowupOrderedCertificate.masked_replay_eq_earlier_sum
    0 2 fiberState boundary
  rw [masked_eq_boundary boundary (fun _ _ ↦ rfl), hr, earlier_boundary_columns] at he
  have hk : hZero ∉ ({kZero} : Finset (Variable target)) := by
    simpa only [Finset.mem_singleton] using zero_columns_distinct
  simp only [Finset.sum_insert hk, Finset.sum_singleton] at he
  change RationalTerms.eval (canonicalValuation boundary)
    (SurfaceGenusTwoBlowupRecursion.row 0 fiberState) =
      SurfaceGenusTwoBlowupScalar.constant 0 fiberState +
        (hZeroCoefficient * canonicalValuation boundary (.inr (Family.hyperplane.query 0)) +
         kZeroCoefficient * canonicalValuation boundary (.inr ((Family.exceptional 0).query 0))) at he
  rw [canonicalValuation_query, canonicalValuation_query] at he
  simp only [boundary, SurfaceGenusTwoBlowupBoundary.value_zero,
    SurfaceGenusTwoBlowupBoundary.initial] at he
  rw [BlowupF1FiberHConstant.constant_eq] at he
  rw [he]
  ring

/-- The full equation evaluated at a boundary-compatible candidate retains its minus-one pivot. -/
theorem eval_row (candidate : State target → ℚ)
    (hboundary : ∀ s, target.planeDegree s.1 = 0 → candidate s = boundary s) :
    RationalTerms.eval (canonicalValuation candidate)
      (SurfaceGenusTwoBlowupRecursion.row 0 fiberState) =
      (1 / 288 : ℚ) - candidate fiberState -
        hZeroCoefficient / 960 - kZeroCoefficient / 2880 := by
  rw [SurfaceGenusTwoBlowupOrderedCertificate.eval_row_masked 0 fiberState candidate
    (by decide +kernel), masked_eq_boundary candidate hboundary, eval_boundary]
  change -1 * candidate fiberState + _ = _
  ring

/-- The original equation determines the requested descendant once the two exact coefficients
are checked. This hypothesis is the original full relation, not a solved recurrence. -/
theorem value_of_equation (candidate : State target → ℚ)
    (hboundary : ∀ s, target.planeDegree s.1 = 0 → candidate s = boundary s)
    (he : RationalTerms.eval (canonicalValuation candidate)
      (SurfaceGenusTwoBlowupRecursion.row 0 fiberState) = 0) :
    candidate fiberState =
      (1 / 288 : ℚ) - hZeroCoefficient / 960 - kZeroCoefficient / 2880 := by
  rw [eval_row candidate hboundary] at he
  linarith

/-- The well-founded formal table has exactly this reduction without extra hypotheses. -/
theorem reconstructed_value :
    SurfaceGenusTwoBlowupRecursion.values 0 fiberState =
      (1 / 288 : ℚ) - hZeroCoefficient / 960 - kZeroCoefficient / 2880 := by
  apply value_of_equation
  · intro s hs
    exact SurfaceGenusTwoBlowupRecursion.values_boundary 0 s hs
  · exact SurfaceGenusTwoBlowupRecursion.values_equations 0 fiberState (by decide +kernel)

end AxiomaticGW.BlowupF1FiberHReduction

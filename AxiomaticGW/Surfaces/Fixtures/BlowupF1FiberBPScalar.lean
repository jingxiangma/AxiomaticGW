/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberBPCoefficients

/-!
# The surviving four-point rational scalar

For the BP diagram with one genus-two flag, class-zero divisor
extraction fixes that flag, its curve class and its point allocation.
The rational component carries the full source class and all added points.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberBPCoefficients
open SurfacePolynomialReduction SurfaceGenusTwo GluingExpression
open BlowupF1FiberHReduction BlowupF1FiberHZeroCoefficients BlowupF1FiberHTwoFlagZero
open SurfaceGenusTwoBlowupPCoefficients

set_option maxRecDepth 20000

private theorem one_flag_terminal : ∀ (r : Fin 2) (m : Fin 3)
    (b : SurfaceBasisLabel target),
    RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
      (residualTerms ((SurfaceAncestorKey.ofLabels 2 (Fin 1) (by norm_num [StableArity])
        (0 : target.Curve) (Pi.single 0 1) ![b]).addPoints m.val)))
      {zeroVariable (requested r)} =
      if m.val = 0 ∧ b = requested r then 1 else 0 := by
  decide +kernel

private theorem paper_one_expanded (r : Fin 2) (n : ℕ) (hn : n ≤ 2)
    (delta : target.Curve) (a : Fin 3 → SurfaceBasisLabel target) :
    remainderPointCoefficient target (zeroVariable (requested r))
      (coefficientVertex target (zeroVariable (requested r)))
      (BelorousskiPandharipande.paperCotangentTerm 1) delta n a =
      ∑ split ∈ target.splittings delta, ∑ t : SurfaceBasisLabel target,
        t.inverseWeight * ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          (n.choose ij.1 : ℚ) *
            ((if split.1 = 0 then (if ij.1 = 0 ∧ t = requested r then 1 else 0) else 0) *
              SurfaceGenusZero.primaryScalar target (SurfaceGenusZero.pointValue target)
                split.2 ij.2 ![a 0, a 1, a 2, t.dual]) := by
  let w := zeroVariable (requested r)
  have hv : ∀ beta m, Sum.inr (SurfaceQuery.points target 2 beta m) ≠ w := fun beta m ↦
    SurfaceFirstDescendant.query_ne_points 0 beta (requested r) 0 m
  have hx : (BelorousskiPandharipande.paperCotangentTerm 1).expression.maxComponentGenus = 2 :=
    by decide +kernel
  rw [remainderPointCoefficient, if_pos hx]
  change remainderContraction target w (remainderVertex target w (coefficientVertex target w))
    (GetzlerGraphs.join (m := 0) (n := 3) 0 3
      (fundamental 2 (Fin 1) (by norm_num [StableArity]))
      (fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (![1], (0 : Fin 4 → ℕ))
    ((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 4)))
    delta n a = _
  have hl (b : SurfaceBasisLabel target) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 0 ⊕ Fin 3 ≃ Fin 3)) ∘ Sum.inl)) ∘
        finSuccEquiv' 0 = ![b] := by funext i; fin_cases i; rfl
  have hr (b : SurfaceBasisLabel target) :
      (Option.elim · b ((a ∘ (finSumFinEquiv : Fin 0 ⊕ Fin 3 ≃ Fin 3)) ∘ Sum.inr)) ∘
        finSuccEquiv' 3 = ![a 0, a 1, a 2, b] := by funext i; fin_cases i <;> rfl
  have hpsi : (![1] : Fin 1 → ℕ) = Pi.single 0 1 := by decide +kernel
  simp only [GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction, hl, hr, primaryPointVertex, and_self]
  apply Finset.sum_congr rfl
  intro split _
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [hpsi, remainderVertex_onePsi_of_not_points w hv]
  change _ * ((if split.1 = 0 then _ else (0 : ℚ)) * _) = _
  rw [show SurfaceGenusZero.variableCurve w = 0 from rfl, one_flag_terminal r ⟨ij.1, by omega⟩]

/-- Exact evaluation of the BP one-flag diagram at either requested divisor. -/
theorem paper_one_scalar (r : Fin 2) (n : ℕ) (hn : n ≤ 2)
    (delta : target.Curve) (a : Fin 3 → SurfaceBasisLabel target) :
    remainderPointCoefficient target (zeroVariable (requested r))
      (coefficientVertex target (zeroVariable (requested r)))
      (BelorousskiPandharipande.paperCotangentTerm 1) delta n a =
      (requested r).inverseWeight *
        SurfaceGenusZero.primaryScalar target (SurfaceGenusZero.pointValue target)
          delta n ![a 0, a 1, a 2, (requested r).dual] := by
  rw [paper_one_expanded r n hn]
  rw [Finset.sum_eq_single (0, delta)]
  · simp only [ite_true]
    rw [Finset.sum_eq_single (requested r)]
    · simp only [and_true]
      congr 1
      rw [Finset.sum_eq_single (0, n)]
      · simp only [ite_true, Nat.choose_zero_right, Nat.cast_one, one_mul]
      · intro ij hij hne
        have hi : ij.1 ≠ 0 := by
          intro hz
          have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
          apply hne
          exact Prod.ext hz (by omega)
        simp only [if_neg hi, zero_mul, mul_zero]
      · intro hm
        exact (hm (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega))).elim
    · intro t _ ht
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro ij _
      have hb : ¬ (ij.1 = 0 ∧ t = requested r) := fun h ↦ ht h.2
      simp only [if_neg hb, zero_mul, mul_zero]
    · intro hm
      exact (hm (Finset.mem_univ _)).elim
  · intro split hs hne
    have hz : split.1 ≠ 0 := by
      intro hz
      have he : split.1 + split.2 = delta := by
        rw [target.splittings_eq] at hs
        exact (target.effective.mem_splittings _ _ _).mp hs
      apply hne
      exact Prod.ext hz (by simpa only [hz, zero_add] using he)
    simp only [if_neg hz, zero_mul, mul_zero, Finset.sum_const_zero]
  · intro hm
    apply False.elim
    apply hm
    rw [target.splittings_eq]
    exact (target.effective.mem_splittings _ _ _).mpr (zero_add delta)

/-- The six assignments retain the original raw coefficient and signed inverse metric. -/
theorem oneFlagCoefficient_scalar (r : Fin 2) (n : ℕ) (hn : n ≤ 2)
    (beta : target.Curve) (a : Fin 3 → Fin 2) :
    oneFlagCoefficient r n beta a =
      BelorousskiPandharipande.rawPaperCoefficient 1 * ∑ e : Fin 6,
        (requested r).inverseWeight *
          SurfaceGenusZero.primaryScalar target (SurfaceGenusZero.pointValue target)
            beta n ![requested (a (BelorousskiPandharipande.labelPermutation e 0)),
              requested (a (BelorousskiPandharipande.labelPermutation e 1)),
              requested (a (BelorousskiPandharipande.labelPermutation e 2)),
              (requested r).dual] := by
  simp only [oneFlagCoefficient, remainder_orbit, paper_one_scalar r n hn, Function.comp_apply]

end AxiomaticGW.BlowupF1FiberBPCoefficients

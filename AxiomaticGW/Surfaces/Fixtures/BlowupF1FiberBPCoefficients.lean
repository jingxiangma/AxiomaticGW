/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHTwoFlagZero
public import AxiomaticGW.Surfaces.GenusTwoBlowupPCoefficients

/-!
# Divisor coefficients at class zero in the first F1 fiber BP equations

The primary diagram and both two-flag diagrams vanish at the requested
first descendant. In the remaining diagram the main component has only
its node flag. Its exact coefficient selects the zero remainder, no added
points and the requested divisor at that node. All six ordered assignments
and the inverse metric of the original graph are retained.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberBPCoefficients
open SurfacePolynomialReduction SurfaceGenusTwo GluingExpression
open BlowupF1FiberHReduction BlowupF1FiberHZeroCoefficients BlowupF1FiberHTwoFlagZero
open SurfaceGenusTwoBlowupPCoefficients

-- The unchanged BP term constructors require the existing coefficient elaboration depth.
set_option maxRecDepth 20000

private abbrev v (r : Fin 2) := zeroVariable (requested r)

private theorem not_points (r : Fin 2) (beta : target.Curve) (n : ℕ) :
    Sum.inr (SurfaceQuery.points target 2 beta n) ≠ v r :=
  SurfaceFirstDescendant.query_ne_points 0 beta (requested r) 0 n

private theorem two_points_wrong_dimension :
    ∀ (s b : Fin 2) (t : SurfaceBasisLabel target),
      ¬ ((SurfaceAncestorKey.ofLabels 2 (Fin 2) (by norm_num [StableArity]) (0 : target.Curve)
        (Pi.single s 1) ![requested b, t]).addPoints 2).DimensionCompatible := by
  decide +kernel

private theorem two_flags (r : Fin 2) (n : ℕ) (hn : n ≤ 2)
    (s b : Fin 2) (delta : target.Curve) (t : SurfaceBasisLabel target) :
    remainderVertex target (v r) (coefficientVertex target (v r)) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single s 1) inferInstance delta ![requested b, t] = 0 := by
  by_cases h : n ≤ 1
  · exact (firstCoefficientVertex_eq (X := target) 0 (requested r) 0) ▸
      remainder_two_flags_zero r n h s _ delta ![requested b, t]
  · have hn' : n = 2 := by omega
    subst n
    rw [remainderVertex_onePsi_of_not_points (v r) (not_points r)]
    split_ifs
    · rw [coefficient_residualTerms_onePsi_of_not_points (v r) (not_points r)]
      exact if_neg (two_points_wrong_dimension s b t)
    · rfl

private theorem paper_pair_zero (r : Fin 2) (n : ℕ) (hn : n ≤ 2)
    (s : Fin 2) (delta : target.Curve) (b : Fin 2) (c d : SurfaceBasisLabel target) :
    remainderPointCoefficient target (v r) (coefficientVertex target (v r))
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3))
      delta n ![requested b, c, d] = 0 := by
  have h0 : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
  have h1 : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
  have he : remainderPointCoefficient target (v r) (coefficientVertex target (v r))
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3))
      delta n ![requested b, c, d] =
      remainderContraction target (v r)
        (remainderVertex target (v r) (coefficientVertex target (v r)))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          (fundamental 2 (Fin 2) (by norm_num [StableArity]))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        (by exact (Pi.single s 1, (0 : Fin 3 → ℕ)))
        (by exact ((inferInstance : DecidableEq (Fin 2)), (inferInstance : DecidableEq (Fin 3))))
        delta n ![requested b, c, d] := by
    rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
    · rw [if_pos rfl, ← h0]
      rfl
    · rw [if_neg (by decide : (1 : Fin 2) ≠ 0), ← h1]
      rfl
  rw [he, pair_join]
  apply Finset.sum_eq_zero
  intro split _
  apply Finset.sum_eq_zero
  intro t _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij hij
  have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  change (n.choose ij.1 : ℚ) * (remainderVertex target (v r) _ _ 2 (Fin 2) _ _ _ _ _ * _) = 0
  rw [two_flags r ij.1 (by omega) s b]
  simp only [zero_mul, mul_zero]

/-- The single remaining weighted orbit, still with the original point pullback. -/
def oneFlagCoefficient (r : Fin 2) (n : ℕ) (beta : target.Curve) (a : Fin 3 → Fin 2) : ℚ :=
  BelorousskiPandharipande.rawPaperCoefficient 1 * ∑ e : Fin 6,
    remainderPointCoefficient target (zeroVariable (requested r))
      (coefficientVertex target (zeroVariable (requested r)))
      (BelorousskiPandharipande.orbitCotangentTerm 1 e) beta n (requested ∘ a)

/-- The one-flag diagram suffices for any divisor triple and at most two added points. -/
theorem oneFlagCoefficient_eq (r : Fin 2) (n : ℕ) (hn : n ≤ 2) (beta : target.Curve)
    (a : Fin 3 → Fin 2) :
    oneFlagCoefficient r n beta a = BelorousskiPandharipande.pointCoefficient target n beta
      (requested ∘ a) (zeroVariable (requested r)) := by
  have hc (i : Fin 20) (e : Fin 6) :
      SurfaceGenusTwo.pointCoefficient target (v r)
        (BelorousskiPandharipande.orbitCotangentTerm i e) beta n (requested ∘ a) =
      remainderPointCoefficient target (v r) (coefficientVertex target (v r))
        (BelorousskiPandharipande.orbitCotangentTerm i e) beta n (requested ∘ a) := by
    rw [remainderPointCoefficient_eq target (v r) _ rfl]
    change _ = SurfaceGenusTwo.pointCoefficient target (v r) _ (0 + beta) _ _
    rw [zero_add]
  have hzero (e : Fin 6) := paper_zero (v r) (not_points r) beta n
    ((requested ∘ a) ∘ BelorousskiPandharipande.labelPermutation e)
  have hpair (s : Fin 2) (e : Fin 6) :
      remainderPointCoefficient target (v r) (coefficientVertex target (v r))
        (BelorousskiPandharipande.orbitCotangentTerm (if s = 0 then 2 else 3) e)
          beta n (requested ∘ a) = 0 := by
    rw [remainder_orbit]
    let p := BelorousskiPandharipande.labelPermutation e
    have ha : (requested ∘ a) ∘ p = ![requested (a (p 0)), requested (a (p 1)),
        requested (a (p 2))] := by funext k; fin_cases k <;> rfl
    rw [show BelorousskiPandharipande.labelPermutation e = p from rfl, ha]
    exact paper_pair_zero r n hn s beta _ _ _
  unfold BelorousskiPandharipande.pointCoefficient
  change _ = ∑ i : Fin 4, _ * ∑ e : Fin 6, SurfaceGenusTwo.pointCoefficient target (v r) _ _ _ _
  simp only [hc, Fin.sum_univ_four]
  have hz (e : Fin 6) : remainderPointCoefficient target (v r) (coefficientVertex target (v r))
      (BelorousskiPandharipande.orbitCotangentTerm 0 e) beta n (requested ∘ a) = 0 :=
    (remainder_orbit _ _ _ _ _ _).trans (hzero e)
  have h2 := hpair 0
  have h3 := hpair 1
  simp only [ite_true, if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h2 h3
  change _ = _ * (∑ e, remainderPointCoefficient target (v r) _
    (BelorousskiPandharipande.orbitCotangentTerm 0 e) beta n (requested ∘ a)) + _ +
    _ * (∑ e, remainderPointCoefficient target (v r) _
    (BelorousskiPandharipande.orbitCotangentTerm 2 e) beta n (requested ∘ a)) +
    _ * (∑ e, remainderPointCoefficient target (v r) _
    (BelorousskiPandharipande.orbitCotangentTerm 3 e) beta n (requested ∘ a))
  simp only [hz, h2, h3, Finset.sum_const_zero, mul_zero, zero_add, add_zero]
  rfl

end AxiomaticGW.BlowupF1FiberBPCoefficients

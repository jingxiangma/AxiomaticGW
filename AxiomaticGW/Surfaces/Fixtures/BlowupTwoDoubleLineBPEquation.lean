/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLinePointPairs
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineBPRows
public import AxiomaticGW.Surfaces.GenusTwoBlowupPPrimary
public import AxiomaticGW.Surfaces.GenusTwoBlowupOrderedCertificate

/-! # The unshifted point equation on twice the strict line

The HHH equation has one additional primary point. Its genus-two columns
live on 0, L or 2L. All five actual canonical values at L vanish. At the requested class
the uniform BP formulas leave the hyperplane and point descendants with weights 18 and −36.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleLineBP
open SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupBoundedCertificate
open SurfaceGenusTwoBlowupScalar SurfacePolynomialReduction
open BlowupTwoDoubleLine (curve)
open BlowupTwoLineBP (canonicalFamily line)

set_option maxRecDepth 20000

abbrev X := SurfaceTarget.blowupTwo
abbrev actual := SurfaceGenusTwoBlowupRecursion.values (X := X) 0
private def classAt : Fin 3 → X.Curve := ![0, line, curve]
private def grid {n : ℕ} (c : Fin n → X.Curve) : List (State X) :=
  (List.ofFn c).flatMap fun beta ↦ (families X).map fun f ↦ (beta, f)

private def col {n : ℕ} (c : Fin n → X.Curve) (p : Fin n × Fin 5) : Variable X :=
  .inr ((canonicalFamily p.2).query (c p.1))

/-- All subclasses of the shifted source E₁+2L. -/
def shiftedClass : Fin 6 → X.Curve := ![0, X.exceptionalCurve 0, line, ![1, 0, 1],
  curve, ![1, 0, 2]]

private def family (shift : Bool) : Family X := if shift then .hyperplane else .point
private def source (shift : Bool) := if shift then curve + X.exceptionalCurve 0 else curve

private theorem supported {n : ℕ} (shift : Bool) (c : Fin n → X.Curve)
    (hc : ∀ p ∈ X.splittings (source shift), p.1 ∈ List.ofFn c) (v : Variable X)
    (hv : v ∈ (RationalTerms.collect (SurfaceGenusTwoBlowupRecursion.row 0
      (curve, family shift))).bind Prod.snd) : v ∈ columns (grid c) := by
  obtain ⟨t, ht, hv⟩ := Multiset.mem_bind.mp hv
  have sup : t.2 = 0 ∨ ∃ g : X.Curve, ∃ q ∈ SurfaceGenusTwo.canonicalQueries X g,
      t.2 = {Sum.inr q} ∧ ∃ d : X.Curve, g + d = source shift := by
    cases shift
    · exact BelorousskiPandharipande.collected_normalized_primary_canonical_support
        (X.effective.energy curve - 1) curve _ ht
    · exact L24Relation.collected_normalized_primary_canonical_support
        (X.effective.energy curve - 1) (curve + X.exceptionalCurve 0) _ ht
  obtain hz | ⟨g, q, hq, h, d, hg⟩ := sup
  · simp only [hz, Multiset.notMem_zero] at hv
  · rw [h, Multiset.mem_singleton] at hv
    obtain ⟨f, hf⟩ := family_of_mem_canonicalQueries hq
    apply (mem_columns _ _).mpr
    have hs : (g, d) ∈ X.splittings (source shift) := by
      rw [X.splittings_eq]
      exact (X.effective.mem_splittings _ _ _).mpr hg
    refine ⟨(g, f), List.mem_flatMap.mpr ⟨g, hc _ hs, ?_⟩, ?_⟩
    · exact List.mem_map.mpr ⟨f, mem_families X f, rfl⟩
    · simpa only [hf] using hv

private theorem row_eval {n : ℕ} (shift : Bool) (c : Fin n → X.Curve) (v : State X → ℚ)
    (hc : ∀ p ∈ X.splittings (source shift), p.1 ∈ List.ofFn c)
    (hgrid : columns (grid c) = Finset.univ.image (col c)) (inj : Function.Injective (col c)) :
    RationalTerms.eval (canonicalValuation v)
        (SurfaceGenusTwoBlowupRecursion.row 0 (curve, family shift)) =
      constant 0 (curve, family shift) + ∑ i : Fin n, ∑ j : Fin 5,
        singletonCoefficient 0 (curve, family shift) (col c (i, j)) *
          v (c i, canonicalFamily j) := by
  rw [← SurfaceGenusTwoBlowupScalar.replay_eq_row 0 (curve, family shift)
    (canonicalValuation v) (grid c) (supported shift c hc), replay, hgrid,
    Finset.sum_image (fun _ _ _ _ h ↦ inj h), Fintype.sum_prod_type]
  simp only [col, canonicalValuation_query]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h
  · rw [h, mul_zero]
  · rfl

/-- At 2L the full-class point coefficient is −36. No primary or exceptional column survives. -/
theorem full_coefficients (j : Fin 5) :
    singletonCoefficient 0 (curve, .point) (.inr ((canonicalFamily j).query curve)) =
      (![18, -36, 0, 0, 0] : Fin 5 → ℚ) j := by
  rw [singletonCoefficient_eq]
  have he : 0 < X.effective.energy curve := by decide +kernel
  fin_cases j
  · exact SurfaceGenusTwoBlowupPCoefficients.hyperplane_coefficient curve he
  · exact (SurfaceGenusTwoBlowupPCoefficients.point_coefficient curve he).trans (by decide +kernel)
  · exact (SurfaceGenusTwoBlowupPPrimary.canonical_primary_row curve he).2
  · exact SurfaceGenusTwoBlowupPCoefficients.exceptional_coefficient curve 0 he
  · exact SurfaceGenusTwoBlowupPCoefficients.exceptional_coefficient curve 1 he

/-- The exact remaining scalar after accounting for the three nonzero constant-curve seeds. -/
def residual : ℚ := constant 0 (curve, .point) +
  ∑ b : Fin 5, singletonCoefficient 0 (curve, .point) (.inr ((canonicalFamily b).query 0)) *
    (![-1/960, 0, 0, -1/2880, -1/2880] : Fin 5 → ℚ) b

private theorem seeds (b : Fin 5) : actual (0, canonicalFamily b) =
    (![-1/960, 0, 0, -1/2880, -1/2880] : Fin 5 → ℚ) b := by
  unfold actual
  rw [SurfaceGenusTwoBlowupRecursion.values_boundary 0 (0, canonicalFamily b)
    (map_zero X.planeDegree)]
  fin_cases b <;> decide +kernel

private theorem primitive_line (b : Fin 5) : actual (line, canonicalFamily b) = 0 := by
  unfold actual
  rw [BlowupTwoLineTable.values_eq (line, canonicalFamily b)
    (by change X.effective.energy line ≤ 1; decide +kernel)]
  fin_cases b <;> decide +kernel

/-- Original recurrence for the value that both point/point marking orders request. -/
theorem point_equation :
    36 * actual (curve, .point) = 18 * actual (curve, .hyperplane) + residual := by
  have hp : 0 < X.planeDegree curve := by decide +kernel
  have he := SurfaceGenusTwoBlowupRecursion.values_equations 0 (curve, .point) hp
  change RationalTerms.eval (canonicalValuation actual)
    (SurfaceGenusTwoBlowupRecursion.row 0 (curve, family false)) = 0 at he
  rw [row_eval false classAt actual (by decide +kernel) (by decide +kernel)
    (by change ∀ a b, col classAt a = col classAt b → a = b; decide +kernel)] at he
  change constant 0 (curve, .point) + (∑ c : Fin 3, ∑ b : Fin 5,
    singletonCoefficient 0 (curve, .point) (.inr ((canonicalFamily b).query (classAt c))) *
      actual (classAt c, canonicalFamily b)) = 0 at he
  have zero (b : Fin 5) : actual (classAt 0, canonicalFamily b) =
      (![-1/960, 0, 0, -1/2880, -1/2880] : Fin 5 → ℚ) b := seeds b
  have prim (b : Fin 5) : actual (classAt 1, canonicalFamily b) = 0 := primitive_line b
  rw [Fin.sum_univ_three] at he
  simp only [zero, prim, mul_zero, Finset.sum_const_zero, add_zero] at he
  change constant 0 (curve, .point) + ((∑ b : Fin 5, singletonCoefficient 0 (curve, .point)
      (.inr ((canonicalFamily b).query 0)) * _) + ∑ b : Fin 5, singletonCoefficient 0
      (curve, .point) (.inr ((canonicalFamily b).query curve)) *
      actual (curve, canonicalFamily b)) = 0 at he
  simp only [full_coefficients] at he
  have rhs : (∑ b : Fin 5, (![18,-36,0,0,0] : Fin 5 → ℚ) b * actual (curve, canonicalFamily b)) =
      18 * actual (curve, .hyperplane) - 36 * actual (curve, .point) := by
    rw [Fin.sum_univ_five]
    change 18 * actual (curve, .hyperplane) + -36 * actual (curve, .point) +
      0 * _ + 0 * _ + 0 * _ = _
    ring
  rw [rhs] at he
  unfold residual
  linarith only [he]

/-- The original shifted hyperplane pivot depends on its constant, its class-zero seeds, and
the canonical family on the one ruling E₁+L in the support of its shifted source. -/
theorem shifted_hyperplane_equation :
    actual (curve, .hyperplane) = constant 0 (curve, .hyperplane) +
      (∑ j : Fin 5, singletonCoefficient 0 (curve, .hyperplane)
        (.inr ((canonicalFamily j).query 0)) *
        (![-1/960, 0, 0, -1/2880, -1/2880] : Fin 5 → ℚ) j) +
      ∑ j : Fin 5, singletonCoefficient 0 (curve, .hyperplane)
        (.inr ((canonicalFamily j).query ![1,0,1])) * actual (![1,0,1], canonicalFamily j) := by
  let state : State X := (curve, .hyperplane)
  let v := SurfaceGenusTwoBlowupOrderedCertificate.earlierCandidate state actual
  have hp : 0 < X.planeDegree curve := by decide +kernel
  have he := SurfaceGenusTwoBlowupRecursion.values_equations 0 state hp
  rw [SurfaceGenusTwoBlowupOrderedCertificate.eval_row_masked 0 state actual hp] at he
  change -1 * actual state + RationalTerms.eval (canonicalValuation v)
    (SurfaceGenusTwoBlowupRecursion.row 0 (curve, family true)) = 0 at he
  rw [row_eval true shiftedClass v (by decide +kernel) (by decide +kernel)
    (by change ∀ a b, col shiftedClass a = col shiftedClass b → a = b; decide +kernel)] at he
  have rule (i : Fin 6) (j : Fin 5) : Earlier X (shiftedClass i, canonicalFamily j) state
      ↔ i.val < 4 := by
    rw [earlier_iff]
    fin_cases i <;> fin_cases j <;> decide +kernel
  have mask (i : Fin 6) (j : Fin 5) : v (shiftedClass i, canonicalFamily j) =
      if i.val < 4 then actual (shiftedClass i, canonicalFamily j) else 0 := by
    unfold v SurfaceGenusTwoBlowupOrderedCertificate.earlierCandidate
    by_cases hi : i.val < 4
    · rw [if_pos ((rule i j).mpr hi), if_pos hi]
    · rw [if_neg (fun h ↦ hi ((rule i j).mp h)), if_neg hi]
  have zero (j : Fin 5) : v (shiftedClass 0, canonicalFamily j) =
      (![-1/960, 0, 0, -1/2880, -1/2880] : Fin 5 → ℚ) j := (mask 0 j).trans (seeds j)
  have e (j : Fin 5) : v (shiftedClass 1, canonicalFamily j) = 0 := by
    refine (mask 1 j).trans ?_
    change SurfaceGenusTwoBlowupRecursion.values 0 (X.exceptionalCurve 0, canonicalFamily j) = 0
    rw [SurfaceGenusTwoBlowupRecursion.values_boundary 0 (X.exceptionalCurve 0, canonicalFamily j)
      (X.planeDegree_exceptionalCurve 0)]
    exact SurfaceGenusTwoBlowupBoundary.value_of_ne_zero _ (X.exceptionalCurve_ne_zero 0) _
  have l (j : Fin 5) : v (shiftedClass 2, canonicalFamily j) = 0 :=
    (mask 2 j).trans (primitive_line j)
  have r (j : Fin 5) : v (shiftedClass 3, canonicalFamily j) =
      actual (![1,0,1], canonicalFamily j) := mask 3 j
  have a (j : Fin 5) : v (shiftedClass 4, canonicalFamily j) = 0 := mask 4 j
  have b (j : Fin 5) : v (shiftedClass 5, canonicalFamily j) = 0 := mask 5 j
  rw [Fin.sum_univ_six] at he
  simp only [zero, e, l, r, a, b, mul_zero, Finset.sum_const_zero, add_zero] at he
  change -1 * actual (curve, .hyperplane) + (constant 0 (curve, .hyperplane) + (_ + _)) = 0 at he
  change actual _ = constant 0 _ + (∑ j : Fin 5, singletonCoefficient 0 (curve, family true)
    (col shiftedClass (0, j)) * _) + ∑ j : Fin 5, singletonCoefficient 0 (curve, family true)
    (col shiftedClass (3, j)) * _
  linarith only [he]

end AxiomaticGW.BlowupTwoDoubleLineBP

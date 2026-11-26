/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneShiftedSystem
public import AxiomaticGW.Coefficients.CollectedTerms

/-!
# Decreasing remainders of the plane genus-two system

The full normalized equations are collected before removing the three
canonical unknowns. Consequently every remaining dependency has degree
strictly below the degree being reconstructed, even when the original graph
terms contain cancelled variables at that degree or at the source degree.

Evaluation retains the constant and all lower-degree terms. Closing these
dependencies against a finite recursive state is a separate obligation.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open SurfacePolynomialReduction SurfaceGenusTwo

/-- The primary, H-descendant and P-descendant requests are distinct,
including at degree zero. -/
theorem planeCanonicalQueries_injective (d : ℕ) :
    Function.Injective (planeCanonicalQueries d) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl |
    simp only [planeCanonicalQueries, Matrix.cons_val_zero', Matrix.cons_val_succ',
      SurfaceQuery.points, SurfaceFirstDescendant.query,
      SurfaceQuery.mk.injEq, List.replicate_succ, List.cons.injEq,
      SurfaceInsertion.mk.injEq, reduceCtorEq, and_self, false_and, and_false] at hij

/-- The finite family removed from each row before recursion. -/
def planeCanonicalVariables (d : ℕ) : Finset (Variable .plane) :=
  Finset.univ.image (fun j ↦ Sum.inr (planeCanonicalQueries d j))

/-- Merge all coefficients before discarding the canonical block. -/
def planeShiftedRemainder (d : ℕ) (i : Fin 3) : RationalTerms (Variable .plane) :=
  (RationalTerms.collect (planeShiftedTerms d i)).filter
    (fun t ↦ ∀ v ∈ planeCanonicalVariables d, t.2 ≠ {v})

/-- The original affine genus-two bound holds in every selected row. -/
theorem planeShiftedTerms_bound (d : ℕ) (i : Fin 3) :
    NormalizedTermsBound ![d + 1] (planeShiftedTerms d i) := by
  fin_cases i <;> exact normalizedGenusTwoTerms_bound _ _ _ _ _

/-- Every dependency actually retained for recursion has smaller degree,
genus two and the exact dimension condition. Constants remain allowed. -/
theorem planeShiftedRemainder_dependencies (d : ℕ) (hd : 0 < d) (i : Fin 3)
    {t : ℚ × Multiset (Variable .plane)} (ht : t ∈ planeShiftedRemainder d i)
    (v : Variable .plane) (hv : v ∈ t.2) :
    SurfaceLowGenus.variableGenus v = 2 ∧ variableDimensionCompatible v ∧
      SurfaceGenusZero.variableCurve v 0 < d := by
  obtain ⟨ht, hex⟩ := Multiset.mem_filter.mp ht
  obtain ⟨hm, hc, hn⟩ := RationalTerms.mem_collect.mp ht
  obtain ⟨u, hu, he⟩ := Multiset.mem_map.mp (Multiset.mem_toFinset.mp hm)
  rcases planeShiftedTerms_bound d i u hu with hz | ⟨w, hw, hg, hdim, _⟩
  · exact (Multiset.notMem_zero v ((he.symm.trans hz) ▸ hv)).elim
  · have htw : t.2 = {w} := he.symm.trans hw
    rw [htw, Multiset.mem_singleton] at hv
    subst w
    refine ⟨hg, hdim, planeShiftedTerms_lower d hd i v ?_ ?_⟩
    · intro j heq
      exact hex _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
        (htw.trans (congrArg (fun w : Variable .plane ↦ ({w} : Multiset _)) heq).symm)
    · rw [← htw, ← hc]
      exact hn

/-- The complete equation is exactly its matrix row plus the collected remainder. -/
theorem eval_planeShiftedTerms (v : Variable .plane → ℚ) (d : ℕ) (i : Fin 3) :
    RationalTerms.eval v (planeShiftedTerms d i) =
      (planeShiftedMatrix d).mulVec (fun j ↦ v (Sum.inr (planeCanonicalQueries d j))) i +
        RationalTerms.eval v (planeShiftedRemainder d i) := by
  have h := RationalTerms.eval_isolate_finset v
    (RationalTerms.collect (planeShiftedTerms d i)) (planeCanonicalVariables d)
  rw [RationalTerms.eval_collect] at h
  simp only [RationalTerms.coefficient_collect, Algebra.algebraMap_self_apply] at h
  rw [planeCanonicalVariables, Finset.sum_image] at h
  · exact h
  · intro j _ k _ hjk
    exact planeCanonicalQueries_injective d (Sum.inr.inj hjk)

/-- The right-hand side retains the constant with its required negative sign. -/
def planeShiftedRightHandSide (v : Variable .plane → ℚ) (d : ℕ) : Fin 3 → ℚ :=
  fun i ↦ -RationalTerms.eval v (planeShiftedRemainder d i)

/-- Evaluation of the right-hand side uses only smaller-degree data. -/
theorem planeShiftedRightHandSide_congr (d : ℕ) (hd : 0 < d)
    (v w : Variable .plane → ℚ)
    (h : ∀ q, SurfaceLowGenus.variableGenus q = 2 → variableDimensionCompatible q →
      SurfaceGenusZero.variableCurve q 0 < d → v q = w q) :
    planeShiftedRightHandSide v d = planeShiftedRightHandSide w d := by
  funext i
  apply congrArg Neg.neg
  apply RationalTerms.eval_congr
  intro t ht q hq
  obtain ⟨hg, hdim, hlt⟩ := planeShiftedRemainder_dependencies d hd i ht q hq
  exact h q hg hdim hlt

/-- The original equations, without any assumed solved recurrence, determine
the canonical values from their strictly smaller-degree remainder. -/
theorem planeShiftedValues_eq_solve (v : Variable .plane → ℚ) (d : ℕ) (hd : 0 < d)
    (h : ∀ i, RationalTerms.eval v (planeShiftedTerms d i) = 0) :
    (fun j ↦ v (Sum.inr (planeCanonicalQueries d j))) =
      planeShiftedSolve d (planeShiftedRightHandSide v d) := by
  apply planeShiftedSolve_unique d hd
  funext i
  have he := h i
  rw [eval_planeShiftedTerms] at he
  exact eq_neg_of_add_eq_zero_left he

/-- Agreement on smaller degrees and the original equations forces agreement
on the three canonical values at the next degree. -/
theorem planeShiftedValues_unique_of_lower (d : ℕ) (hd : 0 < d)
    (v w : Variable .plane → ℚ)
    (hv : ∀ i, RationalTerms.eval v (planeShiftedTerms d i) = 0)
    (hw : ∀ i, RationalTerms.eval w (planeShiftedTerms d i) = 0)
    (hlower : ∀ q, SurfaceLowGenus.variableGenus q = 2 → variableDimensionCompatible q →
      SurfaceGenusZero.variableCurve q 0 < d → v q = w q) :
    (fun j ↦ v (Sum.inr (planeCanonicalQueries d j))) =
      fun j ↦ w (Sum.inr (planeCanonicalQueries d j)) := by
  rw [planeShiftedValues_eq_solve v d hd hv, planeShiftedValues_eq_solve w d hd hw,
    planeShiftedRightHandSide_congr d hd v w hlower]

end AxiomaticGW.BelorousskiPandharipande

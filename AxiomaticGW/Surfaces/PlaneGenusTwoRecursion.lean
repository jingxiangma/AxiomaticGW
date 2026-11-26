/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneGenusTwoInitial

/-!
# Terminating recursion for the three plane genus-two families

Each positive degree solves the full shifted BP system, using only canonical
triples at strictly smaller degrees. The degree-zero primary entry is
computed from the constant of the original BP equation and the existing H
seed; the P query at zero degree vanishes by dimension. This module proves
the algebraic recursion and its determination by the original equations.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open SurfacePolynomialReduction

/-- Extend a table of canonical triples to the variable type used by the
equations. All other variables receive zero and are absent from the proved
support of the selected equations. This is not a general query evaluator. -/
def planeCanonicalValuation (values : ℕ → Fin 3 → ℚ) (v : Variable .plane) : ℚ :=
  ∑ j, if v = Sum.inr (planeCanonicalQueries (SurfaceGenusZero.variableCurve v 0) j)
    then values (SurfaceGenusZero.variableCurve v 0) j else 0

/-- The canonical extension recovers every supplied table entry. -/
theorem planeCanonicalValuation_apply (values : ℕ → Fin 3 → ℚ) (d : ℕ) (j : Fin 3) :
    planeCanonicalValuation values (Sum.inr (planeCanonicalQueries d j)) = values d j := by
  simp only [planeCanonicalValuation, SurfaceGenusZero.variableCurve,
    planeCanonicalQueries_beta, Matrix.cons_val_zero, Sum.inr.injEq,
    (planeCanonicalQueries_injective d).eq_iff, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The initial primary entry is computed from the original equation's
lower-genus constant and the H seed. It is not an additional numerical input.
Evaluating that exact constant efficiently is a separate computational task. -/
def planeCanonicalInitial : Fin 3 → ℚ :=
  ![(planeShiftedConstant 0 1 - 1 / 80) / 36, -1 / 960, 0]

/-- The initial triple follows from the complete initial equation, the H
seed and dimension vanishing of the nominal zero-degree P query. -/
theorem planeCanonicalInitial_eq_of_equation (v : Variable .plane → ℚ)
    (heq : RationalTerms.eval v (planeShiftedTerms 0 1) = 0)
    (hH : v (Sum.inr (planeCanonicalQueries 0 1)) = -1 / 960)
    (hP : v (Sum.inr (planeCanonicalQueries 0 2)) = 0) :
    (fun j ↦ v (Sum.inr (planeCanonicalQueries 0 j))) = planeCanonicalInitial := by
  have hN := planeInitialPrimary_of_equation v heq hH
  generalize hc : planeShiftedConstant 0 1 = c at hN
  rw [planeCanonicalInitial, hc]
  funext j
  fin_cases j
  · exact hN
  · exact hH
  · exact hP

/-- Compute the canonical triple by strictly decreasing degree. The guard
makes the local table total; no actual remainder dependency reaches its
zero branch, by `planeShiftedRemainder_canonical_dependencies`. -/
def planeCanonicalValues (d : ℕ) : Fin 3 → ℚ :=
  if d = 0 then planeCanonicalInitial else
    planeShiftedSolve d (planeShiftedRightHandSide
      (planeCanonicalValuation (fun b ↦ if _hlt : b < d then planeCanonicalValues b else 0)) d)
termination_by d
decreasing_by exact _hlt

theorem planeCanonicalValues_zero : planeCanonicalValues 0 = planeCanonicalInitial := by
  rw [planeCanonicalValues, if_pos rfl]

/-- The guarded recursion agrees with evaluation using the complete earlier table. -/
theorem planeCanonicalValues_step (d : ℕ) (hd : 0 < d) :
    planeCanonicalValues d = planeShiftedSolve d
      (planeShiftedRightHandSide (planeCanonicalValuation planeCanonicalValues) d) := by
  rw [planeCanonicalValues, if_neg (Nat.ne_of_gt hd)]
  congr 1
  apply planeShiftedRightHandSide_congr_canonical d hd
  intro b hb j
  rw [planeCanonicalValuation_apply, planeCanonicalValuation_apply, dif_pos hb]

/-- The computed values satisfy each original full shifted BP equation. -/
theorem planeCanonicalValues_equations (d : ℕ) (hd : 0 < d) (i : Fin 3) :
    RationalTerms.eval (planeCanonicalValuation planeCanonicalValues)
      (planeShiftedTerms d i) = 0 := by
  rw [eval_planeShiftedTerms]
  simp only [planeCanonicalValuation_apply]
  rw [planeCanonicalValues_step d hd]
  have he := congrFun (planeShiftedSolve_spec d hd
    (planeShiftedRightHandSide (planeCanonicalValuation planeCanonicalValues) d)) i
  rw [he]
  exact neg_add_cancel _

/-- The fixed initial triple and the original equations determine the computed
values. This assumption is the unsolved BP polynomial, not a copied recurrence. -/
theorem eq_planeCanonicalValues_of_equations (v : Variable .plane → ℚ)
    (hzero : ∀ j, v (Sum.inr (planeCanonicalQueries 0 j)) = planeCanonicalInitial j)
    (heq : ∀ d, 0 < d → ∀ i, RationalTerms.eval v (planeShiftedTerms d i) = 0)
    (d : ℕ) : (fun j ↦ v (Sum.inr (planeCanonicalQueries d j))) =
      planeCanonicalValues d := by
  have hu := planeShiftedValues_unique v (planeCanonicalValuation planeCanonicalValues)
    (fun j ↦ by rw [planeCanonicalValuation_apply, planeCanonicalValues_zero]; exact hzero j)
    heq planeCanonicalValues_equations d
  simpa only [planeCanonicalValuation_apply] using hu

end AxiomaticGW.BelorousskiPandharipande

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupBoundary
public import AxiomaticGW.Surfaces.GenusTwoBlowupValuation
public import AxiomaticGW.Surfaces.GenusTwoBlowupHRow
public import AxiomaticGW.Surfaces.GenusTwoBlowupPRow
public import AxiomaticGW.Surfaces.GenusTwoBlowupNRow
public import AxiomaticGW.Surfaces.GenusTwoBlowupKRow

/-!
# Terminating canonical genus-two reconstruction on both blowups

The complete H/P/N/K rows determine each positive-plane-degree value from
strictly earlier full-class states. The order is lexicographic in plane degree,
family rank and energy; exceptional labels and full curve coordinates remain in
the table key. A guarded recursive call supplies no ancestor or later-value oracle.

The plane-zero boundary is the finite divisor seed table at class zero and zero
on positive exceptional classes. Its geometric interpretation is proved separately
from the original initial BP equations and exceptional evaluation support. Here
termination, the selected original equations and uniqueness are algebraic results.
No equation or recurrence is replaced by a numerical formula from a paper.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupRecursion
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
variable {X : SurfaceTarget}

-- The existing shifted H row uses the complete 815-column L24 source dispatch.
set_option maxRecDepth 20000

/-- Computable comparison for the reconstruction guard; the instance is local to this module. -/
local instance earlierDecidable : DecidableRel (Earlier X) :=
  fun s t ↦ decidable_of_iff _ (earlier_iff X s t).symm

/-- Select the unchanged full equation for a canonical sector. The chosen exceptional
shift affects H and N; each K sector uses its own exceptional divisor. -/
def row (i : Fin X.blowups) (s : State X) : RationalTerms (Variable X) :=
  match s.2 with
  | .hyperplane => SurfaceGenusTwoBlowupHPivots.row X i s.1
  | .point => SurfaceGenusTwoBlowupPRow.row X s.1
  | .primary => SurfaceGenusTwoBlowupNRelation.row X i s.1
  | .exceptional j => SurfaceGenusTwoBlowupKRow.row X j s.1

/-- The scalar step obtained by isolating the actual pivot of the selected original row. -/
def step (i : Fin X.blowups) (values : Variable X → ℚ) (s : State X) : ℚ :=
  match s.2 with
  | .hyperplane => SurfaceGenusTwoBlowupHRow.step X i values s.1
  | .point => SurfaceGenusTwoBlowupPRow.step X values s.1
  | .primary => SurfaceGenusTwoBlowupNRow.step X i values s.1
  | .exceptional j => SurfaceGenusTwoBlowupKRow.step X j values s.1

private theorem energy_pos {beta : X.Curve} (hd : 0 < X.planeDegree beta) :
    0 < X.effective.energy beta := by
  apply Nat.pos_of_ne_zero
  intro he
  have hb := (X.effective.energy_eq_zero_iff beta).mp he
  rw [hb, map_zero] at hd
  omega

/-- The chosen original equation determines its own value at positive plane degree. -/
theorem value_eq_step (i : Fin X.blowups) (values : Variable X → ℚ) (s : State X)
    (hd : 0 < X.planeDegree s.1) (he : RationalTerms.eval values (row i s) = 0) :
    values (.inr (s.2.query s.1)) = step i values s := by
  obtain ⟨beta, family⟩ := s
  have hb := energy_pos hd
  cases family with
  | hyperplane => exact SurfaceGenusTwoBlowupHRow.value_eq_step X i values beta hb he
  | point => exact SurfaceGenusTwoBlowupPRow.value_eq_step X values beta hb hd he
  | primary => exact SurfaceGenusTwoBlowupNRow.value_eq_step X i values beta hd he
  | exceptional j => exact SurfaceGenusTwoBlowupKRow.value_eq_step X j values beta hb he

/-- The complete collected step depends only on strictly earlier canonical states. -/
theorem step_congr (i : Fin X.blowups) (values other : Variable X → ℚ) (s : State X)
    (hd : 0 < X.planeDegree s.1)
    (h : ∀ t : State X, Earlier X t s →
      values (.inr (t.2.query t.1)) = other (.inr (t.2.query t.1))) :
    step i values s = step i other s := by
  obtain ⟨beta, family⟩ := s
  have hb := energy_pos hd
  cases family with
  | hyperplane =>
      exact SurfaceGenusTwoBlowupHRow.step_congr X i values other beta hb
        (fun gamma f he ↦ h (gamma, f) he)
  | point =>
      exact SurfaceGenusTwoBlowupPRow.step_congr X values other beta hb
        (fun gamma f he ↦ h (gamma, f) he)
  | primary =>
      exact SurfaceGenusTwoBlowupNRow.step_congr X i values other beta
        (fun gamma f he ↦ h (gamma, f) he)
  | exceptional j =>
      exact SurfaceGenusTwoBlowupKRow.step_congr X j values other beta hb
        (fun gamma f he ↦ h (gamma, f) he)

/-- Substituting the solved step satisfies the unchanged selected polynomial equation. -/
theorem equation_of_value_eq_step (i : Fin X.blowups) (v : Variable X → ℚ) (s : State X)
    (hd : 0 < X.planeDegree s.1)
    (h : v (.inr (s.2.query s.1)) = step i v s) :
    RationalTerms.eval v (row i s) = 0 := by
  obtain ⟨beta, family⟩ := s
  have hb := energy_pos hd
  cases family with
  | hyperplane =>
      rw [row, SurfaceGenusTwoBlowupHRow.eval_row X i v beta hb]
      change v (SurfaceGenusTwoBlowupHPivots.hColumn X beta) =
        RationalTerms.eval v (SurfaceGenusTwoBlowupHRow.remainder X i beta) at h
      rw [h]
      ring
  | point =>
      rw [row, SurfaceGenusTwoBlowupPRow.eval_row X v beta hb]
      change v (.inr (Family.point.query beta)) =
        RationalTerms.eval v (SurfaceGenusTwoBlowupPRow.remainder X beta) /
          (18 * (X.planeDegree beta : ℚ)) at h
      have hn : (18 * (X.planeDegree beta : ℚ)) ≠ 0 :=
        mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd))
      have hm := (eq_div_iff hn).mp h
      linarith
  | primary =>
      rw [row, SurfaceGenusTwoBlowupNRow.eval_row X i v beta]
      change v (.inr (Family.primary.query beta)) =
        -RationalTerms.eval v (SurfaceGenusTwoBlowupNRow.remainder X i beta) /
          (6 * (X.planeDegree beta : ℚ)) at h
      have hn : (6 * (X.planeDegree beta : ℚ)) ≠ 0 :=
        mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd))
      have hm := (eq_div_iff hn).mp h
      linarith
  | exceptional j =>
      rw [row, SurfaceGenusTwoBlowupKRow.eval_row X j v beta hb]
      change v (.inr ((Family.exceptional j).query beta)) =
        RationalTerms.eval v (SurfaceGenusTwoBlowupKRow.remainder X j beta) / 18 at h
      have hm := (eq_div_iff (show (18 : ℚ) ≠ 0 by norm_num)).mp h
      linarith

/-- Compute all canonical values by the proved full-class well-founded order.
The guard's zero branch is absent from every genuine remainder dependency. -/
def values (i : Fin X.blowups) (s : State X) : ℚ :=
  if X.planeDegree s.1 = 0 then SurfaceGenusTwoBlowupBoundary.value s.1 s.2 else
    step i (canonicalValuation
      (fun t ↦ if _hlt : Earlier X t s then values i t else 0)) s
termination_by measure X s
decreasing_by exact _hlt

/-- Plane-zero states have the finite boundary value, with every full class retained. -/
theorem values_boundary (i : Fin X.blowups) (s : State X) (hd : X.planeDegree s.1 = 0) :
    values i s = SurfaceGenusTwoBlowupBoundary.value s.1 s.2 := by
  rw [values, if_pos hd]

/-- Removing the recursion guard preserves evaluation of the complete collected step. -/
theorem values_step (i : Fin X.blowups) (s : State X) (hd : 0 < X.planeDegree s.1) :
    values i s = step i (canonicalValuation (values i)) s := by
  rw [values, if_neg (Nat.ne_of_gt hd)]
  apply step_congr i _ _ s hd
  intro t ht
  rw [canonicalValuation_query, canonicalValuation_query, dif_pos ht]

/-- Every computed positive-plane-degree entry satisfies its original selected full row. -/
theorem values_equations (i : Fin X.blowups) (s : State X) (hd : 0 < X.planeDegree s.1) :
    RationalTerms.eval (canonicalValuation (values i)) (row i s) = 0 := by
  apply equation_of_value_eq_step i _ s hd
  rw [canonicalValuation_query]
  exact values_step i s hd

/-- The boundary and original full equations uniquely determine the computed table.
The hypotheses are unsolved polynomial equations, not an assumed numerical recurrence. -/
theorem eq_values_of_equations (i : Fin X.blowups) (v : Variable X → ℚ)
    (hzero : ∀ s : State X, X.planeDegree s.1 = 0 →
      v (.inr (s.2.query s.1)) = SurfaceGenusTwoBlowupBoundary.value s.1 s.2)
    (heq : ∀ s : State X, 0 < X.planeDegree s.1 → RationalTerms.eval v (row i s) = 0)
    (s : State X) : v (.inr (s.2.query s.1)) = values i s := by
  induction s using (earlier_wellFounded X).induction with
  | h s ih =>
      by_cases hd : X.planeDegree s.1 = 0
      · rw [values_boundary i s hd]
        exact hzero s hd
      · have hp := Nat.pos_of_ne_zero hd
        rw [value_eq_step i v s hp (heq s hp), values_step i s hp]
        apply step_congr i _ _ s hp
        intro t ht
        rw [canonicalValuation_query]
        exact ih t ht

/-- Any two valuations satisfying the same boundary and original rows agree on every
canonical full-class request. -/
theorem values_unique (i : Fin X.blowups) (v w : Variable X → ℚ)
    (hvzero : ∀ s : State X, X.planeDegree s.1 = 0 →
      v (.inr (s.2.query s.1)) = SurfaceGenusTwoBlowupBoundary.value s.1 s.2)
    (hwzero : ∀ s : State X, X.planeDegree s.1 = 0 →
      w (.inr (s.2.query s.1)) = SurfaceGenusTwoBlowupBoundary.value s.1 s.2)
    (hv : ∀ s : State X, 0 < X.planeDegree s.1 → RationalTerms.eval v (row i s) = 0)
    (hw : ∀ s : State X, 0 < X.planeDegree s.1 → RationalTerms.eval w (row i s) = 0)
    (s : State X) : v (.inr (s.2.query s.1)) = w (.inr (s.2.query s.1)) := by
  rw [eq_values_of_equations i v hvzero hv s, eq_values_of_equations i w hwzero hw s]

/-- The selected row equations follow from the unchanged original primary BP and L24 families. -/
theorem row_eq_zero_of_original_equations (i : Fin X.blowups) (v : Variable X → ℚ)
    (hBP : ∀ n beta a,
      RationalTerms.eval v (SurfaceGenusTwoBlowupNRelation.bpRow X n beta a) = 0)
    (hL : ∀ n beta (a : Fin 4 → SurfaceBasisLabel X),
      RationalTerms.eval v (L24Relation.normalizedGenusTwoTerms X n beta 0
        (SurfaceGenusZero.pointLabels a n)) = 0)
    (s : State X) : RationalTerms.eval v (row i s) = 0 := by
  obtain ⟨beta, family⟩ := s
  cases family with
  | hyperplane => exact hL _ _ _
  | point => exact hBP _ _ _
  | primary =>
      exact SurfaceGenusTwoBlowupNRelation.eval_row_eq_zero i beta v
        (hBP _ _ _) (hBP _ _ _) (hBP _ _ _) (hBP _ _ _)
  | exceptional j => exact hBP _ _ _

/-- The same original BP family supplies the finite initial equation on either blowup. -/
theorem initialEquation_of_original_BP (v : Variable X → ℚ)
    (hBP : ∀ n beta a,
      RationalTerms.eval v (SurfaceGenusTwoBlowupNRelation.bpRow X n beta a) = 0) :
    SurfaceGenusTwoBlowupBoundary.InitialEquation X v := by
  cases X with
  | plane => trivial
  | hirzebruchOne => exact hBP 0 ![1, 0] (fun _ ↦ .exceptional 0)
  | blowupTwo => exact hBP 0 ![0, 0, 1] ![.exceptional 0, .exceptional 1, .hyperplane]

/-- The terminating table agrees with actual canonical GW queries from the original
unsolved equations, finite divisor seeds, dimension and named exceptional support.
The primitive geometric producers of these equations are separate theorems. -/
theorem values_eq_eval_of_original_equations (i : Fin X.blowups)
    {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (T : SurfaceTheoryIdentification X Omega)
    (V : StableMapIntersection U) (hV : ExceptionalPointSupport V)
    (hHtwo : (SurfaceSeed.genusTwoHyperplane : SurfaceSeed X).query.eval U = -1 / 960)
    (hEtwo : ∀ j, (SurfaceSeed.genusTwoExceptional j : SurfaceSeed X).query.eval U =
      -1 / 2880)
    (hBP : ∀ n beta a, RationalTerms.eval (variableEval U P)
      (SurfaceGenusTwoBlowupNRelation.bpRow X n beta a) = 0)
    (hL : ∀ n beta (a : Fin 4 → SurfaceBasisLabel X),
      RationalTerms.eval (variableEval U P) (L24Relation.normalizedGenusTwoTerms X n beta 0
        (SurfaceGenusZero.pointLabels a n)) = 0)
    (s : State X) : values i s = (s.2.query s.1).eval U := by
  symm
  apply eq_values_of_equations i (variableEval U P)
  · intro t ht
    exact (SurfaceGenusTwoBlowupBoundary.value_eq_eval_of_initialEquation i U P T V hV
      hHtwo hEtwo (initialEquation_of_original_BP _ hBP) t.1 ht t.2).symm
  · intro t _
    exact row_eq_zero_of_original_equations i _ hBP hL t

end AxiomaticGW.SurfaceGenusTwoBlowupRecursion

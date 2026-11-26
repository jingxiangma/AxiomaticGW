/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Candidates
public import AxiomaticGW.Surfaces.ScalarPointRelabel

/-! # Reusing identical decorated graphs at the four pulled-back divisor labels -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoLineH.Frame

/-- The unweighted contraction before applying the original L24 coefficient. -/
def unweighted (i : Fin 815) : ℚ :=
  let z := L24Gluing.term i
  z.expression.scalarPointContraction .blowupTwo (fun _ ↦ lowerVertex)
    z.decoration z.labels shifted 0 labels

private theorem factor (i : Fin 815) (hg : (L24Gluing.term i).expression.maxComponentGenus < 2) :
    cachedWeighted i = L24CorrectionsReplay.fullClaim i * unweighted i := by
  rw [cachedWeighted_eq]
  by_cases hc : L24CorrectionsReplay.fullClaim i = 0
  · simp only [weighted, hc, true_or, if_true, zero_mul]
  · simp only [weighted, hc, false_or, not_le_of_gt hg, if_false, unweighted,
      GluingExpression.scalarPointContraction_eq]
    rw [GluingExpression.zeroPointContraction_eq .blowupTwo (fun _ ↦ lowerVertex)]

/-- Read the original graph below one outer relabelling, together with its marking type. -/
def underlying {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) :
    (T : Type) × (f : Fintype T) × @GluingExpression g T f :=
  match x with
  | @GluingExpression.relabel _ _ _ _ _ _ y => ⟨_, _, y⟩
  | y => ⟨_, _, y⟩

/-- A transferred value retains both rational weights and the entire node contraction. -/
theorem transfer (i j : Fin 815) (hraw : unweighted i = unweighted j)
    (hvalue : cachedWeighted i = candidate i)
    (check : (L24Gluing.term i).expression.maxComponentGenus < 2 ∧
      (L24Gluing.term j).expression.maxComponentGenus < 2 ∧
      L24CorrectionsReplay.fullClaim i ≠ 0 ∧
      L24CorrectionsReplay.fullClaim i * candidate j =
        L24CorrectionsReplay.fullClaim j * candidate i) :
    cachedWeighted j = candidate j := by
  obtain ⟨hi, hj, hn, hc⟩ := check
  rw [factor i hi] at hvalue
  rw [factor j hj, ← hraw]
  apply mul_left_cancel₀ hn
  rw [mul_left_comm, hvalue, ← hc]

/-- Positions removed by the original higher-genus or zero-weight guard. -/
theorem inactive (j : Fin 815)
    (h : (L24CorrectionsReplay.fullClaim j = 0 ∨
      2 ≤ (L24Gluing.term j).expression.maxComponentGenus) ∧ candidate j = 0) :
    cachedWeighted j = candidate j := by
  rw [cachedWeighted, if_pos h.1, h.2]

end AxiomaticGW.BlowupTwoLineH.Frame

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneGenusTwoScalar
public import AxiomaticGW.Surfaces.PlaneGenusTwoInitialValues

/-!
# Finite certificates for the canonical plane genus-two values

Every degree through the held bound is checked, including zero entries.
The scalar remainder equals the original complete BP remainder. Strong
induction therefore identifies accepted tables with the already proved
terminating reconstruction, without introducing a new numerical seed.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande

/-- Scalar remainder evaluation depends only on strictly earlier triples. -/
theorem planeScalarRemainder_congr (v w : ℕ → Fin 3 → ℚ) (d : ℕ)
    (h : ∀ b, b < d → v b = w b) (i : Fin 3) :
    planeScalarRemainder v d i = planeScalarRemainder w d i := by
  unfold planeScalarRemainder
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [h b.val b.isLt]

/-- The scalar calculation gives the same step as the full original polynomial. -/
theorem planeCanonicalValues_step_scalar (d : ℕ) (hd : 0 < d) :
    planeCanonicalValues d =
      planeShiftedSolve d (fun i ↦ -planeScalarRemainder planeCanonicalValues d i) := by
  rw [planeCanonicalValues_step d hd]
  congr 1
  funext i
  exact congrArg Neg.neg (planeScalarRemainder_eq planeCanonicalValues d hd i).symm

/-- Check the derived initial triple or the complete scalar recursion at one degree. -/
def planeCheckCanonicalRow (values : ℕ → Fin 3 → ℚ) (d : ℕ) : Bool :=
  if d = 0 then decide (values d = ![0, -1 / 960, 0]) else
    decide (values d = planeShiftedSolve d (fun i ↦ -planeScalarRemainder values d i))

/-- Check every degree in the independently specified bound. -/
def planeCheckCanonicalTable (bound : ℕ) (values : ℕ → Fin 3 → ℚ) : Bool :=
  decide (∀ d : Fin (bound + 1), planeCheckCanonicalRow values d.val = true)

/-- A completely checked finite table agrees with the original reconstruction. -/
theorem planeCheckCanonicalTable_sound (bound : ℕ) (values : ℕ → Fin 3 → ℚ)
    (hcheck : planeCheckCanonicalTable bound values = true)
    (d : ℕ) (hd : d ≤ bound) : values d = planeCanonicalValues d := by
  rw [planeCheckCanonicalTable, decide_eq_true_eq] at hcheck
  induction d using Nat.strong_induction_on with
  | h d ih =>
    have hrow := hcheck ⟨d, Nat.lt_succ_of_le hd⟩
    change planeCheckCanonicalRow values d = true at hrow
    by_cases hz : d = 0
    · subst d
      rw [planeCheckCanonicalRow, if_pos rfl, decide_eq_true_eq] at hrow
      exact hrow.trans planeCanonicalValues_initial.symm
    · rw [planeCheckCanonicalRow, if_neg hz, decide_eq_true_eq] at hrow
      rw [hrow, planeCanonicalValues_step_scalar d (Nat.pos_of_ne_zero hz)]
      congr 1
      funext i
      congr 1
      exact planeScalarRemainder_congr values planeCanonicalValues d
        (fun b hb ↦ ih b hb (Nat.le_of_lt hb |>.trans hd)) i

/-- Bind replay to the requested full query and claimed value, not just a table digest. -/
def planeCheckCanonicalClaim (bound : ℕ) (values : ℕ → Fin 3 → ℚ)
    (query : SurfaceQuery .plane) (claimed : ℚ) : Bool :=
  decide (∃ d : Fin (bound + 1), ∃ j : Fin 3,
    query = planeCanonicalQueries d.val j ∧ values d.val j = claimed) &&
      planeCheckCanonicalTable bound values

/-- An accepted claim names precisely the certified canonical query and value. -/
theorem planeCheckCanonicalClaim_sound (bound : ℕ) (values : ℕ → Fin 3 → ℚ)
    (query : SurfaceQuery .plane) (claimed : ℚ)
    (hcheck : planeCheckCanonicalClaim bound values query claimed = true) :
    ∃ d, d ≤ bound ∧ ∃ j,
      query = planeCanonicalQueries d j ∧ planeCanonicalValues d j = claimed := by
  rw [planeCheckCanonicalClaim, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨d, j, hquery, hvalue⟩ := hcheck.1
  have hd : d.val ≤ bound := Nat.le_of_lt_succ d.isLt
  refine ⟨d.val, hd, j, hquery, ?_⟩
  rw [← planeCheckCanonicalTable_sound bound values hcheck.2 d.val hd]
  exact hvalue

end AxiomaticGW.BelorousskiPandharipande

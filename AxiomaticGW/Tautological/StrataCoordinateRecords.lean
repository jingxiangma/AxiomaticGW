/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.StrataOperationReplay

/-!
# Finite coefficient records for efficient coordinate replay

Check a short list of destination/coefficient pairs once, then accumulate
that literal list. This avoids recomputing a source table at every output
coordinate. Equality of the records is required, including zero coefficients
and repeated destinations; the semantic graph coverage remains unchanged.
-/

@[expose] public section

namespace AxiomaticGW.StrataOperation
open RelationCertificate

/-- Retain every source coefficient and its proposed image, in source order. -/
def imageRecords {m n : ℕ} (destination : Fin m → Fin n) (q : Coordinates m) :
    List (Fin n × ℚ) := List.ofFn fun i ↦ (destination i, q i)

/-- Add all record coefficients, retaining collisions and cancellations. -/
def recordCoordinates {n : ℕ} (data : List (Fin n × ℚ)) : Coordinates n :=
  fun i ↦ ((data.filter fun t ↦ decide (t.1 = i)).map Prod.snd).sum

/-- Filtering a coordinate avoids adding zeros but preserves the full linear sum. -/
theorem recordCoordinates_eq_sum {n : ℕ} (data : List (Fin n × ℚ)) :
    recordCoordinates data = (data.map fun t ↦ Pi.single t.1 t.2).sum := by
  funext i
  induction data with
  | nil => rfl
  | cons t data ih =>
    unfold recordCoordinates at ih ⊢
    by_cases ht : t.1 = i
    · simp only [List.filter_cons, ht, decide_true, ↓reduceIte, List.map_cons,
        List.sum_cons, Pi.add_apply, Pi.single_eq_same, ih]
    · simp only [List.filter_cons, ht, decide_false, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.sum_cons, Pi.add_apply, Pi.single_eq_of_ne (Ne.symm ht),
        zero_add, ih]

/-- The efficient list representation is exactly the original finite linear image. -/
theorem imageCoordinates_eq_records {m n : ℕ}
    (destination : Fin m → Fin n) (q : Coordinates m) :
    imageCoordinates destination q = recordCoordinates (imageRecords destination q) := by
  simp only [imageCoordinates, recordCoordinates_eq_sum, imageRecords, List.map_ofFn,
    List.sum_ofFn, Function.comp_def]

end AxiomaticGW.StrataOperation

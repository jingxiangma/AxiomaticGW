/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupBoundedCertificate

/-!
# Ordered scalar replay of the original blowup reconstruction rows

The own H/P/N/K coefficient has already been proved symbolically. Every other
surviving column is strictly earlier. Masking the canonical candidate outside
this strict order makes the existing zero-value guard skip expensive own and
later coefficient computations. No coefficient or full class is discarded
without the actual complete-row support theorem.

The replay is also bound to the producer's exact earlier nonzero full-query
columns, including coefficients which themselves are zero. Its row and table
checks are equivalent to the bounded scalar certificate; no new acceptance
assumption, value formula or numerical suite is introduced.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwoBlowupOrderedCertificate
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
variable {X : SurfaceTarget}
set_option maxRecDepth 20000

local instance earlierDecidable : DecidableRel (Earlier X) :=
  fun s t ↦ decidable_of_iff _ (earlier_iff X s t).symm

/-- Closed coefficient of the exact own column in each unchanged selected equation. -/
def pivot (s : State X) : ℚ :=
  match s.2 with
  | .hyperplane => -1
  | .point => -18 * (X.planeDegree s.1 : ℚ)
  | .primary => 6 * (X.planeDegree s.1 : ℚ)
  | .exceptional _ => -18

private theorem energy_pos (s : State X) (hd : 0 < X.planeDegree s.1) :
    0 < X.effective.energy s.1 := by
  apply Nat.pos_of_ne_zero
  intro h
  have hz := (X.effective.energy_eq_zero_iff s.1).mp h
  rw [hz, map_zero] at hd
  omega

/-- The closed pivot is the actual full normalized singleton coefficient. -/
theorem pivot_eq (i : Fin X.blowups) (s : State X) (hd : 0 < X.planeDegree s.1) :
    pivot s = RationalTerms.coefficient (SurfaceGenusTwoBlowupRecursion.row i s)
      {.inr (s.2.query s.1)} := by
  obtain ⟨beta, family⟩ := s
  have hb := energy_pos (beta, family) hd
  cases family with
  | hyperplane =>
    exact (SurfaceGenusTwoBlowupHContributions.row_coefficient_eq_neg_one X i beta hb).symm
  | point => exact (SurfaceGenusTwoBlowupPCoefficients.point_coefficient beta hb).symm
  | primary => exact (SurfaceGenusTwoBlowupNCoefficients.row_primary_coefficient i beta).symm
  | exceptional j =>
    exact (SurfaceGenusTwoBlowupKCoefficients.exceptional_coefficient_self j beta hb).symm

/-- Every row used by reconstruction has a nonzero closed own pivot. -/
theorem pivot_ne_zero (s : State X) (hd : 0 < X.planeDegree s.1) : pivot s ≠ 0 := by
  obtain ⟨beta, family⟩ := s
  have hdc : (X.planeDegree beta : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  cases family <;> simp only [pivot]
  · norm_num
  · exact mul_ne_zero (by norm_num) hdc
  · exact mul_ne_zero (by norm_num) hdc
  · norm_num

/-- Only strictly earlier candidate values are supplied to expensive coefficient replay. -/
def earlierCandidate (s : State X) (candidate : State X → ℚ) (t : State X) : ℚ :=
  if Earlier X t s then candidate t else 0

/-- Exact own-column lookup is zero under the strict-order mask. -/
theorem earlierCandidate_own_zero (s : State X) (candidate : State X → ℚ) :
    earlierCandidate s candidate s = 0 := by
  have hn : ¬ Earlier X s s := by rw [earlier_iff]; omega
  exact if_neg hn

/-- Actual full-row support permits the strict-order mask once the own pivot is isolated. -/
theorem eval_row_masked (i : Fin X.blowups) (s : State X) (candidate : State X → ℚ)
    (hd : 0 < X.planeDegree s.1) :
    RationalTerms.eval (canonicalValuation candidate) (SurfaceGenusTwoBlowupRecursion.row i s) =
      pivot s * candidate s + RationalTerms.eval
        (canonicalValuation (earlierCandidate s candidate))
        (SurfaceGenusTwoBlowupRecursion.row i s) := by
  let own : Variable X := .inr (s.2.query s.1)
  let rest := (RationalTerms.collect (SurfaceGenusTwoBlowupRecursion.row i s)).filter
    (fun t ↦ t.2 ≠ {own})
  have he : RationalTerms.eval (canonicalValuation candidate) rest =
      RationalTerms.eval (canonicalValuation (earlierCandidate s candidate)) rest := by
    apply RationalTerms.eval_congr
    intro t ht v hv
    obtain ⟨ht, hn⟩ := Multiset.mem_filter.mp ht
    have hv' : v ∈ SurfaceGenusTwoBlowupCertificate.rowVariables i s :=
      Multiset.mem_toFinset.mpr (Multiset.mem_bind.mpr ⟨t, ht, hv⟩)
    rcases SurfaceGenusTwoBlowupBoundedCertificate.rowVariables_support i s hd v hv' with
      hown | ⟨u, hu, hq, _⟩
    · rcases SurfaceGenusTwoBlowupScalar.collected_row_affine i s ht with hz | ⟨w, hm⟩
      · exact (Multiset.notMem_zero v (hz ▸ hv)).elim
      · rw [hm, Multiset.mem_singleton] at hv
        exact (hn (hm.trans (congrArg (fun x : Variable X ↦ ({x} : Multiset _))
          (hv.symm.trans hown)))).elim
    · rw [hq, canonicalValuation_query, canonicalValuation_query]
      exact (if_pos hu).symm
  have hown : canonicalValuation (earlierCandidate s candidate) own = 0 := by
    dsimp only [own]
    rw [canonicalValuation_query, earlierCandidate_own_zero]
  have hm : RationalTerms.eval (canonicalValuation (earlierCandidate s candidate))
      (SurfaceGenusTwoBlowupRecursion.row i s) =
      RationalTerms.eval (canonicalValuation (earlierCandidate s candidate)) rest := by
    rw [← RationalTerms.eval_collect, RationalTerms.eval_isolate_singleton _ _ own]
    rw [hown, mul_zero, zero_add]
  calc
    RationalTerms.eval (canonicalValuation candidate)
        (SurfaceGenusTwoBlowupRecursion.row i s) =
        pivot s * candidate s + RationalTerms.eval (canonicalValuation candidate) rest := by
      rw [← RationalTerms.eval_collect, RationalTerms.eval_isolate_singleton _ _ own,
        RationalTerms.coefficient_collect, Algebra.algebraMap_self_apply,
        ← pivot_eq i s hd, canonicalValuation_query]
    _ = pivot s * candidate s + RationalTerms.eval
        (canonicalValuation (earlierCandidate s candidate)) rest := by rw [he]
    _ = pivot s * candidate s + RationalTerms.eval
        (canonicalValuation (earlierCandidate s candidate))
        (SurfaceGenusTwoBlowupRecursion.row i s) := by rw [hm]

/-- Exact predecessor list used by the native producer, including all nonzero earlier values. -/
def earlierStates (B : ℕ) (s : State X) (candidate : State X → ℚ) : List (State X) :=
  (SurfaceGenusTwoBlowupBoundedCertificate.states X B).filter
    (fun t ↦ decide (Earlier X t s ∧ candidate t ≠ 0))

/-- Membership retains the complete state and requires strict order and a nonzero candidate. -/
theorem mem_earlierStates (B : ℕ) (s t : State X) (candidate : State X → ℚ) :
    t ∈ earlierStates B s candidate ↔
      t ∈ SurfaceGenusTwoBlowupBoundedCertificate.states X B ∧
        Earlier X t s ∧ candidate t ≠ 0 := by
  simp only [earlierStates, List.mem_filter, decide_eq_true_eq]

private theorem earlier_columns_subset (B : ℕ) (s : State X) (candidate : State X → ℚ) :
    SurfaceGenusTwoBlowupScalar.columns (earlierStates B s candidate) ⊆
      SurfaceGenusTwoBlowupScalar.columns (SurfaceGenusTwoBlowupBoundedCertificate.states X B) := by
  intro v hv
  obtain ⟨t, ht, hq⟩ := (SurfaceGenusTwoBlowupScalar.mem_columns _ v).mp hv
  exact (SurfaceGenusTwoBlowupScalar.mem_columns _ v).mpr
    ⟨t, ((mem_earlierStates B s t candidate).mp ht).1, hq⟩

private theorem masked_value_zero_of_not_mem_columns (B : ℕ) (s : State X)
    (candidate : State X → ℚ) (v : Variable X)
    (hv : v ∈ SurfaceGenusTwoBlowupScalar.columns
      (SurfaceGenusTwoBlowupBoundedCertificate.states X B))
    (hn : v ∉ SurfaceGenusTwoBlowupScalar.columns (earlierStates B s candidate)) :
    canonicalValuation (earlierCandidate s candidate) v = 0 := by
  obtain ⟨t, ht, hq⟩ := (SurfaceGenusTwoBlowupScalar.mem_columns _ v).mp hv
  rw [hq, canonicalValuation_query]
  unfold earlierCandidate
  by_cases he : Earlier X t s
  · rw [if_pos he]
    by_contra hc
    apply hn
    exact (SurfaceGenusTwoBlowupScalar.mem_columns _ v).mpr
      ⟨t, (mem_earlierStates B s t candidate).mpr ⟨ht, he, hc⟩, hq⟩
  · exact if_neg he

/-- The guarded masked replay is exactly the sum over earlier nonzero full-query columns.
Coefficients equal to zero remain honest entries of this sum. -/
theorem masked_replay_eq_earlier_sum (i : Fin X.blowups) (B : ℕ) (s : State X)
    (candidate : State X → ℚ) :
    SurfaceGenusTwoBlowupScalar.replay i s (canonicalValuation (earlierCandidate s candidate))
      (SurfaceGenusTwoBlowupBoundedCertificate.states X B) =
      SurfaceGenusTwoBlowupScalar.constant i s +
        ∑ v ∈ SurfaceGenusTwoBlowupScalar.columns (earlierStates B s candidate),
          SurfaceGenusTwoBlowupScalar.singletonCoefficient i s v *
            canonicalValuation candidate v := by
  unfold SurfaceGenusTwoBlowupScalar.replay
  congr 1
  calc
    _ = ∑ v ∈ SurfaceGenusTwoBlowupScalar.columns (earlierStates B s candidate),
        if canonicalValuation (earlierCandidate s candidate) v = 0 then 0 else
          SurfaceGenusTwoBlowupScalar.singletonCoefficient i s v *
            canonicalValuation (earlierCandidate s candidate) v := by
      apply (Finset.sum_subset (earlier_columns_subset B s candidate) ?_).symm
      intro v hv hn
      rw [if_pos (masked_value_zero_of_not_mem_columns B s candidate v hv hn)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      obtain ⟨t, ht, hq⟩ := (SurfaceGenusTwoBlowupScalar.mem_columns _ v).mp hv
      have ht' := (mem_earlierStates B s t candidate).mp ht
      rw [hq, canonicalValuation_query, canonicalValuation_query]
      simp only [earlierCandidate, if_pos ht'.2.1, if_neg ht'.2.2]

/-- Closed own pivot plus guarded earlier replay skips all own/later coefficient computations. -/
def replay (i : Fin X.blowups) (B : ℕ) (candidate : State X → ℚ) (s : State X) : ℚ :=
  pivot s * candidate s + SurfaceGenusTwoBlowupScalar.replay i s
    (canonicalValuation (earlierCandidate s candidate))
    (SurfaceGenusTwoBlowupBoundedCertificate.states X B)

/-- Exact equation shape emitted by the native scalar producer. -/
theorem replay_eq_explicit (i : Fin X.blowups) (B : ℕ) (candidate : State X → ℚ)
    (s : State X) : replay i B candidate s =
      SurfaceGenusTwoBlowupScalar.constant i s + pivot s * candidate s +
        ∑ v ∈ SurfaceGenusTwoBlowupScalar.columns (earlierStates B s candidate),
          SurfaceGenusTwoBlowupScalar.singletonCoefficient i s v *
            canonicalValuation candidate v := by
  rw [replay, masked_replay_eq_earlier_sum]
  ring

/-- Ordered replay is the same complete equation as the existing bounded scalar replay. -/
theorem replay_eq_bounded (i : Fin X.blowups) (B : ℕ) (candidate : State X → ℚ)
    (s : State X) (hs : s ∈ SurfaceGenusTwoBlowupBoundedCertificate.states X B)
    (hd : 0 < X.planeDegree s.1) :
    replay i B candidate s = SurfaceGenusTwoBlowupScalar.replay i s
      (canonicalValuation candidate) (SurfaceGenusTwoBlowupBoundedCertificate.states X B) := by
  rw [replay, SurfaceGenusTwoBlowupBoundedCertificate.replay_eq_row i B s _ hs hd,
    SurfaceGenusTwoBlowupBoundedCertificate.replay_eq_row i B s _ hs hd]
  exact (eval_row_masked i s candidate hd).symm

/-- Preserve the original boundary guard; positive-plane checks use only ordered replay. -/
def checkRow (i : Fin X.blowups) (B : ℕ) (candidate : State X → ℚ) (s : State X) : Bool :=
  if X.planeDegree s.1 = 0 then
    decide (candidate s = SurfaceGenusTwoBlowupBoundary.value s.1 s.2)
  else decide (replay i B candidate s = 0)

/-- The faster row check is equivalent to the existing bounded check at every complete key. -/
theorem checkRow_eq (i : Fin X.blowups) (B : ℕ) (candidate : State X → ℚ)
    (s : State X) (hs : s ∈ SurfaceGenusTwoBlowupBoundedCertificate.states X B) :
    checkRow i B candidate s =
      SurfaceGenusTwoBlowupBoundedCertificate.checkRow i B candidate s := by
  by_cases hd : X.planeDegree s.1 = 0
  · rw [checkRow, SurfaceGenusTwoBlowupBoundedCertificate.checkRow, if_pos hd, if_pos hd]
  · rw [checkRow, SurfaceGenusTwoBlowupBoundedCertificate.checkRow, if_neg hd, if_neg hd,
      replay_eq_bounded i B candidate s hs (Nat.pos_of_ne_zero hd)]

/-- Check every bounded state using the exact ordered scalar equations. -/
def checkTable (i : Fin X.blowups) (B : ℕ) (candidate : State X → ℚ) : Bool :=
  (SurfaceGenusTwoBlowupBoundedCertificate.states X B).all (checkRow i B candidate)

/-- Ordered table acceptance is exactly bounded scalar acceptance. -/
theorem checkTable_eq (i : Fin X.blowups) (B : ℕ) (candidate : State X → ℚ) :
    checkTable i B candidate =
      SurfaceGenusTwoBlowupBoundedCertificate.checkTable i B candidate := by
  apply Bool.eq_iff_iff.mpr
  simp only [checkTable, SurfaceGenusTwoBlowupBoundedCertificate.checkTable, List.all_eq_true]
  constructor <;> intro h s hs
  · rw [← checkRow_eq i B candidate s hs]
    exact h s hs
  · rw [checkRow_eq i B candidate s hs]
    exact h s hs

/-- Accepted ordered rows equal the original well-founded reconstruction,
without new assumptions. -/
theorem checkTable_sound (i : Fin X.blowups) (B : ℕ) (candidate : State X → ℚ)
    (hc : checkTable i B candidate = true) (s : State X) (hs : X.effective.energy s.1 ≤ B) :
    candidate s = SurfaceGenusTwoBlowupRecursion.values i s := by
  rw [checkTable_eq] at hc
  exact SurfaceGenusTwoBlowupBoundedCertificate.checkTable_sound i B candidate hc s hs

end AxiomaticGW.SurfaceGenusTwoBlowupOrderedCertificate

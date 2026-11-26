/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Coefficients.RationalTerms

/-!
# Membership in executable rational term operations

These rules expose actual uncollected terms for dependency proofs. Scaling
by zero removes its entire input, while multiplication retains each pair of
monomials, including zero coefficients already present in the factors.
-/

@[expose] public section

namespace AxiomaticGW.RationalTerms
variable {σ : Type*}

theorem mem_term {c : ℚ} {m : Multiset σ} {t : ℚ × Multiset σ} :
    t ∈ term c m ↔ c ≠ 0 ∧ t = (c, m) := by
  unfold term
  split_ifs with hc
  · simp only [hc, ne_eq, not_true_eq_false, false_and, Multiset.notMem_zero]
  · simp only [hc, ne_eq, not_false_eq_true, true_and, Multiset.mem_singleton]

theorem mem_scale {c : ℚ} {p : RationalTerms σ} {t : ℚ × Multiset σ} :
    t ∈ scale c p ↔ c ≠ 0 ∧ ∃ s ∈ p, t = (c * s.1, s.2) := by
  unfold scale
  split_ifs with hc
  · simp only [hc, ne_eq, not_true_eq_false, false_and, Multiset.notMem_zero]
  · simp only [hc, ne_eq, not_false_eq_true, true_and, Multiset.mem_map, eq_comm]

theorem mem_mul {p q : RationalTerms σ} {t : ℚ × Multiset σ} :
    t ∈ mul p q ↔ ∃ s ∈ p, ∃ u ∈ q, t = (s.1 * u.1, s.2 + u.2) := by
  simp only [mul, Multiset.mem_bind, Multiset.mem_map, eq_comm]

end AxiomaticGW.RationalTerms

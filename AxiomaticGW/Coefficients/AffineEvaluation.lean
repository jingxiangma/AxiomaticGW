/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Coefficients.CollectedTerms

/-!
# Scalar evaluation from finite affine support

Once every monomial is constant or a singleton in a known finite set, the
constant and singleton coefficients evaluate the complete polynomial. This
allows certificates to reuse independently checked scalar computations.
-/

@[expose] public section

namespace AxiomaticGW.RationalTerms
variable {σ : Type*} [DecidableEq σ]

/-- A finite affine support permits exact scalar evaluation, including the constant. -/
theorem eval_eq_constant_add_sum (v : σ → ℚ) (p : RationalTerms σ) (s : Finset σ)
    (hp : ∀ t ∈ p, t.2 = 0 ∨ ∃ x ∈ s, t.2 = {x}) :
    eval v p = eval (fun _ ↦ (0 : ℚ)) p + ∑ x ∈ s, coefficient p {x} * v x := by
  let rest := p.filter (fun t ↦ ∀ x ∈ s, t.2 ≠ {x})
  have he : eval v rest = eval (fun _ ↦ (0 : ℚ)) rest := by
    apply eval_congr
    intro t ht x hx
    obtain ⟨ht, hrest⟩ := Multiset.mem_filter.mp ht
    rcases hp t ht with hz | ⟨y, hy, hm⟩
    · exact (Multiset.notMem_zero x (hz ▸ hx)).elim
    · exact (hrest y hy hm).elim
  have hz := eval_isolate_finset (fun _ ↦ (0 : ℚ)) p s
  simp only [mul_zero, Finset.sum_const_zero, zero_add] at hz
  rw [eval_isolate_finset v p s]
  change (∑ x ∈ s, coefficient p {x} * v x) + eval v rest = _
  rw [he, ← hz, add_comm]

end AxiomaticGW.RationalTerms

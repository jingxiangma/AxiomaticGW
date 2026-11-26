/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Coefficients.AffineSubstitution

/-!
# Coefficients after renaming variables

Renaming preserves addition, scalar multiplication and individual terms.
No injectivity assumption is needed: any coincident renamed monomials are
still collected by the existing coefficient function.
-/

@[expose] public section

namespace AxiomaticGW.RationalTerms
variable {σ τ : Type*}

theorem rename_zero (f : σ → τ) : rename f 0 = 0 := rfl

theorem rename_add (f : σ → τ) (p q : RationalTerms σ) :
    rename f (p + q) = rename f p + rename f q := Multiset.map_add _ _ _

theorem rename_scale (f : σ → τ) (c : ℚ) (p : RationalTerms σ) :
    rename f (scale c p) = scale c (rename f p) := by
  unfold scale
  by_cases hc : c = 0
  · simp only [if_pos hc, rename_zero]
  · simp only [if_neg hc, rename, Multiset.map_map, Function.comp_def]

theorem rename_term (f : σ → τ) (c : ℚ) (m : Multiset σ) :
    rename f (term c m) = term c (m.map f) := by
  unfold term
  by_cases hc : c = 0
  · simp only [if_pos hc, rename_zero]
  · simp only [if_neg hc, rename, Multiset.map_singleton]

variable [DecidableEq τ]

theorem coefficient_rename_add (f : σ → τ) (p q : RationalTerms σ) (m : Multiset τ) :
    coefficient (rename f (p + q)) m =
      coefficient (rename f p) m + coefficient (rename f q) m := by
  rw [rename_add, coefficient_add]

theorem coefficient_rename_scale (f : σ → τ) (c : ℚ) (p : RationalTerms σ)
    (m : Multiset τ) :
    coefficient (rename f (scale c p)) m = c * coefficient (rename f p) m := by
  rw [rename_scale, coefficient_scale]

theorem coefficient_rename_term (f : σ → τ) (c : ℚ) (m : Multiset σ) (n : Multiset τ) :
    coefficient (rename f (term c m)) n = if m.map f = n then c else 0 := by
  rw [rename_term, coefficient_term]

end AxiomaticGW.RationalTerms

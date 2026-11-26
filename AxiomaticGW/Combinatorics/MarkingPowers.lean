/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Multiset.Filter

/-! # Identifying finite marking sets with repeated cotangent powers -/

@[expose] public section
namespace AxiomaticGW

/-- A relabeling preserving each exponent exists whenever the two multisets of powers agree. -/
theorem markingEquiv_of_powers {S T : Type*} [Fintype S] [Fintype T] (d : S → ℕ) (k : T → ℕ)
    (h : Finset.univ.val.map d = Finset.univ.val.map k) : ∃ e : S ≃ T, ∀ s, k (e s) = d s := by
  classical
  have hc (a : ℕ) : Fintype.card {s // d s = a} = Fintype.card {t // k t = a} := by
    have hh := congrArg (Multiset.count a) h
    simpa only [Fintype.card_subtype, Finset.card, Finset.filter_val, Multiset.count_map,
      eq_comm (a := a)] using hh
  let e (a : ℕ) := Fintype.equivOfCardEq (hc a)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

end AxiomaticGW

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Coefficients.RationalTerms

/-!
# Substitution in affine rational certificate equations

The surface genus-two equations have already proved affine support. This
module substitutes finite expressions into their variables, preserving
constant terms. Its soundness theorem requires the support proof; it does
not silently treat nonlinear monomials as affine.
-/

@[expose] public section

namespace AxiomaticGW.RationalTerms
variable {σ τ : Type*} {A : Type*} [CommRing A] [Algebra ℚ A]

/-- Change variable labels without changing coefficients or multiplicities. -/
def rename (f : σ → τ) (p : RationalTerms σ) : RationalTerms τ :=
  p.map (fun t ↦ (t.1, t.2.map f))

theorem eval_rename (v : τ → A) (f : σ → τ) (p : RationalTerms σ) :
    eval v (rename f p) = eval (v ∘ f) p := by
  simp only [rename, eval, Multiset.map_map, Function.comp_def]

/-- Evaluation distributes across a finite multiset of term expansions. -/
theorem eval_bind {ι : Type*} (v : σ → A) (s : Multiset ι) (f : ι → RationalTerms σ) :
    eval v (s.bind f) = (s.map (fun i ↦ eval v (f i))).sum := by
  simp only [eval, Multiset.map_bind, Multiset.sum_bind]

/-- Substitute variables in a polynomial whose support is proved affine.
The support hypothesis is explicit in `eval_affineSubstitute`. -/
def affineSubstitute (f : σ → RationalTerms τ) (p : RationalTerms σ) : RationalTerms τ :=
  p.bind (fun t ↦ if t.2.card = 0 then term t.1 0 else scale t.1 (t.2.bind f))

/-- Every affine substitution agrees with evaluation in any commutative
rational algebra. The input constant is retained exactly. -/
theorem eval_affineSubstitute (v : τ → A) (w : σ → A)
    (f : σ → RationalTerms τ) (hf : ∀ x, eval v (f x) = w x)
    (p : RationalTerms σ) (hp : ∀ t ∈ p, t.2.card ≤ 1) :
    eval v (affineSubstitute f p) = eval w p := by
  rw [affineSubstitute, eval_bind, eval]
  congr 1
  apply Multiset.map_congr rfl
  intro t ht
  by_cases hz : t.2.card = 0
  · have hm : t.2 = 0 := Multiset.card_eq_zero.mp hz
    simp only [hm, Multiset.card_zero, ite_true, eval_term,
      Multiset.map_zero, Multiset.prod_zero]
  · have hc : t.2.card = 1 := by have := hp t ht; omega
    obtain ⟨x, hm⟩ := Multiset.card_eq_one.mp hc
    simp only [hm, Multiset.card_singleton, one_ne_zero, if_false, Multiset.singleton_bind,
      eval_scale, hf, Multiset.map_singleton, Multiset.prod_singleton]

/-- A checked compact input can replace the expanded affine equation before
substitution. Both affine-support obligations are retained. -/
theorem eval_affineSubstitute_eq_of_equivalent [DecidableEq σ] (v : τ → A)
    (f : σ → RationalTerms τ) (p q : RationalTerms σ) (heq : Equivalent p q)
    (hp : ∀ t ∈ p, t.2.card ≤ 1) (hq : ∀ t ∈ q, t.2.card ≤ 1) :
    eval v (affineSubstitute f p) = eval v (affineSubstitute f q) := by
  rw [eval_affineSubstitute v (fun x ↦ eval v (f x)) f (fun _ ↦ rfl) p hp,
    eval_affineSubstitute v (fun x ↦ eval v (f x)) f (fun _ ↦ rfl) q hq]
  exact eval_eq_of_equivalent _ p q heq

end AxiomaticGW.RationalTerms

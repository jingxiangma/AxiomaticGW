/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoPulledSquare

/-! # Certifying zero scalar contractions by individual vertex factors

A vertex predicate may recognize any proven zeros and leave other factors
unevaluated. A separating edge asks for a zero partner at every effective
splitting and paired node label. A loop checks each of its paired labels.
-/

@[expose] public section
namespace AxiomaticGW.GluingExpression
variable {X : SurfaceTarget}

/-- The Boolean test covers each assignment of effective classes and contraction labels. -/
def zeroSupport (z : SurfaceCotangentVertexValues X Bool) :
    {g : ℕ} → {S : Type} → [Fintype S] → (x : GluingExpression g S) →
      x.CotangentDecoration → x.DecidableLabels → X.Curve → (S → SurfaceBasisLabel X) → Bool
  | _, _, _, @fundamental g S _ h, d, l, beta, a => z g S h d l beta a
  | _, _, _, @relabel _ _ _ _ _ e x, d, l, beta, a =>
    zeroSupport z x d l beta (a ∘ e)
  | _, _, _, @separating _ _ _ _ _ _ x y, d, l, beta, a =>
    decide (∀ c : ↥(Fintype.piFinset (fun i ↦ Finset.range (beta i + 1))),
      ∀ b : SurfaceBasisLabel X,
        zeroSupport z y d.2 l.2 (beta - c.1) (Option.elim · b.dual (a ∘ Sum.inr)) = true ∨
        zeroSupport z x d.1 l.1 c.1 (Option.elim · b (a ∘ Sum.inl)) = true)
  | _, _, _, @nonseparating _ _ _ x, d, l, beta, a =>
    decide (∀ b : SurfaceBasisLabel X,
      zeroSupport z x d l beta (Option.elim · b (fun t ↦ Option.elim t b.dual a)) = true)

/-- Only the implication from recognized zero to actual vertex vanishing is required. -/
theorem zeroPointContraction_of_support
    (z : SurfaceCotangentVertexValues X Bool) (v : SurfaceCotangentVertexValues X ℚ)
    (sound : ∀ g S [Fintype S] h d l beta a, z g S h d l beta a = true → v g S h d l beta a = 0)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (d : x.CotangentDecoration)
    (l : x.DecidableLabels) (beta : X.Curve) (a : S → SurfaceBasisLabel X) :
    zeroSupport z x d l beta a = true → zeroPointContraction X v x d l beta a = 0 := by
  induction x generalizing beta with
  | fundamental => exact sound _ _ _ _ _ _ _
  | relabel e x ih => exact ih _ _ _ _
  | separating x y ihx ihy =>
    intro h
    rw [zeroSupport] at h
    have h := of_decide_eq_true h
    rw [zeroPointContraction, SurfaceTarget.sumSubcurves_eq]
    apply Finset.sum_eq_zero
    intro c hc
    apply Finset.sum_eq_zero
    intro b _
    rcases h ⟨c, hc⟩ b with hy | hx
    · simp only [ihy _ _ _ _ hy, if_true, mul_zero]
    · rw [ihx _ _ _ _ hx]
      simp only [zero_mul, ite_self, mul_zero]
  | nonseparating x ih =>
    intro h
    rw [zeroSupport] at h
    have h := of_decide_eq_true h
    rw [zeroPointContraction]
    apply Finset.sum_eq_zero
    intro b _
    rw [ih _ _ _ _ (h b), mul_zero]

end AxiomaticGW.GluingExpression

namespace AxiomaticGW.SurfaceGenusTwo
open GluingExpression
variable {X : SurfaceTarget}

/-- Test the vertex factors of a single decorated graph after assigning its external powers. -/
def externalZero (z : SurfaceCotangentVertexValues X Bool)
    {g : ℕ} {S : Type} [Fintype S] (t : CotangentTerm g S) (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) : Bool :=
  zeroSupport z t.expression (t.expression.withExternalPowers t.decoration k) t.labels beta a

/-- A finite multiset passes precisely when every occurrence passes its Boolean test. -/
def allRecognized {α : Type*} (m : Multiset α) (f : α → Bool) : Bool :=
  (m.map (fun t : α ↦ if f t then 0 else (1 : ℕ))).sum == 0

private theorem sum_eq_zero_of_recognized {α : Type*} (m : Multiset α)
    (f : α → Bool) (v : α → ℚ) (hv : ∀ t, f t = true → v t = 0)
    (h : allRecognized m f = true) : (m.map v).sum = 0 := by
  have hz : (m.map (fun t : α ↦ if f t then 0 else (1 : ℕ))).sum = 0 := eq_of_beq h
  apply Multiset.sum_eq_zero
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hx
  apply hv
  have h₀ := Multiset.sum_eq_zero_iff.mp hz _ (Multiset.mem_map_of_mem _ ht)
  cases e : f t <;> simp only [e, Bool.false_eq_true, if_false, one_ne_zero] at h₀ ⊢

/-- Every decorated summand of the indicated source has zero support. -/
def pulledSquareZero (z : SurfaceCotangentVertexValues X Bool) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 1) → ℕ) (a : ExtraMarkings n (Fin 1) → SurfaceBasisLabel X) :
    Fin 11 → Bool := Fin.cases
  (allRecognized (fundamentalCorrections GenusTwoPsiSquare.stableArity (fun _ : Fin 1 ↦ 2) n)
    (fun t ↦ externalZero z t.2 beta k a))
  (fun i ↦ allRecognized ((GenusTwoPsiSquare.boundaryCotangentTerm i).addMarkings n)
    (fun t ↦ externalZero z t.2 beta k a))

theorem pulledSquarePart_eq_zero_of_support
    (z : SurfaceCotangentVertexValues X Bool) (v : SurfaceVertexValues X ℚ)
    (hs : ∀ g S [Fintype S] h d l beta a, z g S h d l beta a = true → v g S h beta d a = 0)
    (n : ℕ) (beta : X.Curve) (k : ExtraMarkings n (Fin 1) → ℕ)
    (a : ExtraMarkings n (Fin 1) → SurfaceBasisLabel X) (i : Fin 11) :
    pulledSquareZero z n beta k a i = true → pulledSquarePart v n beta k a i = 0 := by
  have he (t : CotangentTerm 2 (ExtraMarkings n (Fin 1))) :
      externalZero z t beta k a = true → externalScalar X v t beta k a = 0 :=
    zeroPointContraction_of_support z (fun g S _ h d _ b x ↦ v g S h b d x) hs _ _ _ _ _
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp only [pulledSquareZero, pulledSquarePart, Fin.cases_zero]
    apply sum_eq_zero_of_recognized
    intro t h
    rw [he t.2 h, mul_zero]
  · simp only [pulledSquareZero, pulledSquarePart, Fin.cases_succ]
    apply sum_eq_zero_of_recognized
    intro t h
    rw [he t.2 h, mul_zero]

end AxiomaticGW.SurfaceGenusTwo

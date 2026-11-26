/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Contraction
public import AxiomaticGW.Tautological.GetzlerForgetful

/-!
# Finite surface evaluation of gluing expressions

Every edge is expanded in the actual surface inverse metric, and every
separating vertex keeps all ordered full-class splittings. Terminal component
values are supplied explicitly: the operation is executable when they are,
and can also be used over polynomial rings for relation exploration.

With the actual GW ancestor invariants as terminal values, the evaluation
equals the previously proved contraction. Thus the checked Getzler exchange
gives this explicit finite equation without any new geometric law or assumed
numerical recurrence. Solving the equation and proving recursive decrease
remain separate obligations.
-/

@[expose] public section

namespace AxiomaticGW

/-- Values only at the fundamental components of a gluing expression.
This is an argument to finite evaluation, not a reconstruction oracle. -/
abbrev SurfaceVertexValues (X : SurfaceTarget) (A : Type*) :=
  ∀ (g : ℕ) (S : Type) [Fintype S], StableArity g S → X.Curve →
    (S → ℕ) → (S → SurfaceBasisLabel X) → A

namespace GluingExpression

/-- Explicit signed inverse-metric and full-class evaluation. -/
def surfaceEval {A : Type*} [CommRing A] [Algebra ℚ A]
    (X : SurfaceTarget) (vertex : SurfaceVertexValues X A)
    {g : ℕ} {S : Type} [Fintype S] :
    GluingExpression g S → X.Curve → (S → ℕ) → (S → SurfaceBasisLabel X) → A
  | @fundamental g S _ h, beta, k, a => vertex g S h beta k a
  | @relabel _ _ _ _ _ e x, beta, k, a => x.surfaceEval X vertex beta (k ∘ e) (a ∘ e)
  | @separating _ _ _ _ _ _ x y, beta, k, a =>
      ∑ split ∈ X.splittings beta, ∑ b : SurfaceBasisLabel X,
        algebraMap ℚ A b.inverseWeight *
          (x.surfaceEval X vertex split.1 (PsiClasses.separatingLeftPowers k)
            (Option.elim · b (a ∘ Sum.inl)) *
           y.surfaceEval X vertex split.2 (PsiClasses.separatingRightPowers k)
            (Option.elim · b.dual (a ∘ Sum.inr)))
  | @nonseparating _ _ _ x, beta, k, a =>
      ∑ b : SurfaceBasisLabel X, algebraMap ℚ A b.inverseWeight *
        x.surfaceEval X vertex beta (PsiClasses.nonseparatingPowers k)
          (Option.elim · b (fun t ↦ Option.elim t b.dual a))

/-- Polynomial substitution commutes with every finite graph operation. -/
theorem surfaceEval_map {A B : Type*} [CommRing A] [Algebra ℚ A]
    [CommRing B] [Algebra ℚ B] (f : A →ₐ[ℚ] B)
    (X : SurfaceTarget) (vertex : SurfaceVertexValues X A)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    f (x.surfaceEval X vertex beta k a) =
      x.surfaceEval X (fun g S _ h beta k a ↦ f (vertex g S h beta k a)) beta k a := by
  induction x generalizing beta with
  | fundamental g S h => rfl
  | relabel e x ih => exact ih beta (k ∘ e) (a ∘ e)
  | separating x y ihx ihy =>
    simp only [surfaceEval, map_sum, map_mul, f.commutes, ihx, ihy]
  | nonseparating x ih =>
    simp only [surfaceEval, map_sum, map_mul, f.commutes, ih]

end GluingExpression

namespace GromovWittenTheory

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}

/-- The terminal values are the supplied theory's actual ancestor invariants. -/
def surfaceVertexValues
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C) (I : StableCurveIntegration C) : SurfaceVertexValues X ℚ :=
  fun g S _ h beta k a ↦ Omega.ancestorInvariant P I g S h beta k (fun s ↦ (a s).value)

end GromovWittenTheory

namespace GluingExpression

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}

/-- The executable edge expansion equals the existing geometric contraction.
Only identification of the supplied pairing with the surface pairing is needed. -/
theorem surfaceEval_eq_gwAncestorContraction
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C) (I : StableCurveIntegration C)
    (hp : Omega.pairing = (SurfaceCohomology.frobenius X.blowups).pairing)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    x.surfaceEval X (Omega.surfaceVertexValues P I) beta k a =
      x.gwAncestorContraction Omega P I beta k (fun s ↦ (a s).value) := by
  induction x generalizing beta with
  | fundamental g S h => rfl
  | relabel e x ih =>
    exact ih beta (k ∘ e) (a ∘ e)
  | separating x y ihx ihy =>
    simp only [surfaceEval, gwAncestorContraction, sum_apply, hp,
      SurfaceCohomology.pairContract_eq_sum, X.splittings_eq, Algebra.algebraMap_self_apply]
    apply Finset.sum_congr rfl
    intro split _
    apply Finset.sum_congr rfl
    intro b _
    rw [ihx, ihy]
    congr 2 <;> congr 1 <;> funext s <;> cases s <;> rfl
  | nonseparating x ih =>
    simp only [surfaceEval, gwAncestorContraction, hp,
      SurfaceCohomology.selfContract_eq_sum, MultilinearMap.domDomCongr_apply,
      Algebra.algebraMap_self_apply]
    apply Finset.sum_congr rfl
    intro b _
    rw [ih]
    congr 2
    funext s
    rcases s with _ | (_ | s) <;> rfl

end GluingExpression

namespace GetzlerGraphs

/-- Finite surface channel with all ordered placements and node states. -/
def surfaceChannel {A : Type*} [CommRing A] [Algebra ℚ A]
    (X : SurfaceTarget) (vertex : SurfaceVertexValues X A)
    (n : ℕ) (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) (i : Fin 33) : A :=
  (((expression i).addMarkings n).map fun z ↦ z.surfaceEval X vertex beta k a).sum

/-- The exact requested Getzler combination in the explicit surface evaluator. -/
def surfaceEquation {A : Type*} [CommRing A] [Algebra ℚ A]
    (X : SurfaceTarget) (vertex : SurfaceVertexValues X A)
    (n : ℕ) (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) : A :=
  ∑ i, algebraMap ℚ A (requested i) * surfaceChannel X vertex n beta k a i

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}

theorem surfaceChannel_eq_gwAncestorChannelWithMarkings
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C) (I : StableCurveIntegration C)
    (hp : Omega.pairing = (SurfaceCohomology.frobenius X.blowups).pairing)
    (n : ℕ) (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) (i : Fin 33) :
    surfaceChannel X (Omega.surfaceVertexValues P I) n beta k a i =
      gwAncestorChannelWithMarkings Omega P I n beta k (fun s ↦ (a s).value) i := by
  unfold surfaceChannel gwAncestorChannelWithMarkings
  simp only [GluingExpression.surfaceEval_eq_gwAncestorContraction Omega P I hp]

/-- Actual claim-bound replay implies the explicit finite surface equation. -/
theorem exchange_surfaceEquation_eq_zero
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (expression i).Compatible A F N)
    (G : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (A 1 (Fin 4)).map (cycle x) = G.cycle x)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C)
    (hp : Omega.pairing = (SurfaceCohomology.frobenius X.blowups).pairing)
    (n : ℕ)
    (houtput : ∀ i z, z ∈ (expression i).addMarkings n → z.Compatible A F N)
    (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (p : RelationCertificate.Presentation 1 (Fin 4) 1 33) (haccept : AcceptsExchange p) :
    surfaceEquation X (Omega.surfaceVertexValues P I) n beta k a = 0 := by
  unfold surfaceEquation
  simp only [surfaceChannel_eq_gwAncestorChannelWithMarkings Omega P I hp]
  exact exchange_ancestor_with_markings_eq_zero A F N H hsource G hcycle Omega P n
    houtput beta k (fun s ↦ (a s).value) p haccept

end GetzlerGraphs

end AxiomaticGW

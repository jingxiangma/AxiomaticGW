/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.DecoratedGluing
public import AxiomaticGW.Tautological.GluingForgetful
public import AxiomaticGW.Tautological.LegPsiRealization

/-!
# Realizing component cotangent decorations

The original cotangent powers are evaluated before raw gluing. Primitive
single-psi and graph-map compatibility identify this evaluation with the
existing decorated stratum. No numerical reconstruction law is assumed.
-/

@[expose] public section

namespace AxiomaticGW.GluingExpression

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

attribute [local instance] strataRealizationModule

/-- Primitive single-psi realization is required only on original components. -/
def CotangentCompatible (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (P : PsiClasses C) {g : ℕ} {S : Type} [Fintype S] : GluingExpression g S → Prop
  | @fundamental g S _ h => (A g S).LegPsiCompatible P h
  | @relabel _ _ _ _ _ _ x => x.CotangentCompatible A P
  | @separating _ _ _ _ _ _ x y => x.CotangentCompatible A P ∧ y.CotangentCompatible A P
  | @nonseparating _ _ _ x => x.CotangentCompatible A P

/-- Evaluate component monomials through the original raw gluing construction. -/
noncomputable def decoratedClassValue (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C)
    {g : ℕ} {S : Type} [Fintype S] :
    (x : GluingExpression g S) → x.CotangentDecoration → C.H g S
  | @fundamental g S _ h, d => P.monomial g S h d
  | @relabel g S T _ _ e x, d =>
      C.rename g S T x.stable (x.relabel e).stable e (x.decoratedClassValue F N P d)
  | @separating g₁ g₂ S T _ _ x y, d =>
      F.push g₁ g₂ S T x.stable y.stable
        (x.decoratedClassValue F N P d.1 ⊗ₜ[R] y.decoratedClassValue F N P d.2)
  | @nonseparating g S _ x, d =>
      N.push g S x.nonseparating.stable (x.decoratedClassValue F N P d)

/-- Existing primitive compatibility identifies the actual decorated class. -/
theorem map_decoratedStratum_eq_classValue
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (d : x.CotangentDecoration)
    (hx : x.Compatible A F N) (hp : x.CotangentCompatible A P) :
    (A g S).map (StrataModule.basis (x.decoratedStratum d)) =
      x.decoratedClassValue F N P d := by
  induction x with
  | fundamental g S h =>
    rw [decoratedStratum_fundamental, (A g S).map_addLegPsi P h hp, hx, one_mul]
    rfl
  | relabel e x ih =>
    rw [decoratedStratum_relabel, hx.2, ih d hx.1 hp]
    rfl
  | separating x y ihx ihy =>
    rw [decoratedStratum_separating, hx.2.2, ihx d.1 hx.1 hp.1, ihy d.2 hx.2.1 hp.2]
    rfl
  | nonseparating x ih =>
    rw [decoratedStratum_nonseparating, hx.2, ih d hx.1 hp]
    rfl

/-- Zero powers recover the existing undecorated evaluation. -/
theorem decoratedClassValue_zero (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) :
    x.decoratedClassValue F N P x.zeroDecoration = x.classValue F N := by
  induction x with
  | fundamental g S h => exact P.monomial_zero g S h
  | relabel e x ih => simp only [decoratedClassValue, zeroDecoration, classValue, ih]
  | separating x y ihx ihy =>
    simp only [decoratedClassValue, zeroDecoration, classValue, ihx, ihy]
  | nonseparating x ih => simp only [decoratedClassValue, zeroDecoration, classValue, ih]

end AxiomaticGW.GluingExpression

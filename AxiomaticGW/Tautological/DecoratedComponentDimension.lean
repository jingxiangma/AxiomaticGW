/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.DecoratedGluingRealization
public import AxiomaticGW.CohFT.PsiGluing

/-!
# Component dimension vanishing for decorated gluings

The free strata module retains monomials that admcycles removes by a local
component dimension bound. Their omission must therefore be justified in
cohomology, rather than treated as a formal graph identity. The executable
test below transports external powers to the original components, including
all existing node powers. Projection formula and the degree bound prove its
soundness; no extra vanishing relation is assumed.
-/

@[expose] public section

namespace AxiomaticGW.GluingExpression

/-- Some original component has more cotangent degree than its dimension. -/
def exceedsComponentDimension {g : ℕ} {S : Type} [Fintype S] :
    (x : GluingExpression g S) → x.CotangentDecoration → (S → ℕ) → Bool
  | @fundamental g S _ _, d, k => decide (StableArity.dimension g S < (∑ s, (k s + d s)))
  | @relabel _ _ _ _ _ e x, d, k => x.exceedsComponentDimension d (k ∘ e)
  | @separating _ _ _ _ _ _ x y, d, k =>
      x.exceedsComponentDimension d.1 (PsiClasses.separatingLeftPowers k) ||
        y.exceedsComponentDimension d.2 (PsiClasses.separatingRightPowers k)
  | @nonseparating _ _ _ x, d, k =>
      x.exceedsComponentDimension d (PsiClasses.nonseparatingPowers k)

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- A component dimension excess annihilates the actual decorated pushforward. -/
theorem monomial_mul_classValue_eq_zero_of_component_dimension
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (d : x.CotangentDecoration) (k : S → ℕ)
    (hd : x.exceedsComponentDimension d k = true) :
    P.monomial g S x.stable k * x.decoratedClassValue F N P d = 0 := by
  induction x with
  | fundamental g S h =>
    change P.monomial g S h k * P.monomial g S h d = 0
    rw [← P.monomial_add]
    exact C.eq_zero_of_dimension_lt g S h _ _ (P.monomial_degree g S h (k + d))
      (of_decide_eq_true hd)
  | @relabel g S T _ _ e x ih =>
    change P.monomial g T _ k * C.rename g S T _ _ e (x.decoratedClassValue F N P d) = 0
    rw [← P.rename_monomial_comp g S T x.stable (x.relabel e).stable e k,
      ← map_mul, ih d (k ∘ e) hd, map_zero]
  | @separating g₁ g₂ S T _ _ x y ihx ihy =>
    change P.monomial (g₁ + g₂) (S ⊕ T) _ k * F.push g₁ g₂ S T _ _
      (x.decoratedClassValue F N P d.1 ⊗ₜ[R] y.decoratedClassValue F N P d.2) = 0
    rw [← F.projection_formula, P.separating_monomial, Algebra.TensorProduct.tmul_mul_tmul]
    have hor : x.exceedsComponentDimension d.1 (PsiClasses.separatingLeftPowers k) = true ∨
        y.exceedsComponentDimension d.2 (PsiClasses.separatingRightPowers k) = true := by
      simpa only [exceedsComponentDimension, Bool.or_eq_true_iff] using hd
    rcases hor with hx | hy
    · rw [ihx d.1 (PsiClasses.separatingLeftPowers k) hx, TensorProduct.zero_tmul, map_zero]
    · rw [ihy d.2 (PsiClasses.separatingRightPowers k) hy, TensorProduct.tmul_zero, map_zero]
  | @nonseparating g S _ x ih =>
    change P.monomial (g + 1) S _ k * N.push g S _ (x.decoratedClassValue F N P d) = 0
    rw [← N.projection_formula, P.nonseparating_monomial,
      ih d (PsiClasses.nonseparatingPowers k) hd, map_zero]

/-- The actual graph with added external psi powers realizes to zero when a component does. -/
theorem map_addLegPsi_eq_zero_of_component_dimension
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (d : x.CotangentDecoration) (k : S → ℕ)
    (hx : x.Compatible A F N) (hp : x.CotangentCompatible A P)
    (ht : (A g S).LegPsiCompatible P x.stable)
    (hd : x.exceedsComponentDimension d k = true) :
    (A g S).map (StrataModule.basis ((x.decoratedStratum d).addLegPsi k)) = 0 := by
  rw [StrataRealization.map_addLegPsi _ P _ ht,
    x.map_decoratedStratum_eq_classValue A F N P d hx hp, mul_comm]
  exact x.monomial_mul_classValue_eq_zero_of_component_dimension F N P d k hd

end AxiomaticGW.GluingExpression

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.DecoratedGluingRealization
public import AxiomaticGW.Tautological.GluingAncestors

/-!
# Contraction of cotangent-decorated raw gluing expressions

Original component powers remain at their flags when these flags become node
branches. External ancestor powers are pulled back by the existing cotangent
laws and added to those original powers at each leaf. Full curve splittings
and inverse-metric contractions are unchanged. Soundness uses primitive
cotangent realization only on terminal components and the existing raw gluing
compatibility; no numerical recurrence is assumed.
-/

@[expose] public section

namespace AxiomaticGW.GluingExpression

universe u

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

attribute [local instance] strataRealizationModule

/-- Integrate a realized raw graph together with arbitrary external ancestor powers. -/
noncomputable def gwDecoratedAncestorIntegral
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (I : StableCurveIntegration C) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (d : x.CotangentDecoration) (beta : B) (k : S → ℕ) :
    MultilinearMap R (fun _ : S ↦ V) R :=
  ((I.integrate g S x.stable).comp (LinearMap.mulRight R
    (P.monomial g S x.stable k * (A g S).map (StrataModule.basis (x.decoratedStratum d)))))
    |>.compMultilinearMap (Omega.omega g S x.stable beta)

/-- Exact recursive contraction; original branch powers are added at terminal components. -/
noncomputable def gwDecoratedAncestorContraction (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (I : StableCurveIntegration C)
    {g : ℕ} {S : Type} [Fintype S] :
    (x : GluingExpression g S) → x.CotangentDecoration → B → (S → ℕ) →
      MultilinearMap R (fun _ : S ↦ V) R
  | @fundamental g S _ h, d, beta, k => Omega.ancestorInvariant P I g S h beta (k + d)
  | @relabel _ _ _ _ _ e x, d, beta, k =>
      (x.gwDecoratedAncestorContraction Omega P I d beta (k ∘ e)).domDomCongr e
  | @separating _ _ _ _ _ _ x y, d, beta, k =>
      ∑ split ∈ D.splittings beta, Omega.pairing.pairContract
        (x.gwDecoratedAncestorContraction Omega P I d.1 split.1 (PsiClasses.separatingLeftPowers k))
        (y.gwDecoratedAncestorContraction Omega P I d.2 split.2
          (PsiClasses.separatingRightPowers k))
  | @nonseparating _ S _ x, d, beta, k =>
      Omega.pairing.selfContract
        ((x.gwDecoratedAncestorContraction Omega P I d beta
          (PsiClasses.nonseparatingPowers k)).domDomCongr
          (doubleOptionEquiv S))

/-- The integral form agrees with pairing the external ancestor insertion
against the existing graph basis element. -/
theorem gwDecoratedAncestorIntegral_apply
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (I : StableCurveIntegration C) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (d : x.CotangentDecoration) (beta : B) (k : S → ℕ) (a : S → V) :
    x.gwDecoratedAncestorIntegral A Omega P I d beta k a =
      (A g S).integrateAgainst I x.stable
        (P.monomial g S x.stable k * Omega.omega g S x.stable beta a)
        (StrataModule.basis (x.decoratedStratum d)) := by
  change I.integrate g S x.stable (_ * (_ * _)) =
    I.integrate g S x.stable ((_ * _) * _)
  rw [mul_left_comm, ← mul_assoc]

/-- Decorated contraction soundness follows from primitive cotangent realization,
cotangent pullbacks and the existing raw geometric gluing compatibility. -/
theorem gwDecoratedAncestorIntegral_eq_contraction
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (d : x.CotangentDecoration)
    (hx : x.Compatible A F N) (hp : x.CotangentCompatible A P) (beta : B) (k : S → ℕ) :
    x.gwDecoratedAncestorIntegral A Omega P I d beta k =
      x.gwDecoratedAncestorContraction Omega P I d beta k := by
  induction x generalizing beta with
  | fundamental g S h =>
    ext a
    change I.integrate g S h (Omega.omega g S h beta a *
      (P.monomial g S h k * (A g S).map
        (StrataModule.basis ((fundamental g S h).decoratedStratum d)))) = _
    rw [decoratedStratum_fundamental, (A g S).map_addLegPsi P h hp,
      hx, one_mul, ← P.monomial_add]
    rfl
  | @relabel g S T _ _ e x ih =>
    ext a
    change I.integrate g T _ (Omega.omega g T _ beta a *
      (P.monomial g T _ k * (A g T).map
        (StrataModule.basis ((x.relabel e).decoratedStratum d)))) = _
    rw [decoratedStratum_relabel, hx.2 (x.decoratedStratum d)]
    have ho := congrArg (fun f ↦ f a) (Omega.relabel g S T x.stable (x.relabel e).stable e beta)
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.domDomCongr_apply,
      AlgEquiv.toLinearMap_apply] at ho
    rw [← ho, ← P.rename_monomial_comp g S T x.stable (x.relabel e).stable e k,
      ← map_mul, ← map_mul, I.integrate_rename]
    exact congrArg (fun f ↦ f (a ∘ e)) (ih d hx.1 hp beta (k ∘ e))
  | @separating g₁ g₂ S T _ _ x y ihx ihy =>
    have heq : (x.separating y).gwDecoratedAncestorIntegral A Omega P I d beta k =
        Omega.separatingInvariant F g₁ g₂ S T x.stable y.stable beta
          ((P.monomial g₁ (Option S) x.stable (PsiClasses.separatingLeftPowers k) *
            (A g₁ (Option S)).map (StrataModule.basis (x.decoratedStratum d.1))) ⊗ₜ[R]
           (P.monomial g₂ (Option T) y.stable (PsiClasses.separatingRightPowers k) *
            (A g₂ (Option T)).map (StrataModule.basis (y.decoratedStratum d.2)))) := by
      ext a
      change I.integrate (g₁ + g₂) (S ⊕ T) _ (Omega.omega _ _ _ beta a *
        (P.monomial _ _ _ k * (A _ _).map
          (StrataModule.basis ((x.separating y).decoratedStratum d)))) = _
      rw [decoratedStratum_separating, hx.2.2 (x.decoratedStratum d.1) (y.decoratedStratum d.2),
        ← F.projection_formula,
        P.separating_monomial, Algebra.TensorProduct.tmul_mul_tmul]
      rfl
    rw [heq, Omega.separatingInvariant_tmul]
    change (∑ split ∈ D.splittings beta, Omega.pairing.pairContract
      (x.gwDecoratedAncestorIntegral A Omega P I d.1 split.1 (PsiClasses.separatingLeftPowers k))
      (y.gwDecoratedAncestorIntegral A Omega P I d.2 split.2
          (PsiClasses.separatingRightPowers k))) = _
    simp only [ihx d.1 hx.1 hp.1, ihy d.2 hx.2.1 hp.2, gwDecoratedAncestorContraction]
  | @nonseparating g S _ x ih =>
    have heq : x.nonseparating.gwDecoratedAncestorIntegral A Omega P I d beta k =
        Omega.nonseparatingInvariant N g S x.nonseparating.stable beta
          (P.monomial g (Option (Option S)) x.stable (PsiClasses.nonseparatingPowers k) *
            (A g (Option (Option S))).map (StrataModule.basis (x.decoratedStratum d))) := by
      ext a
      change I.integrate (g + 1) S _ (Omega.omega _ _ _ beta a *
        (P.monomial _ _ _ k * (A _ _).map
          (StrataModule.basis (x.nonseparating.decoratedStratum d)))) = _
      rw [decoratedStratum_nonseparating, hx.2 (x.decoratedStratum d), ← N.projection_formula,
        P.nonseparating_monomial]
      rfl
    rw [heq, Omega.nonseparatingInvariant_eq_selfContract,
      ← LinearMap.compMultilinearMap_domDomCongr]
    change Omega.pairing.selfContract
      ((x.gwDecoratedAncestorIntegral A Omega P I d beta
          (PsiClasses.nonseparatingPowers k)).domDomCongr
        (doubleOptionEquiv S)) = _
    rw [ih d hx.1 hp]
    rfl

end AxiomaticGW.GluingExpression

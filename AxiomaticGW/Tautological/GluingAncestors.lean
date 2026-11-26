/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GluingEvaluation
public import AxiomaticGW.CohFT.PsiGluing

/-!
# Ancestor evaluation of explicit gluing expressions

External cotangent powers restrict recursively to component markings. Every
new node receives zero exponent; existing powers follow their marking labels.
The terminal factors are the actual component GW ancestor invariants, with
every effective full-class splitting retained. Soundness uses the same raw
realization compatibility as primary evaluation and the existing PsiClasses
pullback laws. Stable-map descendants remain a separate comparison problem.
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
noncomputable def gwAncestorIntegral
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (I : StableCurveIntegration C) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (beta : B) (k : S → ℕ) :
    MultilinearMap R (fun _ : S ↦ V) R :=
  ((I.integrate g S x.stable).comp (LinearMap.mulRight R
    (P.monomial g S x.stable k * (A g S).map (StrataModule.basis x.stratum))))
    |>.compMultilinearMap (Omega.omega g S x.stable beta)

/-- Exact recursive contraction with powers transported by the actual labels. -/
noncomputable def gwAncestorContraction (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (I : StableCurveIntegration C)
    {g : ℕ} {S : Type} [Fintype S] :
    GluingExpression g S → B → (S → ℕ) → MultilinearMap R (fun _ : S ↦ V) R
  | @fundamental g S _ h, beta, k => Omega.ancestorInvariant P I g S h beta k
  | @relabel _ _ _ _ _ e x, beta, k =>
      (x.gwAncestorContraction Omega P I beta (k ∘ e)).domDomCongr e
  | @separating _ _ _ _ _ _ x y, beta, k =>
      ∑ split ∈ D.splittings beta, Omega.pairing.pairContract
        (x.gwAncestorContraction Omega P I split.1 (PsiClasses.separatingLeftPowers k))
        (y.gwAncestorContraction Omega P I split.2 (PsiClasses.separatingRightPowers k))
  | @nonseparating _ S _ x, beta, k =>
      Omega.pairing.selfContract
        ((x.gwAncestorContraction Omega P I beta (PsiClasses.nonseparatingPowers k)).domDomCongr
          (doubleOptionEquiv S))

/-- The integral form agrees with pairing the external ancestor insertion
against the existing graph basis element. -/
theorem gwAncestorIntegral_apply
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (I : StableCurveIntegration C) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (beta : B) (k : S → ℕ) (a : S → V) :
    x.gwAncestorIntegral A Omega P I beta k a =
      (A g S).integrateAgainst I x.stable
        (P.monomial g S x.stable k * Omega.omega g S x.stable beta a)
        (StrataModule.basis x.stratum) := by
  change I.integrate g S x.stable (_ * (_ * _)) =
    I.integrate g S x.stable ((_ * _) * _)
  rw [mul_left_comm, ← mul_assoc]

/-- Ancestor contraction soundness follows from primitive cotangent pullbacks
and the same geometric realization compatibility as the primary theorem. -/
theorem gwAncestorIntegral_eq_contraction
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (hx : x.Compatible A F N) (beta : B) (k : S → ℕ) :
    x.gwAncestorIntegral A Omega P I beta k = x.gwAncestorContraction Omega P I beta k := by
  induction x generalizing beta with
  | fundamental g S h =>
    ext a
    change I.integrate g S h (Omega.omega g S h beta a *
      (P.monomial g S h k * (A g S).map
        (StrataModule.basis (TautologicalStratum.fundamental g S h)))) = _
    rw [hx, mul_one]
    rfl
  | @relabel g S T _ _ e x ih =>
    ext a
    change I.integrate g T _ (Omega.omega g T _ beta a *
      (P.monomial g T _ k * (A g T).map
        (StrataModule.basis (x.relabel e).stratum))) = _
    rw [stratum_relabel, hx.2 x.stratum]
    have ho := congrArg (fun f ↦ f a) (Omega.relabel g S T x.stable (x.relabel e).stable e beta)
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.domDomCongr_apply,
      AlgEquiv.toLinearMap_apply] at ho
    rw [← ho, ← P.rename_monomial_comp g S T x.stable (x.relabel e).stable e k,
      ← map_mul, ← map_mul, I.integrate_rename]
    exact congrArg (fun f ↦ f (a ∘ e)) (ih hx.1 beta (k ∘ e))
  | @separating g₁ g₂ S T _ _ x y ihx ihy =>
    have heq : (x.separating y).gwAncestorIntegral A Omega P I beta k =
        Omega.separatingInvariant F g₁ g₂ S T x.stable y.stable beta
          ((P.monomial g₁ (Option S) x.stable (PsiClasses.separatingLeftPowers k) *
            (A g₁ (Option S)).map (StrataModule.basis x.stratum)) ⊗ₜ[R]
           (P.monomial g₂ (Option T) y.stable (PsiClasses.separatingRightPowers k) *
            (A g₂ (Option T)).map (StrataModule.basis y.stratum))) := by
      ext a
      change I.integrate (g₁ + g₂) (S ⊕ T) _ (Omega.omega _ _ _ beta a *
        (P.monomial _ _ _ k * (A _ _).map
          (StrataModule.basis (x.separating y).stratum))) = _
      rw [stratum_separating, hx.2.2 x.stratum y.stratum, ← F.projection_formula,
        P.separating_monomial, Algebra.TensorProduct.tmul_mul_tmul]
      rfl
    rw [heq, Omega.separatingInvariant_tmul]
    change (∑ split ∈ D.splittings beta, Omega.pairing.pairContract
      (x.gwAncestorIntegral A Omega P I split.1 (PsiClasses.separatingLeftPowers k))
      (y.gwAncestorIntegral A Omega P I split.2 (PsiClasses.separatingRightPowers k))) = _
    simp only [ihx hx.1, ihy hx.2.1, gwAncestorContraction]
  | @nonseparating g S _ x ih =>
    have heq : x.nonseparating.gwAncestorIntegral A Omega P I beta k =
        Omega.nonseparatingInvariant N g S x.nonseparating.stable beta
          (P.monomial g (Option (Option S)) x.stable (PsiClasses.nonseparatingPowers k) *
            (A g (Option (Option S))).map (StrataModule.basis x.stratum)) := by
      ext a
      change I.integrate (g + 1) S _ (Omega.omega _ _ _ beta a *
        (P.monomial _ _ _ k * (A _ _).map
          (StrataModule.basis x.nonseparating.stratum))) = _
      rw [stratum_nonseparating, hx.2 x.stratum, ← N.projection_formula,
        P.nonseparating_monomial]
      rfl
    rw [heq, Omega.nonseparatingInvariant_eq_selfContract,
      ← LinearMap.compMultilinearMap_domDomCongr]
    change Omega.pairing.selfContract
      ((x.gwAncestorIntegral A Omega P I beta (PsiClasses.nonseparatingPowers k)).domDomCongr
        (doubleOptionEquiv S)) = _
    rw [ih hx.1]
    rfl

/-- Zero ancestor powers recover the existing primary graph integral. -/
theorem gwAncestorIntegral_zero
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (I : StableCurveIntegration C) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (beta : B) :
    x.gwAncestorIntegral A Omega P I beta 0 = x.gwIntegral A Omega I beta := by
  ext a
  change I.integrate g S x.stable (Omega.omega g S x.stable beta a *
    (P.monomial g S x.stable (fun _ ↦ 0) *
      (A g S).map (StrataModule.basis x.stratum))) = _
  rw [P.monomial_zero, one_mul]
  rfl

/-- The new contraction is an extension of the primary formula, with no
change in node normalization or effective-class enumeration. -/
theorem gwAncestorContraction_zero (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (I : StableCurveIntegration C)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (beta : B) :
    x.gwAncestorContraction Omega P I beta 0 = x.gwContraction Omega I beta := by
  induction x generalizing beta with
  | fundamental g S h =>
    ext a
    change I.integrate g S h
      (Omega.omega g S h beta a * P.monomial g S h (fun _ ↦ 0)) = _
    rw [P.monomial_zero, mul_one]
    rfl
  | relabel e x ih =>
    change (x.gwAncestorContraction Omega P I beta 0).domDomCongr e = _
    rw [ih]
    rfl
  | separating x y ihx ihy =>
    simp only [gwAncestorContraction, PsiClasses.separatingLeftPowers_zero,
      PsiClasses.separatingRightPowers_zero, ihx, ihy, gwContraction]
  | nonseparating x ih =>
    simp only [gwAncestorContraction, PsiClasses.nonseparatingPowers_zero, ih, gwContraction]

end AxiomaticGW.GluingExpression

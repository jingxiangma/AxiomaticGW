/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GluingExpression
public import AxiomaticGW.Tautological.RelabelRealization
public import AxiomaticGW.Tautological.SeparatingRealization
public import AxiomaticGW.Tautological.NonseparatingRealization

/-!
# GW evaluation of explicit gluing expressions

Recursive evaluation contracts the actual component GW integrals with the
inverse metric. Separating nodes sum over every ordered splitting of the
full curve class; nonseparating nodes retain that class. The soundness proof
uses only fundamental normalization and the existing primitive graph-map,
Gysin, integration, and GW gluing laws.

Compatibility is checked only along the supplied expression. It contains no
GW family, no numerical equation, and no reconstruction assumption. In
particular it cannot certify geometric applicability of a supplied theory.
-/

@[expose] public section

namespace AxiomaticGW.GluingExpression

universe u

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

attribute [local instance] strataRealizationModule

/-- Exactly the primitive realization laws used by a particular expression. -/
def Compatible (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    {g : ℕ} {S : Type} [Fintype S] : GluingExpression g S → Prop
  | @fundamental g S _ h =>
      (A g S).map (StrataModule.basis (TautologicalStratum.fundamental g S h)) = 1
  | @relabel g S T _ _ e x =>
      Compatible A F N x ∧
        (A g S).RelabelCompatible (A g T) x.stable (x.relabel e).stable e
  | @separating g₁ g₂ S T _ _ x y =>
      Compatible A F N x ∧ Compatible A F N y ∧
        (A g₁ (Option S)).SeparatingCompatible (A g₂ (Option T))
          (A (g₁ + g₂) (S ⊕ T)) F x.stable y.stable
  | @nonseparating g S _ x =>
      Compatible A F N x ∧
        (A g (Option (Option S))).NonseparatingCompatible (A (g + 1) S) N
          x.nonseparating.stable

variable {V B : Type u} [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V] [AddCancelCommMonoid B]
  {D : EffectiveCurveMonoid B}

/-- Integral of the actual GW class against the realized raw graph. -/
noncomputable def gwIntegral (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (Omega : GromovWittenTheory R V B D C) (I : StableCurveIntegration C)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (beta : B) :
    MultilinearMap R (fun _ : S ↦ V) R :=
  ((I.integrate g S x.stable).comp
    (LinearMap.mulRight R ((A g S).map (StrataModule.basis x.stratum)))).compMultilinearMap
      (Omega.omega g S x.stable beta)

/-- Finite recursive contraction of component invariants. No realization or
geometric relation is an argument to this numerical expression. -/
noncomputable def gwContraction (Omega : GromovWittenTheory R V B D C)
    (I : StableCurveIntegration C) {g : ℕ} {S : Type} [Fintype S] :
    GluingExpression g S → B → MultilinearMap R (fun _ : S ↦ V) R
  | @fundamental g S _ h, beta =>
      (I.integrate g S h).compMultilinearMap (Omega.omega g S h beta)
  | @relabel _ _ _ _ _ e x, beta => (x.gwContraction Omega I beta).domDomCongr e
  | @separating _ _ _ _ _ _ x y, beta =>
      ∑ split ∈ D.splittings beta,
        Omega.pairing.pairContract
          (x.gwContraction Omega I split.1) (y.gwContraction Omega I split.2)
  | @nonseparating _ S _ x, beta =>
      Omega.pairing.selfContract
        ((x.gwContraction Omega I beta).domDomCongr (doubleOptionEquiv S))

/-- The primitive geometric laws derive the entire iterated contraction.
The equation is a conclusion, never a field of `Compatible`. -/
theorem gwIntegral_eq_contraction
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (Omega : GromovWittenTheory R V B D C)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (hx : x.Compatible A F N) (beta : B) :
    x.gwIntegral A Omega I beta = x.gwContraction Omega I beta := by
  induction x generalizing beta with
  | fundamental g S h =>
    ext a
    change I.integrate g S h
      (Omega.omega g S h beta a * (A g S).map
        (StrataModule.basis (TautologicalStratum.fundamental g S h))) = _
    rw [hx, mul_one]
    rfl
  | relabel e x ih =>
    ext a
    change (A _ _).integrateAgainst I _ (Omega.omega _ _ _ beta a)
      (StrataModule.basis (x.relabel e).stratum) = _
    rw [stratum_relabel, ← StrataModule.relabel_basis,
      StrataRealization.integrateAgainst_relabel_gw _ _ I _ _ e hx.2]
    exact congrArg (fun f ↦ f (a ∘ e)) (ih hx.1 beta)
  | @separating g₁ g₂ S T _ _ x y ihx ihy =>
    have heq : (x.separating y).gwIntegral A Omega I beta =
        Omega.separatingInvariant F g₁ g₂ S T x.stable y.stable beta
          ((A g₁ (Option S)).map (StrataModule.basis x.stratum) ⊗ₜ[R]
            (A g₂ (Option T)).map (StrataModule.basis y.stratum)) := by
      ext a
      change (A _ _).integrateAgainst I _ (Omega.omega _ _ _ beta a)
        (StrataModule.basis (x.separating y).stratum) = _
      rw [stratum_separating, ← StrataModule.separating_basis_basis,
        StrataRealization.integrateAgainst_separating_gw _ _ _ F _ _ hx.2.2]
    rw [heq, Omega.separatingInvariant_tmul]
    change (∑ split ∈ D.splittings beta, Omega.pairing.pairContract
      (x.gwIntegral A Omega I split.1) (y.gwIntegral A Omega I split.2)) = _
    simp only [ihx hx.1, ihy hx.2.1, gwContraction]
  | @nonseparating g S _ x ih =>
    have heq : x.nonseparating.gwIntegral A Omega I beta =
        Omega.nonseparatingInvariant N g S x.nonseparating.stable beta
          ((A g (Option (Option S))).map (StrataModule.basis x.stratum)) := by
      ext a
      change (A _ _).integrateAgainst I _ (Omega.omega _ _ _ beta a)
        (StrataModule.basis x.nonseparating.stratum) = _
      rw [stratum_nonseparating, ← StrataModule.nonseparating_basis,
        StrataRealization.integrateAgainst_nonseparating_gw _ _ N _ hx.2]
    rw [heq, Omega.nonseparatingInvariant_eq_selfContract,
      ← LinearMap.compMultilinearMap_domDomCongr]
    change Omega.pairing.selfContract
      ((x.gwIntegral A Omega I beta).domDomCongr (doubleOptionEquiv S)) = _
    rw [ih hx.1]
    rfl

end AxiomaticGW.GluingExpression

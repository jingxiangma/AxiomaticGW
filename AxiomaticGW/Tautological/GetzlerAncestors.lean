/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GetzlerGW
public import AxiomaticGW.Tautological.GluingAncestors

/-!
# The checked Getzler equation with external ancestor powers

The same held 33 columns, normalized coefficients, and incoming witness now
give an equation of actual component ancestor contractions. External powers
are arbitrary and move together with the state insertions. Node powers are
zero because the relation graphs are undecorated. No additional geometric
law is assumed beyond the existing PsiClasses and primary realization data.

This statement concerns stable-curve ancestors with four external markings.
Additional markings and the stable-map descendant comparison remain separate.
-/

@[expose] public section

namespace AxiomaticGW.GetzlerGraphs

universe u

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

attribute [local instance] strataRealizationModule

/-- The explicit iterated GW contraction with arbitrary external ancestor powers. -/
noncomputable def gwAncestorChannel (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (I : StableCurveIntegration C) (beta : B)
    (k : Fin 4 → ℕ) (a : Fin 4 → V) (i : Fin 33) : R :=
  (expression i).gwAncestorContraction Omega P I beta k a

/-- Primary channels and their raw coefficients are unchanged. -/
theorem gwAncestorChannel_zero (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (I : StableCurveIntegration C) (beta : B)
    (a : Fin 4 → V) (i : Fin 33) :
    gwAncestorChannel Omega P I beta 0 a i = gwChannel Omega I beta a i :=
  congrArg (fun f ↦ f a) ((expression i).gwAncestorContraction_zero Omega P I beta)

variable (A : ∀ g S, [Fintype S] → StrataRealization C g S)
  (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
  (hcompat : ∀ i, (expression i).Compatible A F N)

include hcompat

/-- Each raw graph integral with ancestor insertions is its actual component
contraction. This step does not use the geometric Getzler relation. -/
theorem integrate_column_ancestor (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (beta : B) (k : Fin 4 → ℕ) (a : Fin 4 → V) (i : Fin 33) :
    (A 1 (Fin 4)).integrateAgainst I stableArity
      (P.monomial 1 (Fin 4) stableArity k * Omega.omega 1 (Fin 4) stableArity beta a)
      (StrataModule.basis (columns i)) = gwAncestorChannel Omega P I beta k a i := by
  rw [← expression_stratum i, ← GluingExpression.gwAncestorIntegral_apply]
  exact congrArg (fun f ↦ f a)
    ((expression i).gwAncestorIntegral_eq_contraction A F N Omega P (hcompat i) beta k)

variable (G : GetzlerRelationGeometry C)
  (hcycle : ∀ x, (A 1 (Fin 4)).map (cycle x) = G.cycle x)

include G hcycle

/-- Exact replay gives the held equation of ancestor contractions, preserving
every marked column, full curve class, and normalization factor. -/
theorem certificate_ancestor_eq_zero (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (beta : B) (k : Fin 4 → ℕ) (a : Fin 4 → V)
    (c : RelationCertificate.Certificate 1)
    (hcheck : RelationCertificate.check rows requested c = true) :
    (∑ i, algebraMap ℚ R (requested i) * gwAncestorChannel Omega P I beta k a i) = 0 := by
  have h := ancestor_integral_sum_eq_zero (A 1 (Fin 4)) G hcycle Omega P I beta k a c hcheck
  simpa only [integrate_column_ancestor A F N hcompat Omega P beta k a] using h

/-- The actual incoming graph presentation and witness are bound to the same
held request before deriving its ancestor equation. -/
theorem exchange_ancestor_eq_zero (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (beta : B) (k : Fin 4 → ℕ) (a : Fin 4 → V)
    (p : RelationCertificate.Presentation 1 (Fin 4) 1 33) (hp : AcceptsExchange p) :
    (∑ i, algebraMap ℚ R (requested i) * gwAncestorChannel Omega P I beta k a i) = 0 :=
  certificate_ancestor_eq_zero A F N hcompat G hcycle Omega P beta k a p.certificate
    ((RelationCertificate.check_eq_true_iff _ _ _).mpr hp.2)

end AxiomaticGW.GetzlerGraphs

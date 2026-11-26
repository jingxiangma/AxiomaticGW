/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.WDVVRealization
public import AxiomaticGW.Tautological.GluingAncestors
public import AxiomaticGW.Tautological.GluingForgetful

/-!
# The checked WDVV equation with arbitrary additional markings

The original three boundary columns are explicit gluing expressions.
Primitive forgetful/gluing compatibility derives their pullbacks and all
marking placements. Equality of the original boundary classes, followed by
the unchanged two-row certificate, gives the ancestor equation upstairs.
No numerical recursion or descendant--ancestor comparison is assumed here.
-/

@[expose] public section

namespace AxiomaticGW.WDVV

/-- The existing labelled channel, as an explicit raw gluing construction. -/
def expression (i : Fin 3) : GluingExpression 0 (Fin 4) :=
  ((GluingExpression.fundamental 0 (Option (Fin 2)) StableArity.zero_option_fin_two).separating
    (.fundamental 0 (Option (Fin 2)) StableArity.zero_option_fin_two)).relabel (labels i)

/-- No new graph frame is introduced by the gluing construction. -/
theorem expression_stratum (i : Fin 3) : (expression i).stratum = columns i := rfl

/-- Every additional marking is assigned to either of the two components. -/
theorem sum_length_addMarkings (n : ℕ) :
    (∑ i : Fin 3, ((expression i).addMarkings n).length) = 3 * 2 ^ n := by
  simp only [GluingExpression.length_addMarkings]
  have hv (i : Fin 3) : (expression i).graph.graph.vertexCount = 2 := rfl
  simp only [hv, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat]

universe u

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

attribute [local instance] strataRealizationModule

/-- All component ancestors, full class splits and ordered marking placements. -/
noncomputable def gwAncestorChannelWithMarkings (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (I : StableCurveIntegration C) (n : ℕ) (beta : B)
    (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → V) (i : Fin 3) : R :=
  (((expression i).addMarkings n).map fun z ↦ z.gwAncestorContraction Omega P I beta k a).sum

variable (A : ∀ g S, [Fintype S] → StrataRealization C g S)
  (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
  (hsource : ∀ i, (expression i).Compatible A F N)

include hsource

/-- Primitive graph compatibility identifies the original geometric boundary class. -/
theorem map_column_of_compatible (i : Fin 3) :
    (A 0 (Fin 4)).map (StrataModule.basis (columns i)) = boundaryClass F i := by
  rw [← expression_stratum i, (expression i).map_stratum_eq_classValue A F N (hsource i)]
  rfl

/-- The existing geometric boundary equality annihilates each original row. -/
theorem map_relation_eq_zero_of_compatible (hboundary : BoundaryClassesEqual F) (row : Fin 2) :
    (A 0 (Fin 4)).map (relation row) = 0 := by
  have hcol : ∀ i, (A 0 (Fin 4)).map (StrataModule.basis (columns i)) = boundaryClass F 0 :=
    fun i ↦ (map_column_of_compatible A F N hsource i).trans (hboundary i)
  simp only [relation, RelationCertificate.interpret_apply, map_sum, map_smul, hcol]
  fin_cases row <;> norm_num [rows, Fin.sum_univ_three, Matrix.cons_val_two]

variable (H : GluingForgetfulCompatibility F N)

include H

/-- The pulled-back marked column evaluates as the complete ancestor convolution. -/
theorem integrate_column_with_markings (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (n : ℕ)
    (houtput : ∀ i z, z ∈ (expression i).addMarkings n → z.Compatible A F N)
    (beta : B) (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → V)
    (i : Fin 3) :
    (A 0 (Fin 4)).integrateForgetExtra I stableArity n
      (P.monomial 0 (ExtraMarkings n (Fin 4)) (stableArity.extraMarkings n) k *
        Omega.omega 0 (ExtraMarkings n (Fin 4)) (stableArity.extraMarkings n) beta a)
      (StrataModule.basis (columns i)) =
      gwAncestorChannelWithMarkings Omega P I n beta k a i := by
  rw [← expression_stratum i,
    (expression i).integrateForgetExtra_eq_sum A F N H n (hsource i) (houtput i)]
  unfold gwAncestorChannelWithMarkings
  congr 1
  apply List.map_congr_left
  intro z hz
  rw [← z.gwAncestorIntegral_apply A Omega P I beta k a]
  exact congrArg (fun f ↦ f a)
    (z.gwAncestorIntegral_eq_contraction A F N Omega P (houtput i z hz) beta k)

/-- The original two-row certificate remains sound after any number of markings. -/
theorem certificate_ancestor_with_markings_eq_zero (hboundary : BoundaryClassesEqual F)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C) (n : ℕ)
    (houtput : ∀ i z, z ∈ (expression i).addMarkings n → z.Compatible A F N)
    (beta : B) (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → V)
    (c : RelationCertificate.Certificate 2)
    (hcheck : RelationCertificate.check rows requested c = true) :
    (∑ i, algebraMap ℚ R (requested i) *
      gwAncestorChannelWithMarkings Omega P I n beta k a i) = 0 := by
  let w := P.monomial 0 (ExtraMarkings n (Fin 4)) (stableArity.extraMarkings n) k *
    Omega.omega 0 (ExtraMarkings n (Fin 4)) (stableArity.extraMarkings n) beta a
  have h : (A 0 (Fin 4)).integrateForgetExtra I stableArity n w
      (RelationCertificate.interpret columns requested) = 0 := by
    apply RelationCertificate.evaluation_eq_zero columns rows requested c hcheck
    intro row
    rw [StrataRealization.integrateForgetExtra_apply]
    change I.integrate 0 (ExtraMarkings n (Fin 4)) (stableArity.extraMarkings n)
      (w * C.forgetExtra 0 (Fin 4) stableArity n ((A 0 (Fin 4)).map (relation row))) = 0
    rw [map_relation_eq_zero_of_compatible A F N hsource hboundary row,
      map_zero, mul_zero, map_zero]
  rw [RelationCertificate.interpret_apply, map_sum] at h
  dsimp only [w] at h
  simpa only [map_smul, Algebra.smul_def,
    integrate_column_with_markings A F N hsource H Omega P n houtput beta k a] using h

/-- Incoming columns, rows, normalization, request and witness remain checked
against the independently held original WDVV frame. -/
theorem exchange_ancestor_with_markings_eq_zero (hboundary : BoundaryClassesEqual F)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C) (n : ℕ)
    (houtput : ∀ i z, z ∈ (expression i).addMarkings n → z.Compatible A F N)
    (beta : B) (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → V)
    (p : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hp : AcceptsExchange p) :
    (∑ i, algebraMap ℚ R (requested i) *
      gwAncestorChannelWithMarkings Omega P I n beta k a i) = 0 :=
  certificate_ancestor_with_markings_eq_zero A F N hsource H hboundary Omega P n houtput
    beta k a p.certificate ((RelationCertificate.check_eq_true_iff _ _ _).mpr hp.2)

end AxiomaticGW.WDVV

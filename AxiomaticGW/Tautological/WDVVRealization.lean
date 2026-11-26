/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.WDVV
public import AxiomaticGW.Tautological.RelabelRealization
public import AxiomaticGW.Tautological.SeparatingRealization

/-!
# From explicit four-point boundary certificates to GW equations

The geometric input is equality of the three raw boundary point classes in
`Mbar(0,4)`, as in Keel, Section 4, Theorem 1, Part I(2). It mentions neither
a CohFT nor its numerical recurrences. Raw graph-map composition, relabelling,
and fundamental normalization identify the fixed certificate columns with
those classes. Proper push-pull and the existing GW gluing axiom then give
the full-curve-class contraction equation, with the states transported by
the actual channel labels. Geometric class equality remains an explicit input.
-/

@[expose] public section

namespace AxiomaticGW.WDVV

open TensorProduct

universe u

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

attribute [local instance] strataRealizationModule

/-- The raw boundary point obtained from two normalized three-point components. -/
def boundaryClass (F : SeparatingPushforward C I) (i : Fin 3) : C.H 0 (Fin 4) :=
  C.rename 0 (Fin 2 ⊕ Fin 2) (Fin 4)
    (StableArity.separating StableArity.zero_option_fin_two
      StableArity.zero_option_fin_two) stableArity (labels i)
    (F.push 0 0 (Fin 2) (Fin 2) StableArity.zero_option_fin_two
      StableArity.zero_option_fin_two (1 ⊗ₜ[R] 1))

/-- Equality of boundary point classes on the full stable locus. This is a
named geometric relation, independent of the class family being evaluated. -/
def BoundaryClassesEqual (F : SeparatingPushforward C I) : Prop :=
  ∀ i, boundaryClass F i = boundaryClass F 0

variable (A : StrataRealization C 0 (Option (Fin 2)))
  (U : StrataRealization C 0 (Fin 2 ⊕ Fin 2))
  (W : StrataRealization C 0 (Fin 4)) (F : SeparatingPushforward C I)
  (hsep : A.SeparatingCompatible A U F
    StableArity.zero_option_fin_two StableArity.zero_option_fin_two)
  (hfund : A.map (StrataModule.basis (TautologicalStratum.fundamental
    0 (Option (Fin 2)) StableArity.zero_option_fin_two)) = 1)
  (hlabels : ∀ i, U.RelabelCompatible W
    (StableArity.separating StableArity.zero_option_fin_two
      StableArity.zero_option_fin_two) stableArity (labels i))

include hsep hfund hlabels

/-- The fixed formal columns realize to the raw geometric boundary classes. -/
theorem map_column (i : Fin 3) : W.map (StrataModule.basis (columns i)) =
    boundaryClass F i := by
  rw [columns_eq_relabel_separating, hlabels i, hsep, hfund]
  rfl

/-- Original row vanishing is derived from boundary-class equality, rather
than supplied as a hypothesis on the desired GW equation. -/
theorem map_relation_eq_zero (hboundary : BoundaryClassesEqual F) (row : Fin 2) :
    W.map (relation row) = 0 := by
  have hcol : ∀ j, W.map (StrataModule.basis (columns j)) = boundaryClass F 0 :=
    fun j ↦ (map_column A U W F hsep hfund hlabels j).trans (hboundary j)
  simp only [relation, RelationCertificate.interpret_apply, map_sum, map_smul, hcol]
  fin_cases row <;> norm_num [rows, Fin.sum_univ_three, Matrix.cons_val_two]

/-- A checked witness gives a zero integral against every held cohomology
insertion, using the independently fixed original geometric relation. -/
theorem certificate_integral_eq_zero (hboundary : BoundaryClassesEqual F)
    (w : C.H 0 (Fin 4)) (c : RelationCertificate.Certificate 2)
    (hcheck : RelationCertificate.check rows requested c = true) :
    W.integrateAgainst I stableArity w
      (RelationCertificate.interpret columns requested) = 0 := by
  apply RelationCertificate.evaluation_eq_zero columns rows requested c hcheck
  intro row
  rw [StrataRealization.integrateAgainst_apply]
  change I.integrate 0 (Fin 4) stableArity (w * W.map (relation row)) = 0
  rw [map_relation_eq_zero A U W F hsep hfund hlabels hboundary, mul_zero, map_zero]

variable {V B : Type u} [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V] [AddCancelCommMonoid B]
  {D : EffectiveCurveMonoid B}

/-- Primary component contraction for one marked channel, retaining every
ordered effective splitting of the full class, including zero factors. -/
noncomputable def gwChannel (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (I : StableCurveIntegration C)
    (beta : B) (a : Fin 4 → V) (i : Fin 3) : R :=
  ∑ split ∈ D.splittings beta,
    Omega.pairing.pairContract
      (Omega.ancestorInvariant P I 0 (Option (Fin 2))
        StableArity.zero_option_fin_two split.1 (fun _ ↦ 0))
      (Omega.ancestorInvariant P I 0 (Option (Fin 2))
        StableArity.zero_option_fin_two split.2 (fun _ ↦ 0)) (a ∘ labels i)

/-- Evaluation of the actual marked graph is the existing GW convolution;
this theorem needs no boundary-equality hypothesis. -/
theorem integrate_column_gw (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (beta : B) (a : Fin 4 → V) (i : Fin 3) :
    W.integrateAgainst I stableArity (Omega.omega 0 (Fin 4) stableArity beta a)
      (StrataModule.basis (columns i)) = gwChannel Omega P I beta a i := by
  rw [columns_eq_relabel_separating, ← StrataModule.relabel_basis,
    U.integrateAgainst_relabel_gw W I _ stableArity (labels i) (hlabels i)]
  rw [← StrataModule.separating_basis_basis,
    A.integrateAgainst_separating_gw A U F _ _ hsep, hfund]
  have heq := congrArg (fun f ↦ f (a ∘ labels i))
    (Omega.separatingInvariant_monomial P F 0 0 (Fin 2) (Fin 2)
      StableArity.zero_option_fin_two StableArity.zero_option_fin_two
      beta (fun _ ↦ 0) (fun _ ↦ 0))
  simpa only [gwChannel, PsiClasses.monomial_zero, sum_apply] using heq

/-- Exact certificate replay produces the marked full-class GW equation
from geometric boundary classes, primitive realization, and gluing laws. -/
theorem certificate_gw_eq_zero (hboundary : BoundaryClassesEqual F)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (beta : B) (a : Fin 4 → V) (c : RelationCertificate.Certificate 2)
    (hcheck : RelationCertificate.check rows requested c = true) :
    (∑ i, requested i • gwChannel Omega P I beta a i) = 0 := by
  have hz := certificate_integral_eq_zero A U W F hsep hfund hlabels hboundary
    (Omega.omega 0 (Fin 4) stableArity beta a) c hcheck
  simpa only [RelationCertificate.interpret_apply, map_sum, map_smul,
    integrate_column_gw A U W F hsep hfund hlabels Omega P beta a] using hz

/-- The fixed two-row witness equates the `01|23` and `03|12` primary
convolutions. Its proof uses the marked graph certificate, not an assumed recurrence. -/
theorem gw_channel_zero_eq_two (hboundary : BoundaryClassesEqual F)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (beta : B) (a : Fin 4 → V) :
    gwChannel Omega P I beta a 0 = gwChannel Omega P I beta a 2 := by
  have hz := certificate_gw_eq_zero A U W F hsep hfund hlabels hboundary
    Omega P beta a certificate check_requested
  have hr₀ : requested 0 = 1 := rfl
  have hr₁ : requested 1 = 0 := rfl
  have hr₂ : requested 2 = -1 := rfl
  rw [Fin.sum_univ_three, hr₀, hr₁, hr₂, one_smul, zero_smul, neg_one_smul, add_zero] at hz
  apply sub_eq_zero.mp
  simpa only [sub_eq_add_neg] using hz

/-- The exchange theorem holds only after the incoming graph columns,
factors, rows, request, and witness match the separately held fixed frame. -/
theorem exchange_gw_eq_zero (hboundary : BoundaryClassesEqual F)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (beta : B) (a : Fin 4 → V)
    (p : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hp : AcceptsExchange p) :
    (∑ i, requested i • gwChannel Omega P I beta a i) = 0 :=
  certificate_gw_eq_zero A U W F hsep hfund hlabels hboundary Omega P beta a p.certificate
    ((RelationCertificate.check_eq_true_iff rows requested p.certificate).mpr hp.2)

end AxiomaticGW.WDVV

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24Symmetry
public import AxiomaticGW.Tautological.BelorousskiPandharipandeForgetful
public import AxiomaticGW.Tautological.BelorousskiPandharipandeCoefficients
public import AxiomaticGW.Tautological.CotangentCombination

/-!
# The initial BP pullback in the L24 derivation

Retain all twenty BP diagrams and six marking assignments, pull back one
marking with the signed cotangent algorithm, and place the new marking first.
Multiply by (-psi_0 + 3 psi_1 + psi_2 + psi_3)/12 and average the three free
markings. The factor twelve accounts for the original six assignments and
the factor two in the published formula. This is the initial expression;
the high-psi, rational-psi and WDVV corrections are still required for L24.
-/

@[expose] public section

namespace AxiomaticGW.L24Initial
open BelorousskiPandharipande CotangentCombination RelationCertificate

/-- The existing full BP relation as executable signed decorated terms. -/
def bp : CotangentCombination 2 (Fin 3) :=
  Finset.univ.val.bind fun i : Fin 20 ↦ Finset.univ.val.map fun e : Fin 6 ↦
    (rawPaperCoefficient i, orbitCotangentTerm i e)

/-- The direct checked coefficient lookup preserves the original weighted expression.
It avoids traversing the large graph vector during native module initialization. -/
theorem bp_eq_original : bp =
    (Finset.univ.val.bind fun i : Fin 20 ↦ Finset.univ.val.map fun e : Fin 6 ↦
      (paperCoefficient i * paperNormalization i, orbitCotangentTerm i e)) := by
  simp only [bp, rawPaperCoefficient_eq]

/-- The executable terms have exactly the old BP normalization and marking sum. -/
theorem bp_strata : bp.strata = paperRelation := by
  simp only [bp_eq_original, strata, Multiset.map_bind, Multiset.sum_bind,
    Multiset.map_map, Function.comp_def]
  change (∑ i : Fin 20, ∑ e : Fin 6, (paperCoefficient i * paperNormalization i) •
    StrataModule.basis ((orbitCotangentTerm i e).expression.decoratedStratum
      (orbitCotangentTerm i e).decoration)) = paperRelation
  rw [paperRelation_as_terms]
  simp only [Finset.smul_sum, orbitCotangentTerm_stratum, orbitTerm_stratum]

/-- Put the new label first, followed by the three original BP markings. -/
def labels : ExtraMarkings 1 (Fin 3) ≃ Fin 4 :=
  (ExtraMarkings.finEquiv 1 3).trans
    ⟨![1, 2, 3, 0], ![3, 0, 1, 2], by decide +kernel, by decide +kernel⟩

/-- Actual signed pullback; both external and node cotangent corrections survive. -/
def pullback : CotangentCombination 2 (Fin 4) := (bp.pullback 1).relabel labels

/-- The linear cotangent factor from the published construction. -/
def psiWeights : Fin 4 → ℚ := ![-1, 3, 1, 1]

/-- The initial class expression, before its prescribed correction steps. -/
noncomputable def expression : StrataModule 2 (Fin 4) :=
  L24Symmetry.average ((1 / 12 : ℚ) • ∑ i : Fin 4,
    psiWeights i • StrataModule.mulLegPsi (Pi.single i 1) pullback.strata)

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- The initial class vanishes by the original BP equation and primitive geometry. -/
theorem expression_vanishes
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (K : PsiForgetFormula P) (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (H : PsiBoundaryExpansion.TailForgetCompatible C) (G : GluingForgetfulCompatibility F N)
    (hbp : (A 2 (Fin 3)).map paperRelation = 0)
    (hin : ∀ t ∈ bp, t.2.expression.Compatible A F N ∧
      t.2.expression.CotangentCompatible A P)
    (hout : ∀ t ∈ bp, ∀ z ∈ t.2.addMarkings 1,
      z.2.expression.Compatible A F N ∧ z.2.expression.CotangentCompatible A P)
    (hl : (A 2 (ExtraMarkings 1 (Fin 3))).RelabelCompatible (A 2 (Fin 4))
      (BelorousskiPandharipande.stableArity.extraMarkings 1) L24Symmetry.stableArity labels)
    (hp : (A 2 (Fin 4)).LegPsiCompatible P L24Symmetry.stableArity)
    (hs : ∀ p, (A 2 (Fin 4)).RelabelCompatible (A 2 (Fin 4))
      L24Symmetry.stableArity L24Symmetry.stableArity (L24Symmetry.labels p)) :
    (A 2 (Fin 4)).map expression = 0 := by
  have hb : (A 2 (Fin 3)).map bp.strata = 0 := by rw [bp_strata]; exact hbp
  have hu := bp.pullback_vanishes A F N P K hK H G
    BelorousskiPandharipande.stableArity 1 hin hout hb
  have hv : (A 2 (Fin 4)).map pullback.strata = 0 := by
    rw [pullback, strata_relabel, StrataRealization.map_relabel _ _ _ _ _ hl, hu, map_zero]
  apply L24Symmetry.average_vanishes (A 2 (Fin 4)) hs
  have hz (i : Fin 4) :
      (A 2 (Fin 4)).map (StrataModule.mulLegPsi (Pi.single i 1) pullback.strata) = 0 := by
    rw [StrataRealization.map_mulLegPsi _ P _ hp, hv, zero_mul]
  simp only [map_smul, map_sum, hz, smul_zero, Finset.sum_const_zero]

end AxiomaticGW.L24Initial

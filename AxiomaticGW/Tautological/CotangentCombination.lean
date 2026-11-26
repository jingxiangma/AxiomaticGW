/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.DecoratedGluingForgetful
public import AxiomaticGW.Tautological.DecoratedGluingEvaluation

/-!
# Signed cotangent combinations and their actual forgetful pullbacks

A finite rational combination retains its raw gluing constructions and node
powers. Pullback expands each term with the existing signed universal-curve
algorithm. Its class identity and GW contraction follow from the primitive
geometry; no new relation validity is imposed by this bookkeeping layer.
-/

@[expose] public section

namespace AxiomaticGW
open GluingExpression PsiBoundaryExpansion

/-- Rational weights on actual decorated gluings, with repeated terms retained. -/
abbrev CotangentCombination (g : ℕ) (S : Type) [Fintype S] :=
  Multiset (ℚ × CotangentTerm g S)

namespace CotangentCombination

variable {g : ℕ} {S : Type} [Fintype S]

/-- Interpret every coefficient in the existing free rational strata module. -/
noncomputable def strata (r : CotangentCombination g S) : StrataModule g S :=
  (r.map fun t ↦ t.1 • StrataModule.basis
    (t.2.expression.decoratedStratum t.2.decoration)).sum

/-- Add markings with all signed rational-tail and component-placement terms. -/
def pullback (r : CotangentCombination g S) (n : ℕ) :
    CotangentCombination g (ExtraMarkings n S) :=
  r.bind fun t ↦ (t.2.addMarkings n).map fun z ↦ (t.1 * (z.1 : ℚ), z.2)

/-- A pulled term retains its original source, signed placement and product coefficient. -/
theorem mem_pullback (r : CotangentCombination g S) (n : ℕ)
    (t : ℚ × CotangentTerm g (ExtraMarkings n S)) :
    t ∈ r.pullback n ↔ ∃ s ∈ r, ∃ z ∈ s.2.addMarkings n,
      (s.1 * (z.1 : ℚ), z.2) = t := by
  simp only [pullback, Multiset.mem_bind, Multiset.mem_map]

/-- Actual label transport preserves every coefficient and component power. -/
def relabel {T : Type} [Fintype T] (e : S ≃ T) (r : CotangentCombination g S) :
    CotangentCombination g T := r.map fun t ↦ (t.1, t.2.relabel e)

/-- The finite combination uses precisely the existing linear relabelling. -/
theorem strata_relabel {T : Type} [Fintype T] (e : S ≃ T)
    (r : CotangentCombination g S) :
    (r.relabel e).strata = StrataModule.relabel e r.strata := by
  simp only [relabel, strata, Multiset.map_map, Function.comp_def,
    map_multiset_sum, map_smul, StrataModule.relabel_basis]
  rfl

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- Realization of the computed combination is the primitive iterated pullback. -/
theorem map_strata_pullback
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (K : PsiForgetFormula P) (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (H : TailForgetCompatible C) (G : GluingForgetfulCompatibility F N)
    (r : CotangentCombination g S) (h : StableArity g S) (n : ℕ)
    (hin : ∀ t ∈ r, t.2.expression.Compatible A F N ∧
      t.2.expression.CotangentCompatible A P)
    (hout : ∀ t ∈ r, ∀ z ∈ t.2.addMarkings n,
      z.2.expression.Compatible A F N ∧ z.2.expression.CotangentCompatible A P) :
    (A g (ExtraMarkings n S)).map (r.pullback n).strata =
      C.forgetExtra g S h n ((A g S).map r.strata) := by
  have ht (t : ℚ × CotangentTerm g S) (hm : t ∈ r) :
      (((t.2.addMarkings n).map fun z ↦
        (t.1 * (z.1 : ℚ)) • (A g (ExtraMarkings n S)).map
          (StrataModule.basis (z.2.expression.decoratedStratum z.2.decoration))).sum) =
      C.forgetExtra g S h n (t.1 • (A g S).map
        (StrataModule.basis (t.2.expression.decoratedStratum t.2.decoration))) := by
    have he := congrArg (fun x ↦ t.1 • x)
      (t.2.sum_map_stratum_addMarkings A F N P K hK H G n (hin t hm).1
        (hin t hm).2 (hout t hm))
    simpa only [Multiset.smul_sum, Multiset.map_map, Function.comp_def,
      mul_smul, Int.cast_smul_eq_zsmul, map_rat_smul] using he
  simp only [strata, pullback, Multiset.map_bind, Multiset.sum_bind,
    map_multiset_sum, Multiset.map_map, Function.comp_def, map_smul]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  exact ht

/-- Vanishing downstairs is preserved by the explicit signed graph expansion. -/
theorem pullback_vanishes
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (K : PsiForgetFormula P) (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (H : TailForgetCompatible C) (G : GluingForgetfulCompatibility F N)
    (r : CotangentCombination g S) (h : StableArity g S) (n : ℕ)
    (hin : ∀ t ∈ r, t.2.expression.Compatible A F N ∧
      t.2.expression.CotangentCompatible A P)
    (hout : ∀ t ∈ r, ∀ z ∈ t.2.addMarkings n,
      z.2.expression.Compatible A F N ∧ z.2.expression.CotangentCompatible A P)
    (hz : (A g S).map r.strata = 0) :
    (A g (ExtraMarkings n S)).map (r.pullback n).strata = 0 := by
  rw [map_strata_pullback A F N P K hK H G r h n hin hout, hz, map_zero]

/-- Full-curve-class GW evaluation of a finite raw combination. -/
noncomputable def gwContraction {V B : Type u}
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C) (I : StableCurveIntegration C)
    (r : CotangentCombination g S) (beta : B) (k : S → ℕ) (a : S → V) : R :=
  (r.map fun t ↦ t.1 • t.2.expression.gwDecoratedAncestorContraction
    Omega P I t.2.decoration beta k a).sum

/-- A realized class relation gives the entire decorated GW equation. -/
theorem gwContraction_eq_zero {V B : Type u}
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (r : CotangentCombination g S) (h : StableArity g S)
    (hc : ∀ t ∈ r, t.2.expression.Compatible A F N ∧
      t.2.expression.CotangentCompatible A P)
    (hz : (A g S).map r.strata = 0) (beta : B) (k : S → ℕ) (a : S → V) :
    r.gwContraction Omega P I beta k a = 0 := by
  let ev := (A g S).integrateAgainst I h
    (P.monomial g S h k * Omega.omega g S h beta a)
  have he : ev r.strata = 0 := by
    rw [StrataRealization.integrateAgainst_apply, hz, mul_zero, map_zero]
  have ht (t : ℚ × CotangentTerm g S) (hm : t ∈ r) :
      ev (StrataModule.basis (t.2.expression.decoratedStratum t.2.decoration)) =
        t.2.expression.gwDecoratedAncestorContraction Omega P I t.2.decoration beta k a := by
    rw [← t.2.expression.gwDecoratedAncestorIntegral_apply A Omega P I
      t.2.decoration beta k a]
    exact congrArg (fun f ↦ f a)
      (t.2.expression.gwDecoratedAncestorIntegral_eq_contraction A F N Omega P
        t.2.decoration (hc t hm).1 (hc t hm).2 beta k)
  change (r.map _).sum = 0
  rw [strata, map_multiset_sum, Multiset.map_map] at he
  have hs : (r.map fun t ↦ ev (t.1 • StrataModule.basis
      (t.2.expression.decoratedStratum t.2.decoration))) =
      (r.map fun t ↦ t.1 • t.2.expression.gwDecoratedAncestorContraction
        Omega P I t.2.decoration beta k a) := by
    apply Multiset.map_congr rfl
    intro t hm
    rw [map_smul, ht t hm]
  exact (congrArg Multiset.sum hs).symm.trans he

end CotangentCombination
end AxiomaticGW

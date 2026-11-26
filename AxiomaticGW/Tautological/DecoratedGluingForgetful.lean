/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.DecoratedGluingMarking
public import AxiomaticGW.Tautological.DecoratedGluingRealization
public import AxiomaticGW.Tautological.RationalTailPullback

/-!
# Soundness of signed decorated forgetful pullbacks

The finite expansion is derived from the one-component monomial formula and
primitive universal-curve base change for raw gluings. Its signs and repeated
terms are evaluated before any graph-isomorphism consolidation. No decorated
pullback identity or numerical recurrence is assumed as geometric input.
-/

@[expose] public section

namespace AxiomaticGW.GluingExpression

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

namespace CotangentTerm

/-- The class of the existing expression with its original component powers. -/
noncomputable def classValue (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C)
    {g : ℕ} {S : Type} [Fintype S] (z : CotangentTerm g S) : C.H g S :=
  z.expression.decoratedClassValue F N P z.decoration

/-- Evaluate the coefficient before consolidating repeated graph classes. -/
noncomputable def weightedClassValue (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C)
    {g : ℕ} {S : Type} [Fintype S] (z : ℤ × CotangentTerm g S) : C.H g S :=
  z.1 • z.2.classValue F N P

/-- The explicit tail evaluates by the primitive raw section pushforward. -/
theorem classValue_tail (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C)
    {g : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (h : StableArity g S) (d : S → ℕ) (s : S) :
    (tail h d s).classValue F N P = PsiBoundaryExpansion.tailPush F h s
      (P.monomial g S h (Function.update d s (d s - 1))) := by
  simp only [tail, classValue, fundamental, relabel, separating, decoratedClassValue,
    P.monomial_zero, PsiBoundaryExpansion.tailPush, LinearMap.comp_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply, AlgEquiv.toLinearMap_apply]

end CotangentTerm

open CotangentTerm PsiBoundaryExpansion

/-- Each component placement and rational-tail correction is the actual pullback. -/
theorem sum_classValue_addCotangentMarking (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (K : PsiForgetFormula P) (hK : TailCompatible K F N) (H : TailForgetCompatible C)
    (G : GluingForgetfulCompatibility F N)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (d : x.CotangentDecoration) (l : x.DecidableLabels) :
    ((x.addCotangentMarking d l).map (weightedClassValue F N P)).sum =
      C.forget g S x.stable (x.decoratedClassValue F N P d) := by
  induction x with
  | fundamental g S h =>
    letI := l
    rw [decoratedClassValue, forget_monomial F N P K hK H]
    simp only [addCotangentMarking, Multiset.map_add, Multiset.sum_add,
      Multiset.map_singleton, Multiset.sum_singleton, Multiset.map_map,
      Function.comp_def, weightedClassValue, one_zsmul, neg_one_zsmul, classValue_tail]
    change P.monomial g (Option S) h.option (fun s ↦ s.elim 0 d) +
      ((Finset.univ.filter fun s ↦ d s ≠ 0).val.map fun s ↦
        -tailPush F h s (P.monomial g S h (Function.update d s (d s - 1)))).sum = _
    rw [← Finset.sum_eq_multiset_sum, Finset.sum_filter]
    simp only [ite_not, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : d s = 0 <;> simp only [hs, ↓reduceIte, neg_zero]
  | @relabel g S T _ _ e x ih =>
    have hn := congrArg (fun f ↦ f (x.decoratedClassValue F N P d))
      (C.forget_natural g S T x.stable (x.relabel e).stable e)
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at hn
    simp only [addCotangentMarking, Multiset.map_map, Function.comp_def,
      weightedClassValue, CotangentTerm.classValue, CotangentTerm.relabel, decoratedClassValue]
    rw [hn, ← ih d l, map_multiset_sum, Multiset.map_map]
    simp only [Function.comp_def, weightedClassValue, CotangentTerm.classValue, map_zsmul]
  | @separating g₁ g₂ S T _ _ x y ihx ihy =>
    rw [decoratedClassValue, G.separating, ← ihx d.1 l.1, ← ihy d.2 l.2]
    simp only [addCotangentMarking, Multiset.map_add, Multiset.sum_add, Multiset.map_map,
      Function.comp_def, weightedClassValue, CotangentTerm.classValue,
      CotangentTerm.relabel, CotangentTerm.separating, decoratedClassValue]
    congr 1
    · induction x.addCotangentMarking d.1 l.1 using Multiset.induction_on with
      | empty => simp only [Multiset.map_zero, Multiset.sum_zero, map_zero,
          TensorProduct.zero_tmul]
      | cons z zs ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, map_add, TensorProduct.add_tmul, ih,
          map_zsmul, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    · induction y.addCotangentMarking d.2 l.2 using Multiset.induction_on with
      | empty => simp only [Multiset.map_zero, Multiset.sum_zero, map_zero,
          TensorProduct.tmul_zero]
      | cons z zs ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, map_add, TensorProduct.tmul_add, ih,
          map_zsmul, TensorProduct.tmul_smul]
  | @nonseparating g S _ x ih =>
    rw [decoratedClassValue, G.nonseparating, ← ih d l]
    simp only [addCotangentMarking, Multiset.map_map, Function.comp_def,
      weightedClassValue, CotangentTerm.classValue, CotangentTerm.relabel,
      CotangentTerm.nonseparating, decoratedClassValue, map_multiset_sum,
      Multiset.map_map, map_zsmul]

namespace CotangentTerm

/-- Any finite number of added markings has the computed signed pullback. -/
theorem sum_classValue_addMarkings (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (K : PsiForgetFormula P) (hK : TailCompatible K F N) (H : TailForgetCompatible C)
    (G : GluingForgetfulCompatibility F N)
    {g : ℕ} {S : Type} [Fintype S] (z : CotangentTerm g S) (n : ℕ) :
    ((z.addMarkings n).map (weightedClassValue F N P)).sum =
      C.forgetExtra g S z.expression.stable n (z.classValue F N P) := by
  induction n with
  | zero =>
    simp only [addMarkings, Multiset.map_singleton, Multiset.sum_singleton,
      weightedClassValue, one_zsmul, StableCurveCohomology.forgetExtra, AlgHom.id_apply]
  | succ n ih =>
    have hstep (t : ℤ × CotangentTerm g (ExtraMarkings n S)) :
        ((t.2.addMarking.map fun w ↦ (t.1 * w.1, w.2)).map
          (weightedClassValue F N P)).sum =
        C.forget g (ExtraMarkings n S) (z.expression.stable.extraMarkings n)
          (weightedClassValue F N P t) := by
      have he := congrArg (fun a ↦ t.1 • a)
        (t.2.expression.sum_classValue_addCotangentMarking F N P K hK H G
          t.2.decoration t.2.labels)
      simpa only [addMarking, weightedClassValue, classValue, Multiset.map_map,
        Function.comp_def, mul_smul, Multiset.smul_sum, map_zsmul] using he
    rw [addMarkings, Multiset.map_bind, Multiset.sum_bind]
    simp only [hstep]
    change ((z.addMarkings n).map
      ((C.forget g (ExtraMarkings n S) (z.expression.stable.extraMarkings n)) ∘
        weightedClassValue F N P)).sum = _
    rw [← Multiset.map_map, ← map_multiset_sum, ih]
    rfl

attribute [local instance] strataRealizationModule

/-- Primitive realization compatibility turns the class calculation into a graph formula. -/
theorem sum_map_stratum_addMarkings
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (K : PsiForgetFormula P) (hK : TailCompatible K F N) (H : TailForgetCompatible C)
    (G : GluingForgetfulCompatibility F N)
    {g : ℕ} {S : Type} [Fintype S] (z : CotangentTerm g S) (n : ℕ)
    (hz : z.expression.Compatible A F N) (hp : z.expression.CotangentCompatible A P)
    (hout : ∀ t ∈ z.addMarkings n,
      t.2.expression.Compatible A F N ∧ t.2.expression.CotangentCompatible A P) :
    ((z.addMarkings n).map fun t ↦ t.1 •
      (A g (ExtraMarkings n S)).map
        (StrataModule.basis (t.2.expression.decoratedStratum t.2.decoration))).sum =
      C.forgetExtra g S z.expression.stable n
        ((A g S).map (StrataModule.basis (z.expression.decoratedStratum z.decoration))) := by
  rw [z.expression.map_decoratedStratum_eq_classValue A F N P z.decoration hz hp]
  have he : ((z.addMarkings n).map fun t ↦ t.1 •
      (A g (ExtraMarkings n S)).map
        (StrataModule.basis (t.2.expression.decoratedStratum t.2.decoration))) =
      (z.addMarkings n).map (weightedClassValue F N P) := by
    apply Multiset.map_congr rfl
    intro t ht
    rw [t.2.expression.map_decoratedStratum_eq_classValue A F N P t.2.decoration
      (hout t ht).1 (hout t ht).2]
    rfl
  rw [he, z.sum_classValue_addMarkings F N P K hK H G n]
  rfl

/-- Pair the actual iterated pullback with an arbitrary upstairs insertion. -/
theorem integrateForgetExtra_eq_sum
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (K : PsiForgetFormula P) (hK : TailCompatible K F N) (H : TailForgetCompatible C)
    (G : GluingForgetfulCompatibility F N)
    {g : ℕ} {S : Type} [Fintype S] (z : CotangentTerm g S) (n : ℕ)
    (hz : z.expression.Compatible A F N) (hp : z.expression.CotangentCompatible A P)
    (hout : ∀ t ∈ z.addMarkings n,
      t.2.expression.Compatible A F N ∧ t.2.expression.CotangentCompatible A P)
    (w : C.H g (ExtraMarkings n S)) :
    (A g S).integrateForgetExtra I z.expression.stable n w
      (StrataModule.basis (z.expression.decoratedStratum z.decoration)) =
      ((z.addMarkings n).map fun t ↦ t.1 •
        (A g (ExtraMarkings n S)).integrateAgainst I (z.expression.stable.extraMarkings n) w
          (StrataModule.basis (t.2.expression.decoratedStratum t.2.decoration))).sum := by
  let L := (I.integrate g (ExtraMarkings n S) (z.expression.stable.extraMarkings n)).comp
    (LinearMap.mulLeft R w)
  change L (C.forgetExtra g S z.expression.stable n
    ((A g S).map (StrataModule.basis (z.expression.decoratedStratum z.decoration)))) = _
  rw [← z.sum_map_stratum_addMarkings A F N P K hK H G n hz hp hout,
    map_multiset_sum, Multiset.map_map]
  simp only [Function.comp_def, map_zsmul]
  rfl

end CotangentTerm

end AxiomaticGW.GluingExpression

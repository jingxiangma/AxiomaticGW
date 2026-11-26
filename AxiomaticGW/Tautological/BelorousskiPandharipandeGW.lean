/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.BelorousskiPandharipande
public import AxiomaticGW.Tautological.GetzlerGluing
public import AxiomaticGW.Tautological.DecoratedGluingEvaluation

/-!
# The full BP equation as decorated GW contractions

All twenty published diagrams are built by actual elementary gluings.
Component cotangent powers are present before gluing, so the genus-two node
powers retain their specified branches. All six labellings and all curve-class
splittings remain in the equation. The first four diagrams can contain a
genus-two component; every other leaf has genus at most one.

The resulting GW equation uses the original 3-spin geometric inputs and
primitive gluing/psi compatibility. It holds over commutative rational algebras,
full effective classes and three external ancestor powers. It is an equation
for reconstruction, not yet a terminating genus-two numerical evaluator.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open RelationCertificate GluingExpression GetzlerGraphs

/-- A checked node-flag reordering used by the explicit constructions. -/
def flagPermutation0 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 0, 1, 5]
  invFun := ![3, 4, 0, 1, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- A checked node-flag reordering used by the explicit constructions. -/
def flagPermutation1 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 0, 1, 4]
  invFun := ![2, 3, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- A checked node-flag reordering used by the explicit constructions. -/
def flagPermutation2 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- A checked node-flag reordering used by the explicit constructions. -/
def flagPermutation3 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 4, 0, 1]
  invFun := ![3, 4, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- A checked node-flag reordering used by the explicit constructions. -/
def flagPermutation4 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 0, 4, 1]
  invFun := ![2, 4, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- A checked node-flag reordering used by the explicit constructions. -/
def flagPermutation5 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 3, 4, 1]
  invFun := ![1, 4, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Elementary gluing constructions for the twenty diagrams, in published order. -/
def paperExpression : Fin 20 → GluingExpression 2 (Fin 3) :=
  ![(join (m := 1) (n := 2) 1 2
      (join (m := 0) (n := 2) 0 1
      (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))
      (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))),
    (join (m := 0) (n := 3) 0 3
      (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))
      (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))),
    (join (m := 1) (n := 2) 1 2
      (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity]))
      (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))),
    (join (m := 1) (n := 2) 1 2
      (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity]))
      (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))),
    (join (m := 3) (n := 0) 3 0
      (join (m := 0) (n := 4) 0 3
      (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
      (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
      (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))),
    (join (m := 2) (n := 1) 2 1
      (join (m := 0) (n := 3) 0 2
      (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
      (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
      (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))),
    (join (m := 1) (n := 2) 1 2
      (join (m := 0) (n := 2) 0 1
      (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
      (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))),
    (join (m := 2) (n := 1) 2 1
      (join (m := 1) (n := 2) 1 1
      (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
      (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))),
    (join (m := 0) (n := 3) 0 3
      (join (m := 0) (n := 1) 0 0
      (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
      (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
      (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))),
    (join (m := 1) (n := 2) 1 2
      (join (m := 1) (n := 1) 1 0
      (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
      (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
      (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))),
    (join (m := 1) (n := 2) 1 2
      (join (m := 0) (n := 2) 0 1
      (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
      (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))
      (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))),
    (join (m := 3) (n := 0) 3 0
      (close ((GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity])).relabel
        (flagPermutation0)))
      (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))),
    (join (m := 2) (n := 1) 2 1
      (close ((GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])).relabel
        (flagPermutation1)))
      (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))),
    (join (m := 1) (n := 2) 1 2
      (close ((GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])).relabel
        (flagPermutation2)))
      (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))),
    (join (m := 0) (n := 3) 0 3
      (close (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]))),
    (close ((join (m := 4) (n := 1) 3 0
      (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
      (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel
        (flagPermutation3))),
    (close ((join (m := 3) (n := 2) 2 1
      (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
      (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel
        (flagPermutation4))),
    (close ((join (m := 2) (n := 3) 1 2
      (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
      (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]))).relabel
        (flagPermutation5))),
    (join (m := 0) (n := 3) 0 3
      (close (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))
      (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))),
    (join (m := 1) (n := 2) 1 2
      (close ((GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])).relabel
        (flagPermutation2)))
      (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))]

/-- Original component cotangent powers, including the marked genus-two node branches. -/
def paperTerm : Fin 20 → (x : GluingExpression 2 (Fin 3)) × x.CotangentDecoration :=
  ![⟨paperExpression 0, ((![0], ![0, 0, 0]), ![0, 0, 0])⟩,
    ⟨paperExpression 1, (![1], ![0, 0, 0, 0])⟩,
    ⟨paperExpression 2, (![1, 0], ![0, 0, 0])⟩,
    ⟨paperExpression 3, (![0, 1], ![0, 0, 0])⟩,
    ⟨paperExpression 4, ((![0], ![0, 0, 0, 0, 0]), ![0])⟩,
    ⟨paperExpression 5, ((![0], ![0, 0, 0, 0]), ![0, 0])⟩,
    ⟨paperExpression 6, ((![0], ![0, 0, 0]), ![0, 0, 0])⟩,
    ⟨paperExpression 7, ((![0, 0], ![0, 0, 0]), ![0, 0])⟩,
    ⟨paperExpression 8, ((![0], ![0, 0]), ![0, 0, 0, 0])⟩,
    ⟨paperExpression 9, ((![0, 0], ![0, 0]), ![0, 0, 0])⟩,
    ⟨paperExpression 10, ((![0], ![0, 0, 0]), ![0, 0, 0])⟩,
    ⟨paperExpression 11, (![0, 0, 0, 0, 0, 0], ![0])⟩,
    ⟨paperExpression 12, (![0, 0, 0, 0, 0], ![0, 0])⟩,
    ⟨paperExpression 13, (![0, 0, 0, 0], ![0, 0, 0])⟩,
    ⟨paperExpression 14, (![0, 0, 0], ![0, 0, 0, 0])⟩,
    ⟨paperExpression 15, (![0, 0, 0, 0, 0], ![0, 0])⟩,
    ⟨paperExpression 16, (![0, 0, 0, 0], ![0, 0, 0])⟩,
    ⟨paperExpression 17, (![0, 0, 0], ![0, 0, 0, 0])⟩,
    ⟨paperExpression 18, (![0, 0, 0], ![0, 0, 0, 0])⟩,
    ⟨paperExpression 19, (![0, 0, 0, 0], ![0, 0, 0])⟩]

/-- The actual constructions recover the published decorated graph classes. -/
theorem paperTerm_stratum (i : Fin 20) :
    (paperTerm i).1.decoratedStratum (paperTerm i).2 = paperStratum i := by
  apply Quotient.sound
  apply (DecoratedStableGraph.isomorphic?_eq_true_iff _ _).mp
  simp only [paperGraph, tableGraph, DecoratedStableGraph.toDecoration_eq_mk]
  fin_cases i <;> decide +kernel

/-- Only the first four terms retain a genus-two component. -/
theorem paperTerm_lower_genus : ∀ i, 4 ≤ i.val → (paperTerm i).1.maxComponentGenus ≤ 1 := by
  decide +kernel

/-- Relabelling preserves the component decoration and all raw multiplicities. -/
def orbitTerm (i : Fin 20) (e : Fin 6) :
    (x : GluingExpression 2 (Fin 3)) × x.CotangentDecoration :=
  ⟨(paperTerm i).1.relabel (labelPermutation e), (paperTerm i).2⟩

/-- Each labelled term is the corresponding published stratum. -/
theorem orbitTerm_stratum (i : Fin 20) (e : Fin 6) :
    (orbitTerm i e).1.decoratedStratum (orbitTerm i e).2 =
      (paperStratum i).relabel (labelPermutation e) := by
  rw [orbitTerm, GluingExpression.decoratedStratum_relabel, paperTerm_stratum]

/-- The full relation includes every actual decorated gluing term. -/
theorem paperRelation_as_terms : paperRelation =
    ∑ i, (paperCoefficient i * paperNormalization i) •
      ∑ e, StrataModule.basis ((orbitTerm i e).1.decoratedStratum (orbitTerm i e).2) := by
  simp only [orbitTerm_stratum, paperRelation]

universe u
attribute [local instance] strataRealizationModule

/-- The complete class relation gives a full-class GW equation from original generators.
No top-genus recurrence or numerical value is among the hypotheses. -/
theorem gw_relation_from_generators {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (p : Exchange) (hp : AcceptsExchange p)
    (hl : ∀ e, (Z 2 (Fin 3)).RelabelCompatible (Z 2 (Fin 3))
      stableArity stableArity (labelPermutation e))
    (hc : ∀ b, SourceMapCompatible Z F b)
    (hinterior : ∀ i : Fin 4, (Z 2 (Fin 3)).map
      (interpret columns (unsymmetrizedRows (Fin.castAdd 16 i))) = 0)
    (hsource : ∀ i, (Z (sourceGenus (sourceFamily i)) (Fin (sourceArity (sourceFamily i)))).map
      (sourceExpression i) = 0)
    (hglue : ∀ i e, (orbitTerm i e).1.Compatible Z F N)
    (hcotangent : ∀ i e, (orbitTerm i e).1.CotangentCompatible Z P)
    (beta : B) (k : Fin 3 → ℕ) (a : Fin 3 → V) :
    (∑ i, (paperCoefficient i * paperNormalization i) •
      ∑ e, (orbitTerm i e).1.gwDecoratedAncestorContraction Omega P I (orbitTerm i e).2
        beta k a) = 0 := by
  let ev := (Z 2 (Fin 3)).integrateAgainst I stableArity
    (P.monomial 2 (Fin 3) stableArity k * Omega.omega 2 (Fin 3) stableArity beta a)
  have hz : ev paperRelation = 0 := by
    rw [StrataRealization.integrateAgainst_apply,
      realized_relation_from_generators Z F p hp hl hc hinterior hsource, mul_zero, map_zero]
  have ht : ∀ i e,
      ev (StrataModule.basis ((orbitTerm i e).1.decoratedStratum (orbitTerm i e).2)) =
        (orbitTerm i e).1.gwDecoratedAncestorContraction Omega P I (orbitTerm i e).2 beta k a := by
    intro i e
    rw [← (orbitTerm i e).1.gwDecoratedAncestorIntegral_apply Z Omega P I
      (orbitTerm i e).2 beta k a]
    exact congrArg (fun f ↦ f a)
      ((orbitTerm i e).1.gwDecoratedAncestorIntegral_eq_contraction Z F N Omega P
        (orbitTerm i e).2 (hglue i e) (hcotangent i e) beta k)
  simpa only [paperRelation_as_terms, map_sum, map_smul, ht] using hz

end AxiomaticGW.BelorousskiPandharipande

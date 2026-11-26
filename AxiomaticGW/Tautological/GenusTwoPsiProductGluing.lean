/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GenusTwoPsiProductSources
public import AxiomaticGW.Tautological.GetzlerGluing
public import AxiomaticGW.Tautological.DecoratedGluingEvaluation

/-!
# Raw decorated gluings for the complete cotangent-product boundary

All 25 terms are built from actual component moduli spaces. External labels
and original node cotangent powers are checked against the held frame.
The numerical equation uses full curve-class splittings and inverse metrics.
Its sole genus-two factor is one-marked; it is retained, not discarded.
-/

@[expose] public section

namespace AxiomaticGW.GenusTwoPsiProduct
open RelationCertificate GluingExpression GetzlerGraphs

/-- Exact flag transport before closing a node or naming external markings. -/
def flagPermutation0 : Equiv.Perm (Fin 2) where
  toFun := ![1, 0]
  invFun := ![1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Exact flag transport before closing a node or naming external markings. -/
def flagPermutation1 : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Exact flag transport before closing a node or naming external markings. -/
def flagPermutation2 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 3, 1]
  invFun := ![1, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Exact flag transport before closing a node or naming external markings. -/
def flagPermutation3 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Exact flag transport before closing a node or naming external markings. -/
def flagPermutation4 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 0, 1, 4, 5]
  invFun := ![2, 3, 0, 1, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual raw gluing for held boundary column 8. -/
def boundaryExpression0 : GluingExpression 2 (Fin 2) :=
  (join (m := 2) (n := 0) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity])))

/-- Actual raw gluing for held boundary column 10. -/
def boundaryExpression1 : GluingExpression 2 (Fin 2) :=
  (join (m := 0) (n := 2) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

/-- Actual raw gluing for held boundary column 11. -/
def boundaryExpression2 : GluingExpression 2 (Fin 2) :=
  (join (m := 0) (n := 2) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

/-- Actual raw gluing for held boundary column 12. -/
def boundaryExpression3 : GluingExpression 2 (Fin 2) :=
  (join (m := 0) (n := 2) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

/-- Actual raw gluing for held boundary column 15. -/
def boundaryExpression4 : GluingExpression 2 (Fin 2) :=
  ((join (m := 1) (n := 1) 1 1
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation0)

/-- Actual raw gluing for held boundary column 16. -/
def boundaryExpression5 : GluingExpression 2 (Fin 2) :=
  ((join (m := 1) (n := 1) 1 1
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation0)

/-- Actual raw gluing for held boundary column 17. -/
def boundaryExpression6 : GluingExpression 2 (Fin 2) :=
  ((join (m := 1) (n := 1) 1 1
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation0)

/-- Actual raw gluing for held boundary column 18. -/
def boundaryExpression7 : GluingExpression 2 (Fin 2) :=
  ((join (m := 1) (n := 1) 1 1
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation0)

/-- Actual raw gluing for held boundary column 19. -/
def boundaryExpression8 : GluingExpression 2 (Fin 2) :=
  (join (m := 0) (n := 2) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))))

/-- Actual raw gluing for held boundary column 20. -/
def boundaryExpression9 : GluingExpression 2 (Fin 2) :=
  ((join (m := 1) (n := 1) 1 1
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation0)

/-- Actual raw gluing for held boundary column 21. -/
def boundaryExpression10 : GluingExpression 2 (Fin 2) :=
  (join (m := 1) (n := 1) 1 1
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))

/-- Actual raw gluing for held boundary column 22. -/
def boundaryExpression11 : GluingExpression 2 (Fin 2) :=
  (join (m := 2) (n := 0) 2 0
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity])))

/-- Actual raw gluing for held boundary column 24. -/
def boundaryExpression12 : GluingExpression 2 (Fin 2) :=
  (join (m := 0) (n := 2) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

/-- Actual raw gluing for held boundary column 26. -/
def boundaryExpression13 : GluingExpression 2 (Fin 2) :=
  (close ((GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])).relabel
    flagPermutation1))

/-- Actual raw gluing for held boundary column 27. -/
def boundaryExpression14 : GluingExpression 2 (Fin 2) :=
  (close ((GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])).relabel
    flagPermutation1))

/-- Actual raw gluing for held boundary column 28. -/
def boundaryExpression15 : GluingExpression 2 (Fin 2) :=
  (close ((GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])).relabel
    flagPermutation1))

/-- Actual raw gluing for held boundary column 29. -/
def boundaryExpression16 : GluingExpression 2 (Fin 2) :=
  (close ((join (m := 2) (n := 2) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation1))

/-- Actual raw gluing for held boundary column 30. -/
def boundaryExpression17 : GluingExpression 2 (Fin 2) :=
  ((close ((join (m := 2) (n := 2) 1 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel
      flagPermutation2)).relabel
      flagPermutation0)

/-- Actual raw gluing for held boundary column 31. -/
def boundaryExpression18 : GluingExpression 2 (Fin 2) :=
  (close ((join (m := 2) (n := 2) 1 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation2))

/-- Actual raw gluing for held boundary column 32. -/
def boundaryExpression19 : GluingExpression 2 (Fin 2) :=
  (close ((join (m := 3) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation1))

/-- Actual raw gluing for held boundary column 33. -/
def boundaryExpression20 : GluingExpression 2 (Fin 2) :=
  (close (join (m := 2) (n := 2) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))))

/-- Actual raw gluing for held boundary column 34. -/
def boundaryExpression21 : GluingExpression 2 (Fin 2) :=
  ((close ((join (m := 3) (n := 1) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel
      flagPermutation3)).relabel
      flagPermutation0)

/-- Actual raw gluing for held boundary column 35. -/
def boundaryExpression22 : GluingExpression 2 (Fin 2) :=
  (close ((join (m := 3) (n := 1) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation3))

/-- Actual raw gluing for held boundary column 36. -/
def boundaryExpression23 : GluingExpression 2 (Fin 2) :=
  (close ((join (m := 4) (n := 0) 4 0
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation1))

/-- Actual raw gluing for held boundary column 37. -/
def boundaryExpression24 : GluingExpression 2 (Fin 2) :=
  (close ((close ((GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity])).relabel
    flagPermutation4)).relabel flagPermutation1))

/-- The complete nonzero boundary support, with the genus-two tail first. -/
def boundaryIndex (i : Fin 25) : Fin 38 :=
  (#[8, 10, 11, 12, 15, 16, 17, 18, 19, 20, 21, 22, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36,
    37] : Array (Fin 38))[i.val]

/-- Powers belong to the original component flags, including nodes. -/
def boundaryTerm (i : Fin 25) : (x : GluingExpression 2 (Fin 2)) × x.CotangentDecoration :=
  (#[⟨boundaryExpression0, (![0, 0, 0], ![1])⟩,
    ⟨boundaryExpression1, (![0], ![1, 0, 0])⟩,
    ⟨boundaryExpression2, (![0], ![0, 1, 0])⟩,
    ⟨boundaryExpression3, (![0], ![0, 0, 1])⟩,
    ⟨boundaryExpression4, (![1, 0], ![0, 0])⟩,
    ⟨boundaryExpression5, (![0, 1], ![0, 0])⟩,
    ⟨boundaryExpression6, (![0, 0], ![1, 0])⟩,
    ⟨boundaryExpression7, (![0, 0], ![0, 1])⟩,
    ⟨boundaryExpression8, (![0], (![0, 0, 0], ![0, 0]))⟩,
    ⟨boundaryExpression9, ((![0], ![0, 0, 0]), ![0, 0])⟩,
    ⟨boundaryExpression10, ((![0], ![0, 0, 0]), ![0, 0])⟩,
    ⟨boundaryExpression11, ((![0], ![0, 0, 0, 0]), ![0])⟩,
    ⟨boundaryExpression12, (![1], ![0, 0, 0])⟩,
    ⟨boundaryExpression13, ![0, 0, 1, 0]⟩,
    ⟨boundaryExpression14, ![1, 0, 0, 0]⟩,
    ⟨boundaryExpression15, ![0, 1, 0, 0]⟩,
    ⟨boundaryExpression16, (![0, 0, 0], ![0, 0, 0])⟩,
    ⟨boundaryExpression17, (![0, 0, 0], ![0, 0, 0])⟩,
    ⟨boundaryExpression18, (![0, 0, 0], ![0, 0, 0])⟩,
    ⟨boundaryExpression19, (![0, 0, 0, 0], ![0, 0])⟩,
    ⟨boundaryExpression20, (![0, 0, 0], ![0, 0, 0])⟩,
    ⟨boundaryExpression21, (![0, 0, 0, 0], ![0, 0])⟩,
    ⟨boundaryExpression22, (![0, 0, 0, 0], ![0, 0])⟩,
    ⟨boundaryExpression23, (![0, 0, 0, 0, 0], ![0])⟩,
    ⟨boundaryExpression24, ![0, 0, 0, 0, 0, 0]⟩] :
      Array ((x : GluingExpression 2 (Fin 2)) × x.CotangentDecoration))[i.val]

/-- All incidences, marking orders and decorated branches agree in the kernel. -/
theorem boundaryTerm_stratum (i : Fin 25) :
    (boundaryTerm i).1.decoratedStratum (boundaryTerm i).2 = columns (boundaryIndex i) := by
  apply Quotient.sound
  apply (DecoratedStableGraph.isomorphic?_eq_true_iff _ _).mp
  simp only [graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  fin_cases i <;> decide +kernel

/-- Exactly one term retains genus two; the other 24 lower component genus. -/
theorem boundaryTerm_lower_genus : ∀ i, i ≠ 0 →
    (boundaryTerm i).1.maxComponentGenus ≤ 1 := by decide +kernel

/-- The genus-two component is one-marked and its sole flag carries psi. -/
theorem genusTwo_tail : boundaryTerm 0 =
    ⟨join (m := 2) (n := 0) 2 0
      (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
      (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity])), (![0, 0, 0], ![1])⟩ :=
        rfl

/-- The retained genus-two term has coefficient three in raw normalization. -/
theorem genusTwo_tail_coefficient : boundary (boundaryIndex 0) = 3 := by decide +kernel

/-- Every nonzero boundary coefficient is included, with no omitted remainder. -/
theorem boundary_coordinates : boundary =
    combination (fun i ↦ Pi.single (boundaryIndex i) 1)
      ⟨fun i ↦ boundary (boundaryIndex i)⟩ := by decide +kernel

/-- The formal boundary is precisely this complete constructed graph sum. -/
theorem interpret_boundary : interpret columns boundary =
    ∑ i, boundary (boundaryIndex i) •
      StrataModule.basis ((boundaryTerm i).1.decoratedStratum (boundaryTerm i).2) := by
  conv_lhs => rw [boundary_coordinates, interpret_combination]
  simp only [interpret, Fintype.linearCombination_apply_single, one_smul, boundaryTerm_stratum]

universe u
attribute [local instance] strataRealizationModule

/-- The complete GW equation, with arbitrary remaining powers at both markings,
follows from original source classes and primitive gluing/cotangent geometry. -/
theorem gwAncestor_reduction_from_generators
    {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (p : Exchange) (hp : AcceptsExchange p)
    (hc : ∀ b, SourceCompatible Z F b)
    (hsource : ∀ b, (Z (BelorousskiPandharipande.sourceGenus (sourceFamily b))
      (Fin (BelorousskiPandharipande.sourceArity (sourceFamily b)))).map
        (BelorousskiPandharipande.sourceExpression (sourceIndex b)) = 0)
    (hinterior : ∀ i : Fin 10,
      (Z 2 (Fin 2)).map (interpret columns (rows (i.castLE (by decide)))) = 0)
    (hpsi : (Z 2 (Fin 2)).LegPsiCompatible P stableArity)
    (hfund : (Z 2 (Fin 2)).map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 2) stableArity)) = 1)
    (hglue : ∀ i, (boundaryTerm i).1.Compatible Z F N)
    (hcotangent : ∀ i, (boundaryTerm i).1.CotangentCompatible Z P)
    (beta : B) (k : Fin 2 → ℕ) (a : Fin 2 → V) :
    Omega.ancestorInvariant P I 2 (Fin 2) stableArity beta (k + fun _ ↦ 1) a =
      ∑ i, boundary (boundaryIndex i) •
        (boundaryTerm i).1.gwDecoratedAncestorContraction Omega P I (boundaryTerm i).2
          beta k a := by
  let ev := (Z 2 (Fin 2)).integrateAgainst I stableArity
    (P.monomial 2 (Fin 2) stableArity k * Omega.omega 2 (Fin 2) stableArity beta a)
  have hz := rows_vanish_from_generators Z F hc hsource hinterior
  have he := evaluated_relation p hp ev (by
    intro i
    rw [StrataRealization.integrateAgainst_apply, hz i, mul_zero, map_zero])
  have hl : ev (StrataModule.basis (columns 5)) =
      Omega.ancestorInvariant P I 2 (Fin 2) stableArity beta (k + fun _ ↦ 1) a := by
    rw [psi_product_column]
    change (Z 2 (Fin 2)).integrateAgainst I stableArity _ _ = _
    rw [StrataRealization.integrateAgainst_apply,
      (Z 2 (Fin 2)).map_addLegPsi P stableArity hpsi, hfund, one_mul,
      GromovWittenTheory.ancestorInvariant_apply, P.monomial_add]
    congr 1
    ac_rfl
  rw [hl, interpret_boundary, map_sum] at he
  simp only [map_smul] at he
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← (boundaryTerm i).1.gwDecoratedAncestorIntegral_apply Z Omega P I
    (boundaryTerm i).2 beta k a]
  exact congrArg (fun f ↦ f a)
    ((boundaryTerm i).1.gwDecoratedAncestorIntegral_eq_contraction Z F N Omega P
      (boundaryTerm i).2 (hglue i) (hcotangent i) beta k)

end AxiomaticGW.GenusTwoPsiProduct

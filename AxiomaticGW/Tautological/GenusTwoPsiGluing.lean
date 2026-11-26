/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GenusTwoPsiSquare
public import AxiomaticGW.Tautological.GetzlerGluing
public import AxiomaticGW.Tautological.DecoratedGluingEvaluation

/-!
# Actual decorated gluings for the genus-two psi-square boundary

All ten nonzero boundary columns are constructed from genus-zero or genus-one
components. Cotangent factors on node branches are present before those
branches are glued. Kernel isomorphisms bind the constructions to the held
marked relation. Coefficients remain raw; no automorphism division is added.
-/

@[expose] public section

namespace AxiomaticGW.GenusTwoPsiSquare
open GluingExpression GetzlerGraphs RelationCertificate

/-- The unmarked elliptic component is joined to the marked elliptic component. -/
def separatingExpression : GluingExpression 2 (Fin 1) :=
  join (m := 0) (n := 1) 0 0
    (.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (.fundamental 1 (Fin 2) (by norm_num [StableArity]))

/-- Two elliptic tails attached to the marked rational middle component. -/
def chainExpression : GluingExpression 2 (Fin 1) :=
  join (m := 1) (n := 0) 0 0
    (join (m := 0) (n := 2) 0 0
      (.fundamental 1 (Fin 1) (by norm_num [StableArity]))
      (.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (.fundamental 1 (Fin 1) (by norm_num [StableArity]))

/-- The first two elliptic markings form a loop; the third stays external. -/
def loopExpression : GluingExpression 2 (Fin 1) :=
  close (.fundamental 1 (Fin 3) (by norm_num [StableArity]))

/-- One separating edge followed by a second edge between the same two vertices. -/
def parallelExpression : GluingExpression 2 (Fin 1) :=
  close ((join (m := 2) (n := 1) 0 0
    (.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel (Equiv.swap 1 2))

/-- A rational loop joined to an elliptic component carrying the external marking. -/
def loopBridgeMarkedEllipticExpression : GluingExpression 2 (Fin 1) :=
  join (m := 0) (n := 1) 0 0
    (close (.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (.fundamental 1 (Fin 2) (by norm_num [StableArity]))

/-- A marked rational loop joined to an unmarked elliptic component. -/
def loopBridgeMarkedRationalExpression : GluingExpression 2 (Fin 1) :=
  join (m := 1) (n := 0) 0 0
    (close (.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (.fundamental 1 (Fin 1) (by norm_num [StableArity]))

/-- Two ordered self-gluings of the rational five-point component. -/
def twoLoopsExpression : GluingExpression 2 (Fin 1) :=
  close (close (.fundamental 0 (Fin 5) (by norm_num [StableArity])))

/-- The ten nonzero boundary slots of the independently held relation. -/
def boundaryIndex : Fin 10 → Fin 17 := ![5, 6, 7, 9, 11, 12, 13, 14, 15, 16]

/-- Every original component power is explicit, including the chosen node branch. -/
def boundaryTerm : Fin 10 → (x : GluingExpression 2 (Fin 1)) × x.CotangentDecoration :=
  ![⟨separatingExpression, (![0], ![0, 1])⟩,
    ⟨separatingExpression, (![0], ![1, 0])⟩,
    ⟨chainExpression, chainExpression.zeroDecoration⟩,
    ⟨separatingExpression, (![1], ![0, 0])⟩,
    ⟨loopExpression, ![1, 0, 0]⟩,
    ⟨loopExpression, ![0, 0, 1]⟩,
    ⟨parallelExpression, parallelExpression.zeroDecoration⟩,
    ⟨loopBridgeMarkedEllipticExpression, loopBridgeMarkedEllipticExpression.zeroDecoration⟩,
    ⟨loopBridgeMarkedRationalExpression, loopBridgeMarkedRationalExpression.zeroDecoration⟩,
    ⟨twoLoopsExpression, twoLoopsExpression.zeroDecoration⟩]

/-- Kernel graph isomorphisms check actual labels, incidence and cotangent decorations. -/
theorem boundaryTerm_stratum (i : Fin 10) :
    (boundaryTerm i).1.decoratedStratum (boundaryTerm i).2 = columns (boundaryIndex i) := by
  apply Quotient.sound
  apply (DecoratedStableGraph.isomorphic?_eq_true_iff _ _).mp
  simp only [graph, decorate, DecoratedStableGraph.toDecoration_eq_mk]
  fin_cases i <;> decide +kernel

/-- Every numerical dependency has genus at most one. -/
theorem boundaryTerm_genus : ∀ i, (boundaryTerm i).1.maxComponentGenus ≤ 1 := by
  decide +kernel

/-- The ten terms include the entire boundary side, with all signed weights. -/
theorem boundary_coordinates : boundary =
    combination (fun i ↦ Pi.single (boundaryIndex i) 1)
      ⟨fun i ↦ boundary (boundaryIndex i)⟩ := by decide +kernel

/-- The geometric boundary is the sum of precisely these constructed raw strata. -/
theorem interpret_boundary : interpret columns boundary =
    ∑ i, boundary (boundaryIndex i) •
      StrataModule.basis ((boundaryTerm i).1.decoratedStratum (boundaryTerm i).2) := by
  conv_lhs => rw [boundary_coordinates, interpret_combination]
  simp only [interpret, Fintype.linearCombination_apply_single, one_smul, boundaryTerm_stratum]

universe u
attribute [local instance] strataRealizationModule

/-- The accepted psi-square relation reduces actual one-marked GW ancestors to
full-class contractions of the ten decorated lower-genus graphs. -/
theorem gwAncestor_reduction {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (p : Exchange) (hp : AcceptsExchange p)
    (hpsi : (Z 2 (Fin 1)).LegPsiCompatible P stableArity)
    (hfund : (Z 2 (Fin 1)).map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) stableArity)) = 1)
    (hrows : ∀ i, (Z 2 (Fin 1)).map (interpret columns (rows i)) = 0)
    (hglue : ∀ i, (boundaryTerm i).1.Compatible Z F N)
    (hcotangent : ∀ i, (boundaryTerm i).1.CotangentCompatible Z P)
    (beta : B) (k : ℕ) (a : Fin 1 → V) :
    Omega.ancestorInvariant P I 2 (Fin 1) stableArity beta (Pi.single 0 (2 + k)) a =
      ∑ i, boundary (boundaryIndex i) •
        (boundaryTerm i).1.gwDecoratedAncestorContraction Omega P I (boundaryTerm i).2
          beta (Pi.single 0 k) a := by
  let ev := (Z 2 (Fin 1)).integrateAgainst I stableArity
    (P.monomial 2 (Fin 1) stableArity (Pi.single 0 k) *
      Omega.omega 2 (Fin 1) stableArity beta a)
  have he := evaluated_relation p.presentation hp.1 ev (by
    intro i
    rw [StrataRealization.integrateAgainst_apply, hrows i, mul_zero, map_zero])
  have hl : ev (StrataModule.basis (columns 3)) =
      Omega.ancestorInvariant P I 2 (Fin 1) stableArity beta (Pi.single 0 (2 + k)) a := by
    rw [psi_square_column]
    change (Z 2 (Fin 1)).integrateAgainst I stableArity _ _ = _
    rw [StrataRealization.integrateAgainst_apply,
      (Z 2 (Fin 1)).map_addLegPsi_single P stableArity hpsi, hfund, one_mul,
      GromovWittenTheory.ancestorInvariant_apply, P.monomial_single, P.monomial_single]
    congr 1
    rw [pow_add]
    ac_rfl
  rw [hl, interpret_boundary, map_sum] at he
  simp only [map_smul] at he
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← (boundaryTerm i).1.gwDecoratedAncestorIntegral_apply Z Omega P I
    (boundaryTerm i).2 beta (Pi.single 0 k) a]
  exact congrArg (fun f ↦ f a)
    ((boundaryTerm i).1.gwDecoratedAncestorIntegral_eq_contraction Z F N Omega P
      (boundaryTerm i).2 (hglue i) (hcotangent i) beta (Pi.single 0 k))

end AxiomaticGW.GenusTwoPsiSquare

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Tautological.Fixtures.GenusTwoPsiSquareReplay

/-! Regression examples for the marked relation's geometric meaning and source boundary. -/

open AxiomaticGW RelationCertificate
open GenusTwoPsiSquare

-- Moving a cotangent factor from the marked to the unmarked node branch changes the stratum.
example : columns 6 ≠ columns 9 := by
  exact fun h ↦ (by decide : (6 : Fin 17) ≠ 9) (columns_injective h)

-- An external cotangent factor is distinct from either node branch factor.
example : columns 5 ≠ columns 6 := by
  exact fun h ↦ (by decide : (5 : Fin 17) ≠ 6) (columns_injective h)

-- A cotangent decoration breaks the branch-exchange symmetry of a loop.
example : (graph 11).automorphismCount = 1 ∧ (graph 12).automorphismCount = 2 := by
  simp only [graph, decorate, DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

-- The two-loop raw pushforward has all eight automorphisms; its coefficient is not divided again.
example : (graph 16).automorphismCount = 8 ∧ boundary 16 = 1 / 56160 := by
  simp only [graph, decorate, DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

-- Kappa_1 squared and the corresponding pushforward basis vector differ by kappa_2.
example : toMonomial (Pi.single 1 1) = Pi.single 1 1 + Pi.single 0 1 := by
  rw [toMonomial, Fintype.linearCombination_apply_single, one_smul]
  rfl

-- Eliminating the kappa contribution is not the identity conversion.
example : pushforwardRows 0 ≠ rows 0 := by decide +kernel

-- The retained boundary combination has an essential negative coefficient.
example : boundary 9 = -328 / 1989 := by decide +kernel

-- Its support is exactly the ten lower-genus boundary columns.
example : (Finset.univ.filter fun i ↦ boundary i ≠ 0) =
    ({5, 6, 7, 9, 11, 12, 13, 14, 15, 16} : Finset (Fin 17)) := by decide +kernel

-- The certificate consumes the actual incoming JSON data, bound to the held frame.
example : GenusTwoPsiSquare.AcceptsExchange GenusTwoPsiSquareReplay.exchange :=
  GenusTwoPsiSquareReplay.accepted

-- The last row is obtained by a graph operation, not supplied as a final numerical recursion.
example : interpret columns (rows 6) =
    glueElliptic (interpret GenusOnePsi.columns (GenusOnePsi.rows 0)) := elliptic_row_gluing

attribute [local instance] strataRealizationModule

-- A downstream geometric consumer needs only original generators and primitive compatibility.
example {R : Type} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (E : StrataRealization C 1 (Fin 1)) (L : StrataRealization C 1 (Option (Fin 0)))
    (B : StrataRealization C 1 (Option (Fin 1)))
    (U : StrataRealization C 2 (Fin 0 ⊕ Fin 1)) (A : StrataRealization C 2 (Fin 1))
    (F : SeparatingPushforward C I) (P : PsiClasses C)
    (hEL : E.RelabelCompatible L GenusOnePsi.stableArity ellipticSourceStable (finSuccEquiv 0))
    (hLB : L.SeparatingCompatible B U F ellipticSourceStable ellipticMarkedStable)
    (hUA : U.RelabelCompatible A separatingStable stableArity (Equiv.emptySum (Fin 0) (Fin 1)))
    (hA : A.LegPsiCompatible P stableArity)
    (hfund : A.map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) stableArity)) = 1)
    (hrows : ∀ i : Fin 6, A.map (interpret columns (rows i.castSucc)) = 0)
    (hsource : E.map (interpret GenusOnePsi.columns (GenusOnePsi.rows 0)) = 0) :
    P.psi 2 (Fin 1) stableArity 0 ^ 2 = A.map (interpret columns boundary) :=
  realized_psi_square_from_generators GenusTwoPsiSquareReplay.exchange
    GenusTwoPsiSquareReplay.accepted E L B U A F P hEL hLB hUA hA hfund hrows hsource

-- Arbitrary higher powers use the checked square relation and the existing psi operation.
example {R : Type} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R}
    (A : StrataRealization C 2 (Fin 1)) (P : PsiClasses C)
    (hA : A.LegPsiCompatible P stableArity)
    (hfund : A.map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) stableArity)) = 1)
    (hrows : ∀ i, A.map (interpret columns (rows i)) = 0) (k : ℕ) :
    P.psi 2 (Fin 1) stableArity 0 ^ (2 + k) =
      A.map (StrataModule.mulLegPsi (Pi.single 0 k) (interpret columns boundary)) :=
  realized_psi_power GenusTwoPsiSquareReplay.exchange.presentation
    GenusTwoPsiSquareReplay.accepted.1 A P hA hfund hrows k

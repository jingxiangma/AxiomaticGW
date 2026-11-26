/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GetzlerGraphs
public import AxiomaticGW.Tautological.GluingExpression

/-!
# Constructing Getzler's raw graphs by elementary gluings

Each of the seven representatives is built from its stable component curves.
The loop terms use a self-gluing before a separating gluing. The parallel-edge
term first joins two rational components and then glues their remaining node
flags. Kernel graph isomorphism checks bind these expressions to the existing
fixed Getzler columns, with every external marking retained.
-/

@[expose] public section

namespace AxiomaticGW.GetzlerGraphs

open GluingExpression

/-- Join selected component flags, then enumerate the surviving left labels
before the surviving right labels, preserving their relative orders. -/
def join {g₁ g₂ m n : ℕ} (i : Fin (m + 1)) (j : Fin (n + 1))
    (x : GluingExpression g₁ (Fin (m + 1)))
    (y : GluingExpression g₂ (Fin (n + 1))) :
    GluingExpression (g₁ + g₂) (Fin (m + n)) :=
  ((x.relabel (finSuccEquiv' i)).separating
    (y.relabel (finSuccEquiv' j))).relabel finSumFinEquiv

/-- Close the first two flags into an ordered node; external labels keep
their relative order. Automorphism division is deliberately absent. -/
def close {g n : ℕ} (x : GluingExpression g (Fin (n + 2))) :
    GluingExpression (g + 1) (Fin n) :=
  (x.relabel ((finSuccEquiv (n + 1)).trans
    (Equiv.optionCongr (finSuccEquiv n)))).nonseparating

/-- Relabel the elliptic/single/pair ordering as the fixed delta23 markings. -/
def delta23Labels : Equiv.Perm (Fin 4) where
  toFun := ![3, 2, 0, 1]
  invFun := ![2, 3, 1, 0]
  left_inv := by decide
  right_inv := by decide

/-- The two tail markings precede the two middle-component markings. -/
def delta24Labels : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv := by decide
  right_inv := by decide

/-- Two rational three-point tails attached to a two-point elliptic component. -/
def delta22Expression : GluingExpression 1 (Fin 4) :=
  join (m := 2) (n := 2) 0 0
    (join (m := 1) (n := 2) 0 0 (.fundamental 1 (Fin 2) (by norm_num [StableArity]))
      (.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (.fundamental 0 (Fin 3) (by norm_num [StableArity]))

/-- The chain with a marked elliptic component and a marked rational middle component. -/
def delta23Expression : GluingExpression 1 (Fin 4) :=
  (join (m := 2) (n := 2) 2 0
    (join (m := 1) (n := 2) 0 0 (.fundamental 1 (Fin 2) (by norm_num [StableArity]))
      (.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (.fundamental 0 (Fin 3) (by norm_num [StableArity]))).relabel delta23Labels

/-- The chain with two markings on each rational component. -/
def delta24Expression : GluingExpression 1 (Fin 4) :=
  (join (m := 2) (n := 2) 2 0
    (join (m := 0) (n := 3) 0 0 (.fundamental 1 (Fin 1) (by norm_num [StableArity]))
      (.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (.fundamental 0 (Fin 3) (by norm_num [StableArity]))).relabel delta24Labels

/-- A triple-marked tail attached through a singly marked rational component. -/
def delta34Expression : GluingExpression 1 (Fin 4) :=
  join (m := 1) (n := 3) 1 0
    (join (m := 0) (n := 2) 0 0 (.fundamental 1 (Fin 1) (by norm_num [StableArity]))
      (.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (.fundamental 0 (Fin 4) (by norm_num [StableArity]))

/-- A singly marked loop component and a triple-marked rational tail. -/
def delta03Expression : GluingExpression 1 (Fin 4) :=
  join (m := 1) (n := 3) 0 0 (close (n := 2) (.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (.fundamental 0 (Fin 4) (by norm_num [StableArity]))

/-- An unmarked loop component and a rational tail carrying all four markings. -/
def delta04Expression : GluingExpression 1 (Fin 4) :=
  join (m := 0) (n := 4) 0 0 (close (n := 1) (.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (.fundamental 0 (Fin 5) (by norm_num [StableArity]))

/-- The second node joins the same two components as the first node.
The permutation moves the remaining right node flag next to the left one. -/
def deltaBetaExpression : GluingExpression 1 (Fin 4) :=
  close (n := 4) ((join (m := 3) (n := 3) 0 0 (.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (.fundamental 0 (Fin 4) (by norm_num [StableArity]))).relabel (Equiv.swap 1 3))

/-- The seven concrete raw gluing expressions. -/
def representativeExpression : GetzlerStratum → GluingExpression 1 (Fin 4)
  | .delta22 => delta22Expression
  | .delta23 => delta23Expression
  | .delta24 => delta24Expression
  | .delta34 => delta34Expression
  | .delta03 => delta03Expression
  | .delta04 => delta04Expression
  | .deltaBeta => deltaBetaExpression

/-- The composite graph is the original fixed representative, with all
markings fixed under graph isomorphism. -/
theorem representativeExpression_stratum (x : GetzlerStratum) :
    (representativeExpression x).stratum = columns (representative x) := by
  apply Quotient.sound
  apply (DecoratedStableGraph.isomorphic?_eq_true_iff _ _).mp
  cases x <;> decide


/-- A fixed bijection carrying each representative to its labelled column.
The inverse tables are kernel-checked; no marking orbit is averaged. -/
def markingPermutation (i : Fin 33) : Equiv.Perm (Fin 4) where
  toFun := ![![0, 1, 2, 3],
    ![0, 2, 1, 3],
    ![0, 3, 1, 2],
    ![0, 1, 2, 3],
    ![0, 1, 3, 2],
    ![0, 2, 1, 3],
    ![0, 2, 3, 1],
    ![0, 3, 1, 2],
    ![0, 3, 2, 1],
    ![1, 2, 0, 3],
    ![1, 2, 3, 0],
    ![1, 3, 0, 2],
    ![1, 3, 2, 0],
    ![2, 3, 0, 1],
    ![2, 3, 1, 0],
    ![0, 1, 2, 3],
    ![0, 2, 1, 3],
    ![0, 3, 1, 2],
    ![1, 2, 0, 3],
    ![1, 3, 0, 2],
    ![2, 3, 0, 1],
    ![0, 1, 2, 3],
    ![1, 0, 2, 3],
    ![2, 0, 1, 3],
    ![3, 0, 1, 2],
    ![0, 1, 2, 3],
    ![1, 0, 2, 3],
    ![2, 0, 1, 3],
    ![3, 0, 1, 2],
    ![0, 1, 2, 3],
    ![0, 1, 2, 3],
    ![0, 2, 1, 3],
    ![0, 3, 1, 2]] i
  invFun := ![![0, 1, 2, 3],
    ![0, 2, 1, 3],
    ![0, 2, 3, 1],
    ![0, 1, 2, 3],
    ![0, 1, 3, 2],
    ![0, 2, 1, 3],
    ![0, 3, 1, 2],
    ![0, 2, 3, 1],
    ![0, 3, 2, 1],
    ![2, 0, 1, 3],
    ![3, 0, 1, 2],
    ![2, 0, 3, 1],
    ![3, 0, 2, 1],
    ![2, 3, 0, 1],
    ![3, 2, 0, 1],
    ![0, 1, 2, 3],
    ![0, 2, 1, 3],
    ![0, 2, 3, 1],
    ![2, 0, 1, 3],
    ![2, 0, 3, 1],
    ![2, 3, 0, 1],
    ![0, 1, 2, 3],
    ![1, 0, 2, 3],
    ![1, 2, 0, 3],
    ![1, 2, 3, 0],
    ![0, 1, 2, 3],
    ![1, 0, 2, 3],
    ![1, 2, 0, 3],
    ![1, 2, 3, 0],
    ![0, 1, 2, 3],
    ![0, 1, 2, 3],
    ![0, 2, 1, 3],
    ![0, 2, 3, 1]] i
  left_inv := by fin_cases i <;> decide
  right_inv := by fin_cases i <;> decide

/-- Every one of the 33 raw columns has an explicit gluing construction. -/
def expression (i : Fin 33) : GluingExpression 1 (Fin 4) :=
  (representativeExpression (kind i)).relabel (markingPermutation i)

/-- The gluing construction agrees with the held certificate column,
including all external markings and both node branches. -/
theorem expression_stratum (i : Fin 33) : (expression i).stratum = columns i := by
  rw [expression, GluingExpression.stratum_relabel, representativeExpression_stratum]
  apply Quotient.sound
  apply (DecoratedStableGraph.isomorphic?_eq_true_iff _ _).mp
  fin_cases i <;> decide

end AxiomaticGW.GetzlerGraphs

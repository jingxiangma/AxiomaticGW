/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24Graphs
public import AxiomaticGW.Tautological.GetzlerGluing
public import AxiomaticGW.Tautological.CotangentCombination
public import AxiomaticGW.Tautological.GraphIsomorphismHint

/-!
# Actual decorated gluings for the full L24 frame

Every held column is built from stable components and the existing raw
separating and nonseparating operations. Component powers are attached
before nodes close. Explicit bijections check all incidences and powers
against the independently held frame; no relation coefficient changes.
-/

@[expose] public section

namespace AxiomaticGW.L24Gluing
open RelationCertificate GluingExpression GetzlerGraphs

set_option maxRecDepth 20000

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation0 : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation1 : Equiv.Perm (Fin 4) where
  toFun := ![1, 3, 0, 2]
  invFun := ![2, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation2 : Equiv.Perm (Fin 4) where
  toFun := ![1, 2, 0, 3]
  invFun := ![2, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation3 : Equiv.Perm (Fin 4) where
  toFun := ![1, 2, 3, 0]
  invFun := ![3, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation4 : Equiv.Perm (Fin 4) where
  toFun := ![0, 3, 1, 2]
  invFun := ![0, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation5 : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 1, 3]
  invFun := ![0, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation6 : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 3, 1]
  invFun := ![0, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation7 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 3, 2]
  invFun := ![0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation8 : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 1, 0]
  invFun := ![3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation9 : Equiv.Perm (Fin 4) where
  toFun := ![1, 3, 2, 0]
  invFun := ![3, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation10 : Equiv.Perm (Fin 4) where
  toFun := ![0, 3, 2, 1]
  invFun := ![0, 3, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation11 : Equiv.Perm (Fin 4) where
  toFun := ![2, 1, 3, 0]
  invFun := ![3, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation12 : Equiv.Perm (Fin 4) where
  toFun := ![3, 1, 2, 0]
  invFun := ![3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation13 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 3, 1]
  invFun := ![1, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation14 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 2, 1]
  invFun := ![1, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation15 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation16 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation17 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation18 : Equiv.Perm (Fin 4) where
  toFun := ![3, 2, 0, 1]
  invFun := ![2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation19 : Equiv.Perm (Fin 4) where
  toFun := ![3, 1, 0, 2]
  invFun := ![2, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation20 : Equiv.Perm (Fin 4) where
  toFun := ![2, 1, 0, 3]
  invFun := ![2, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation21 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 3, 2]
  invFun := ![1, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation22 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 5, 0, 1]
  invFun := ![4, 5, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation23 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 3, 4, 5, 1]
  invFun := ![1, 5, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation24 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 0, 4, 5, 1]
  invFun := ![2, 5, 0, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation25 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 0, 5, 1]
  invFun := ![3, 5, 0, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation26 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation27 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 0, 1, 4, 5]
  invFun := ![2, 3, 0, 1, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation28 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 0, 1, 5]
  invFun := ![3, 4, 0, 1, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Actual component-flag transport, before closing nodes or naming markings. -/
def flagPermutation29 : Equiv.Perm (Fin 8) where
  toFun := ![2, 3, 4, 5, 0, 1, 6, 7]
  invFun := ![4, 5, 0, 1, 2, 3, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression0 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 2 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression1 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 2 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression2 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 2 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression3 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression4 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 2 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression5 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 2 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression6 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression7 : GluingExpression 2 (Fin 4) :=
  (join (m := 2) (n := 2) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 2 (Fin 3) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression8 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression9 : GluingExpression 2 (Fin 4) :=
  (join (m := 3) (n := 1) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression10 : GluingExpression 2 (Fin 4) :=
  (join (m := 4) (n := 0) 4 0
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression11 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation8)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression12 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression13 : GluingExpression 2 (Fin 4) :=
  (join (m := 2) (n := 2) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity]))))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression14 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression15 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation9)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression16 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression17 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity])))).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression18 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression19 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression20 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression21 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity])))).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression22 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression23 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression24 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation10)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression25 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression26 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression27 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression28 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression29 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression30 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression31 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression32 : GluingExpression 2 (Fin 4) :=
  (join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression33 : GluingExpression 2 (Fin 4) :=
  (join (m := 4) (n := 0) 4 0
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression34 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression35 : GluingExpression 2 (Fin 4) :=
  (join (m := 4) (n := 0) 4 0
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression36 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation8)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression37 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression38 : GluingExpression 2 (Fin 4) :=
  (join (m := 4) (n := 0) 4 0
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression39 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation9)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression40 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression41 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression42 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression43 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression44 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression45 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation10)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression46 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression47 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression48 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression49 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression50 : GluingExpression 2 (Fin 4) :=
  (join (m := 4) (n := 0) 4 0
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression51 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])))).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression52 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression53 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression54 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation8)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression55 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])))).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression56 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression57 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation11)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression58 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation9)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression59 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])))).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression60 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression61 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation12)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression62 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression63 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression64 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression65 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])))).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression66 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression67 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation13)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression68 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation10)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression69 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])))).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression70 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression71 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation14)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression72 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression73 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression74 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression75 : GluingExpression 2 (Fin 4) :=
  (join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]))))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression76 : GluingExpression 2 (Fin 4) :=
  (join (m := 2) (n := 2) 2 2
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression77 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation15)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression78 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression79 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression80 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression81 : GluingExpression 2 (Fin 4) :=
  (join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression82 : GluingExpression 2 (Fin 4) :=
  (join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression83 : GluingExpression 2 (Fin 4) :=
  (join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 4 0
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression84 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]))).relabel flagPermutation15)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression85 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]))).relabel flagPermutation16)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression86 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression87 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]))).relabel flagPermutation17)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression88 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression89 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression90 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression91 : GluingExpression 2 (Fin 4) :=
  (join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression92 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression93 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression94 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression95 : GluingExpression 2 (Fin 4) :=
  (join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression96 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression97 : GluingExpression 2 (Fin 4) :=
  (join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression98 : GluingExpression 2 (Fin 4) :=
  (join (m := 4) (n := 0) 4 0
    (join (m := 0) (n := 5) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression99 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 1) (n := 2) 1 1
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation18)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression100 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 1) (n := 2) 1 1
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation19)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression101 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation12)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression102 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 1) (n := 2) 1 1
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation15)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression103 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation14)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression104 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation15)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression105 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 1) (n := 2) 1 1
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression106 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 1) (n := 2) 1 1
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation20)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression107 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation11)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression108 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 1) (n := 2) 1 1
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation16)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression109 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation13)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression110 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation8)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression111 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression112 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 1) (n := 2) 1 1
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression113 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 1) (n := 2) 1 1
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression114 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression115 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation9)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression116 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression117 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))).relabel flagPermutation8)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression118 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation8)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression119 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression120 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression121 : GluingExpression 2 (Fin 4) :=
  (join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression122 : GluingExpression 2 (Fin 4) :=
  (join (m := 2) (n := 2) 2 2
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression123 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 4 0
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression124 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))).relabel flagPermutation9)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression125 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation9)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression126 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression127 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression128 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )))).relabel
      flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression129 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression130 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 4 0
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression131 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression132 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression133 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression134 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression135 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )))).relabel
      flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression136 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression137 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 4 0
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression138 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 4 0
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression139 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation10)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression140 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation10)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression141 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression142 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression143 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 4 0
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression144 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression145 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression146 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression147 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression148 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 4 0
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression149 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 4 0
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression150 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression151 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression152 : GluingExpression 2 (Fin 4) :=
  (join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression153 : GluingExpression 2 (Fin 4) :=
  (join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression154 : GluingExpression 2 (Fin 4) :=
  (join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 4 0
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression155 : GluingExpression 2 (Fin 4) :=
  ((join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 4 0
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression156 : GluingExpression 2 (Fin 4) :=
  (join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 4 0
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression157 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression158 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression159 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation8)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression160 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression161 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression162 : GluingExpression 2 (Fin 4) :=
  (join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression163 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 0) (n := 5) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 4) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression164 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation8)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression165 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression166 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression167 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression168 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation11)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression169 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation9)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression170 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression171 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression172 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression173 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 0) (n := 5) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 4) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression174 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation9)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression175 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression176 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation11)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression177 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression178 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation12)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression179 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression180 : GluingExpression 2 (Fin 4) :=
  (join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression181 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression182 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression183 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 0) (n := 5) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 4) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression184 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression185 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression186 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation12)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression187 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression188 : GluingExpression 2 (Fin 4) :=
  (join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 3) (n := 1) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression189 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 0) (n := 5) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 3) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression190 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression191 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation13)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression192 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation10)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression193 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation21)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression194 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression195 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression196 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 0) (n := 5) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 4) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression197 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation10)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression198 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression199 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation13)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression200 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression201 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation14)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression202 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression203 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation17)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression204 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression205 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression206 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 0) (n := 5) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 4) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression207 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression208 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression209 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation14)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression210 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression211 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 3) (n := 1) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation17)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression212 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 0) (n := 5) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 3) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression213 : GluingExpression 2 (Fin 4) :=
  (join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression214 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation15)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression215 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression216 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation16)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression217 : GluingExpression 2 (Fin 4) :=
  (join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression218 : GluingExpression 2 (Fin 4) :=
  ((join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression219 : GluingExpression 2 (Fin 4) :=
  (join (m := 4) (n := 0) 4 0
    (join (m := 0) (n := 5) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 4) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression220 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression221 : GluingExpression 2 (Fin 4) :=
  (join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression222 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation15)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression223 : GluingExpression 2 (Fin 4) :=
  ((join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression224 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 3) (n := 1) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation16)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression225 : GluingExpression 2 (Fin 4) :=
  ((join (m := 4) (n := 0) 4 0
    (join (m := 0) (n := 5) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 3) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression226 : GluingExpression 2 (Fin 4) :=
  (join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression227 : GluingExpression 2 (Fin 4) :=
  ((join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 3) (n := 1) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation15)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression228 : GluingExpression 2 (Fin 4) :=
  (join (m := 4) (n := 0) 4 0
    (join (m := 0) (n := 5) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 3) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity])))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression229 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 5) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression230 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 5) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression231 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 5) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression232 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression233 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 5) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression234 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 5) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression235 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression236 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 5) (by norm_num [StableArity]) )).relabel
      flagPermutation22))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression237 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression238 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression239 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation22))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression240 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 1 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 5) (by norm_num [StableArity]) )).relabel
      flagPermutation23)).relabel flagPermutation15)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression241 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 1 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 5) (by norm_num [StableArity]) )).relabel
      flagPermutation23)).relabel flagPermutation16)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression242 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation24)).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression243 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 1 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 5) (by norm_num [StableArity]) )).relabel
      flagPermutation23)).relabel flagPermutation17)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression244 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation24)).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression245 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation24)).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression246 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation25)).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression247 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 2) (n := 4) 1 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 5) (by norm_num [StableArity]) )).relabel
      flagPermutation23))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression248 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation24)).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression249 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation24)).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression250 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation25)).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression251 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 3) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation24))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression252 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation25)).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression253 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 4) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation25))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression254 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 5) (n := 1) 4 0
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation22))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression255 : GluingExpression 2 (Fin 4) :=
  (close (join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 5) (by norm_num [StableArity]))))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression256 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation26)).relabel flagPermutation15)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression257 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation26)).relabel flagPermutation16)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression258 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression259 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation26)).relabel flagPermutation17)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression260 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression261 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression262 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 5) (n := 1) 5 1
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression263 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation26))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression264 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression265 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression266 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 5) (n := 1) 5 1
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression267 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression268 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 5) (n := 1) 5 1
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression269 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 5) (n := 1) 5 1
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression270 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 6) (n := 0) 6 0
    (GluingExpression.fundamental 0 (Fin 7) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]) )).relabel
      flagPermutation22))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression271 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation8)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression272 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression273 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation22))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression274 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression275 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 0 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation24)).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression276 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 1 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation8)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression277 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 1 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation8)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression278 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 1 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression279 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 1 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression280 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression281 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression282 : GluingExpression 2 (Fin 4) :=
  ((close (join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )))).relabel
      flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression283 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression284 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation26)).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression285 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 5) (n := 1) 5 1
    (join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)).relabel flagPermutation8)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression286 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation26)).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression287 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 5) (n := 1) 5 1
    (join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression288 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation27))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression289 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 6) (n := 0) 6 0
    (join (m := 2) (n := 5) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression290 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation9)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression291 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression292 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression293 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression294 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 0 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation24)).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression295 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 1 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation9)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression296 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 1 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation9)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression297 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 1 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression298 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 1 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression299 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression300 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression301 : GluingExpression 2 (Fin 4) :=
  ((close (join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )))).relabel
      flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression302 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression303 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation26)).relabel flagPermutation11)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression304 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 5) (n := 1) 5 1
    (join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)).relabel flagPermutation9)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression305 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation26)).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression306 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 5) (n := 1) 5 1
    (join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression307 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation27)).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression308 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 6) (n := 0) 6 0
    (join (m := 2) (n := 5) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression309 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression310 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression311 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression312 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression313 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 0 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation24)).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression314 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 1 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression315 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 1 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression316 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 1 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression317 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 1 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression318 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression319 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression320 : GluingExpression 2 (Fin 4) :=
  ((close (join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )))).relabel
      flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression321 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression322 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation26)).relabel flagPermutation12)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression323 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 5) (n := 1) 5 1
    (join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression324 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation26))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression325 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 5) (n := 1) 5 1
    (join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression326 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation27)).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression327 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 6) (n := 0) 6 0
    (join (m := 2) (n := 5) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression328 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression329 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 0 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression330 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 1 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression331 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 3) (n := 1) 1 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression332 : GluingExpression 2 (Fin 4) :=
  ((close (join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )))).relabel
      flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression333 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 5) (n := 1) 5 1
    (join (m := 3) (n := 3) 3 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression334 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 3) (n := 1) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation26))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression335 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 6) (n := 0) 6 0
    (join (m := 3) (n := 4) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression336 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation10)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression337 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression338 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression339 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 0 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation24)).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression340 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 1 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation10)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression341 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 1 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation10)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression342 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 1 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression343 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 1 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression344 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression345 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression346 : GluingExpression 2 (Fin 4) :=
  ((close (join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )))).relabel
      flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression347 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression348 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation26)).relabel flagPermutation13)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression349 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 5) (n := 1) 5 1
    (join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)).relabel flagPermutation10)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression350 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation26)).relabel flagPermutation21)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression351 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 5) (n := 1) 5 1
    (join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression352 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation27)).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression353 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 6) (n := 0) 6 0
    (join (m := 2) (n := 5) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression354 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression355 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression356 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression357 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 0 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation24)).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression358 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 1 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression359 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 1 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression360 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 1 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression361 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 1 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression362 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression363 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression364 : GluingExpression 2 (Fin 4) :=
  ((close (join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )))).relabel
      flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression365 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression366 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation26)).relabel flagPermutation14)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression367 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 5) (n := 1) 5 1
    (join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression368 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation26)).relabel flagPermutation17)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression369 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 5) (n := 1) 5 1
    (join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression370 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation27)).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression371 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 6) (n := 0) 6 0
    (join (m := 2) (n := 5) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression372 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression373 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 0 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression374 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 1 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression375 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 3) (n := 1) 1 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression376 : GluingExpression 2 (Fin 4) :=
  ((close (join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )))).relabel
      flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression377 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 5) (n := 1) 5 1
    (join (m := 3) (n := 3) 3 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression378 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 3) (n := 1) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation26)).relabel flagPermutation17)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression379 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 6) (n := 0) 6 0
    (join (m := 3) (n := 4) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression380 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression381 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 3) (n := 3) 3 3
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression382 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 4) (n := 2) 4 2
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation22))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression383 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 2) (n := 4) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 0 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation24))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression384 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 1 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression385 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 2) (n := 4) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 1 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression386 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 1 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation25))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression387 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 2) (n := 4) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 1 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation25))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression388 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation22))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression389 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 2) (n := 4) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation22))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression390 : GluingExpression 2 (Fin 4) :=
  (close (join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])))))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression391 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 4) (n := 2) 4 2
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression392 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation26)).relabel flagPermutation15)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression393 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 5) (n := 1) 5 1
    (join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression394 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation26)).relabel flagPermutation16)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression395 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 5) (n := 1) 5 1
    (join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression396 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation27)).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression397 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 6) (n := 0) 6 0
    (join (m := 2) (n := 5) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]) )).relabel
      flagPermutation22))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression398 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 4) (n := 2) 4 2
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression399 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 0 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression400 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 1 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression401 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 3) (n := 1) 1 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression402 : GluingExpression 2 (Fin 4) :=
  ((close (join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )))).relabel
      flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression403 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 5) (n := 1) 5 1
    (join (m := 3) (n := 3) 3 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression404 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 3) (n := 1) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation26)).relabel flagPermutation16)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression405 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 6) (n := 0) 6 0
    (join (m := 3) (n := 4) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]) )).relabel
      flagPermutation22)).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression406 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 4) (n := 2) 4 2
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation22))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression407 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 3) (n := 3) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 0 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation25))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression408 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 3) (n := 3) 3 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 1 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation22))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression409 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 3) (n := 3) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 3) (n := 1) 1 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation22))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression410 : GluingExpression 2 (Fin 4) :=
  (close (join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression411 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 5) (n := 1) 5 1
    (join (m := 3) (n := 3) 3 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression412 : GluingExpression 2 (Fin 4) :=
  ((close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 3) (n := 1) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation26)).relabel flagPermutation15)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression413 : GluingExpression 2 (Fin 4) :=
  (close ((join (m := 6) (n := 0) 6 0
    (join (m := 3) (n := 4) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]) )).relabel
      flagPermutation22))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression414 : GluingExpression 2 (Fin 4) :=
  ((close ((close ((join (m := 2) (n := 6) 2 6
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 7) (by norm_num [StableArity]) )).relabel
      flagPermutation29)).relabel flagPermutation22)).relabel flagPermutation0)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression415 : GluingExpression 2 (Fin 4) :=
  ((close ((close ((join (m := 2) (n := 6) 2 6
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 7) (by norm_num [StableArity]) )).relabel
      flagPermutation29)).relabel flagPermutation22)).relabel flagPermutation1)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression416 : GluingExpression 2 (Fin 4) :=
  ((close ((close ((join (m := 2) (n := 6) 2 6
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 7) (by norm_num [StableArity]) )).relabel
      flagPermutation29)).relabel flagPermutation22)).relabel flagPermutation2)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression417 : GluingExpression 2 (Fin 4) :=
  ((close ((close ((join (m := 3) (n := 5) 3 5
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity]) )).relabel
      flagPermutation29)).relabel flagPermutation22)).relabel flagPermutation3)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression418 : GluingExpression 2 (Fin 4) :=
  ((close ((close ((join (m := 2) (n := 6) 2 6
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 7) (by norm_num [StableArity]) )).relabel
      flagPermutation29)).relabel flagPermutation22)).relabel flagPermutation4)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression419 : GluingExpression 2 (Fin 4) :=
  ((close ((close ((join (m := 2) (n := 6) 2 6
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 7) (by norm_num [StableArity]) )).relabel
      flagPermutation29)).relabel flagPermutation22)).relabel flagPermutation5)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression420 : GluingExpression 2 (Fin 4) :=
  ((close ((close ((join (m := 3) (n := 5) 3 5
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity]) )).relabel
      flagPermutation29)).relabel flagPermutation22)).relabel flagPermutation6)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression421 : GluingExpression 2 (Fin 4) :=
  (close ((close ((join (m := 2) (n := 6) 2 6
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 7) (by norm_num [StableArity]) )).relabel
      flagPermutation29)).relabel flagPermutation22))

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression422 : GluingExpression 2 (Fin 4) :=
  ((close ((close ((join (m := 3) (n := 5) 3 5
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity]) )).relabel
      flagPermutation29)).relabel flagPermutation22)).relabel flagPermutation7)

/-- A shared raw gluing construction for the held four-marked frame. -/
def expression423 : GluingExpression 2 (Fin 4) :=
  (close ((close ((join (m := 3) (n := 5) 3 5
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity]) )).relabel
      flagPermutation29)).relabel flagPermutation22))

/-- Held column 0, with all original external and node cotangent powers. -/
def term0 : CotangentTerm 2 (Fin 4) :=
  ⟨expression0, (![0, 0, 0], ![1, 1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 1, with all original external and node cotangent powers. -/
def term1 : CotangentTerm 2 (Fin 4) :=
  ⟨expression0, (![0, 0, 0], ![1, 0, 1]), (inferInstance, inferInstance)⟩

/-- Held column 2, with all original external and node cotangent powers. -/
def term2 : CotangentTerm 2 (Fin 4) :=
  ⟨expression0, (![0, 0, 0], ![0, 2, 0]), (inferInstance, inferInstance)⟩

/-- Held column 3, with all original external and node cotangent powers. -/
def term3 : CotangentTerm 2 (Fin 4) :=
  ⟨expression0, (![0, 0, 0], ![0, 1, 1]), (inferInstance, inferInstance)⟩

/-- Held column 4, with all original external and node cotangent powers. -/
def term4 : CotangentTerm 2 (Fin 4) :=
  ⟨expression1, (![0, 0, 0], ![2, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 5, with all original external and node cotangent powers. -/
def term5 : CotangentTerm 2 (Fin 4) :=
  ⟨expression1, (![0, 0, 0], ![1, 1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 6, with all original external and node cotangent powers. -/
def term6 : CotangentTerm 2 (Fin 4) :=
  ⟨expression1, (![0, 0, 0], ![0, 2, 0]), (inferInstance, inferInstance)⟩

/-- Held column 7, with all original external and node cotangent powers. -/
def term7 : CotangentTerm 2 (Fin 4) :=
  ⟨expression2, (![0, 0, 0], ![2, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 8, with all original external and node cotangent powers. -/
def term8 : CotangentTerm 2 (Fin 4) :=
  ⟨expression2, (![0, 0, 0], ![1, 1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 9, with all original external and node cotangent powers. -/
def term9 : CotangentTerm 2 (Fin 4) :=
  ⟨expression2, (![0, 0, 0], ![0, 2, 0]), (inferInstance, inferInstance)⟩

/-- Held column 10, with all original external and node cotangent powers. -/
def term10 : CotangentTerm 2 (Fin 4) :=
  ⟨expression3, (![1, 0, 0, 0], ![1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 11, with all original external and node cotangent powers. -/
def term11 : CotangentTerm 2 (Fin 4) :=
  ⟨expression3, (![0, 1, 0, 0], ![0, 1]), (inferInstance, inferInstance)⟩

/-- Held column 12, with all original external and node cotangent powers. -/
def term12 : CotangentTerm 2 (Fin 4) :=
  ⟨expression3, (![0, 0, 1, 0], ![0, 1]), (inferInstance, inferInstance)⟩

/-- Held column 13, with all original external and node cotangent powers. -/
def term13 : CotangentTerm 2 (Fin 4) :=
  ⟨expression3, (![0, 0, 0, 0], ![2, 0]), (inferInstance, inferInstance)⟩

/-- Held column 14, with all original external and node cotangent powers. -/
def term14 : CotangentTerm 2 (Fin 4) :=
  ⟨expression3, (![0, 0, 0, 0], ![1, 1]), (inferInstance, inferInstance)⟩

/-- Held column 15, with all original external and node cotangent powers. -/
def term15 : CotangentTerm 2 (Fin 4) :=
  ⟨expression4, (![0, 0, 0], ![2, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 16, with all original external and node cotangent powers. -/
def term16 : CotangentTerm 2 (Fin 4) :=
  ⟨expression4, (![0, 0, 0], ![1, 1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 17, with all original external and node cotangent powers. -/
def term17 : CotangentTerm 2 (Fin 4) :=
  ⟨expression4, (![0, 0, 0], ![1, 0, 1]), (inferInstance, inferInstance)⟩

/-- Held column 18, with all original external and node cotangent powers. -/
def term18 : CotangentTerm 2 (Fin 4) :=
  ⟨expression4, (![0, 0, 0], ![0, 1, 1]), (inferInstance, inferInstance)⟩

/-- Held column 19, with all original external and node cotangent powers. -/
def term19 : CotangentTerm 2 (Fin 4) :=
  ⟨expression5, (![0, 0, 0], ![2, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 20, with all original external and node cotangent powers. -/
def term20 : CotangentTerm 2 (Fin 4) :=
  ⟨expression5, (![0, 0, 0], ![1, 1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 21, with all original external and node cotangent powers. -/
def term21 : CotangentTerm 2 (Fin 4) :=
  ⟨expression5, (![0, 0, 0], ![1, 0, 1]), (inferInstance, inferInstance)⟩

/-- Held column 22, with all original external and node cotangent powers. -/
def term22 : CotangentTerm 2 (Fin 4) :=
  ⟨expression5, (![0, 0, 0], ![0, 1, 1]), (inferInstance, inferInstance)⟩

/-- Held column 23, with all original external and node cotangent powers. -/
def term23 : CotangentTerm 2 (Fin 4) :=
  ⟨expression6, (![1, 0, 0, 0], ![1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 24, with all original external and node cotangent powers. -/
def term24 : CotangentTerm 2 (Fin 4) :=
  ⟨expression6, (![1, 0, 0, 0], ![0, 1]), (inferInstance, inferInstance)⟩

/-- Held column 25, with all original external and node cotangent powers. -/
def term25 : CotangentTerm 2 (Fin 4) :=
  ⟨expression6, (![0, 1, 0, 0], ![1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 26, with all original external and node cotangent powers. -/
def term26 : CotangentTerm 2 (Fin 4) :=
  ⟨expression6, (![0, 1, 0, 0], ![0, 1]), (inferInstance, inferInstance)⟩

/-- Held column 27, with all original external and node cotangent powers. -/
def term27 : CotangentTerm 2 (Fin 4) :=
  ⟨expression6, (![0, 0, 1, 0], ![1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 28, with all original external and node cotangent powers. -/
def term28 : CotangentTerm 2 (Fin 4) :=
  ⟨expression6, (![0, 0, 1, 0], ![0, 1]), (inferInstance, inferInstance)⟩

/-- Held column 29, with all original external and node cotangent powers. -/
def term29 : CotangentTerm 2 (Fin 4) :=
  ⟨expression6, (![0, 0, 0, 0], ![2, 0]), (inferInstance, inferInstance)⟩

/-- Held column 30, with all original external and node cotangent powers. -/
def term30 : CotangentTerm 2 (Fin 4) :=
  ⟨expression6, (![0, 0, 0, 0], ![1, 1]), (inferInstance, inferInstance)⟩

/-- Held column 31, with all original external and node cotangent powers. -/
def term31 : CotangentTerm 2 (Fin 4) :=
  ⟨expression7, (![0, 0, 0], ![2, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 32, with all original external and node cotangent powers. -/
def term32 : CotangentTerm 2 (Fin 4) :=
  ⟨expression7, (![0, 0, 0], ![1, 1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 33, with all original external and node cotangent powers. -/
def term33 : CotangentTerm 2 (Fin 4) :=
  ⟨expression7, (![0, 0, 0], ![0, 2, 0]), (inferInstance, inferInstance)⟩

/-- Held column 34, with all original external and node cotangent powers. -/
def term34 : CotangentTerm 2 (Fin 4) :=
  ⟨expression8, (![1, 0, 0, 0], ![0, 1]), (inferInstance, inferInstance)⟩

/-- Held column 35, with all original external and node cotangent powers. -/
def term35 : CotangentTerm 2 (Fin 4) :=
  ⟨expression8, (![0, 1, 0, 0], ![1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 36, with all original external and node cotangent powers. -/
def term36 : CotangentTerm 2 (Fin 4) :=
  ⟨expression8, (![0, 0, 1, 0], ![0, 1]), (inferInstance, inferInstance)⟩

/-- Held column 37, with all original external and node cotangent powers. -/
def term37 : CotangentTerm 2 (Fin 4) :=
  ⟨expression8, (![0, 0, 0, 0], ![2, 0]), (inferInstance, inferInstance)⟩

/-- Held column 38, with all original external and node cotangent powers. -/
def term38 : CotangentTerm 2 (Fin 4) :=
  ⟨expression8, (![0, 0, 0, 0], ![1, 1]), (inferInstance, inferInstance)⟩

/-- Held column 39, with all original external and node cotangent powers. -/
def term39 : CotangentTerm 2 (Fin 4) :=
  ⟨expression9, (![1, 0, 0, 0], ![0, 1]), (inferInstance, inferInstance)⟩

/-- Held column 40, with all original external and node cotangent powers. -/
def term40 : CotangentTerm 2 (Fin 4) :=
  ⟨expression9, (![0, 1, 0, 0], ![1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 41, with all original external and node cotangent powers. -/
def term41 : CotangentTerm 2 (Fin 4) :=
  ⟨expression9, (![0, 0, 1, 0], ![0, 1]), (inferInstance, inferInstance)⟩

/-- Held column 42, with all original external and node cotangent powers. -/
def term42 : CotangentTerm 2 (Fin 4) :=
  ⟨expression9, (![0, 0, 0, 0], ![2, 0]), (inferInstance, inferInstance)⟩

/-- Held column 43, with all original external and node cotangent powers. -/
def term43 : CotangentTerm 2 (Fin 4) :=
  ⟨expression9, (![0, 0, 0, 0], ![1, 1]), (inferInstance, inferInstance)⟩

/-- Held column 44, with all original external and node cotangent powers. -/
def term44 : CotangentTerm 2 (Fin 4) :=
  ⟨expression10, (![1, 0, 0, 0, 0], ![1]), (inferInstance, inferInstance)⟩

/-- Held column 45, with all original external and node cotangent powers. -/
def term45 : CotangentTerm 2 (Fin 4) :=
  ⟨expression10, (![0, 1, 0, 0, 0], ![1]), (inferInstance, inferInstance)⟩

/-- Held column 46, with all original external and node cotangent powers. -/
def term46 : CotangentTerm 2 (Fin 4) :=
  ⟨expression10, (![0, 0, 1, 0, 0], ![1]), (inferInstance, inferInstance)⟩

/-- Held column 47, with all original external and node cotangent powers. -/
def term47 : CotangentTerm 2 (Fin 4) :=
  ⟨expression10, (![0, 0, 0, 1, 0], ![1]), (inferInstance, inferInstance)⟩

/-- Held column 48, with all original external and node cotangent powers. -/
def term48 : CotangentTerm 2 (Fin 4) :=
  ⟨expression11, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 49, with all original external and node cotangent powers. -/
def term49 : CotangentTerm 2 (Fin 4) :=
  ⟨expression11, ((![0, 0, 0], ![0, 0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 50, with all original external and node cotangent powers. -/
def term50 : CotangentTerm 2 (Fin 4) :=
  ⟨expression12, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 51, with all original external and node cotangent powers. -/
def term51 : CotangentTerm 2 (Fin 4) :=
  ⟨expression12, ((![0, 0, 0], ![0, 0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 52, with all original external and node cotangent powers. -/
def term52 : CotangentTerm 2 (Fin 4) :=
  ⟨expression13, (![0, 0, 0], (![0, 0, 0], ![1, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 53, with all original external and node cotangent powers. -/
def term53 : CotangentTerm 2 (Fin 4) :=
  ⟨expression13, (![0, 0, 0], (![0, 0, 0], ![0, 1])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 54, with all original external and node cotangent powers. -/
def term54 : CotangentTerm 2 (Fin 4) :=
  ⟨expression14, ((![0, 0, 0], ![1, 0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 55, with all original external and node cotangent powers. -/
def term55 : CotangentTerm 2 (Fin 4) :=
  ⟨expression14, ((![0, 0, 0], ![0, 1, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 56, with all original external and node cotangent powers. -/
def term56 : CotangentTerm 2 (Fin 4) :=
  ⟨expression14, ((![0, 0, 0], ![0, 0, 0, 0]), ![1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 57, with all original external and node cotangent powers. -/
def term57 : CotangentTerm 2 (Fin 4) :=
  ⟨expression15, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 58, with all original external and node cotangent powers. -/
def term58 : CotangentTerm 2 (Fin 4) :=
  ⟨expression15, ((![0, 0, 0], ![0, 0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 59, with all original external and node cotangent powers. -/
def term59 : CotangentTerm 2 (Fin 4) :=
  ⟨expression16, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 60, with all original external and node cotangent powers. -/
def term60 : CotangentTerm 2 (Fin 4) :=
  ⟨expression16, ((![0, 0, 0], ![0, 0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 61, with all original external and node cotangent powers. -/
def term61 : CotangentTerm 2 (Fin 4) :=
  ⟨expression17, (![0, 0, 0], (![0, 0, 0], ![1, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 62, with all original external and node cotangent powers. -/
def term62 : CotangentTerm 2 (Fin 4) :=
  ⟨expression17, (![0, 0, 0], (![0, 0, 0], ![0, 1])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 63, with all original external and node cotangent powers. -/
def term63 : CotangentTerm 2 (Fin 4) :=
  ⟨expression18, ((![0, 0, 0], ![0, 0, 0, 0]), ![1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 64, with all original external and node cotangent powers. -/
def term64 : CotangentTerm 2 (Fin 4) :=
  ⟨expression19, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 65, with all original external and node cotangent powers. -/
def term65 : CotangentTerm 2 (Fin 4) :=
  ⟨expression19, ((![0, 0, 0], ![0, 0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 66, with all original external and node cotangent powers. -/
def term66 : CotangentTerm 2 (Fin 4) :=
  ⟨expression20, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 67, with all original external and node cotangent powers. -/
def term67 : CotangentTerm 2 (Fin 4) :=
  ⟨expression20, ((![0, 0, 0], ![0, 0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 68, with all original external and node cotangent powers. -/
def term68 : CotangentTerm 2 (Fin 4) :=
  ⟨expression21, (![0, 0, 0], (![0, 0, 0], ![1, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 69, with all original external and node cotangent powers. -/
def term69 : CotangentTerm 2 (Fin 4) :=
  ⟨expression21, (![0, 0, 0], (![0, 0, 0], ![0, 1])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 70, with all original external and node cotangent powers. -/
def term70 : CotangentTerm 2 (Fin 4) :=
  ⟨expression22, ((![0, 0, 0], ![0, 0, 0, 0]), ![1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 71, with all original external and node cotangent powers. -/
def term71 : CotangentTerm 2 (Fin 4) :=
  ⟨expression23, ((![1, 0, 0, 0], ![0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 72, with all original external and node cotangent powers. -/
def term72 : CotangentTerm 2 (Fin 4) :=
  ⟨expression23, ((![0, 1, 0, 0], ![0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 73, with all original external and node cotangent powers. -/
def term73 : CotangentTerm 2 (Fin 4) :=
  ⟨expression23, ((![0, 0, 1, 0], ![0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 74, with all original external and node cotangent powers. -/
def term74 : CotangentTerm 2 (Fin 4) :=
  ⟨expression23, ((![0, 0, 0, 0], ![0, 0, 0]), ![1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 75, with all original external and node cotangent powers. -/
def term75 : CotangentTerm 2 (Fin 4) :=
  ⟨expression24, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 76, with all original external and node cotangent powers. -/
def term76 : CotangentTerm 2 (Fin 4) :=
  ⟨expression24, ((![0, 0, 0], ![0, 0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 77, with all original external and node cotangent powers. -/
def term77 : CotangentTerm 2 (Fin 4) :=
  ⟨expression25, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 78, with all original external and node cotangent powers. -/
def term78 : CotangentTerm 2 (Fin 4) :=
  ⟨expression25, ((![0, 0, 0], ![0, 0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 79, with all original external and node cotangent powers. -/
def term79 : CotangentTerm 2 (Fin 4) :=
  ⟨expression26, ((![0, 0, 0], ![1, 0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 80, with all original external and node cotangent powers. -/
def term80 : CotangentTerm 2 (Fin 4) :=
  ⟨expression26, ((![0, 0, 0], ![0, 1, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 81, with all original external and node cotangent powers. -/
def term81 : CotangentTerm 2 (Fin 4) :=
  ⟨expression26, ((![0, 0, 0], ![0, 0, 0, 0]), ![1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 82, with all original external and node cotangent powers. -/
def term82 : CotangentTerm 2 (Fin 4) :=
  ⟨expression27, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 83, with all original external and node cotangent powers. -/
def term83 : CotangentTerm 2 (Fin 4) :=
  ⟨expression27, ((![0, 0, 0], ![0, 0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 84, with all original external and node cotangent powers. -/
def term84 : CotangentTerm 2 (Fin 4) :=
  ⟨expression28, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 85, with all original external and node cotangent powers. -/
def term85 : CotangentTerm 2 (Fin 4) :=
  ⟨expression28, ((![0, 0, 0], ![0, 0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 86, with all original external and node cotangent powers. -/
def term86 : CotangentTerm 2 (Fin 4) :=
  ⟨expression29, ((![0, 0, 0], ![1, 0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 87, with all original external and node cotangent powers. -/
def term87 : CotangentTerm 2 (Fin 4) :=
  ⟨expression29, ((![0, 0, 0], ![0, 1, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 88, with all original external and node cotangent powers. -/
def term88 : CotangentTerm 2 (Fin 4) :=
  ⟨expression29, ((![0, 0, 0], ![0, 0, 0, 0]), ![1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 89, with all original external and node cotangent powers. -/
def term89 : CotangentTerm 2 (Fin 4) :=
  ⟨expression30, ((![1, 0, 0, 0], ![0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 90, with all original external and node cotangent powers. -/
def term90 : CotangentTerm 2 (Fin 4) :=
  ⟨expression30, ((![0, 1, 0, 0], ![0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 91, with all original external and node cotangent powers. -/
def term91 : CotangentTerm 2 (Fin 4) :=
  ⟨expression30, ((![0, 0, 1, 0], ![0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 92, with all original external and node cotangent powers. -/
def term92 : CotangentTerm 2 (Fin 4) :=
  ⟨expression30, ((![0, 0, 0, 0], ![0, 0, 0]), ![1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 93, with all original external and node cotangent powers. -/
def term93 : CotangentTerm 2 (Fin 4) :=
  ⟨expression31, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 94, with all original external and node cotangent powers. -/
def term94 : CotangentTerm 2 (Fin 4) :=
  ⟨expression31, ((![0, 0, 0], ![0, 0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 95, with all original external and node cotangent powers. -/
def term95 : CotangentTerm 2 (Fin 4) :=
  ⟨expression32, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 96, with all original external and node cotangent powers. -/
def term96 : CotangentTerm 2 (Fin 4) :=
  ⟨expression32, ((![0, 0, 0], ![0, 0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 97, with all original external and node cotangent powers. -/
def term97 : CotangentTerm 2 (Fin 4) :=
  ⟨expression33, ((![0, 0, 0], ![0, 0, 0, 0]), ![1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 98, with all original external and node cotangent powers. -/
def term98 : CotangentTerm 2 (Fin 4) :=
  ⟨expression34, ((![1, 0, 0, 0], ![0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 99, with all original external and node cotangent powers. -/
def term99 : CotangentTerm 2 (Fin 4) :=
  ⟨expression34, ((![0, 1, 0, 0], ![0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 100, with all original external and node cotangent powers. -/
def term100 : CotangentTerm 2 (Fin 4) :=
  ⟨expression34, ((![0, 0, 1, 0], ![0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 101, with all original external and node cotangent powers. -/
def term101 : CotangentTerm 2 (Fin 4) :=
  ⟨expression34, ((![0, 0, 0, 0], ![0, 0, 0]), ![1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 102, with all original external and node cotangent powers. -/
def term102 : CotangentTerm 2 (Fin 4) :=
  ⟨expression35, ((![1, 0, 0, 0], ![0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 103, with all original external and node cotangent powers. -/
def term103 : CotangentTerm 2 (Fin 4) :=
  ⟨expression35, ((![0, 1, 0, 0], ![0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 104, with all original external and node cotangent powers. -/
def term104 : CotangentTerm 2 (Fin 4) :=
  ⟨expression35, ((![0, 0, 1, 0], ![0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 105, with all original external and node cotangent powers. -/
def term105 : CotangentTerm 2 (Fin 4) :=
  ⟨expression35, ((![0, 0, 0, 0], ![0, 0, 0]), ![1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 106, with all original external and node cotangent powers. -/
def term106 : CotangentTerm 2 (Fin 4) :=
  ⟨expression36, (((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0]), ![0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 107, with all original external and node cotangent powers. -/
def term107 : CotangentTerm 2 (Fin 4) :=
  ⟨expression37, (((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0]), ![0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 108, with all original external and node cotangent powers. -/
def term108 : CotangentTerm 2 (Fin 4) :=
  ⟨expression38, ((![0, 0, 0], (![0, 0, 0], ![0, 0, 0])), ![0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 109, with all original external and node cotangent powers. -/
def term109 : CotangentTerm 2 (Fin 4) :=
  ⟨expression39, (((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0]), ![0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 110, with all original external and node cotangent powers. -/
def term110 : CotangentTerm 2 (Fin 4) :=
  ⟨expression40, (((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0]), ![0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 111, with all original external and node cotangent powers. -/
def term111 : CotangentTerm 2 (Fin 4) :=
  ⟨expression41, ((![0, 0, 0], (![0, 0, 0], ![0, 0, 0])), ![0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 112, with all original external and node cotangent powers. -/
def term112 : CotangentTerm 2 (Fin 4) :=
  ⟨expression42, (((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0]), ![0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 113, with all original external and node cotangent powers. -/
def term113 : CotangentTerm 2 (Fin 4) :=
  ⟨expression43, (((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0]), ![0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 114, with all original external and node cotangent powers. -/
def term114 : CotangentTerm 2 (Fin 4) :=
  ⟨expression44, ((![0, 0, 0], (![0, 0, 0], ![0, 0, 0])), ![0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 115, with all original external and node cotangent powers. -/
def term115 : CotangentTerm 2 (Fin 4) :=
  ⟨expression45, (((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0]), ![0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 116, with all original external and node cotangent powers. -/
def term116 : CotangentTerm 2 (Fin 4) :=
  ⟨expression46, (((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0]), ![0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 117, with all original external and node cotangent powers. -/
def term117 : CotangentTerm 2 (Fin 4) :=
  ⟨expression47, (((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0]), ![0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 118, with all original external and node cotangent powers. -/
def term118 : CotangentTerm 2 (Fin 4) :=
  ⟨expression48, (((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0]), ![0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 119, with all original external and node cotangent powers. -/
def term119 : CotangentTerm 2 (Fin 4) :=
  ⟨expression49, (((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0]), ![0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 120, with all original external and node cotangent powers. -/
def term120 : CotangentTerm 2 (Fin 4) :=
  ⟨expression50, (((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0]), ![0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 121, with all original external and node cotangent powers. -/
def term121 : CotangentTerm 2 (Fin 4) :=
  ⟨expression51, (![0], (![0, 0, 0], ![1, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 122, with all original external and node cotangent powers. -/
def term122 : CotangentTerm 2 (Fin 4) :=
  ⟨expression51, (![0], (![0, 0, 0], ![0, 1, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 123, with all original external and node cotangent powers. -/
def term123 : CotangentTerm 2 (Fin 4) :=
  ⟨expression51, (![0], (![0, 0, 0], ![0, 0, 1, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 124, with all original external and node cotangent powers. -/
def term124 : CotangentTerm 2 (Fin 4) :=
  ⟨expression51, (![0], (![0, 0, 0], ![0, 0, 0, 1])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 125, with all original external and node cotangent powers. -/
def term125 : CotangentTerm 2 (Fin 4) :=
  ⟨expression52, ((![0, 0, 0], ![1, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 126, with all original external and node cotangent powers. -/
def term126 : CotangentTerm 2 (Fin 4) :=
  ⟨expression52, ((![0, 0, 0], ![0, 1]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 127, with all original external and node cotangent powers. -/
def term127 : CotangentTerm 2 (Fin 4) :=
  ⟨expression52, ((![0, 0, 0], ![0, 0]), ![1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 128, with all original external and node cotangent powers. -/
def term128 : CotangentTerm 2 (Fin 4) :=
  ⟨expression52, ((![0, 0, 0], ![0, 0]), ![0, 1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 129, with all original external and node cotangent powers. -/
def term129 : CotangentTerm 2 (Fin 4) :=
  ⟨expression52, ((![0, 0, 0], ![0, 0]), ![0, 0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 130, with all original external and node cotangent powers. -/
def term130 : CotangentTerm 2 (Fin 4) :=
  ⟨expression53, (![1, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 131, with all original external and node cotangent powers. -/
def term131 : CotangentTerm 2 (Fin 4) :=
  ⟨expression53, (![0, 1], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 132, with all original external and node cotangent powers. -/
def term132 : CotangentTerm 2 (Fin 4) :=
  ⟨expression53, (![0, 0], (![0, 0, 0], ![1, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 133, with all original external and node cotangent powers. -/
def term133 : CotangentTerm 2 (Fin 4) :=
  ⟨expression53, (![0, 0], (![0, 0, 0], ![0, 1, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 134, with all original external and node cotangent powers. -/
def term134 : CotangentTerm 2 (Fin 4) :=
  ⟨expression53, (![0, 0], (![0, 0, 0], ![0, 0, 1])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 135, with all original external and node cotangent powers. -/
def term135 : CotangentTerm 2 (Fin 4) :=
  ⟨expression54, ((![0, 0, 0], ![1, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 136, with all original external and node cotangent powers. -/
def term136 : CotangentTerm 2 (Fin 4) :=
  ⟨expression54, ((![0, 0, 0], ![0, 1, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 137, with all original external and node cotangent powers. -/
def term137 : CotangentTerm 2 (Fin 4) :=
  ⟨expression54, ((![0, 0, 0], ![0, 0, 1]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 138, with all original external and node cotangent powers. -/
def term138 : CotangentTerm 2 (Fin 4) :=
  ⟨expression54, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 139, with all original external and node cotangent powers. -/
def term139 : CotangentTerm 2 (Fin 4) :=
  ⟨expression54, ((![0, 0, 0], ![0, 0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 140, with all original external and node cotangent powers. -/
def term140 : CotangentTerm 2 (Fin 4) :=
  ⟨expression55, (![0], (![0, 0, 0], ![1, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 141, with all original external and node cotangent powers. -/
def term141 : CotangentTerm 2 (Fin 4) :=
  ⟨expression55, (![0], (![0, 0, 0], ![0, 1, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 142, with all original external and node cotangent powers. -/
def term142 : CotangentTerm 2 (Fin 4) :=
  ⟨expression55, (![0], (![0, 0, 0], ![0, 0, 0, 1])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 143, with all original external and node cotangent powers. -/
def term143 : CotangentTerm 2 (Fin 4) :=
  ⟨expression56, ((![0, 0, 0], ![0, 1]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 144, with all original external and node cotangent powers. -/
def term144 : CotangentTerm 2 (Fin 4) :=
  ⟨expression56, ((![0, 0, 0], ![0, 0]), ![1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 145, with all original external and node cotangent powers. -/
def term145 : CotangentTerm 2 (Fin 4) :=
  ⟨expression56, ((![0, 0, 0], ![0, 0]), ![0, 1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 146, with all original external and node cotangent powers. -/
def term146 : CotangentTerm 2 (Fin 4) :=
  ⟨expression56, ((![0, 0, 0], ![0, 0]), ![0, 0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 147, with all original external and node cotangent powers. -/
def term147 : CotangentTerm 2 (Fin 4) :=
  ⟨expression57, (![1, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 148, with all original external and node cotangent powers. -/
def term148 : CotangentTerm 2 (Fin 4) :=
  ⟨expression57, (![0, 1], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 149, with all original external and node cotangent powers. -/
def term149 : CotangentTerm 2 (Fin 4) :=
  ⟨expression57, (![0, 0], (![0, 0, 0], ![1, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 150, with all original external and node cotangent powers. -/
def term150 : CotangentTerm 2 (Fin 4) :=
  ⟨expression57, (![0, 0], (![0, 0, 0], ![0, 0, 1])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 151, with all original external and node cotangent powers. -/
def term151 : CotangentTerm 2 (Fin 4) :=
  ⟨expression58, ((![0, 0, 0], ![1, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 152, with all original external and node cotangent powers. -/
def term152 : CotangentTerm 2 (Fin 4) :=
  ⟨expression58, ((![0, 0, 0], ![0, 0, 1]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 153, with all original external and node cotangent powers. -/
def term153 : CotangentTerm 2 (Fin 4) :=
  ⟨expression58, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 154, with all original external and node cotangent powers. -/
def term154 : CotangentTerm 2 (Fin 4) :=
  ⟨expression58, ((![0, 0, 0], ![0, 0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 155, with all original external and node cotangent powers. -/
def term155 : CotangentTerm 2 (Fin 4) :=
  ⟨expression59, (![0], (![0, 0, 0], ![1, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 156, with all original external and node cotangent powers. -/
def term156 : CotangentTerm 2 (Fin 4) :=
  ⟨expression59, (![0], (![0, 0, 0], ![0, 1, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 157, with all original external and node cotangent powers. -/
def term157 : CotangentTerm 2 (Fin 4) :=
  ⟨expression59, (![0], (![0, 0, 0], ![0, 0, 0, 1])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 158, with all original external and node cotangent powers. -/
def term158 : CotangentTerm 2 (Fin 4) :=
  ⟨expression60, ((![0, 0, 0], ![0, 1]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 159, with all original external and node cotangent powers. -/
def term159 : CotangentTerm 2 (Fin 4) :=
  ⟨expression60, ((![0, 0, 0], ![0, 0]), ![1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 160, with all original external and node cotangent powers. -/
def term160 : CotangentTerm 2 (Fin 4) :=
  ⟨expression60, ((![0, 0, 0], ![0, 0]), ![0, 1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 161, with all original external and node cotangent powers. -/
def term161 : CotangentTerm 2 (Fin 4) :=
  ⟨expression60, ((![0, 0, 0], ![0, 0]), ![0, 0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 162, with all original external and node cotangent powers. -/
def term162 : CotangentTerm 2 (Fin 4) :=
  ⟨expression61, (![1, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 163, with all original external and node cotangent powers. -/
def term163 : CotangentTerm 2 (Fin 4) :=
  ⟨expression61, (![0, 1], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 164, with all original external and node cotangent powers. -/
def term164 : CotangentTerm 2 (Fin 4) :=
  ⟨expression61, (![0, 0], (![0, 0, 0], ![1, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 165, with all original external and node cotangent powers. -/
def term165 : CotangentTerm 2 (Fin 4) :=
  ⟨expression61, (![0, 0], (![0, 0, 0], ![0, 0, 1])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 166, with all original external and node cotangent powers. -/
def term166 : CotangentTerm 2 (Fin 4) :=
  ⟨expression62, ((![0, 0, 0], ![1, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 167, with all original external and node cotangent powers. -/
def term167 : CotangentTerm 2 (Fin 4) :=
  ⟨expression62, ((![0, 0, 0], ![0, 0, 1]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 168, with all original external and node cotangent powers. -/
def term168 : CotangentTerm 2 (Fin 4) :=
  ⟨expression62, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 169, with all original external and node cotangent powers. -/
def term169 : CotangentTerm 2 (Fin 4) :=
  ⟨expression62, ((![0, 0, 0], ![0, 0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 170, with all original external and node cotangent powers. -/
def term170 : CotangentTerm 2 (Fin 4) :=
  ⟨expression63, (![0], (![1, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 171, with all original external and node cotangent powers. -/
def term171 : CotangentTerm 2 (Fin 4) :=
  ⟨expression63, (![0], (![0, 1, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 172, with all original external and node cotangent powers. -/
def term172 : CotangentTerm 2 (Fin 4) :=
  ⟨expression63, (![0], (![0, 0, 1, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 173, with all original external and node cotangent powers. -/
def term173 : CotangentTerm 2 (Fin 4) :=
  ⟨expression63, (![0], (![0, 0, 0, 0], ![1, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 174, with all original external and node cotangent powers. -/
def term174 : CotangentTerm 2 (Fin 4) :=
  ⟨expression63, (![0], (![0, 0, 0, 0], ![0, 1, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 175, with all original external and node cotangent powers. -/
def term175 : CotangentTerm 2 (Fin 4) :=
  ⟨expression63, (![0], (![0, 0, 0, 0], ![0, 0, 1])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 176, with all original external and node cotangent powers. -/
def term176 : CotangentTerm 2 (Fin 4) :=
  ⟨expression64, ((![0, 1, 0, 0], ![0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 177, with all original external and node cotangent powers. -/
def term177 : CotangentTerm 2 (Fin 4) :=
  ⟨expression64, ((![0, 0, 1, 0], ![0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 178, with all original external and node cotangent powers. -/
def term178 : CotangentTerm 2 (Fin 4) :=
  ⟨expression64, ((![0, 0, 0, 0], ![1, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 179, with all original external and node cotangent powers. -/
def term179 : CotangentTerm 2 (Fin 4) :=
  ⟨expression64, ((![0, 0, 0, 0], ![0, 1]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 180, with all original external and node cotangent powers. -/
def term180 : CotangentTerm 2 (Fin 4) :=
  ⟨expression64, ((![0, 0, 0, 0], ![0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 181, with all original external and node cotangent powers. -/
def term181 : CotangentTerm 2 (Fin 4) :=
  ⟨expression64, ((![0, 0, 0, 0], ![0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 182, with all original external and node cotangent powers. -/
def term182 : CotangentTerm 2 (Fin 4) :=
  ⟨expression65, (![0], (![0, 0, 0], ![1, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 183, with all original external and node cotangent powers. -/
def term183 : CotangentTerm 2 (Fin 4) :=
  ⟨expression65, (![0], (![0, 0, 0], ![0, 1, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 184, with all original external and node cotangent powers. -/
def term184 : CotangentTerm 2 (Fin 4) :=
  ⟨expression65, (![0], (![0, 0, 0], ![0, 0, 1, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 185, with all original external and node cotangent powers. -/
def term185 : CotangentTerm 2 (Fin 4) :=
  ⟨expression65, (![0], (![0, 0, 0], ![0, 0, 0, 1])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 186, with all original external and node cotangent powers. -/
def term186 : CotangentTerm 2 (Fin 4) :=
  ⟨expression66, ((![0, 0, 0], ![1, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 187, with all original external and node cotangent powers. -/
def term187 : CotangentTerm 2 (Fin 4) :=
  ⟨expression66, ((![0, 0, 0], ![0, 1]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 188, with all original external and node cotangent powers. -/
def term188 : CotangentTerm 2 (Fin 4) :=
  ⟨expression66, ((![0, 0, 0], ![0, 0]), ![1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 189, with all original external and node cotangent powers. -/
def term189 : CotangentTerm 2 (Fin 4) :=
  ⟨expression66, ((![0, 0, 0], ![0, 0]), ![0, 1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 190, with all original external and node cotangent powers. -/
def term190 : CotangentTerm 2 (Fin 4) :=
  ⟨expression66, ((![0, 0, 0], ![0, 0]), ![0, 0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 191, with all original external and node cotangent powers. -/
def term191 : CotangentTerm 2 (Fin 4) :=
  ⟨expression67, (![1, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 192, with all original external and node cotangent powers. -/
def term192 : CotangentTerm 2 (Fin 4) :=
  ⟨expression67, (![0, 1], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 193, with all original external and node cotangent powers. -/
def term193 : CotangentTerm 2 (Fin 4) :=
  ⟨expression67, (![0, 0], (![0, 0, 0], ![1, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 194, with all original external and node cotangent powers. -/
def term194 : CotangentTerm 2 (Fin 4) :=
  ⟨expression67, (![0, 0], (![0, 0, 0], ![0, 1, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 195, with all original external and node cotangent powers. -/
def term195 : CotangentTerm 2 (Fin 4) :=
  ⟨expression67, (![0, 0], (![0, 0, 0], ![0, 0, 1])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 196, with all original external and node cotangent powers. -/
def term196 : CotangentTerm 2 (Fin 4) :=
  ⟨expression68, ((![0, 0, 0], ![1, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 197, with all original external and node cotangent powers. -/
def term197 : CotangentTerm 2 (Fin 4) :=
  ⟨expression68, ((![0, 0, 0], ![0, 1, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 198, with all original external and node cotangent powers. -/
def term198 : CotangentTerm 2 (Fin 4) :=
  ⟨expression68, ((![0, 0, 0], ![0, 0, 1]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 199, with all original external and node cotangent powers. -/
def term199 : CotangentTerm 2 (Fin 4) :=
  ⟨expression68, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 200, with all original external and node cotangent powers. -/
def term200 : CotangentTerm 2 (Fin 4) :=
  ⟨expression68, ((![0, 0, 0], ![0, 0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 201, with all original external and node cotangent powers. -/
def term201 : CotangentTerm 2 (Fin 4) :=
  ⟨expression69, (![0], (![0, 0, 0], ![1, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 202, with all original external and node cotangent powers. -/
def term202 : CotangentTerm 2 (Fin 4) :=
  ⟨expression69, (![0], (![0, 0, 0], ![0, 1, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 203, with all original external and node cotangent powers. -/
def term203 : CotangentTerm 2 (Fin 4) :=
  ⟨expression69, (![0], (![0, 0, 0], ![0, 0, 1, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 204, with all original external and node cotangent powers. -/
def term204 : CotangentTerm 2 (Fin 4) :=
  ⟨expression69, (![0], (![0, 0, 0], ![0, 0, 0, 1])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 205, with all original external and node cotangent powers. -/
def term205 : CotangentTerm 2 (Fin 4) :=
  ⟨expression70, ((![0, 0, 0], ![1, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 206, with all original external and node cotangent powers. -/
def term206 : CotangentTerm 2 (Fin 4) :=
  ⟨expression70, ((![0, 0, 0], ![0, 1]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 207, with all original external and node cotangent powers. -/
def term207 : CotangentTerm 2 (Fin 4) :=
  ⟨expression70, ((![0, 0, 0], ![0, 0]), ![1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 208, with all original external and node cotangent powers. -/
def term208 : CotangentTerm 2 (Fin 4) :=
  ⟨expression70, ((![0, 0, 0], ![0, 0]), ![0, 1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 209, with all original external and node cotangent powers. -/
def term209 : CotangentTerm 2 (Fin 4) :=
  ⟨expression70, ((![0, 0, 0], ![0, 0]), ![0, 0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 210, with all original external and node cotangent powers. -/
def term210 : CotangentTerm 2 (Fin 4) :=
  ⟨expression71, (![1, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 211, with all original external and node cotangent powers. -/
def term211 : CotangentTerm 2 (Fin 4) :=
  ⟨expression71, (![0, 1], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 212, with all original external and node cotangent powers. -/
def term212 : CotangentTerm 2 (Fin 4) :=
  ⟨expression71, (![0, 0], (![0, 0, 0], ![1, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 213, with all original external and node cotangent powers. -/
def term213 : CotangentTerm 2 (Fin 4) :=
  ⟨expression71, (![0, 0], (![0, 0, 0], ![0, 1, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 214, with all original external and node cotangent powers. -/
def term214 : CotangentTerm 2 (Fin 4) :=
  ⟨expression71, (![0, 0], (![0, 0, 0], ![0, 0, 1])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 215, with all original external and node cotangent powers. -/
def term215 : CotangentTerm 2 (Fin 4) :=
  ⟨expression72, ((![0, 0, 0], ![1, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 216, with all original external and node cotangent powers. -/
def term216 : CotangentTerm 2 (Fin 4) :=
  ⟨expression72, ((![0, 0, 0], ![0, 1, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 217, with all original external and node cotangent powers. -/
def term217 : CotangentTerm 2 (Fin 4) :=
  ⟨expression72, ((![0, 0, 0], ![0, 0, 1]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 218, with all original external and node cotangent powers. -/
def term218 : CotangentTerm 2 (Fin 4) :=
  ⟨expression72, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 219, with all original external and node cotangent powers. -/
def term219 : CotangentTerm 2 (Fin 4) :=
  ⟨expression72, ((![0, 0, 0], ![0, 0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 220, with all original external and node cotangent powers. -/
def term220 : CotangentTerm 2 (Fin 4) :=
  ⟨expression73, (![0], (![1, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 221, with all original external and node cotangent powers. -/
def term221 : CotangentTerm 2 (Fin 4) :=
  ⟨expression73, (![0], (![0, 1, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 222, with all original external and node cotangent powers. -/
def term222 : CotangentTerm 2 (Fin 4) :=
  ⟨expression73, (![0], (![0, 0, 1, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 223, with all original external and node cotangent powers. -/
def term223 : CotangentTerm 2 (Fin 4) :=
  ⟨expression73, (![0], (![0, 0, 0, 0], ![1, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 224, with all original external and node cotangent powers. -/
def term224 : CotangentTerm 2 (Fin 4) :=
  ⟨expression73, (![0], (![0, 0, 0, 0], ![0, 1, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 225, with all original external and node cotangent powers. -/
def term225 : CotangentTerm 2 (Fin 4) :=
  ⟨expression73, (![0], (![0, 0, 0, 0], ![0, 0, 1])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 226, with all original external and node cotangent powers. -/
def term226 : CotangentTerm 2 (Fin 4) :=
  ⟨expression74, ((![1, 0, 0, 0], ![0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 227, with all original external and node cotangent powers. -/
def term227 : CotangentTerm 2 (Fin 4) :=
  ⟨expression74, ((![0, 1, 0, 0], ![0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 228, with all original external and node cotangent powers. -/
def term228 : CotangentTerm 2 (Fin 4) :=
  ⟨expression74, ((![0, 0, 1, 0], ![0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 229, with all original external and node cotangent powers. -/
def term229 : CotangentTerm 2 (Fin 4) :=
  ⟨expression74, ((![0, 0, 0, 0], ![1, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 230, with all original external and node cotangent powers. -/
def term230 : CotangentTerm 2 (Fin 4) :=
  ⟨expression74, ((![0, 0, 0, 0], ![0, 1]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 231, with all original external and node cotangent powers. -/
def term231 : CotangentTerm 2 (Fin 4) :=
  ⟨expression74, ((![0, 0, 0, 0], ![0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 232, with all original external and node cotangent powers. -/
def term232 : CotangentTerm 2 (Fin 4) :=
  ⟨expression74, ((![0, 0, 0, 0], ![0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 233, with all original external and node cotangent powers. -/
def term233 : CotangentTerm 2 (Fin 4) :=
  ⟨expression75, (![0], (![0, 0, 0], ![1, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 234, with all original external and node cotangent powers. -/
def term234 : CotangentTerm 2 (Fin 4) :=
  ⟨expression75, (![0], (![0, 0, 0], ![0, 1, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 235, with all original external and node cotangent powers. -/
def term235 : CotangentTerm 2 (Fin 4) :=
  ⟨expression75, (![0], (![0, 0, 0], ![0, 0, 0, 1])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 236, with all original external and node cotangent powers. -/
def term236 : CotangentTerm 2 (Fin 4) :=
  ⟨expression76, ((![0, 0, 0], ![0, 1]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 237, with all original external and node cotangent powers. -/
def term237 : CotangentTerm 2 (Fin 4) :=
  ⟨expression76, ((![0, 0, 0], ![0, 0]), ![1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 238, with all original external and node cotangent powers. -/
def term238 : CotangentTerm 2 (Fin 4) :=
  ⟨expression76, ((![0, 0, 0], ![0, 0]), ![0, 1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 239, with all original external and node cotangent powers. -/
def term239 : CotangentTerm 2 (Fin 4) :=
  ⟨expression76, ((![0, 0, 0], ![0, 0]), ![0, 0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 240, with all original external and node cotangent powers. -/
def term240 : CotangentTerm 2 (Fin 4) :=
  ⟨expression77, (![1, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 241, with all original external and node cotangent powers. -/
def term241 : CotangentTerm 2 (Fin 4) :=
  ⟨expression77, (![0, 1], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 242, with all original external and node cotangent powers. -/
def term242 : CotangentTerm 2 (Fin 4) :=
  ⟨expression77, (![0, 0], (![0, 0, 0], ![1, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 243, with all original external and node cotangent powers. -/
def term243 : CotangentTerm 2 (Fin 4) :=
  ⟨expression77, (![0, 0], (![0, 0, 0], ![0, 0, 1])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 244, with all original external and node cotangent powers. -/
def term244 : CotangentTerm 2 (Fin 4) :=
  ⟨expression78, ((![0, 0, 0], ![1, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 245, with all original external and node cotangent powers. -/
def term245 : CotangentTerm 2 (Fin 4) :=
  ⟨expression78, ((![0, 0, 0], ![0, 0, 1]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 246, with all original external and node cotangent powers. -/
def term246 : CotangentTerm 2 (Fin 4) :=
  ⟨expression78, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 247, with all original external and node cotangent powers. -/
def term247 : CotangentTerm 2 (Fin 4) :=
  ⟨expression78, ((![0, 0, 0], ![0, 0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 248, with all original external and node cotangent powers. -/
def term248 : CotangentTerm 2 (Fin 4) :=
  ⟨expression79, (![0], (![1, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 249, with all original external and node cotangent powers. -/
def term249 : CotangentTerm 2 (Fin 4) :=
  ⟨expression79, (![0], (![0, 1, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 250, with all original external and node cotangent powers. -/
def term250 : CotangentTerm 2 (Fin 4) :=
  ⟨expression79, (![0], (![0, 0, 1, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 251, with all original external and node cotangent powers. -/
def term251 : CotangentTerm 2 (Fin 4) :=
  ⟨expression79, (![0], (![0, 0, 0, 0], ![1, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 252, with all original external and node cotangent powers. -/
def term252 : CotangentTerm 2 (Fin 4) :=
  ⟨expression79, (![0], (![0, 0, 0, 0], ![0, 1, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 253, with all original external and node cotangent powers. -/
def term253 : CotangentTerm 2 (Fin 4) :=
  ⟨expression79, (![0], (![0, 0, 0, 0], ![0, 0, 1])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 254, with all original external and node cotangent powers. -/
def term254 : CotangentTerm 2 (Fin 4) :=
  ⟨expression80, ((![1, 0, 0, 0], ![0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 255, with all original external and node cotangent powers. -/
def term255 : CotangentTerm 2 (Fin 4) :=
  ⟨expression80, ((![0, 0, 1, 0], ![0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 256, with all original external and node cotangent powers. -/
def term256 : CotangentTerm 2 (Fin 4) :=
  ⟨expression80, ((![0, 0, 0, 0], ![1, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 257, with all original external and node cotangent powers. -/
def term257 : CotangentTerm 2 (Fin 4) :=
  ⟨expression80, ((![0, 0, 0, 0], ![0, 1]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 258, with all original external and node cotangent powers. -/
def term258 : CotangentTerm 2 (Fin 4) :=
  ⟨expression80, ((![0, 0, 0, 0], ![0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 259, with all original external and node cotangent powers. -/
def term259 : CotangentTerm 2 (Fin 4) :=
  ⟨expression80, ((![0, 0, 0, 0], ![0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 260, with all original external and node cotangent powers. -/
def term260 : CotangentTerm 2 (Fin 4) :=
  ⟨expression81, (![0], (![1, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 261, with all original external and node cotangent powers. -/
def term261 : CotangentTerm 2 (Fin 4) :=
  ⟨expression81, (![0], (![0, 1, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 262, with all original external and node cotangent powers. -/
def term262 : CotangentTerm 2 (Fin 4) :=
  ⟨expression81, (![0], (![0, 0, 1, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 263, with all original external and node cotangent powers. -/
def term263 : CotangentTerm 2 (Fin 4) :=
  ⟨expression81, (![0], (![0, 0, 0, 0], ![1, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 264, with all original external and node cotangent powers. -/
def term264 : CotangentTerm 2 (Fin 4) :=
  ⟨expression81, (![0], (![0, 0, 0, 0], ![0, 1, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 265, with all original external and node cotangent powers. -/
def term265 : CotangentTerm 2 (Fin 4) :=
  ⟨expression81, (![0], (![0, 0, 0, 0], ![0, 0, 1])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 266, with all original external and node cotangent powers. -/
def term266 : CotangentTerm 2 (Fin 4) :=
  ⟨expression82, ((![1, 0, 0, 0], ![0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 267, with all original external and node cotangent powers. -/
def term267 : CotangentTerm 2 (Fin 4) :=
  ⟨expression82, ((![0, 0, 1, 0], ![0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 268, with all original external and node cotangent powers. -/
def term268 : CotangentTerm 2 (Fin 4) :=
  ⟨expression82, ((![0, 0, 0, 0], ![1, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 269, with all original external and node cotangent powers. -/
def term269 : CotangentTerm 2 (Fin 4) :=
  ⟨expression82, ((![0, 0, 0, 0], ![0, 1]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 270, with all original external and node cotangent powers. -/
def term270 : CotangentTerm 2 (Fin 4) :=
  ⟨expression82, ((![0, 0, 0, 0], ![0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 271, with all original external and node cotangent powers. -/
def term271 : CotangentTerm 2 (Fin 4) :=
  ⟨expression82, ((![0, 0, 0, 0], ![0, 0]), ![0, 1]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 272, with all original external and node cotangent powers. -/
def term272 : CotangentTerm 2 (Fin 4) :=
  ⟨expression83, (![0], (![1, 0, 0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 273, with all original external and node cotangent powers. -/
def term273 : CotangentTerm 2 (Fin 4) :=
  ⟨expression83, (![0], (![0, 1, 0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 274, with all original external and node cotangent powers. -/
def term274 : CotangentTerm 2 (Fin 4) :=
  ⟨expression83, (![0], (![0, 0, 1, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 275, with all original external and node cotangent powers. -/
def term275 : CotangentTerm 2 (Fin 4) :=
  ⟨expression83, (![0], (![0, 0, 0, 1, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 276, with all original external and node cotangent powers. -/
def term276 : CotangentTerm 2 (Fin 4) :=
  ⟨expression84, ((![0], ![0, 0, 0]), ![0, 1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 277, with all original external and node cotangent powers. -/
def term277 : CotangentTerm 2 (Fin 4) :=
  ⟨expression85, ((![0], ![0, 0, 0]), ![0, 1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 278, with all original external and node cotangent powers. -/
def term278 : CotangentTerm 2 (Fin 4) :=
  ⟨expression86, ((![0], ![1, 0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 279, with all original external and node cotangent powers. -/
def term279 : CotangentTerm 2 (Fin 4) :=
  ⟨expression86, ((![0], ![0, 1, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 280, with all original external and node cotangent powers. -/
def term280 : CotangentTerm 2 (Fin 4) :=
  ⟨expression86, ((![0], ![0, 0, 0, 0]), ![1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 281, with all original external and node cotangent powers. -/
def term281 : CotangentTerm 2 (Fin 4) :=
  ⟨expression86, ((![0], ![0, 0, 0, 0]), ![0, 1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 282, with all original external and node cotangent powers. -/
def term282 : CotangentTerm 2 (Fin 4) :=
  ⟨expression87, ((![0], ![0, 0, 0]), ![1, 0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 283, with all original external and node cotangent powers. -/
def term283 : CotangentTerm 2 (Fin 4) :=
  ⟨expression87, ((![0], ![0, 0, 0]), ![0, 1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 284, with all original external and node cotangent powers. -/
def term284 : CotangentTerm 2 (Fin 4) :=
  ⟨expression87, ((![0], ![0, 0, 0]), ![0, 0, 1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 285, with all original external and node cotangent powers. -/
def term285 : CotangentTerm 2 (Fin 4) :=
  ⟨expression88, ((![0], ![0, 1, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 286, with all original external and node cotangent powers. -/
def term286 : CotangentTerm 2 (Fin 4) :=
  ⟨expression88, ((![0], ![0, 0, 0, 0]), ![1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 287, with all original external and node cotangent powers. -/
def term287 : CotangentTerm 2 (Fin 4) :=
  ⟨expression88, ((![0], ![0, 0, 0, 0]), ![0, 1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 288, with all original external and node cotangent powers. -/
def term288 : CotangentTerm 2 (Fin 4) :=
  ⟨expression89, ((![0], ![0, 1, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 289, with all original external and node cotangent powers. -/
def term289 : CotangentTerm 2 (Fin 4) :=
  ⟨expression89, ((![0], ![0, 0, 0, 0]), ![1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 290, with all original external and node cotangent powers. -/
def term290 : CotangentTerm 2 (Fin 4) :=
  ⟨expression89, ((![0], ![0, 0, 0, 0]), ![0, 1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 291, with all original external and node cotangent powers. -/
def term291 : CotangentTerm 2 (Fin 4) :=
  ⟨expression90, ((![0], ![1, 0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 292, with all original external and node cotangent powers. -/
def term292 : CotangentTerm 2 (Fin 4) :=
  ⟨expression90, ((![0], ![0, 1, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 293, with all original external and node cotangent powers. -/
def term293 : CotangentTerm 2 (Fin 4) :=
  ⟨expression90, ((![0], ![0, 0, 1, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 294, with all original external and node cotangent powers. -/
def term294 : CotangentTerm 2 (Fin 4) :=
  ⟨expression90, ((![0], ![0, 0, 0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 295, with all original external and node cotangent powers. -/
def term295 : CotangentTerm 2 (Fin 4) :=
  ⟨expression91, ((![0], ![0, 0, 0]), ![1, 0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 296, with all original external and node cotangent powers. -/
def term296 : CotangentTerm 2 (Fin 4) :=
  ⟨expression92, ((![0], ![1, 0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 297, with all original external and node cotangent powers. -/
def term297 : CotangentTerm 2 (Fin 4) :=
  ⟨expression92, ((![0], ![0, 1, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 298, with all original external and node cotangent powers. -/
def term298 : CotangentTerm 2 (Fin 4) :=
  ⟨expression92, ((![0], ![0, 0, 0, 0]), ![1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 299, with all original external and node cotangent powers. -/
def term299 : CotangentTerm 2 (Fin 4) :=
  ⟨expression92, ((![0], ![0, 0, 0, 0]), ![0, 1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 300, with all original external and node cotangent powers. -/
def term300 : CotangentTerm 2 (Fin 4) :=
  ⟨expression93, ((![0], ![1, 0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 301, with all original external and node cotangent powers. -/
def term301 : CotangentTerm 2 (Fin 4) :=
  ⟨expression93, ((![0], ![0, 1, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 302, with all original external and node cotangent powers. -/
def term302 : CotangentTerm 2 (Fin 4) :=
  ⟨expression93, ((![0], ![0, 0, 0, 0]), ![1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 303, with all original external and node cotangent powers. -/
def term303 : CotangentTerm 2 (Fin 4) :=
  ⟨expression93, ((![0], ![0, 0, 0, 0]), ![0, 1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 304, with all original external and node cotangent powers. -/
def term304 : CotangentTerm 2 (Fin 4) :=
  ⟨expression94, ((![0], ![1, 0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 305, with all original external and node cotangent powers. -/
def term305 : CotangentTerm 2 (Fin 4) :=
  ⟨expression94, ((![0], ![0, 1, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 306, with all original external and node cotangent powers. -/
def term306 : CotangentTerm 2 (Fin 4) :=
  ⟨expression94, ((![0], ![0, 0, 1, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 307, with all original external and node cotangent powers. -/
def term307 : CotangentTerm 2 (Fin 4) :=
  ⟨expression94, ((![0], ![0, 0, 0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 308, with all original external and node cotangent powers. -/
def term308 : CotangentTerm 2 (Fin 4) :=
  ⟨expression95, ((![0], ![1, 0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 309, with all original external and node cotangent powers. -/
def term309 : CotangentTerm 2 (Fin 4) :=
  ⟨expression95, ((![0], ![0, 0, 0, 0]), ![1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 310, with all original external and node cotangent powers. -/
def term310 : CotangentTerm 2 (Fin 4) :=
  ⟨expression95, ((![0], ![0, 0, 0, 0]), ![0, 1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 311, with all original external and node cotangent powers. -/
def term311 : CotangentTerm 2 (Fin 4) :=
  ⟨expression96, ((![0], ![1, 0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 312, with all original external and node cotangent powers. -/
def term312 : CotangentTerm 2 (Fin 4) :=
  ⟨expression96, ((![0], ![0, 1, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 313, with all original external and node cotangent powers. -/
def term313 : CotangentTerm 2 (Fin 4) :=
  ⟨expression96, ((![0], ![0, 0, 1, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 314, with all original external and node cotangent powers. -/
def term314 : CotangentTerm 2 (Fin 4) :=
  ⟨expression96, ((![0], ![0, 0, 0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 315, with all original external and node cotangent powers. -/
def term315 : CotangentTerm 2 (Fin 4) :=
  ⟨expression97, ((![0], ![1, 0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 316, with all original external and node cotangent powers. -/
def term316 : CotangentTerm 2 (Fin 4) :=
  ⟨expression97, ((![0], ![0, 1, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 317, with all original external and node cotangent powers. -/
def term317 : CotangentTerm 2 (Fin 4) :=
  ⟨expression97, ((![0], ![0, 0, 1, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 318, with all original external and node cotangent powers. -/
def term318 : CotangentTerm 2 (Fin 4) :=
  ⟨expression97, ((![0], ![0, 0, 0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 319, with all original external and node cotangent powers. -/
def term319 : CotangentTerm 2 (Fin 4) :=
  ⟨expression98, ((![0], ![1, 0, 0, 0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 320, with all original external and node cotangent powers. -/
def term320 : CotangentTerm 2 (Fin 4) :=
  ⟨expression98, ((![0], ![0, 1, 0, 0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 321, with all original external and node cotangent powers. -/
def term321 : CotangentTerm 2 (Fin 4) :=
  ⟨expression98, ((![0], ![0, 0, 1, 0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 322, with all original external and node cotangent powers. -/
def term322 : CotangentTerm 2 (Fin 4) :=
  ⟨expression98, ((![0], ![0, 0, 0, 1, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 323, with all original external and node cotangent powers. -/
def term323 : CotangentTerm 2 (Fin 4) :=
  ⟨expression99, ((![1, 0], ![0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 324, with all original external and node cotangent powers. -/
def term324 : CotangentTerm 2 (Fin 4) :=
  ⟨expression99, ((![0, 0], ![0, 0, 0]), ![1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 325, with all original external and node cotangent powers. -/
def term325 : CotangentTerm 2 (Fin 4) :=
  ⟨expression99, ((![0, 0], ![0, 0, 0]), ![0, 1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 326, with all original external and node cotangent powers. -/
def term326 : CotangentTerm 2 (Fin 4) :=
  ⟨expression100, ((![1, 0], ![0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 327, with all original external and node cotangent powers. -/
def term327 : CotangentTerm 2 (Fin 4) :=
  ⟨expression100, ((![0, 0], ![0, 0, 0]), ![1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 328, with all original external and node cotangent powers. -/
def term328 : CotangentTerm 2 (Fin 4) :=
  ⟨expression100, ((![0, 0], ![0, 0, 0]), ![0, 1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 329, with all original external and node cotangent powers. -/
def term329 : CotangentTerm 2 (Fin 4) :=
  ⟨expression101, ((![1, 0], ![0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 330, with all original external and node cotangent powers. -/
def term330 : CotangentTerm 2 (Fin 4) :=
  ⟨expression101, ((![0, 0], ![1, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 331, with all original external and node cotangent powers. -/
def term331 : CotangentTerm 2 (Fin 4) :=
  ⟨expression101, ((![0, 0], ![0, 1, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 332, with all original external and node cotangent powers. -/
def term332 : CotangentTerm 2 (Fin 4) :=
  ⟨expression101, ((![0, 0], ![0, 0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 333, with all original external and node cotangent powers. -/
def term333 : CotangentTerm 2 (Fin 4) :=
  ⟨expression102, ((![1, 0], ![0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 334, with all original external and node cotangent powers. -/
def term334 : CotangentTerm 2 (Fin 4) :=
  ⟨expression102, ((![0, 0], ![0, 0, 0]), ![1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 335, with all original external and node cotangent powers. -/
def term335 : CotangentTerm 2 (Fin 4) :=
  ⟨expression102, ((![0, 0], ![0, 0, 0]), ![0, 1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 336, with all original external and node cotangent powers. -/
def term336 : CotangentTerm 2 (Fin 4) :=
  ⟨expression103, ((![1, 0], ![0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 337, with all original external and node cotangent powers. -/
def term337 : CotangentTerm 2 (Fin 4) :=
  ⟨expression103, ((![0, 0], ![1, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 338, with all original external and node cotangent powers. -/
def term338 : CotangentTerm 2 (Fin 4) :=
  ⟨expression103, ((![0, 0], ![0, 1, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 339, with all original external and node cotangent powers. -/
def term339 : CotangentTerm 2 (Fin 4) :=
  ⟨expression103, ((![0, 0], ![0, 0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 340, with all original external and node cotangent powers. -/
def term340 : CotangentTerm 2 (Fin 4) :=
  ⟨expression104, ((![1, 0], ![0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 341, with all original external and node cotangent powers. -/
def term341 : CotangentTerm 2 (Fin 4) :=
  ⟨expression104, ((![0, 0], ![1, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 342, with all original external and node cotangent powers. -/
def term342 : CotangentTerm 2 (Fin 4) :=
  ⟨expression104, ((![0, 0], ![0, 1, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 343, with all original external and node cotangent powers. -/
def term343 : CotangentTerm 2 (Fin 4) :=
  ⟨expression104, ((![0, 0], ![0, 0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 344, with all original external and node cotangent powers. -/
def term344 : CotangentTerm 2 (Fin 4) :=
  ⟨expression105, ((![1, 0], ![0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 345, with all original external and node cotangent powers. -/
def term345 : CotangentTerm 2 (Fin 4) :=
  ⟨expression105, ((![0, 0], ![0, 0, 0]), ![1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 346, with all original external and node cotangent powers. -/
def term346 : CotangentTerm 2 (Fin 4) :=
  ⟨expression105, ((![0, 0], ![0, 0, 0]), ![0, 1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 347, with all original external and node cotangent powers. -/
def term347 : CotangentTerm 2 (Fin 4) :=
  ⟨expression106, ((![1, 0], ![0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 348, with all original external and node cotangent powers. -/
def term348 : CotangentTerm 2 (Fin 4) :=
  ⟨expression106, ((![0, 0], ![0, 0, 0]), ![1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 349, with all original external and node cotangent powers. -/
def term349 : CotangentTerm 2 (Fin 4) :=
  ⟨expression106, ((![0, 0], ![0, 0, 0]), ![0, 1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 350, with all original external and node cotangent powers. -/
def term350 : CotangentTerm 2 (Fin 4) :=
  ⟨expression107, ((![1, 0], ![0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 351, with all original external and node cotangent powers. -/
def term351 : CotangentTerm 2 (Fin 4) :=
  ⟨expression107, ((![0, 0], ![1, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 352, with all original external and node cotangent powers. -/
def term352 : CotangentTerm 2 (Fin 4) :=
  ⟨expression107, ((![0, 0], ![0, 1, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 353, with all original external and node cotangent powers. -/
def term353 : CotangentTerm 2 (Fin 4) :=
  ⟨expression107, ((![0, 0], ![0, 0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 354, with all original external and node cotangent powers. -/
def term354 : CotangentTerm 2 (Fin 4) :=
  ⟨expression108, ((![1, 0], ![0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 355, with all original external and node cotangent powers. -/
def term355 : CotangentTerm 2 (Fin 4) :=
  ⟨expression108, ((![0, 0], ![0, 0, 0]), ![1, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 356, with all original external and node cotangent powers. -/
def term356 : CotangentTerm 2 (Fin 4) :=
  ⟨expression108, ((![0, 0], ![0, 0, 0]), ![0, 1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 357, with all original external and node cotangent powers. -/
def term357 : CotangentTerm 2 (Fin 4) :=
  ⟨expression109, ((![1, 0], ![0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 358, with all original external and node cotangent powers. -/
def term358 : CotangentTerm 2 (Fin 4) :=
  ⟨expression109, ((![0, 0], ![1, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 359, with all original external and node cotangent powers. -/
def term359 : CotangentTerm 2 (Fin 4) :=
  ⟨expression109, ((![0, 0], ![0, 1, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 360, with all original external and node cotangent powers. -/
def term360 : CotangentTerm 2 (Fin 4) :=
  ⟨expression109, ((![0, 0], ![0, 0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 361, with all original external and node cotangent powers. -/
def term361 : CotangentTerm 2 (Fin 4) :=
  ⟨expression110, ((![1, 0, 0], ![0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 362, with all original external and node cotangent powers. -/
def term362 : CotangentTerm 2 (Fin 4) :=
  ⟨expression110, ((![0, 1, 0], ![0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 363, with all original external and node cotangent powers. -/
def term363 : CotangentTerm 2 (Fin 4) :=
  ⟨expression110, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 364, with all original external and node cotangent powers. -/
def term364 : CotangentTerm 2 (Fin 4) :=
  ⟨expression111, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 365, with all original external and node cotangent powers. -/
def term365 : CotangentTerm 2 (Fin 4) :=
  ⟨expression112, ((![1, 0], ![0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 366, with all original external and node cotangent powers. -/
def term366 : CotangentTerm 2 (Fin 4) :=
  ⟨expression113, ((![1, 0], ![0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 367, with all original external and node cotangent powers. -/
def term367 : CotangentTerm 2 (Fin 4) :=
  ⟨expression114, ((![1, 0], ![0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 368, with all original external and node cotangent powers. -/
def term368 : CotangentTerm 2 (Fin 4) :=
  ⟨expression114, ((![0, 0], ![1, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 369, with all original external and node cotangent powers. -/
def term369 : CotangentTerm 2 (Fin 4) :=
  ⟨expression114, ((![0, 0], ![0, 1, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 370, with all original external and node cotangent powers. -/
def term370 : CotangentTerm 2 (Fin 4) :=
  ⟨expression114, ((![0, 0], ![0, 0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 371, with all original external and node cotangent powers. -/
def term371 : CotangentTerm 2 (Fin 4) :=
  ⟨expression115, ((![1, 0, 0], ![0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 372, with all original external and node cotangent powers. -/
def term372 : CotangentTerm 2 (Fin 4) :=
  ⟨expression115, ((![0, 1, 0], ![0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 373, with all original external and node cotangent powers. -/
def term373 : CotangentTerm 2 (Fin 4) :=
  ⟨expression115, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 374, with all original external and node cotangent powers. -/
def term374 : CotangentTerm 2 (Fin 4) :=
  ⟨expression116, ((![1, 0, 0], ![0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 375, with all original external and node cotangent powers. -/
def term375 : CotangentTerm 2 (Fin 4) :=
  ⟨expression116, ((![0, 1, 0], ![0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 376, with all original external and node cotangent powers. -/
def term376 : CotangentTerm 2 (Fin 4) :=
  ⟨expression116, ((![0, 0, 0], ![0, 0, 0]), ![1, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 377, with all original external and node cotangent powers. -/
def term377 : CotangentTerm 2 (Fin 4) :=
  ⟨expression117, (![0], ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 378, with all original external and node cotangent powers. -/
def term378 : CotangentTerm 2 (Fin 4) :=
  ⟨expression118, (((![0, 0, 0], ![0, 0, 0]), ![0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 379, with all original external and node cotangent powers. -/
def term379 : CotangentTerm 2 (Fin 4) :=
  ⟨expression119, (![0], ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 380, with all original external and node cotangent powers. -/
def term380 : CotangentTerm 2 (Fin 4) :=
  ⟨expression120, (((![0, 0, 0], ![0, 0, 0]), ![0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 381, with all original external and node cotangent powers. -/
def term381 : CotangentTerm 2 (Fin 4) :=
  ⟨expression121, (![0], (![0, 0, 0], (![0, 0, 0], ![0, 0, 0]))), (inferInstance,
    (inferInstance, (inferInstance, inferInstance)))⟩

/-- Held column 382, with all original external and node cotangent powers. -/
def term382 : CotangentTerm 2 (Fin 4) :=
  ⟨expression122, ((![0, 0, 0], ![0, 0]), (![0, 0, 0], ![0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 383, with all original external and node cotangent powers. -/
def term383 : CotangentTerm 2 (Fin 4) :=
  ⟨expression123, (![0], ((![0, 0, 0], ![0, 0, 0, 0]), ![0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 384, with all original external and node cotangent powers. -/
def term384 : CotangentTerm 2 (Fin 4) :=
  ⟨expression124, (![0], ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 385, with all original external and node cotangent powers. -/
def term385 : CotangentTerm 2 (Fin 4) :=
  ⟨expression125, (((![0, 0, 0], ![0, 0, 0]), ![0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 386, with all original external and node cotangent powers. -/
def term386 : CotangentTerm 2 (Fin 4) :=
  ⟨expression126, (![0], ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 387, with all original external and node cotangent powers. -/
def term387 : CotangentTerm 2 (Fin 4) :=
  ⟨expression127, (((![0, 0, 0], ![0, 0, 0]), ![0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 388, with all original external and node cotangent powers. -/
def term388 : CotangentTerm 2 (Fin 4) :=
  ⟨expression128, (![0], (![0, 0, 0], (![0, 0, 0], ![0, 0, 0]))), (inferInstance,
    (inferInstance, (inferInstance, inferInstance)))⟩

/-- Held column 389, with all original external and node cotangent powers. -/
def term389 : CotangentTerm 2 (Fin 4) :=
  ⟨expression129, ((![0, 0, 0], ![0, 0]), (![0, 0, 0], ![0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 390, with all original external and node cotangent powers. -/
def term390 : CotangentTerm 2 (Fin 4) :=
  ⟨expression130, (![0], ((![0, 0, 0], ![0, 0, 0, 0]), ![0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 391, with all original external and node cotangent powers. -/
def term391 : CotangentTerm 2 (Fin 4) :=
  ⟨expression131, (![0], ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 392, with all original external and node cotangent powers. -/
def term392 : CotangentTerm 2 (Fin 4) :=
  ⟨expression132, (((![0, 0, 0], ![0, 0, 0]), ![0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 393, with all original external and node cotangent powers. -/
def term393 : CotangentTerm 2 (Fin 4) :=
  ⟨expression133, (![0], ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 394, with all original external and node cotangent powers. -/
def term394 : CotangentTerm 2 (Fin 4) :=
  ⟨expression134, (((![0, 0, 0], ![0, 0, 0]), ![0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 395, with all original external and node cotangent powers. -/
def term395 : CotangentTerm 2 (Fin 4) :=
  ⟨expression135, (![0], (![0, 0, 0], (![0, 0, 0], ![0, 0, 0]))), (inferInstance,
    (inferInstance, (inferInstance, inferInstance)))⟩

/-- Held column 396, with all original external and node cotangent powers. -/
def term396 : CotangentTerm 2 (Fin 4) :=
  ⟨expression136, ((![0, 0, 0], ![0, 0]), (![0, 0, 0], ![0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 397, with all original external and node cotangent powers. -/
def term397 : CotangentTerm 2 (Fin 4) :=
  ⟨expression137, (![0], ((![0, 0, 0], ![0, 0, 0, 0]), ![0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 398, with all original external and node cotangent powers. -/
def term398 : CotangentTerm 2 (Fin 4) :=
  ⟨expression138, (![0], ((![0, 0, 0, 0], ![0, 0, 0]), ![0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 399, with all original external and node cotangent powers. -/
def term399 : CotangentTerm 2 (Fin 4) :=
  ⟨expression139, (![0], ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 400, with all original external and node cotangent powers. -/
def term400 : CotangentTerm 2 (Fin 4) :=
  ⟨expression140, (((![0, 0, 0], ![0, 0, 0]), ![0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 401, with all original external and node cotangent powers. -/
def term401 : CotangentTerm 2 (Fin 4) :=
  ⟨expression141, (![0], ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 402, with all original external and node cotangent powers. -/
def term402 : CotangentTerm 2 (Fin 4) :=
  ⟨expression142, (((![0, 0, 0], ![0, 0, 0]), ![0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 403, with all original external and node cotangent powers. -/
def term403 : CotangentTerm 2 (Fin 4) :=
  ⟨expression143, (![0], ((![0, 0, 0], ![0, 0, 0, 0]), ![0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 404, with all original external and node cotangent powers. -/
def term404 : CotangentTerm 2 (Fin 4) :=
  ⟨expression144, (![0], ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 405, with all original external and node cotangent powers. -/
def term405 : CotangentTerm 2 (Fin 4) :=
  ⟨expression145, (((![0, 0, 0], ![0, 0, 0]), ![0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 406, with all original external and node cotangent powers. -/
def term406 : CotangentTerm 2 (Fin 4) :=
  ⟨expression146, (![0], ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 407, with all original external and node cotangent powers. -/
def term407 : CotangentTerm 2 (Fin 4) :=
  ⟨expression147, (((![0, 0, 0], ![0, 0, 0]), ![0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 408, with all original external and node cotangent powers. -/
def term408 : CotangentTerm 2 (Fin 4) :=
  ⟨expression148, (![0], ((![0, 0, 0], ![0, 0, 0, 0]), ![0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 409, with all original external and node cotangent powers. -/
def term409 : CotangentTerm 2 (Fin 4) :=
  ⟨expression149, (![0], ((![0, 0, 0, 0], ![0, 0, 0]), ![0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 410, with all original external and node cotangent powers. -/
def term410 : CotangentTerm 2 (Fin 4) :=
  ⟨expression150, (![0], ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 411, with all original external and node cotangent powers. -/
def term411 : CotangentTerm 2 (Fin 4) :=
  ⟨expression151, (((![0, 0, 0], ![0, 0, 0]), ![0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 412, with all original external and node cotangent powers. -/
def term412 : CotangentTerm 2 (Fin 4) :=
  ⟨expression152, (![0], ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 413, with all original external and node cotangent powers. -/
def term413 : CotangentTerm 2 (Fin 4) :=
  ⟨expression153, (((![0, 0, 0], ![0, 0, 0]), ![0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 414, with all original external and node cotangent powers. -/
def term414 : CotangentTerm 2 (Fin 4) :=
  ⟨expression154, (![0], ((![0, 0, 0], ![0, 0, 0, 0]), ![0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 415, with all original external and node cotangent powers. -/
def term415 : CotangentTerm 2 (Fin 4) :=
  ⟨expression155, (![0], ((![0, 0, 0, 0], ![0, 0, 0]), ![0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 416, with all original external and node cotangent powers. -/
def term416 : CotangentTerm 2 (Fin 4) :=
  ⟨expression156, (![0], ((![0, 0, 0, 0], ![0, 0, 0]), ![0, 0])), (inferInstance,
    ((inferInstance, inferInstance), inferInstance))⟩

/-- Held column 417, with all original external and node cotangent powers. -/
def term417 : CotangentTerm 2 (Fin 4) :=
  ⟨expression157, ((![0], (![0, 0, 0], ![0, 0, 0])), ![0, 0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 418, with all original external and node cotangent powers. -/
def term418 : CotangentTerm 2 (Fin 4) :=
  ⟨expression158, ((![0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 419, with all original external and node cotangent powers. -/
def term419 : CotangentTerm 2 (Fin 4) :=
  ⟨expression159, ((![0], (![0, 0, 0], ![0, 0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 420, with all original external and node cotangent powers. -/
def term420 : CotangentTerm 2 (Fin 4) :=
  ⟨expression160, ((![0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 421, with all original external and node cotangent powers. -/
def term421 : CotangentTerm 2 (Fin 4) :=
  ⟨expression161, ((![0], (![0, 0, 0], ![0, 0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 422, with all original external and node cotangent powers. -/
def term422 : CotangentTerm 2 (Fin 4) :=
  ⟨expression162, ((![0], ![0, 0, 0, 0]), (![0, 0, 0], ![0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 423, with all original external and node cotangent powers. -/
def term423 : CotangentTerm 2 (Fin 4) :=
  ⟨expression163, ((![0], (![0, 0, 0], ![0, 0, 0, 0, 0])), ![0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 424, with all original external and node cotangent powers. -/
def term424 : CotangentTerm 2 (Fin 4) :=
  ⟨expression164, (((![0, 0, 0], ![0, 0]), ![0, 0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 425, with all original external and node cotangent powers. -/
def term425 : CotangentTerm 2 (Fin 4) :=
  ⟨expression165, (((![0, 0, 0], ![0, 0]), ![0, 0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 426, with all original external and node cotangent powers. -/
def term426 : CotangentTerm 2 (Fin 4) :=
  ⟨expression166, ((![0, 0], (![0, 0, 0], ![0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 427, with all original external and node cotangent powers. -/
def term427 : CotangentTerm 2 (Fin 4) :=
  ⟨expression167, ((![0], (![0, 0, 0], ![0, 0, 0])), ![0, 0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 428, with all original external and node cotangent powers. -/
def term428 : CotangentTerm 2 (Fin 4) :=
  ⟨expression168, ((![0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 429, with all original external and node cotangent powers. -/
def term429 : CotangentTerm 2 (Fin 4) :=
  ⟨expression169, ((![0], (![0, 0, 0], ![0, 0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 430, with all original external and node cotangent powers. -/
def term430 : CotangentTerm 2 (Fin 4) :=
  ⟨expression170, ((![0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 431, with all original external and node cotangent powers. -/
def term431 : CotangentTerm 2 (Fin 4) :=
  ⟨expression171, ((![0], (![0, 0, 0], ![0, 0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 432, with all original external and node cotangent powers. -/
def term432 : CotangentTerm 2 (Fin 4) :=
  ⟨expression172, ((![0], ![0, 0, 0, 0]), (![0, 0, 0], ![0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 433, with all original external and node cotangent powers. -/
def term433 : CotangentTerm 2 (Fin 4) :=
  ⟨expression173, ((![0], (![0, 0, 0], ![0, 0, 0, 0, 0])), ![0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 434, with all original external and node cotangent powers. -/
def term434 : CotangentTerm 2 (Fin 4) :=
  ⟨expression174, (((![0, 0, 0], ![0, 0]), ![0, 0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 435, with all original external and node cotangent powers. -/
def term435 : CotangentTerm 2 (Fin 4) :=
  ⟨expression175, (((![0, 0, 0], ![0, 0]), ![0, 0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 436, with all original external and node cotangent powers. -/
def term436 : CotangentTerm 2 (Fin 4) :=
  ⟨expression176, ((![0, 0], (![0, 0, 0], ![0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 437, with all original external and node cotangent powers. -/
def term437 : CotangentTerm 2 (Fin 4) :=
  ⟨expression177, ((![0], (![0, 0, 0], ![0, 0, 0])), ![0, 0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 438, with all original external and node cotangent powers. -/
def term438 : CotangentTerm 2 (Fin 4) :=
  ⟨expression178, ((![0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 439, with all original external and node cotangent powers. -/
def term439 : CotangentTerm 2 (Fin 4) :=
  ⟨expression179, ((![0], (![0, 0, 0], ![0, 0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 440, with all original external and node cotangent powers. -/
def term440 : CotangentTerm 2 (Fin 4) :=
  ⟨expression180, ((![0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 441, with all original external and node cotangent powers. -/
def term441 : CotangentTerm 2 (Fin 4) :=
  ⟨expression181, ((![0], (![0, 0, 0], ![0, 0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 442, with all original external and node cotangent powers. -/
def term442 : CotangentTerm 2 (Fin 4) :=
  ⟨expression182, ((![0], ![0, 0, 0, 0]), (![0, 0, 0], ![0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 443, with all original external and node cotangent powers. -/
def term443 : CotangentTerm 2 (Fin 4) :=
  ⟨expression183, ((![0], (![0, 0, 0], ![0, 0, 0, 0, 0])), ![0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 444, with all original external and node cotangent powers. -/
def term444 : CotangentTerm 2 (Fin 4) :=
  ⟨expression184, (((![0, 0, 0], ![0, 0]), ![0, 0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 445, with all original external and node cotangent powers. -/
def term445 : CotangentTerm 2 (Fin 4) :=
  ⟨expression185, (((![0, 0, 0], ![0, 0]), ![0, 0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 446, with all original external and node cotangent powers. -/
def term446 : CotangentTerm 2 (Fin 4) :=
  ⟨expression186, ((![0, 0], (![0, 0, 0], ![0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 447, with all original external and node cotangent powers. -/
def term447 : CotangentTerm 2 (Fin 4) :=
  ⟨expression187, ((![0], (![0, 0, 0, 0], ![0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 448, with all original external and node cotangent powers. -/
def term448 : CotangentTerm 2 (Fin 4) :=
  ⟨expression188, ((![0], ![0, 0, 0]), (![0, 0, 0, 0], ![0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 449, with all original external and node cotangent powers. -/
def term449 : CotangentTerm 2 (Fin 4) :=
  ⟨expression189, ((![0], (![0, 0, 0, 0], ![0, 0, 0, 0])), ![0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 450, with all original external and node cotangent powers. -/
def term450 : CotangentTerm 2 (Fin 4) :=
  ⟨expression190, ((![0], (![0, 0, 0], ![0, 0, 0])), ![0, 0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 451, with all original external and node cotangent powers. -/
def term451 : CotangentTerm 2 (Fin 4) :=
  ⟨expression191, ((![0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 452, with all original external and node cotangent powers. -/
def term452 : CotangentTerm 2 (Fin 4) :=
  ⟨expression192, ((![0], (![0, 0, 0], ![0, 0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 453, with all original external and node cotangent powers. -/
def term453 : CotangentTerm 2 (Fin 4) :=
  ⟨expression193, ((![0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 454, with all original external and node cotangent powers. -/
def term454 : CotangentTerm 2 (Fin 4) :=
  ⟨expression194, ((![0], (![0, 0, 0], ![0, 0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 455, with all original external and node cotangent powers. -/
def term455 : CotangentTerm 2 (Fin 4) :=
  ⟨expression195, ((![0], ![0, 0, 0, 0]), (![0, 0, 0], ![0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 456, with all original external and node cotangent powers. -/
def term456 : CotangentTerm 2 (Fin 4) :=
  ⟨expression196, ((![0], (![0, 0, 0], ![0, 0, 0, 0, 0])), ![0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 457, with all original external and node cotangent powers. -/
def term457 : CotangentTerm 2 (Fin 4) :=
  ⟨expression197, (((![0, 0, 0], ![0, 0]), ![0, 0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 458, with all original external and node cotangent powers. -/
def term458 : CotangentTerm 2 (Fin 4) :=
  ⟨expression198, (((![0, 0, 0], ![0, 0]), ![0, 0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 459, with all original external and node cotangent powers. -/
def term459 : CotangentTerm 2 (Fin 4) :=
  ⟨expression199, ((![0, 0], (![0, 0, 0], ![0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 460, with all original external and node cotangent powers. -/
def term460 : CotangentTerm 2 (Fin 4) :=
  ⟨expression200, ((![0], (![0, 0, 0], ![0, 0, 0])), ![0, 0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 461, with all original external and node cotangent powers. -/
def term461 : CotangentTerm 2 (Fin 4) :=
  ⟨expression201, ((![0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 462, with all original external and node cotangent powers. -/
def term462 : CotangentTerm 2 (Fin 4) :=
  ⟨expression202, ((![0], (![0, 0, 0], ![0, 0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 463, with all original external and node cotangent powers. -/
def term463 : CotangentTerm 2 (Fin 4) :=
  ⟨expression203, ((![0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 464, with all original external and node cotangent powers. -/
def term464 : CotangentTerm 2 (Fin 4) :=
  ⟨expression204, ((![0], (![0, 0, 0], ![0, 0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 465, with all original external and node cotangent powers. -/
def term465 : CotangentTerm 2 (Fin 4) :=
  ⟨expression205, ((![0], ![0, 0, 0, 0]), (![0, 0, 0], ![0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 466, with all original external and node cotangent powers. -/
def term466 : CotangentTerm 2 (Fin 4) :=
  ⟨expression206, ((![0], (![0, 0, 0], ![0, 0, 0, 0, 0])), ![0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 467, with all original external and node cotangent powers. -/
def term467 : CotangentTerm 2 (Fin 4) :=
  ⟨expression207, (((![0, 0, 0], ![0, 0]), ![0, 0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 468, with all original external and node cotangent powers. -/
def term468 : CotangentTerm 2 (Fin 4) :=
  ⟨expression208, (((![0, 0, 0], ![0, 0]), ![0, 0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 469, with all original external and node cotangent powers. -/
def term469 : CotangentTerm 2 (Fin 4) :=
  ⟨expression209, ((![0, 0], (![0, 0, 0], ![0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 470, with all original external and node cotangent powers. -/
def term470 : CotangentTerm 2 (Fin 4) :=
  ⟨expression210, ((![0], (![0, 0, 0, 0], ![0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 471, with all original external and node cotangent powers. -/
def term471 : CotangentTerm 2 (Fin 4) :=
  ⟨expression211, ((![0], ![0, 0, 0]), (![0, 0, 0, 0], ![0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 472, with all original external and node cotangent powers. -/
def term472 : CotangentTerm 2 (Fin 4) :=
  ⟨expression212, ((![0], (![0, 0, 0, 0], ![0, 0, 0, 0])), ![0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 473, with all original external and node cotangent powers. -/
def term473 : CotangentTerm 2 (Fin 4) :=
  ⟨expression213, ((![0], (![0, 0, 0], ![0, 0, 0])), ![0, 0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 474, with all original external and node cotangent powers. -/
def term474 : CotangentTerm 2 (Fin 4) :=
  ⟨expression214, ((![0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 475, with all original external and node cotangent powers. -/
def term475 : CotangentTerm 2 (Fin 4) :=
  ⟨expression215, ((![0], (![0, 0, 0], ![0, 0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 476, with all original external and node cotangent powers. -/
def term476 : CotangentTerm 2 (Fin 4) :=
  ⟨expression216, ((![0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 477, with all original external and node cotangent powers. -/
def term477 : CotangentTerm 2 (Fin 4) :=
  ⟨expression217, ((![0], (![0, 0, 0], ![0, 0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 478, with all original external and node cotangent powers. -/
def term478 : CotangentTerm 2 (Fin 4) :=
  ⟨expression218, ((![0], ![0, 0, 0, 0]), (![0, 0, 0], ![0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 479, with all original external and node cotangent powers. -/
def term479 : CotangentTerm 2 (Fin 4) :=
  ⟨expression219, ((![0], (![0, 0, 0], ![0, 0, 0, 0, 0])), ![0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 480, with all original external and node cotangent powers. -/
def term480 : CotangentTerm 2 (Fin 4) :=
  ⟨expression220, (((![0, 0, 0], ![0, 0]), ![0, 0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 481, with all original external and node cotangent powers. -/
def term481 : CotangentTerm 2 (Fin 4) :=
  ⟨expression221, (((![0, 0, 0], ![0, 0]), ![0, 0, 0]), ![0, 0]), (((inferInstance,
    inferInstance), inferInstance), inferInstance)⟩

/-- Held column 482, with all original external and node cotangent powers. -/
def term482 : CotangentTerm 2 (Fin 4) :=
  ⟨expression222, ((![0, 0], (![0, 0, 0], ![0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 483, with all original external and node cotangent powers. -/
def term483 : CotangentTerm 2 (Fin 4) :=
  ⟨expression223, ((![0], (![0, 0, 0, 0], ![0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 484, with all original external and node cotangent powers. -/
def term484 : CotangentTerm 2 (Fin 4) :=
  ⟨expression224, ((![0], ![0, 0, 0]), (![0, 0, 0, 0], ![0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 485, with all original external and node cotangent powers. -/
def term485 : CotangentTerm 2 (Fin 4) :=
  ⟨expression225, ((![0], (![0, 0, 0, 0], ![0, 0, 0, 0])), ![0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 486, with all original external and node cotangent powers. -/
def term486 : CotangentTerm 2 (Fin 4) :=
  ⟨expression226, ((![0], (![0, 0, 0, 0], ![0, 0, 0])), ![0, 0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 487, with all original external and node cotangent powers. -/
def term487 : CotangentTerm 2 (Fin 4) :=
  ⟨expression227, ((![0], ![0, 0, 0]), (![0, 0, 0, 0], ![0, 0])), ((inferInstance,
    inferInstance), (inferInstance, inferInstance))⟩

/-- Held column 488, with all original external and node cotangent powers. -/
def term488 : CotangentTerm 2 (Fin 4) :=
  ⟨expression228, ((![0], (![0, 0, 0, 0], ![0, 0, 0, 0])), ![0]), ((inferInstance,
    (inferInstance, inferInstance)), inferInstance)⟩

/-- Held column 489, with all original external and node cotangent powers. -/
def term489 : CotangentTerm 2 (Fin 4) :=
  ⟨expression51, (![1], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 490, with all original external and node cotangent powers. -/
def term490 : CotangentTerm 2 (Fin 4) :=
  ⟨expression55, (![1], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 491, with all original external and node cotangent powers. -/
def term491 : CotangentTerm 2 (Fin 4) :=
  ⟨expression59, (![1], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 492, with all original external and node cotangent powers. -/
def term492 : CotangentTerm 2 (Fin 4) :=
  ⟨expression63, (![1], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 493, with all original external and node cotangent powers. -/
def term493 : CotangentTerm 2 (Fin 4) :=
  ⟨expression65, (![1], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 494, with all original external and node cotangent powers. -/
def term494 : CotangentTerm 2 (Fin 4) :=
  ⟨expression69, (![1], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 495, with all original external and node cotangent powers. -/
def term495 : CotangentTerm 2 (Fin 4) :=
  ⟨expression73, (![1], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 496, with all original external and node cotangent powers. -/
def term496 : CotangentTerm 2 (Fin 4) :=
  ⟨expression75, (![1], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 497, with all original external and node cotangent powers. -/
def term497 : CotangentTerm 2 (Fin 4) :=
  ⟨expression79, (![1], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 498, with all original external and node cotangent powers. -/
def term498 : CotangentTerm 2 (Fin 4) :=
  ⟨expression81, (![1], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 499, with all original external and node cotangent powers. -/
def term499 : CotangentTerm 2 (Fin 4) :=
  ⟨expression229, (![0, 0, 0], ![0, 0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 500, with all original external and node cotangent powers. -/
def term500 : CotangentTerm 2 (Fin 4) :=
  ⟨expression229, (![0, 0, 0], ![1, 0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 501, with all original external and node cotangent powers. -/
def term501 : CotangentTerm 2 (Fin 4) :=
  ⟨expression229, (![0, 0, 0], ![0, 1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 502, with all original external and node cotangent powers. -/
def term502 : CotangentTerm 2 (Fin 4) :=
  ⟨expression229, (![0, 0, 0], ![0, 0, 0, 0, 1]), (inferInstance, inferInstance)⟩

/-- Held column 503, with all original external and node cotangent powers. -/
def term503 : CotangentTerm 2 (Fin 4) :=
  ⟨expression230, (![0, 0, 0], ![0, 0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 504, with all original external and node cotangent powers. -/
def term504 : CotangentTerm 2 (Fin 4) :=
  ⟨expression230, (![0, 0, 0], ![1, 0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 505, with all original external and node cotangent powers. -/
def term505 : CotangentTerm 2 (Fin 4) :=
  ⟨expression230, (![0, 0, 0], ![0, 1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 506, with all original external and node cotangent powers. -/
def term506 : CotangentTerm 2 (Fin 4) :=
  ⟨expression231, (![0, 0, 0], ![0, 0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 507, with all original external and node cotangent powers. -/
def term507 : CotangentTerm 2 (Fin 4) :=
  ⟨expression231, (![0, 0, 0], ![1, 0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 508, with all original external and node cotangent powers. -/
def term508 : CotangentTerm 2 (Fin 4) :=
  ⟨expression231, (![0, 0, 0], ![0, 1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 509, with all original external and node cotangent powers. -/
def term509 : CotangentTerm 2 (Fin 4) :=
  ⟨expression232, (![0, 0, 0, 0], ![0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 510, with all original external and node cotangent powers. -/
def term510 : CotangentTerm 2 (Fin 4) :=
  ⟨expression232, (![1, 0, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 511, with all original external and node cotangent powers. -/
def term511 : CotangentTerm 2 (Fin 4) :=
  ⟨expression232, (![0, 1, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 512, with all original external and node cotangent powers. -/
def term512 : CotangentTerm 2 (Fin 4) :=
  ⟨expression232, (![0, 0, 1, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 513, with all original external and node cotangent powers. -/
def term513 : CotangentTerm 2 (Fin 4) :=
  ⟨expression232, (![0, 0, 0, 0], ![1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 514, with all original external and node cotangent powers. -/
def term514 : CotangentTerm 2 (Fin 4) :=
  ⟨expression232, (![0, 0, 0, 0], ![0, 0, 0, 1]), (inferInstance, inferInstance)⟩

/-- Held column 515, with all original external and node cotangent powers. -/
def term515 : CotangentTerm 2 (Fin 4) :=
  ⟨expression233, (![0, 0, 0], ![0, 0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 516, with all original external and node cotangent powers. -/
def term516 : CotangentTerm 2 (Fin 4) :=
  ⟨expression233, (![0, 0, 0], ![1, 0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 517, with all original external and node cotangent powers. -/
def term517 : CotangentTerm 2 (Fin 4) :=
  ⟨expression233, (![0, 0, 0], ![0, 1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 518, with all original external and node cotangent powers. -/
def term518 : CotangentTerm 2 (Fin 4) :=
  ⟨expression233, (![0, 0, 0], ![0, 0, 0, 0, 1]), (inferInstance, inferInstance)⟩

/-- Held column 519, with all original external and node cotangent powers. -/
def term519 : CotangentTerm 2 (Fin 4) :=
  ⟨expression234, (![0, 0, 0], ![0, 0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 520, with all original external and node cotangent powers. -/
def term520 : CotangentTerm 2 (Fin 4) :=
  ⟨expression234, (![0, 0, 0], ![1, 0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 521, with all original external and node cotangent powers. -/
def term521 : CotangentTerm 2 (Fin 4) :=
  ⟨expression234, (![0, 0, 0], ![0, 1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 522, with all original external and node cotangent powers. -/
def term522 : CotangentTerm 2 (Fin 4) :=
  ⟨expression234, (![0, 0, 0], ![0, 0, 0, 0, 1]), (inferInstance, inferInstance)⟩

/-- Held column 523, with all original external and node cotangent powers. -/
def term523 : CotangentTerm 2 (Fin 4) :=
  ⟨expression235, (![0, 0, 0, 0], ![0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 524, with all original external and node cotangent powers. -/
def term524 : CotangentTerm 2 (Fin 4) :=
  ⟨expression235, (![1, 0, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 525, with all original external and node cotangent powers. -/
def term525 : CotangentTerm 2 (Fin 4) :=
  ⟨expression235, (![0, 1, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 526, with all original external and node cotangent powers. -/
def term526 : CotangentTerm 2 (Fin 4) :=
  ⟨expression235, (![0, 0, 1, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 527, with all original external and node cotangent powers. -/
def term527 : CotangentTerm 2 (Fin 4) :=
  ⟨expression235, (![0, 0, 0, 0], ![1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 528, with all original external and node cotangent powers. -/
def term528 : CotangentTerm 2 (Fin 4) :=
  ⟨expression235, (![0, 0, 0, 0], ![0, 0, 0, 1]), (inferInstance, inferInstance)⟩

/-- Held column 529, with all original external and node cotangent powers. -/
def term529 : CotangentTerm 2 (Fin 4) :=
  ⟨expression236, (![0, 0, 0], ![0, 0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 530, with all original external and node cotangent powers. -/
def term530 : CotangentTerm 2 (Fin 4) :=
  ⟨expression236, (![0, 0, 0], ![1, 0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 531, with all original external and node cotangent powers. -/
def term531 : CotangentTerm 2 (Fin 4) :=
  ⟨expression236, (![0, 0, 0], ![0, 1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 532, with all original external and node cotangent powers. -/
def term532 : CotangentTerm 2 (Fin 4) :=
  ⟨expression237, (![0, 0, 0, 0], ![0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 533, with all original external and node cotangent powers. -/
def term533 : CotangentTerm 2 (Fin 4) :=
  ⟨expression237, (![1, 0, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 534, with all original external and node cotangent powers. -/
def term534 : CotangentTerm 2 (Fin 4) :=
  ⟨expression237, (![0, 1, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 535, with all original external and node cotangent powers. -/
def term535 : CotangentTerm 2 (Fin 4) :=
  ⟨expression237, (![0, 0, 1, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 536, with all original external and node cotangent powers. -/
def term536 : CotangentTerm 2 (Fin 4) :=
  ⟨expression237, (![0, 0, 0, 0], ![1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 537, with all original external and node cotangent powers. -/
def term537 : CotangentTerm 2 (Fin 4) :=
  ⟨expression237, (![0, 0, 0, 0], ![0, 0, 0, 1]), (inferInstance, inferInstance)⟩

/-- Held column 538, with all original external and node cotangent powers. -/
def term538 : CotangentTerm 2 (Fin 4) :=
  ⟨expression238, (![0, 0, 0, 0], ![0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 539, with all original external and node cotangent powers. -/
def term539 : CotangentTerm 2 (Fin 4) :=
  ⟨expression238, (![1, 0, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 540, with all original external and node cotangent powers. -/
def term540 : CotangentTerm 2 (Fin 4) :=
  ⟨expression238, (![0, 1, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 541, with all original external and node cotangent powers. -/
def term541 : CotangentTerm 2 (Fin 4) :=
  ⟨expression238, (![0, 0, 1, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 542, with all original external and node cotangent powers. -/
def term542 : CotangentTerm 2 (Fin 4) :=
  ⟨expression238, (![0, 0, 0, 0], ![1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 543, with all original external and node cotangent powers. -/
def term543 : CotangentTerm 2 (Fin 4) :=
  ⟨expression238, (![0, 0, 0, 0], ![0, 0, 0, 1]), (inferInstance, inferInstance)⟩

/-- Held column 544, with all original external and node cotangent powers. -/
def term544 : CotangentTerm 2 (Fin 4) :=
  ⟨expression239, (![1, 0, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 545, with all original external and node cotangent powers. -/
def term545 : CotangentTerm 2 (Fin 4) :=
  ⟨expression239, (![0, 1, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 546, with all original external and node cotangent powers. -/
def term546 : CotangentTerm 2 (Fin 4) :=
  ⟨expression239, (![0, 0, 1, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 547, with all original external and node cotangent powers. -/
def term547 : CotangentTerm 2 (Fin 4) :=
  ⟨expression239, (![0, 0, 0, 1, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 548, with all original external and node cotangent powers. -/
def term548 : CotangentTerm 2 (Fin 4) :=
  ⟨expression240, (![0, 0, 0], ![0, 1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 549, with all original external and node cotangent powers. -/
def term549 : CotangentTerm 2 (Fin 4) :=
  ⟨expression241, (![0, 0, 0], ![0, 1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 550, with all original external and node cotangent powers. -/
def term550 : CotangentTerm 2 (Fin 4) :=
  ⟨expression242, (![1, 0, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 551, with all original external and node cotangent powers. -/
def term551 : CotangentTerm 2 (Fin 4) :=
  ⟨expression242, (![0, 1, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 552, with all original external and node cotangent powers. -/
def term552 : CotangentTerm 2 (Fin 4) :=
  ⟨expression242, (![0, 0, 0, 0], ![1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 553, with all original external and node cotangent powers. -/
def term553 : CotangentTerm 2 (Fin 4) :=
  ⟨expression242, (![0, 0, 0, 0], ![0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 554, with all original external and node cotangent powers. -/
def term554 : CotangentTerm 2 (Fin 4) :=
  ⟨expression243, (![0, 0, 0], ![1, 0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 555, with all original external and node cotangent powers. -/
def term555 : CotangentTerm 2 (Fin 4) :=
  ⟨expression243, (![0, 0, 0], ![0, 1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 556, with all original external and node cotangent powers. -/
def term556 : CotangentTerm 2 (Fin 4) :=
  ⟨expression243, (![0, 0, 0], ![0, 0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 557, with all original external and node cotangent powers. -/
def term557 : CotangentTerm 2 (Fin 4) :=
  ⟨expression244, (![1, 0, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 558, with all original external and node cotangent powers. -/
def term558 : CotangentTerm 2 (Fin 4) :=
  ⟨expression244, (![0, 1, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 559, with all original external and node cotangent powers. -/
def term559 : CotangentTerm 2 (Fin 4) :=
  ⟨expression244, (![0, 0, 0, 0], ![1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 560, with all original external and node cotangent powers. -/
def term560 : CotangentTerm 2 (Fin 4) :=
  ⟨expression244, (![0, 0, 0, 0], ![0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 561, with all original external and node cotangent powers. -/
def term561 : CotangentTerm 2 (Fin 4) :=
  ⟨expression245, (![1, 0, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 562, with all original external and node cotangent powers. -/
def term562 : CotangentTerm 2 (Fin 4) :=
  ⟨expression245, (![0, 1, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 563, with all original external and node cotangent powers. -/
def term563 : CotangentTerm 2 (Fin 4) :=
  ⟨expression245, (![0, 0, 0, 0], ![1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 564, with all original external and node cotangent powers. -/
def term564 : CotangentTerm 2 (Fin 4) :=
  ⟨expression245, (![0, 0, 0, 0], ![0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 565, with all original external and node cotangent powers. -/
def term565 : CotangentTerm 2 (Fin 4) :=
  ⟨expression246, (![1, 0, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 566, with all original external and node cotangent powers. -/
def term566 : CotangentTerm 2 (Fin 4) :=
  ⟨expression246, (![0, 1, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 567, with all original external and node cotangent powers. -/
def term567 : CotangentTerm 2 (Fin 4) :=
  ⟨expression246, (![0, 0, 1, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 568, with all original external and node cotangent powers. -/
def term568 : CotangentTerm 2 (Fin 4) :=
  ⟨expression246, (![0, 0, 0, 0, 0], ![1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 569, with all original external and node cotangent powers. -/
def term569 : CotangentTerm 2 (Fin 4) :=
  ⟨expression247, (![0, 0, 0], ![1, 0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 570, with all original external and node cotangent powers. -/
def term570 : CotangentTerm 2 (Fin 4) :=
  ⟨expression248, (![1, 0, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 571, with all original external and node cotangent powers. -/
def term571 : CotangentTerm 2 (Fin 4) :=
  ⟨expression248, (![0, 1, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 572, with all original external and node cotangent powers. -/
def term572 : CotangentTerm 2 (Fin 4) :=
  ⟨expression248, (![0, 0, 0, 0], ![1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 573, with all original external and node cotangent powers. -/
def term573 : CotangentTerm 2 (Fin 4) :=
  ⟨expression248, (![0, 0, 0, 0], ![0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 574, with all original external and node cotangent powers. -/
def term574 : CotangentTerm 2 (Fin 4) :=
  ⟨expression249, (![1, 0, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 575, with all original external and node cotangent powers. -/
def term575 : CotangentTerm 2 (Fin 4) :=
  ⟨expression249, (![0, 1, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 576, with all original external and node cotangent powers. -/
def term576 : CotangentTerm 2 (Fin 4) :=
  ⟨expression249, (![0, 0, 0, 0], ![1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 577, with all original external and node cotangent powers. -/
def term577 : CotangentTerm 2 (Fin 4) :=
  ⟨expression249, (![0, 0, 0, 0], ![0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 578, with all original external and node cotangent powers. -/
def term578 : CotangentTerm 2 (Fin 4) :=
  ⟨expression250, (![1, 0, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 579, with all original external and node cotangent powers. -/
def term579 : CotangentTerm 2 (Fin 4) :=
  ⟨expression250, (![0, 1, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 580, with all original external and node cotangent powers. -/
def term580 : CotangentTerm 2 (Fin 4) :=
  ⟨expression250, (![0, 0, 1, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 581, with all original external and node cotangent powers. -/
def term581 : CotangentTerm 2 (Fin 4) :=
  ⟨expression250, (![0, 0, 0, 0, 0], ![1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 582, with all original external and node cotangent powers. -/
def term582 : CotangentTerm 2 (Fin 4) :=
  ⟨expression251, (![1, 0, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 583, with all original external and node cotangent powers. -/
def term583 : CotangentTerm 2 (Fin 4) :=
  ⟨expression251, (![0, 1, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 584, with all original external and node cotangent powers. -/
def term584 : CotangentTerm 2 (Fin 4) :=
  ⟨expression251, (![0, 0, 0, 0], ![1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 585, with all original external and node cotangent powers. -/
def term585 : CotangentTerm 2 (Fin 4) :=
  ⟨expression251, (![0, 0, 0, 0], ![0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 586, with all original external and node cotangent powers. -/
def term586 : CotangentTerm 2 (Fin 4) :=
  ⟨expression252, (![1, 0, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 587, with all original external and node cotangent powers. -/
def term587 : CotangentTerm 2 (Fin 4) :=
  ⟨expression252, (![0, 1, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 588, with all original external and node cotangent powers. -/
def term588 : CotangentTerm 2 (Fin 4) :=
  ⟨expression252, (![0, 0, 1, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 589, with all original external and node cotangent powers. -/
def term589 : CotangentTerm 2 (Fin 4) :=
  ⟨expression252, (![0, 0, 0, 0, 0], ![1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 590, with all original external and node cotangent powers. -/
def term590 : CotangentTerm 2 (Fin 4) :=
  ⟨expression253, (![1, 0, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 591, with all original external and node cotangent powers. -/
def term591 : CotangentTerm 2 (Fin 4) :=
  ⟨expression253, (![0, 1, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 592, with all original external and node cotangent powers. -/
def term592 : CotangentTerm 2 (Fin 4) :=
  ⟨expression253, (![0, 0, 1, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 593, with all original external and node cotangent powers. -/
def term593 : CotangentTerm 2 (Fin 4) :=
  ⟨expression253, (![0, 0, 0, 0, 0], ![1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 594, with all original external and node cotangent powers. -/
def term594 : CotangentTerm 2 (Fin 4) :=
  ⟨expression254, (![1, 0, 0, 0, 0, 0], ![0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 595, with all original external and node cotangent powers. -/
def term595 : CotangentTerm 2 (Fin 4) :=
  ⟨expression254, (![0, 1, 0, 0, 0, 0], ![0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 596, with all original external and node cotangent powers. -/
def term596 : CotangentTerm 2 (Fin 4) :=
  ⟨expression254, (![0, 0, 1, 0, 0, 0], ![0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 597, with all original external and node cotangent powers. -/
def term597 : CotangentTerm 2 (Fin 4) :=
  ⟨expression254, (![0, 0, 0, 1, 0, 0], ![0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 598, with all original external and node cotangent powers. -/
def term598 : CotangentTerm 2 (Fin 4) :=
  ⟨expression255, (![0, 0, 0], ![1, 0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 599, with all original external and node cotangent powers. -/
def term599 : CotangentTerm 2 (Fin 4) :=
  ⟨expression255, (![0, 0, 0], ![0, 1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 600, with all original external and node cotangent powers. -/
def term600 : CotangentTerm 2 (Fin 4) :=
  ⟨expression255, (![0, 0, 0], ![0, 0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 601, with all original external and node cotangent powers. -/
def term601 : CotangentTerm 2 (Fin 4) :=
  ⟨expression255, (![0, 0, 0], ![0, 0, 0, 1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 602, with all original external and node cotangent powers. -/
def term602 : CotangentTerm 2 (Fin 4) :=
  ⟨expression256, (![1, 0, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 603, with all original external and node cotangent powers. -/
def term603 : CotangentTerm 2 (Fin 4) :=
  ⟨expression256, (![0, 0, 0, 0], ![1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 604, with all original external and node cotangent powers. -/
def term604 : CotangentTerm 2 (Fin 4) :=
  ⟨expression256, (![0, 0, 0, 0], ![0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 605, with all original external and node cotangent powers. -/
def term605 : CotangentTerm 2 (Fin 4) :=
  ⟨expression256, (![0, 0, 0, 0], ![0, 0, 1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 606, with all original external and node cotangent powers. -/
def term606 : CotangentTerm 2 (Fin 4) :=
  ⟨expression257, (![1, 0, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 607, with all original external and node cotangent powers. -/
def term607 : CotangentTerm 2 (Fin 4) :=
  ⟨expression257, (![0, 0, 0, 0], ![1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 608, with all original external and node cotangent powers. -/
def term608 : CotangentTerm 2 (Fin 4) :=
  ⟨expression257, (![0, 0, 0, 0], ![0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 609, with all original external and node cotangent powers. -/
def term609 : CotangentTerm 2 (Fin 4) :=
  ⟨expression257, (![0, 0, 0, 0], ![0, 0, 1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 610, with all original external and node cotangent powers. -/
def term610 : CotangentTerm 2 (Fin 4) :=
  ⟨expression258, (![1, 0, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 611, with all original external and node cotangent powers. -/
def term611 : CotangentTerm 2 (Fin 4) :=
  ⟨expression258, (![0, 1, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 612, with all original external and node cotangent powers. -/
def term612 : CotangentTerm 2 (Fin 4) :=
  ⟨expression258, (![0, 0, 0, 0, 0], ![1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 613, with all original external and node cotangent powers. -/
def term613 : CotangentTerm 2 (Fin 4) :=
  ⟨expression258, (![0, 0, 0, 0, 0], ![0, 1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 614, with all original external and node cotangent powers. -/
def term614 : CotangentTerm 2 (Fin 4) :=
  ⟨expression259, (![1, 0, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 615, with all original external and node cotangent powers. -/
def term615 : CotangentTerm 2 (Fin 4) :=
  ⟨expression259, (![0, 0, 0, 0], ![1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 616, with all original external and node cotangent powers. -/
def term616 : CotangentTerm 2 (Fin 4) :=
  ⟨expression259, (![0, 0, 0, 0], ![0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 617, with all original external and node cotangent powers. -/
def term617 : CotangentTerm 2 (Fin 4) :=
  ⟨expression259, (![0, 0, 0, 0], ![0, 0, 1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 618, with all original external and node cotangent powers. -/
def term618 : CotangentTerm 2 (Fin 4) :=
  ⟨expression260, (![1, 0, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 619, with all original external and node cotangent powers. -/
def term619 : CotangentTerm 2 (Fin 4) :=
  ⟨expression260, (![0, 1, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 620, with all original external and node cotangent powers. -/
def term620 : CotangentTerm 2 (Fin 4) :=
  ⟨expression260, (![0, 0, 0, 0, 0], ![1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 621, with all original external and node cotangent powers. -/
def term621 : CotangentTerm 2 (Fin 4) :=
  ⟨expression260, (![0, 0, 0, 0, 0], ![0, 1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 622, with all original external and node cotangent powers. -/
def term622 : CotangentTerm 2 (Fin 4) :=
  ⟨expression261, (![1, 0, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 623, with all original external and node cotangent powers. -/
def term623 : CotangentTerm 2 (Fin 4) :=
  ⟨expression261, (![0, 1, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 624, with all original external and node cotangent powers. -/
def term624 : CotangentTerm 2 (Fin 4) :=
  ⟨expression261, (![0, 0, 0, 0, 0], ![1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 625, with all original external and node cotangent powers. -/
def term625 : CotangentTerm 2 (Fin 4) :=
  ⟨expression261, (![0, 0, 0, 0, 0], ![0, 1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 626, with all original external and node cotangent powers. -/
def term626 : CotangentTerm 2 (Fin 4) :=
  ⟨expression262, (![1, 0, 0, 0, 0, 0], ![0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 627, with all original external and node cotangent powers. -/
def term627 : CotangentTerm 2 (Fin 4) :=
  ⟨expression262, (![0, 1, 0, 0, 0, 0], ![0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 628, with all original external and node cotangent powers. -/
def term628 : CotangentTerm 2 (Fin 4) :=
  ⟨expression262, (![0, 0, 1, 0, 0, 0], ![0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 629, with all original external and node cotangent powers. -/
def term629 : CotangentTerm 2 (Fin 4) :=
  ⟨expression262, (![0, 0, 0, 0, 0, 0], ![1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 630, with all original external and node cotangent powers. -/
def term630 : CotangentTerm 2 (Fin 4) :=
  ⟨expression263, (![1, 0, 0, 0], ![0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 631, with all original external and node cotangent powers. -/
def term631 : CotangentTerm 2 (Fin 4) :=
  ⟨expression263, (![0, 0, 0, 0], ![1, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 632, with all original external and node cotangent powers. -/
def term632 : CotangentTerm 2 (Fin 4) :=
  ⟨expression263, (![0, 0, 0, 0], ![0, 1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 633, with all original external and node cotangent powers. -/
def term633 : CotangentTerm 2 (Fin 4) :=
  ⟨expression263, (![0, 0, 0, 0], ![0, 0, 1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 634, with all original external and node cotangent powers. -/
def term634 : CotangentTerm 2 (Fin 4) :=
  ⟨expression264, (![1, 0, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 635, with all original external and node cotangent powers. -/
def term635 : CotangentTerm 2 (Fin 4) :=
  ⟨expression264, (![0, 1, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 636, with all original external and node cotangent powers. -/
def term636 : CotangentTerm 2 (Fin 4) :=
  ⟨expression264, (![0, 0, 0, 0, 0], ![1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 637, with all original external and node cotangent powers. -/
def term637 : CotangentTerm 2 (Fin 4) :=
  ⟨expression264, (![0, 0, 0, 0, 0], ![0, 1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 638, with all original external and node cotangent powers. -/
def term638 : CotangentTerm 2 (Fin 4) :=
  ⟨expression265, (![1, 0, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 639, with all original external and node cotangent powers. -/
def term639 : CotangentTerm 2 (Fin 4) :=
  ⟨expression265, (![0, 1, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 640, with all original external and node cotangent powers. -/
def term640 : CotangentTerm 2 (Fin 4) :=
  ⟨expression265, (![0, 0, 0, 0, 0], ![1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 641, with all original external and node cotangent powers. -/
def term641 : CotangentTerm 2 (Fin 4) :=
  ⟨expression265, (![0, 0, 0, 0, 0], ![0, 1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 642, with all original external and node cotangent powers. -/
def term642 : CotangentTerm 2 (Fin 4) :=
  ⟨expression266, (![1, 0, 0, 0, 0, 0], ![0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 643, with all original external and node cotangent powers. -/
def term643 : CotangentTerm 2 (Fin 4) :=
  ⟨expression266, (![0, 1, 0, 0, 0, 0], ![0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 644, with all original external and node cotangent powers. -/
def term644 : CotangentTerm 2 (Fin 4) :=
  ⟨expression266, (![0, 0, 1, 0, 0, 0], ![0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 645, with all original external and node cotangent powers. -/
def term645 : CotangentTerm 2 (Fin 4) :=
  ⟨expression266, (![0, 0, 0, 0, 0, 0], ![1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 646, with all original external and node cotangent powers. -/
def term646 : CotangentTerm 2 (Fin 4) :=
  ⟨expression267, (![1, 0, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 647, with all original external and node cotangent powers. -/
def term647 : CotangentTerm 2 (Fin 4) :=
  ⟨expression267, (![0, 1, 0, 0, 0], ![0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 648, with all original external and node cotangent powers. -/
def term648 : CotangentTerm 2 (Fin 4) :=
  ⟨expression267, (![0, 0, 0, 0, 0], ![1, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 649, with all original external and node cotangent powers. -/
def term649 : CotangentTerm 2 (Fin 4) :=
  ⟨expression267, (![0, 0, 0, 0, 0], ![0, 1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 650, with all original external and node cotangent powers. -/
def term650 : CotangentTerm 2 (Fin 4) :=
  ⟨expression268, (![1, 0, 0, 0, 0, 0], ![0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 651, with all original external and node cotangent powers. -/
def term651 : CotangentTerm 2 (Fin 4) :=
  ⟨expression268, (![0, 1, 0, 0, 0, 0], ![0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 652, with all original external and node cotangent powers. -/
def term652 : CotangentTerm 2 (Fin 4) :=
  ⟨expression268, (![0, 0, 1, 0, 0, 0], ![0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 653, with all original external and node cotangent powers. -/
def term653 : CotangentTerm 2 (Fin 4) :=
  ⟨expression268, (![0, 0, 0, 0, 0, 0], ![1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 654, with all original external and node cotangent powers. -/
def term654 : CotangentTerm 2 (Fin 4) :=
  ⟨expression269, (![1, 0, 0, 0, 0, 0], ![0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 655, with all original external and node cotangent powers. -/
def term655 : CotangentTerm 2 (Fin 4) :=
  ⟨expression269, (![0, 1, 0, 0, 0, 0], ![0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 656, with all original external and node cotangent powers. -/
def term656 : CotangentTerm 2 (Fin 4) :=
  ⟨expression269, (![0, 0, 1, 0, 0, 0], ![0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 657, with all original external and node cotangent powers. -/
def term657 : CotangentTerm 2 (Fin 4) :=
  ⟨expression269, (![0, 0, 0, 0, 0, 0], ![1, 0]), (inferInstance, inferInstance)⟩

/-- Held column 658, with all original external and node cotangent powers. -/
def term658 : CotangentTerm 2 (Fin 4) :=
  ⟨expression270, (![1, 0, 0, 0, 0, 0, 0], ![0]), (inferInstance, inferInstance)⟩

/-- Held column 659, with all original external and node cotangent powers. -/
def term659 : CotangentTerm 2 (Fin 4) :=
  ⟨expression270, (![0, 1, 0, 0, 0, 0, 0], ![0]), (inferInstance, inferInstance)⟩

/-- Held column 660, with all original external and node cotangent powers. -/
def term660 : CotangentTerm 2 (Fin 4) :=
  ⟨expression270, (![0, 0, 1, 0, 0, 0, 0], ![0]), (inferInstance, inferInstance)⟩

/-- Held column 661, with all original external and node cotangent powers. -/
def term661 : CotangentTerm 2 (Fin 4) :=
  ⟨expression270, (![0, 0, 0, 1, 0, 0, 0], ![0]), (inferInstance, inferInstance)⟩

/-- Held column 662, with all original external and node cotangent powers. -/
def term662 : CotangentTerm 2 (Fin 4) :=
  ⟨expression271, ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 663, with all original external and node cotangent powers. -/
def term663 : CotangentTerm 2 (Fin 4) :=
  ⟨expression272, ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 664, with all original external and node cotangent powers. -/
def term664 : CotangentTerm 2 (Fin 4) :=
  ⟨expression273, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 665, with all original external and node cotangent powers. -/
def term665 : CotangentTerm 2 (Fin 4) :=
  ⟨expression274, ((![0, 0, 0], ![0, 0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 666, with all original external and node cotangent powers. -/
def term666 : CotangentTerm 2 (Fin 4) :=
  ⟨expression275, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 667, with all original external and node cotangent powers. -/
def term667 : CotangentTerm 2 (Fin 4) :=
  ⟨expression276, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 668, with all original external and node cotangent powers. -/
def term668 : CotangentTerm 2 (Fin 4) :=
  ⟨expression277, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 669, with all original external and node cotangent powers. -/
def term669 : CotangentTerm 2 (Fin 4) :=
  ⟨expression278, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 670, with all original external and node cotangent powers. -/
def term670 : CotangentTerm 2 (Fin 4) :=
  ⟨expression279, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 671, with all original external and node cotangent powers. -/
def term671 : CotangentTerm 2 (Fin 4) :=
  ⟨expression280, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 672, with all original external and node cotangent powers. -/
def term672 : CotangentTerm 2 (Fin 4) :=
  ⟨expression281, (![0, 0, 0], (![0, 0, 0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 673, with all original external and node cotangent powers. -/
def term673 : CotangentTerm 2 (Fin 4) :=
  ⟨expression282, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 674, with all original external and node cotangent powers. -/
def term674 : CotangentTerm 2 (Fin 4) :=
  ⟨expression283, ((![0, 0, 0], ![0, 0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 675, with all original external and node cotangent powers. -/
def term675 : CotangentTerm 2 (Fin 4) :=
  ⟨expression284, (![0, 0, 0, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 676, with all original external and node cotangent powers. -/
def term676 : CotangentTerm 2 (Fin 4) :=
  ⟨expression285, ((![0, 0, 0], ![0, 0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 677, with all original external and node cotangent powers. -/
def term677 : CotangentTerm 2 (Fin 4) :=
  ⟨expression286, (![0, 0, 0, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 678, with all original external and node cotangent powers. -/
def term678 : CotangentTerm 2 (Fin 4) :=
  ⟨expression287, ((![0, 0, 0], ![0, 0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 679, with all original external and node cotangent powers. -/
def term679 : CotangentTerm 2 (Fin 4) :=
  ⟨expression288, (![0, 0, 0, 0, 0], (![0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 680, with all original external and node cotangent powers. -/
def term680 : CotangentTerm 2 (Fin 4) :=
  ⟨expression289, ((![0, 0, 0], ![0, 0, 0, 0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 681, with all original external and node cotangent powers. -/
def term681 : CotangentTerm 2 (Fin 4) :=
  ⟨expression290, ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 682, with all original external and node cotangent powers. -/
def term682 : CotangentTerm 2 (Fin 4) :=
  ⟨expression291, ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 683, with all original external and node cotangent powers. -/
def term683 : CotangentTerm 2 (Fin 4) :=
  ⟨expression292, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 684, with all original external and node cotangent powers. -/
def term684 : CotangentTerm 2 (Fin 4) :=
  ⟨expression293, ((![0, 0, 0], ![0, 0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 685, with all original external and node cotangent powers. -/
def term685 : CotangentTerm 2 (Fin 4) :=
  ⟨expression294, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 686, with all original external and node cotangent powers. -/
def term686 : CotangentTerm 2 (Fin 4) :=
  ⟨expression295, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 687, with all original external and node cotangent powers. -/
def term687 : CotangentTerm 2 (Fin 4) :=
  ⟨expression296, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 688, with all original external and node cotangent powers. -/
def term688 : CotangentTerm 2 (Fin 4) :=
  ⟨expression297, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 689, with all original external and node cotangent powers. -/
def term689 : CotangentTerm 2 (Fin 4) :=
  ⟨expression298, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 690, with all original external and node cotangent powers. -/
def term690 : CotangentTerm 2 (Fin 4) :=
  ⟨expression299, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 691, with all original external and node cotangent powers. -/
def term691 : CotangentTerm 2 (Fin 4) :=
  ⟨expression300, (![0, 0, 0], (![0, 0, 0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 692, with all original external and node cotangent powers. -/
def term692 : CotangentTerm 2 (Fin 4) :=
  ⟨expression301, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 693, with all original external and node cotangent powers. -/
def term693 : CotangentTerm 2 (Fin 4) :=
  ⟨expression302, ((![0, 0, 0], ![0, 0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 694, with all original external and node cotangent powers. -/
def term694 : CotangentTerm 2 (Fin 4) :=
  ⟨expression303, (![0, 0, 0, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 695, with all original external and node cotangent powers. -/
def term695 : CotangentTerm 2 (Fin 4) :=
  ⟨expression304, ((![0, 0, 0], ![0, 0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 696, with all original external and node cotangent powers. -/
def term696 : CotangentTerm 2 (Fin 4) :=
  ⟨expression305, (![0, 0, 0, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 697, with all original external and node cotangent powers. -/
def term697 : CotangentTerm 2 (Fin 4) :=
  ⟨expression306, ((![0, 0, 0], ![0, 0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 698, with all original external and node cotangent powers. -/
def term698 : CotangentTerm 2 (Fin 4) :=
  ⟨expression307, (![0, 0, 0, 0, 0], (![0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 699, with all original external and node cotangent powers. -/
def term699 : CotangentTerm 2 (Fin 4) :=
  ⟨expression308, ((![0, 0, 0], ![0, 0, 0, 0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 700, with all original external and node cotangent powers. -/
def term700 : CotangentTerm 2 (Fin 4) :=
  ⟨expression309, ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 701, with all original external and node cotangent powers. -/
def term701 : CotangentTerm 2 (Fin 4) :=
  ⟨expression310, ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 702, with all original external and node cotangent powers. -/
def term702 : CotangentTerm 2 (Fin 4) :=
  ⟨expression311, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 703, with all original external and node cotangent powers. -/
def term703 : CotangentTerm 2 (Fin 4) :=
  ⟨expression312, ((![0, 0, 0], ![0, 0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 704, with all original external and node cotangent powers. -/
def term704 : CotangentTerm 2 (Fin 4) :=
  ⟨expression313, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 705, with all original external and node cotangent powers. -/
def term705 : CotangentTerm 2 (Fin 4) :=
  ⟨expression314, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 706, with all original external and node cotangent powers. -/
def term706 : CotangentTerm 2 (Fin 4) :=
  ⟨expression315, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 707, with all original external and node cotangent powers. -/
def term707 : CotangentTerm 2 (Fin 4) :=
  ⟨expression316, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 708, with all original external and node cotangent powers. -/
def term708 : CotangentTerm 2 (Fin 4) :=
  ⟨expression317, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 709, with all original external and node cotangent powers. -/
def term709 : CotangentTerm 2 (Fin 4) :=
  ⟨expression318, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 710, with all original external and node cotangent powers. -/
def term710 : CotangentTerm 2 (Fin 4) :=
  ⟨expression319, (![0, 0, 0], (![0, 0, 0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 711, with all original external and node cotangent powers. -/
def term711 : CotangentTerm 2 (Fin 4) :=
  ⟨expression320, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 712, with all original external and node cotangent powers. -/
def term712 : CotangentTerm 2 (Fin 4) :=
  ⟨expression321, ((![0, 0, 0], ![0, 0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 713, with all original external and node cotangent powers. -/
def term713 : CotangentTerm 2 (Fin 4) :=
  ⟨expression322, (![0, 0, 0, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 714, with all original external and node cotangent powers. -/
def term714 : CotangentTerm 2 (Fin 4) :=
  ⟨expression323, ((![0, 0, 0], ![0, 0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 715, with all original external and node cotangent powers. -/
def term715 : CotangentTerm 2 (Fin 4) :=
  ⟨expression324, (![0, 0, 0, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 716, with all original external and node cotangent powers. -/
def term716 : CotangentTerm 2 (Fin 4) :=
  ⟨expression325, ((![0, 0, 0], ![0, 0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 717, with all original external and node cotangent powers. -/
def term717 : CotangentTerm 2 (Fin 4) :=
  ⟨expression326, (![0, 0, 0, 0, 0], (![0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 718, with all original external and node cotangent powers. -/
def term718 : CotangentTerm 2 (Fin 4) :=
  ⟨expression327, ((![0, 0, 0], ![0, 0, 0, 0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 719, with all original external and node cotangent powers. -/
def term719 : CotangentTerm 2 (Fin 4) :=
  ⟨expression328, ((![0, 0, 0, 0], ![0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 720, with all original external and node cotangent powers. -/
def term720 : CotangentTerm 2 (Fin 4) :=
  ⟨expression329, (![0, 0, 0, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 721, with all original external and node cotangent powers. -/
def term721 : CotangentTerm 2 (Fin 4) :=
  ⟨expression330, (![0, 0, 0, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 722, with all original external and node cotangent powers. -/
def term722 : CotangentTerm 2 (Fin 4) :=
  ⟨expression331, (![0, 0, 0, 0], (![0, 0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 723, with all original external and node cotangent powers. -/
def term723 : CotangentTerm 2 (Fin 4) :=
  ⟨expression332, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 724, with all original external and node cotangent powers. -/
def term724 : CotangentTerm 2 (Fin 4) :=
  ⟨expression333, ((![0, 0, 0, 0], ![0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 725, with all original external and node cotangent powers. -/
def term725 : CotangentTerm 2 (Fin 4) :=
  ⟨expression334, (![0, 0, 0, 0], (![0, 0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 726, with all original external and node cotangent powers. -/
def term726 : CotangentTerm 2 (Fin 4) :=
  ⟨expression335, ((![0, 0, 0, 0], ![0, 0, 0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 727, with all original external and node cotangent powers. -/
def term727 : CotangentTerm 2 (Fin 4) :=
  ⟨expression336, ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 728, with all original external and node cotangent powers. -/
def term728 : CotangentTerm 2 (Fin 4) :=
  ⟨expression337, ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 729, with all original external and node cotangent powers. -/
def term729 : CotangentTerm 2 (Fin 4) :=
  ⟨expression338, ((![0, 0, 0], ![0, 0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 730, with all original external and node cotangent powers. -/
def term730 : CotangentTerm 2 (Fin 4) :=
  ⟨expression339, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 731, with all original external and node cotangent powers. -/
def term731 : CotangentTerm 2 (Fin 4) :=
  ⟨expression340, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 732, with all original external and node cotangent powers. -/
def term732 : CotangentTerm 2 (Fin 4) :=
  ⟨expression341, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 733, with all original external and node cotangent powers. -/
def term733 : CotangentTerm 2 (Fin 4) :=
  ⟨expression342, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 734, with all original external and node cotangent powers. -/
def term734 : CotangentTerm 2 (Fin 4) :=
  ⟨expression343, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 735, with all original external and node cotangent powers. -/
def term735 : CotangentTerm 2 (Fin 4) :=
  ⟨expression344, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 736, with all original external and node cotangent powers. -/
def term736 : CotangentTerm 2 (Fin 4) :=
  ⟨expression345, (![0, 0, 0], (![0, 0, 0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 737, with all original external and node cotangent powers. -/
def term737 : CotangentTerm 2 (Fin 4) :=
  ⟨expression346, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 738, with all original external and node cotangent powers. -/
def term738 : CotangentTerm 2 (Fin 4) :=
  ⟨expression347, ((![0, 0, 0], ![0, 0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 739, with all original external and node cotangent powers. -/
def term739 : CotangentTerm 2 (Fin 4) :=
  ⟨expression348, (![0, 0, 0, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 740, with all original external and node cotangent powers. -/
def term740 : CotangentTerm 2 (Fin 4) :=
  ⟨expression349, ((![0, 0, 0], ![0, 0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 741, with all original external and node cotangent powers. -/
def term741 : CotangentTerm 2 (Fin 4) :=
  ⟨expression350, (![0, 0, 0, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 742, with all original external and node cotangent powers. -/
def term742 : CotangentTerm 2 (Fin 4) :=
  ⟨expression351, ((![0, 0, 0], ![0, 0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 743, with all original external and node cotangent powers. -/
def term743 : CotangentTerm 2 (Fin 4) :=
  ⟨expression352, (![0, 0, 0, 0, 0], (![0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 744, with all original external and node cotangent powers. -/
def term744 : CotangentTerm 2 (Fin 4) :=
  ⟨expression353, ((![0, 0, 0], ![0, 0, 0, 0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 745, with all original external and node cotangent powers. -/
def term745 : CotangentTerm 2 (Fin 4) :=
  ⟨expression354, ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 746, with all original external and node cotangent powers. -/
def term746 : CotangentTerm 2 (Fin 4) :=
  ⟨expression355, ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 747, with all original external and node cotangent powers. -/
def term747 : CotangentTerm 2 (Fin 4) :=
  ⟨expression356, ((![0, 0, 0], ![0, 0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 748, with all original external and node cotangent powers. -/
def term748 : CotangentTerm 2 (Fin 4) :=
  ⟨expression357, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 749, with all original external and node cotangent powers. -/
def term749 : CotangentTerm 2 (Fin 4) :=
  ⟨expression358, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 750, with all original external and node cotangent powers. -/
def term750 : CotangentTerm 2 (Fin 4) :=
  ⟨expression359, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 751, with all original external and node cotangent powers. -/
def term751 : CotangentTerm 2 (Fin 4) :=
  ⟨expression360, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 752, with all original external and node cotangent powers. -/
def term752 : CotangentTerm 2 (Fin 4) :=
  ⟨expression361, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 753, with all original external and node cotangent powers. -/
def term753 : CotangentTerm 2 (Fin 4) :=
  ⟨expression362, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 754, with all original external and node cotangent powers. -/
def term754 : CotangentTerm 2 (Fin 4) :=
  ⟨expression363, (![0, 0, 0], (![0, 0, 0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 755, with all original external and node cotangent powers. -/
def term755 : CotangentTerm 2 (Fin 4) :=
  ⟨expression364, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 756, with all original external and node cotangent powers. -/
def term756 : CotangentTerm 2 (Fin 4) :=
  ⟨expression365, ((![0, 0, 0], ![0, 0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 757, with all original external and node cotangent powers. -/
def term757 : CotangentTerm 2 (Fin 4) :=
  ⟨expression366, (![0, 0, 0, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 758, with all original external and node cotangent powers. -/
def term758 : CotangentTerm 2 (Fin 4) :=
  ⟨expression367, ((![0, 0, 0], ![0, 0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 759, with all original external and node cotangent powers. -/
def term759 : CotangentTerm 2 (Fin 4) :=
  ⟨expression368, (![0, 0, 0, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 760, with all original external and node cotangent powers. -/
def term760 : CotangentTerm 2 (Fin 4) :=
  ⟨expression369, ((![0, 0, 0], ![0, 0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 761, with all original external and node cotangent powers. -/
def term761 : CotangentTerm 2 (Fin 4) :=
  ⟨expression370, (![0, 0, 0, 0, 0], (![0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 762, with all original external and node cotangent powers. -/
def term762 : CotangentTerm 2 (Fin 4) :=
  ⟨expression371, ((![0, 0, 0], ![0, 0, 0, 0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 763, with all original external and node cotangent powers. -/
def term763 : CotangentTerm 2 (Fin 4) :=
  ⟨expression372, ((![0, 0, 0, 0], ![0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 764, with all original external and node cotangent powers. -/
def term764 : CotangentTerm 2 (Fin 4) :=
  ⟨expression373, (![0, 0, 0, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 765, with all original external and node cotangent powers. -/
def term765 : CotangentTerm 2 (Fin 4) :=
  ⟨expression374, (![0, 0, 0, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 766, with all original external and node cotangent powers. -/
def term766 : CotangentTerm 2 (Fin 4) :=
  ⟨expression375, (![0, 0, 0, 0], (![0, 0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 767, with all original external and node cotangent powers. -/
def term767 : CotangentTerm 2 (Fin 4) :=
  ⟨expression376, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 768, with all original external and node cotangent powers. -/
def term768 : CotangentTerm 2 (Fin 4) :=
  ⟨expression377, ((![0, 0, 0, 0], ![0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 769, with all original external and node cotangent powers. -/
def term769 : CotangentTerm 2 (Fin 4) :=
  ⟨expression378, (![0, 0, 0, 0], (![0, 0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 770, with all original external and node cotangent powers. -/
def term770 : CotangentTerm 2 (Fin 4) :=
  ⟨expression379, ((![0, 0, 0, 0], ![0, 0, 0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 771, with all original external and node cotangent powers. -/
def term771 : CotangentTerm 2 (Fin 4) :=
  ⟨expression380, ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 772, with all original external and node cotangent powers. -/
def term772 : CotangentTerm 2 (Fin 4) :=
  ⟨expression381, ((![0, 0, 0], ![0, 0, 0]), ![0, 0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 773, with all original external and node cotangent powers. -/
def term773 : CotangentTerm 2 (Fin 4) :=
  ⟨expression382, ((![0, 0, 0], ![0, 0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 774, with all original external and node cotangent powers. -/
def term774 : CotangentTerm 2 (Fin 4) :=
  ⟨expression383, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 775, with all original external and node cotangent powers. -/
def term775 : CotangentTerm 2 (Fin 4) :=
  ⟨expression384, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 776, with all original external and node cotangent powers. -/
def term776 : CotangentTerm 2 (Fin 4) :=
  ⟨expression385, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 777, with all original external and node cotangent powers. -/
def term777 : CotangentTerm 2 (Fin 4) :=
  ⟨expression386, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 778, with all original external and node cotangent powers. -/
def term778 : CotangentTerm 2 (Fin 4) :=
  ⟨expression387, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 779, with all original external and node cotangent powers. -/
def term779 : CotangentTerm 2 (Fin 4) :=
  ⟨expression388, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 780, with all original external and node cotangent powers. -/
def term780 : CotangentTerm 2 (Fin 4) :=
  ⟨expression389, (![0, 0, 0], (![0, 0, 0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 781, with all original external and node cotangent powers. -/
def term781 : CotangentTerm 2 (Fin 4) :=
  ⟨expression390, (![0, 0, 0], (![0, 0, 0], ![0, 0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 782, with all original external and node cotangent powers. -/
def term782 : CotangentTerm 2 (Fin 4) :=
  ⟨expression391, ((![0, 0, 0], ![0, 0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 783, with all original external and node cotangent powers. -/
def term783 : CotangentTerm 2 (Fin 4) :=
  ⟨expression392, (![0, 0, 0, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 784, with all original external and node cotangent powers. -/
def term784 : CotangentTerm 2 (Fin 4) :=
  ⟨expression393, ((![0, 0, 0], ![0, 0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 785, with all original external and node cotangent powers. -/
def term785 : CotangentTerm 2 (Fin 4) :=
  ⟨expression394, (![0, 0, 0, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 786, with all original external and node cotangent powers. -/
def term786 : CotangentTerm 2 (Fin 4) :=
  ⟨expression395, ((![0, 0, 0], ![0, 0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 787, with all original external and node cotangent powers. -/
def term787 : CotangentTerm 2 (Fin 4) :=
  ⟨expression396, (![0, 0, 0, 0, 0], (![0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 788, with all original external and node cotangent powers. -/
def term788 : CotangentTerm 2 (Fin 4) :=
  ⟨expression397, ((![0, 0, 0], ![0, 0, 0, 0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 789, with all original external and node cotangent powers. -/
def term789 : CotangentTerm 2 (Fin 4) :=
  ⟨expression398, ((![0, 0, 0, 0], ![0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 790, with all original external and node cotangent powers. -/
def term790 : CotangentTerm 2 (Fin 4) :=
  ⟨expression399, (![0, 0, 0, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 791, with all original external and node cotangent powers. -/
def term791 : CotangentTerm 2 (Fin 4) :=
  ⟨expression400, (![0, 0, 0, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 792, with all original external and node cotangent powers. -/
def term792 : CotangentTerm 2 (Fin 4) :=
  ⟨expression401, (![0, 0, 0, 0], (![0, 0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 793, with all original external and node cotangent powers. -/
def term793 : CotangentTerm 2 (Fin 4) :=
  ⟨expression402, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 794, with all original external and node cotangent powers. -/
def term794 : CotangentTerm 2 (Fin 4) :=
  ⟨expression403, ((![0, 0, 0, 0], ![0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 795, with all original external and node cotangent powers. -/
def term795 : CotangentTerm 2 (Fin 4) :=
  ⟨expression404, (![0, 0, 0, 0], (![0, 0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 796, with all original external and node cotangent powers. -/
def term796 : CotangentTerm 2 (Fin 4) :=
  ⟨expression405, ((![0, 0, 0, 0], ![0, 0, 0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 797, with all original external and node cotangent powers. -/
def term797 : CotangentTerm 2 (Fin 4) :=
  ⟨expression406, ((![0, 0, 0, 0], ![0, 0, 0]), ![0, 0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 798, with all original external and node cotangent powers. -/
def term798 : CotangentTerm 2 (Fin 4) :=
  ⟨expression407, (![0, 0, 0, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 799, with all original external and node cotangent powers. -/
def term799 : CotangentTerm 2 (Fin 4) :=
  ⟨expression408, (![0, 0, 0, 0], (![0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 800, with all original external and node cotangent powers. -/
def term800 : CotangentTerm 2 (Fin 4) :=
  ⟨expression409, (![0, 0, 0, 0], (![0, 0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 801, with all original external and node cotangent powers. -/
def term801 : CotangentTerm 2 (Fin 4) :=
  ⟨expression410, (![0, 0, 0], (![0, 0, 0, 0], ![0, 0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 802, with all original external and node cotangent powers. -/
def term802 : CotangentTerm 2 (Fin 4) :=
  ⟨expression411, ((![0, 0, 0, 0], ![0, 0, 0, 0]), ![0, 0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 803, with all original external and node cotangent powers. -/
def term803 : CotangentTerm 2 (Fin 4) :=
  ⟨expression412, (![0, 0, 0, 0], (![0, 0, 0, 0], ![0, 0])), (inferInstance, (inferInstance,
    inferInstance))⟩

/-- Held column 804, with all original external and node cotangent powers. -/
def term804 : CotangentTerm 2 (Fin 4) :=
  ⟨expression413, ((![0, 0, 0, 0], ![0, 0, 0, 0, 0]), ![0]), ((inferInstance, inferInstance),
    inferInstance)⟩

/-- Held column 805, with all original external and node cotangent powers. -/
def term805 : CotangentTerm 2 (Fin 4) :=
  ⟨expression414, (![0, 0, 0], ![0, 0, 0, 0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 806, with all original external and node cotangent powers. -/
def term806 : CotangentTerm 2 (Fin 4) :=
  ⟨expression415, (![0, 0, 0], ![0, 0, 0, 0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 807, with all original external and node cotangent powers. -/
def term807 : CotangentTerm 2 (Fin 4) :=
  ⟨expression416, (![0, 0, 0], ![0, 0, 0, 0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 808, with all original external and node cotangent powers. -/
def term808 : CotangentTerm 2 (Fin 4) :=
  ⟨expression417, (![0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 809, with all original external and node cotangent powers. -/
def term809 : CotangentTerm 2 (Fin 4) :=
  ⟨expression418, (![0, 0, 0], ![0, 0, 0, 0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 810, with all original external and node cotangent powers. -/
def term810 : CotangentTerm 2 (Fin 4) :=
  ⟨expression419, (![0, 0, 0], ![0, 0, 0, 0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 811, with all original external and node cotangent powers. -/
def term811 : CotangentTerm 2 (Fin 4) :=
  ⟨expression420, (![0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 812, with all original external and node cotangent powers. -/
def term812 : CotangentTerm 2 (Fin 4) :=
  ⟨expression421, (![0, 0, 0], ![0, 0, 0, 0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 813, with all original external and node cotangent powers. -/
def term813 : CotangentTerm 2 (Fin 4) :=
  ⟨expression422, (![0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- Held column 814, with all original external and node cotangent powers. -/
def term814 : CotangentTerm 2 (Fin 4) :=
  ⟨expression423, (![0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]), (inferInstance, inferInstance)⟩

/-- All 815 actual constructions in exactly the existing column order. -/
def term (i : Fin 815) : CotangentTerm 2 (Fin 4) :=
  (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if i.val <
    25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then term0
    else (if i.val < 2 then term1 else term2)) else (if i.val < 4 then term3 else (if i.val < 5
    then term4 else term5))) else (if i.val < 9 then (if i.val < 7 then term6 else (if i.val < 8
    then term7 else term8)) else (if i.val < 10 then term9 else (if i.val < 11 then term10 else
    term11)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then term12 else (if
    i.val < 14 then term13 else term14)) else (if i.val < 16 then term15 else (if i.val < 17
    then term16 else term17))) else (if i.val < 21 then (if i.val < 19 then term18 else (if
    i.val < 20 then term19 else term20)) else (if i.val < 23 then (if i.val < 22 then term21
    else term22) else (if i.val < 24 then term23 else term24))))) else (if i.val < 37 then (if
    i.val < 31 then (if i.val < 28 then (if i.val < 26 then term25 else (if i.val < 27 then
    term26 else term27)) else (if i.val < 29 then term28 else (if i.val < 30 then term29 else
    term30))) else (if i.val < 34 then (if i.val < 32 then term31 else (if i.val < 33 then
    term32 else term33)) else (if i.val < 35 then term34 else (if i.val < 36 then term35 else
    term36)))) else (if i.val < 43 then (if i.val < 40 then (if i.val < 38 then term37 else (if
    i.val < 39 then term38 else term39)) else (if i.val < 41 then term40 else (if i.val < 42
    then term41 else term42))) else (if i.val < 46 then (if i.val < 44 then term43 else (if
    i.val < 45 then term44 else term45)) else (if i.val < 48 then (if i.val < 47 then term46
    else term47) else (if i.val < 49 then term48 else term49)))))) else (if i.val < 75 then (if
    i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if i.val < 51 then term50 else (if
    i.val < 52 then term51 else term52)) else (if i.val < 54 then term53 else (if i.val < 55
    then term54 else term55))) else (if i.val < 59 then (if i.val < 57 then term56 else (if
    i.val < 58 then term57 else term58)) else (if i.val < 60 then term59 else (if i.val < 61
    then term60 else term61)))) else (if i.val < 68 then (if i.val < 65 then (if i.val < 63 then
    term62 else (if i.val < 64 then term63 else term64)) else (if i.val < 66 then term65 else
    (if i.val < 67 then term66 else term67))) else (if i.val < 71 then (if i.val < 69 then
    term68 else (if i.val < 70 then term69 else term70)) else (if i.val < 73 then (if i.val < 72
    then term71 else term72) else (if i.val < 74 then term73 else term74))))) else (if i.val <
    88 then (if i.val < 81 then (if i.val < 78 then (if i.val < 76 then term75 else (if i.val <
    77 then term76 else term77)) else (if i.val < 79 then term78 else (if i.val < 80 then term79
    else term80))) else (if i.val < 84 then (if i.val < 82 then term81 else (if i.val < 83 then
    term82 else term83)) else (if i.val < 86 then (if i.val < 85 then term84 else term85) else
    (if i.val < 87 then term86 else term87)))) else (if i.val < 94 then (if i.val < 91 then (if
    i.val < 89 then term88 else (if i.val < 90 then term89 else term90)) else (if i.val < 92
    then term91 else (if i.val < 93 then term92 else term93))) else (if i.val < 97 then (if
    i.val < 95 then term94 else (if i.val < 96 then term95 else term96)) else (if i.val < 99
    then (if i.val < 98 then term97 else term98) else (if i.val < 100 then term99 else
    term100))))))) else (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then (if i.val
    < 107 then (if i.val < 104 then (if i.val < 102 then term101 else (if i.val < 103 then
    term102 else term103)) else (if i.val < 105 then term104 else (if i.val < 106 then term105
    else term106))) else (if i.val < 110 then (if i.val < 108 then term107 else (if i.val < 109
    then term108 else term109)) else (if i.val < 111 then term110 else (if i.val < 112 then
    term111 else term112)))) else (if i.val < 119 then (if i.val < 116 then (if i.val < 114 then
    term113 else (if i.val < 115 then term114 else term115)) else (if i.val < 117 then term116
    else (if i.val < 118 then term117 else term118))) else (if i.val < 122 then (if i.val < 120
    then term119 else (if i.val < 121 then term120 else term121)) else (if i.val < 124 then (if
    i.val < 123 then term122 else term123) else (if i.val < 125 then term124 else term125)))))
    else (if i.val < 139 then (if i.val < 132 then (if i.val < 129 then (if i.val < 127 then
    term126 else (if i.val < 128 then term127 else term128)) else (if i.val < 130 then term129
    else (if i.val < 131 then term130 else term131))) else (if i.val < 135 then (if i.val < 133
    then term132 else (if i.val < 134 then term133 else term134)) else (if i.val < 137 then (if
    i.val < 136 then term135 else term136) else (if i.val < 138 then term137 else term138))))
    else (if i.val < 145 then (if i.val < 142 then (if i.val < 140 then term139 else (if i.val <
    141 then term140 else term141)) else (if i.val < 143 then term142 else (if i.val < 144 then
    term143 else term144))) else (if i.val < 148 then (if i.val < 146 then term145 else (if
    i.val < 147 then term146 else term147)) else (if i.val < 150 then (if i.val < 149 then
    term148 else term149) else (if i.val < 151 then term150 else term151)))))) else (if i.val <
    177 then (if i.val < 164 then (if i.val < 158 then (if i.val < 155 then (if i.val < 153 then
    term152 else (if i.val < 154 then term153 else term154)) else (if i.val < 156 then term155
    else (if i.val < 157 then term156 else term157))) else (if i.val < 161 then (if i.val < 159
    then term158 else (if i.val < 160 then term159 else term160)) else (if i.val < 162 then
    term161 else (if i.val < 163 then term162 else term163)))) else (if i.val < 170 then (if
    i.val < 167 then (if i.val < 165 then term164 else (if i.val < 166 then term165 else
    term166)) else (if i.val < 168 then term167 else (if i.val < 169 then term168 else
    term169))) else (if i.val < 173 then (if i.val < 171 then term170 else (if i.val < 172 then
    term171 else term172)) else (if i.val < 175 then (if i.val < 174 then term173 else term174)
    else (if i.val < 176 then term175 else term176))))) else (if i.val < 190 then (if i.val <
    183 then (if i.val < 180 then (if i.val < 178 then term177 else (if i.val < 179 then term178
    else term179)) else (if i.val < 181 then term180 else (if i.val < 182 then term181 else
    term182))) else (if i.val < 186 then (if i.val < 184 then term183 else (if i.val < 185 then
    term184 else term185)) else (if i.val < 188 then (if i.val < 187 then term186 else term187)
    else (if i.val < 189 then term188 else term189)))) else (if i.val < 196 then (if i.val < 193
    then (if i.val < 191 then term190 else (if i.val < 192 then term191 else term192)) else (if
    i.val < 194 then term193 else (if i.val < 195 then term194 else term195))) else (if i.val <
    199 then (if i.val < 197 then term196 else (if i.val < 198 then term197 else term198)) else
    (if i.val < 201 then (if i.val < 200 then term199 else term200) else (if i.val < 202 then
    term201 else term202)))))))) else (if i.val < 305 then (if i.val < 254 then (if i.val < 228
    then (if i.val < 215 then (if i.val < 209 then (if i.val < 206 then (if i.val < 204 then
    term203 else (if i.val < 205 then term204 else term205)) else (if i.val < 207 then term206
    else (if i.val < 208 then term207 else term208))) else (if i.val < 212 then (if i.val < 210
    then term209 else (if i.val < 211 then term210 else term211)) else (if i.val < 213 then
    term212 else (if i.val < 214 then term213 else term214)))) else (if i.val < 221 then (if
    i.val < 218 then (if i.val < 216 then term215 else (if i.val < 217 then term216 else
    term217)) else (if i.val < 219 then term218 else (if i.val < 220 then term219 else
    term220))) else (if i.val < 224 then (if i.val < 222 then term221 else (if i.val < 223 then
    term222 else term223)) else (if i.val < 226 then (if i.val < 225 then term224 else term225)
    else (if i.val < 227 then term226 else term227))))) else (if i.val < 241 then (if i.val <
    234 then (if i.val < 231 then (if i.val < 229 then term228 else (if i.val < 230 then term229
    else term230)) else (if i.val < 232 then term231 else (if i.val < 233 then term232 else
    term233))) else (if i.val < 237 then (if i.val < 235 then term234 else (if i.val < 236 then
    term235 else term236)) else (if i.val < 239 then (if i.val < 238 then term237 else term238)
    else (if i.val < 240 then term239 else term240)))) else (if i.val < 247 then (if i.val < 244
    then (if i.val < 242 then term241 else (if i.val < 243 then term242 else term243)) else (if
    i.val < 245 then term244 else (if i.val < 246 then term245 else term246))) else (if i.val <
    250 then (if i.val < 248 then term247 else (if i.val < 249 then term248 else term249)) else
    (if i.val < 252 then (if i.val < 251 then term250 else term251) else (if i.val < 253 then
    term252 else term253)))))) else (if i.val < 279 then (if i.val < 266 then (if i.val < 260
    then (if i.val < 257 then (if i.val < 255 then term254 else (if i.val < 256 then term255
    else term256)) else (if i.val < 258 then term257 else (if i.val < 259 then term258 else
    term259))) else (if i.val < 263 then (if i.val < 261 then term260 else (if i.val < 262 then
    term261 else term262)) else (if i.val < 264 then term263 else (if i.val < 265 then term264
    else term265)))) else (if i.val < 272 then (if i.val < 269 then (if i.val < 267 then term266
    else (if i.val < 268 then term267 else term268)) else (if i.val < 270 then term269 else (if
    i.val < 271 then term270 else term271))) else (if i.val < 275 then (if i.val < 273 then
    term272 else (if i.val < 274 then term273 else term274)) else (if i.val < 277 then (if i.val
    < 276 then term275 else term276) else (if i.val < 278 then term277 else term278))))) else
    (if i.val < 292 then (if i.val < 285 then (if i.val < 282 then (if i.val < 280 then term279
    else (if i.val < 281 then term280 else term281)) else (if i.val < 283 then term282 else (if
    i.val < 284 then term283 else term284))) else (if i.val < 288 then (if i.val < 286 then
    term285 else (if i.val < 287 then term286 else term287)) else (if i.val < 290 then (if i.val
    < 289 then term288 else term289) else (if i.val < 291 then term290 else term291)))) else (if
    i.val < 298 then (if i.val < 295 then (if i.val < 293 then term292 else (if i.val < 294 then
    term293 else term294)) else (if i.val < 296 then term295 else (if i.val < 297 then term296
    else term297))) else (if i.val < 301 then (if i.val < 299 then term298 else (if i.val < 300
    then term299 else term300)) else (if i.val < 303 then (if i.val < 302 then term301 else
    term302) else (if i.val < 304 then term303 else term304))))))) else (if i.val < 356 then (if
    i.val < 330 then (if i.val < 317 then (if i.val < 311 then (if i.val < 308 then (if i.val <
    306 then term305 else (if i.val < 307 then term306 else term307)) else (if i.val < 309 then
    term308 else (if i.val < 310 then term309 else term310))) else (if i.val < 314 then (if
    i.val < 312 then term311 else (if i.val < 313 then term312 else term313)) else (if i.val <
    315 then term314 else (if i.val < 316 then term315 else term316)))) else (if i.val < 323
    then (if i.val < 320 then (if i.val < 318 then term317 else (if i.val < 319 then term318
    else term319)) else (if i.val < 321 then term320 else (if i.val < 322 then term321 else
    term322))) else (if i.val < 326 then (if i.val < 324 then term323 else (if i.val < 325 then
    term324 else term325)) else (if i.val < 328 then (if i.val < 327 then term326 else term327)
    else (if i.val < 329 then term328 else term329))))) else (if i.val < 343 then (if i.val <
    336 then (if i.val < 333 then (if i.val < 331 then term330 else (if i.val < 332 then term331
    else term332)) else (if i.val < 334 then term333 else (if i.val < 335 then term334 else
    term335))) else (if i.val < 339 then (if i.val < 337 then term336 else (if i.val < 338 then
    term337 else term338)) else (if i.val < 341 then (if i.val < 340 then term339 else term340)
    else (if i.val < 342 then term341 else term342)))) else (if i.val < 349 then (if i.val < 346
    then (if i.val < 344 then term343 else (if i.val < 345 then term344 else term345)) else (if
    i.val < 347 then term346 else (if i.val < 348 then term347 else term348))) else (if i.val <
    352 then (if i.val < 350 then term349 else (if i.val < 351 then term350 else term351)) else
    (if i.val < 354 then (if i.val < 353 then term352 else term353) else (if i.val < 355 then
    term354 else term355)))))) else (if i.val < 381 then (if i.val < 368 then (if i.val < 362
    then (if i.val < 359 then (if i.val < 357 then term356 else (if i.val < 358 then term357
    else term358)) else (if i.val < 360 then term359 else (if i.val < 361 then term360 else
    term361))) else (if i.val < 365 then (if i.val < 363 then term362 else (if i.val < 364 then
    term363 else term364)) else (if i.val < 366 then term365 else (if i.val < 367 then term366
    else term367)))) else (if i.val < 374 then (if i.val < 371 then (if i.val < 369 then term368
    else (if i.val < 370 then term369 else term370)) else (if i.val < 372 then term371 else (if
    i.val < 373 then term372 else term373))) else (if i.val < 377 then (if i.val < 375 then
    term374 else (if i.val < 376 then term375 else term376)) else (if i.val < 379 then (if i.val
    < 378 then term377 else term378) else (if i.val < 380 then term379 else term380))))) else
    (if i.val < 394 then (if i.val < 387 then (if i.val < 384 then (if i.val < 382 then term381
    else (if i.val < 383 then term382 else term383)) else (if i.val < 385 then term384 else (if
    i.val < 386 then term385 else term386))) else (if i.val < 390 then (if i.val < 388 then
    term387 else (if i.val < 389 then term388 else term389)) else (if i.val < 392 then (if i.val
    < 391 then term390 else term391) else (if i.val < 393 then term392 else term393)))) else (if
    i.val < 400 then (if i.val < 397 then (if i.val < 395 then term394 else (if i.val < 396 then
    term395 else term396)) else (if i.val < 398 then term397 else (if i.val < 399 then term398
    else term399))) else (if i.val < 403 then (if i.val < 401 then term400 else (if i.val < 402
    then term401 else term402)) else (if i.val < 405 then (if i.val < 404 then term403 else
    term404) else (if i.val < 406 then term405 else term406))))))))) else (if i.val < 611 then
    (if i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if
    i.val < 413 then (if i.val < 410 then (if i.val < 408 then term407 else (if i.val < 409 then
    term408 else term409)) else (if i.val < 411 then term410 else (if i.val < 412 then term411
    else term412))) else (if i.val < 416 then (if i.val < 414 then term413 else (if i.val < 415
    then term414 else term415)) else (if i.val < 417 then term416 else (if i.val < 418 then
    term417 else term418)))) else (if i.val < 425 then (if i.val < 422 then (if i.val < 420 then
    term419 else (if i.val < 421 then term420 else term421)) else (if i.val < 423 then term422
    else (if i.val < 424 then term423 else term424))) else (if i.val < 428 then (if i.val < 426
    then term425 else (if i.val < 427 then term426 else term427)) else (if i.val < 430 then (if
    i.val < 429 then term428 else term429) else (if i.val < 431 then term430 else term431)))))
    else (if i.val < 445 then (if i.val < 438 then (if i.val < 435 then (if i.val < 433 then
    term432 else (if i.val < 434 then term433 else term434)) else (if i.val < 436 then term435
    else (if i.val < 437 then term436 else term437))) else (if i.val < 441 then (if i.val < 439
    then term438 else (if i.val < 440 then term439 else term440)) else (if i.val < 443 then (if
    i.val < 442 then term441 else term442) else (if i.val < 444 then term443 else term444))))
    else (if i.val < 451 then (if i.val < 448 then (if i.val < 446 then term445 else (if i.val <
    447 then term446 else term447)) else (if i.val < 449 then term448 else (if i.val < 450 then
    term449 else term450))) else (if i.val < 454 then (if i.val < 452 then term451 else (if
    i.val < 453 then term452 else term453)) else (if i.val < 456 then (if i.val < 455 then
    term454 else term455) else (if i.val < 457 then term456 else term457)))))) else (if i.val <
    483 then (if i.val < 470 then (if i.val < 464 then (if i.val < 461 then (if i.val < 459 then
    term458 else (if i.val < 460 then term459 else term460)) else (if i.val < 462 then term461
    else (if i.val < 463 then term462 else term463))) else (if i.val < 467 then (if i.val < 465
    then term464 else (if i.val < 466 then term465 else term466)) else (if i.val < 468 then
    term467 else (if i.val < 469 then term468 else term469)))) else (if i.val < 476 then (if
    i.val < 473 then (if i.val < 471 then term470 else (if i.val < 472 then term471 else
    term472)) else (if i.val < 474 then term473 else (if i.val < 475 then term474 else
    term475))) else (if i.val < 479 then (if i.val < 477 then term476 else (if i.val < 478 then
    term477 else term478)) else (if i.val < 481 then (if i.val < 480 then term479 else term480)
    else (if i.val < 482 then term481 else term482))))) else (if i.val < 496 then (if i.val <
    489 then (if i.val < 486 then (if i.val < 484 then term483 else (if i.val < 485 then term484
    else term485)) else (if i.val < 487 then term486 else (if i.val < 488 then term487 else
    term488))) else (if i.val < 492 then (if i.val < 490 then term489 else (if i.val < 491 then
    term490 else term491)) else (if i.val < 494 then (if i.val < 493 then term492 else term493)
    else (if i.val < 495 then term494 else term495)))) else (if i.val < 502 then (if i.val < 499
    then (if i.val < 497 then term496 else (if i.val < 498 then term497 else term498)) else (if
    i.val < 500 then term499 else (if i.val < 501 then term500 else term501))) else (if i.val <
    505 then (if i.val < 503 then term502 else (if i.val < 504 then term503 else term504)) else
    (if i.val < 507 then (if i.val < 506 then term505 else term506) else (if i.val < 508 then
    term507 else term508))))))) else (if i.val < 560 then (if i.val < 534 then (if i.val < 521
    then (if i.val < 515 then (if i.val < 512 then (if i.val < 510 then term509 else (if i.val <
    511 then term510 else term511)) else (if i.val < 513 then term512 else (if i.val < 514 then
    term513 else term514))) else (if i.val < 518 then (if i.val < 516 then term515 else (if
    i.val < 517 then term516 else term517)) else (if i.val < 519 then term518 else (if i.val <
    520 then term519 else term520)))) else (if i.val < 527 then (if i.val < 524 then (if i.val <
    522 then term521 else (if i.val < 523 then term522 else term523)) else (if i.val < 525 then
    term524 else (if i.val < 526 then term525 else term526))) else (if i.val < 530 then (if
    i.val < 528 then term527 else (if i.val < 529 then term528 else term529)) else (if i.val <
    532 then (if i.val < 531 then term530 else term531) else (if i.val < 533 then term532 else
    term533))))) else (if i.val < 547 then (if i.val < 540 then (if i.val < 537 then (if i.val <
    535 then term534 else (if i.val < 536 then term535 else term536)) else (if i.val < 538 then
    term537 else (if i.val < 539 then term538 else term539))) else (if i.val < 543 then (if
    i.val < 541 then term540 else (if i.val < 542 then term541 else term542)) else (if i.val <
    545 then (if i.val < 544 then term543 else term544) else (if i.val < 546 then term545 else
    term546)))) else (if i.val < 553 then (if i.val < 550 then (if i.val < 548 then term547 else
    (if i.val < 549 then term548 else term549)) else (if i.val < 551 then term550 else (if i.val
    < 552 then term551 else term552))) else (if i.val < 556 then (if i.val < 554 then term553
    else (if i.val < 555 then term554 else term555)) else (if i.val < 558 then (if i.val < 557
    then term556 else term557) else (if i.val < 559 then term558 else term559)))))) else (if
    i.val < 585 then (if i.val < 572 then (if i.val < 566 then (if i.val < 563 then (if i.val <
    561 then term560 else (if i.val < 562 then term561 else term562)) else (if i.val < 564 then
    term563 else (if i.val < 565 then term564 else term565))) else (if i.val < 569 then (if
    i.val < 567 then term566 else (if i.val < 568 then term567 else term568)) else (if i.val <
    570 then term569 else (if i.val < 571 then term570 else term571)))) else (if i.val < 578
    then (if i.val < 575 then (if i.val < 573 then term572 else (if i.val < 574 then term573
    else term574)) else (if i.val < 576 then term575 else (if i.val < 577 then term576 else
    term577))) else (if i.val < 581 then (if i.val < 579 then term578 else (if i.val < 580 then
    term579 else term580)) else (if i.val < 583 then (if i.val < 582 then term581 else term582)
    else (if i.val < 584 then term583 else term584))))) else (if i.val < 598 then (if i.val <
    591 then (if i.val < 588 then (if i.val < 586 then term585 else (if i.val < 587 then term586
    else term587)) else (if i.val < 589 then term588 else (if i.val < 590 then term589 else
    term590))) else (if i.val < 594 then (if i.val < 592 then term591 else (if i.val < 593 then
    term592 else term593)) else (if i.val < 596 then (if i.val < 595 then term594 else term595)
    else (if i.val < 597 then term596 else term597)))) else (if i.val < 604 then (if i.val < 601
    then (if i.val < 599 then term598 else (if i.val < 600 then term599 else term600)) else (if
    i.val < 602 then term601 else (if i.val < 603 then term602 else term603))) else (if i.val <
    607 then (if i.val < 605 then term604 else (if i.val < 606 then term605 else term606)) else
    (if i.val < 609 then (if i.val < 608 then term607 else term608) else (if i.val < 610 then
    term609 else term610)))))))) else (if i.val < 713 then (if i.val < 662 then (if i.val < 636
    then (if i.val < 623 then (if i.val < 617 then (if i.val < 614 then (if i.val < 612 then
    term611 else (if i.val < 613 then term612 else term613)) else (if i.val < 615 then term614
    else (if i.val < 616 then term615 else term616))) else (if i.val < 620 then (if i.val < 618
    then term617 else (if i.val < 619 then term618 else term619)) else (if i.val < 621 then
    term620 else (if i.val < 622 then term621 else term622)))) else (if i.val < 629 then (if
    i.val < 626 then (if i.val < 624 then term623 else (if i.val < 625 then term624 else
    term625)) else (if i.val < 627 then term626 else (if i.val < 628 then term627 else
    term628))) else (if i.val < 632 then (if i.val < 630 then term629 else (if i.val < 631 then
    term630 else term631)) else (if i.val < 634 then (if i.val < 633 then term632 else term633)
    else (if i.val < 635 then term634 else term635))))) else (if i.val < 649 then (if i.val <
    642 then (if i.val < 639 then (if i.val < 637 then term636 else (if i.val < 638 then term637
    else term638)) else (if i.val < 640 then term639 else (if i.val < 641 then term640 else
    term641))) else (if i.val < 645 then (if i.val < 643 then term642 else (if i.val < 644 then
    term643 else term644)) else (if i.val < 647 then (if i.val < 646 then term645 else term646)
    else (if i.val < 648 then term647 else term648)))) else (if i.val < 655 then (if i.val < 652
    then (if i.val < 650 then term649 else (if i.val < 651 then term650 else term651)) else (if
    i.val < 653 then term652 else (if i.val < 654 then term653 else term654))) else (if i.val <
    658 then (if i.val < 656 then term655 else (if i.val < 657 then term656 else term657)) else
    (if i.val < 660 then (if i.val < 659 then term658 else term659) else (if i.val < 661 then
    term660 else term661)))))) else (if i.val < 687 then (if i.val < 674 then (if i.val < 668
    then (if i.val < 665 then (if i.val < 663 then term662 else (if i.val < 664 then term663
    else term664)) else (if i.val < 666 then term665 else (if i.val < 667 then term666 else
    term667))) else (if i.val < 671 then (if i.val < 669 then term668 else (if i.val < 670 then
    term669 else term670)) else (if i.val < 672 then term671 else (if i.val < 673 then term672
    else term673)))) else (if i.val < 680 then (if i.val < 677 then (if i.val < 675 then term674
    else (if i.val < 676 then term675 else term676)) else (if i.val < 678 then term677 else (if
    i.val < 679 then term678 else term679))) else (if i.val < 683 then (if i.val < 681 then
    term680 else (if i.val < 682 then term681 else term682)) else (if i.val < 685 then (if i.val
    < 684 then term683 else term684) else (if i.val < 686 then term685 else term686))))) else
    (if i.val < 700 then (if i.val < 693 then (if i.val < 690 then (if i.val < 688 then term687
    else (if i.val < 689 then term688 else term689)) else (if i.val < 691 then term690 else (if
    i.val < 692 then term691 else term692))) else (if i.val < 696 then (if i.val < 694 then
    term693 else (if i.val < 695 then term694 else term695)) else (if i.val < 698 then (if i.val
    < 697 then term696 else term697) else (if i.val < 699 then term698 else term699)))) else (if
    i.val < 706 then (if i.val < 703 then (if i.val < 701 then term700 else (if i.val < 702 then
    term701 else term702)) else (if i.val < 704 then term703 else (if i.val < 705 then term704
    else term705))) else (if i.val < 709 then (if i.val < 707 then term706 else (if i.val < 708
    then term707 else term708)) else (if i.val < 711 then (if i.val < 710 then term709 else
    term710) else (if i.val < 712 then term711 else term712))))))) else (if i.val < 764 then (if
    i.val < 738 then (if i.val < 725 then (if i.val < 719 then (if i.val < 716 then (if i.val <
    714 then term713 else (if i.val < 715 then term714 else term715)) else (if i.val < 717 then
    term716 else (if i.val < 718 then term717 else term718))) else (if i.val < 722 then (if
    i.val < 720 then term719 else (if i.val < 721 then term720 else term721)) else (if i.val <
    723 then term722 else (if i.val < 724 then term723 else term724)))) else (if i.val < 731
    then (if i.val < 728 then (if i.val < 726 then term725 else (if i.val < 727 then term726
    else term727)) else (if i.val < 729 then term728 else (if i.val < 730 then term729 else
    term730))) else (if i.val < 734 then (if i.val < 732 then term731 else (if i.val < 733 then
    term732 else term733)) else (if i.val < 736 then (if i.val < 735 then term734 else term735)
    else (if i.val < 737 then term736 else term737))))) else (if i.val < 751 then (if i.val <
    744 then (if i.val < 741 then (if i.val < 739 then term738 else (if i.val < 740 then term739
    else term740)) else (if i.val < 742 then term741 else (if i.val < 743 then term742 else
    term743))) else (if i.val < 747 then (if i.val < 745 then term744 else (if i.val < 746 then
    term745 else term746)) else (if i.val < 749 then (if i.val < 748 then term747 else term748)
    else (if i.val < 750 then term749 else term750)))) else (if i.val < 757 then (if i.val < 754
    then (if i.val < 752 then term751 else (if i.val < 753 then term752 else term753)) else (if
    i.val < 755 then term754 else (if i.val < 756 then term755 else term756))) else (if i.val <
    760 then (if i.val < 758 then term757 else (if i.val < 759 then term758 else term759)) else
    (if i.val < 762 then (if i.val < 761 then term760 else term761) else (if i.val < 763 then
    term762 else term763)))))) else (if i.val < 789 then (if i.val < 776 then (if i.val < 770
    then (if i.val < 767 then (if i.val < 765 then term764 else (if i.val < 766 then term765
    else term766)) else (if i.val < 768 then term767 else (if i.val < 769 then term768 else
    term769))) else (if i.val < 773 then (if i.val < 771 then term770 else (if i.val < 772 then
    term771 else term772)) else (if i.val < 774 then term773 else (if i.val < 775 then term774
    else term775)))) else (if i.val < 782 then (if i.val < 779 then (if i.val < 777 then term776
    else (if i.val < 778 then term777 else term778)) else (if i.val < 780 then term779 else (if
    i.val < 781 then term780 else term781))) else (if i.val < 785 then (if i.val < 783 then
    term782 else (if i.val < 784 then term783 else term784)) else (if i.val < 787 then (if i.val
    < 786 then term785 else term786) else (if i.val < 788 then term787 else term788))))) else
    (if i.val < 802 then (if i.val < 795 then (if i.val < 792 then (if i.val < 790 then term789
    else (if i.val < 791 then term790 else term791)) else (if i.val < 793 then term792 else (if
    i.val < 794 then term793 else term794))) else (if i.val < 798 then (if i.val < 796 then
    term795 else (if i.val < 797 then term796 else term797)) else (if i.val < 800 then (if i.val
    < 799 then term798 else term799) else (if i.val < 801 then term800 else term801)))) else (if
    i.val < 808 then (if i.val < 805 then (if i.val < 803 then term802 else (if i.val < 804 then
    term803 else term804)) else (if i.val < 806 then term805 else (if i.val < 807 then term806
    else term807))) else (if i.val < 811 then (if i.val < 809 then term808 else (if i.val < 810
    then term809 else term810)) else (if i.val < 813 then (if i.val < 812 then term811 else
    term812) else (if i.val < 814 then term813 else term814))))))))))

/-- Proposed vertex and edge bijections, verified by the complete checker. -/
def hint (i : Fin 815) : GraphIsomorphismHint :=
  (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then (if i.val <
    25 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 37 then ⟨[0, 1], [0], [false]⟩ else (if
    i.val < 43 then ⟨[0, 1], [0], [false]⟩ else (if i.val < 46 then ⟨[0, 1], [0], [false]⟩ else
    (if i.val < 48 then ⟨[0, 1], [0], [false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩)))))
    else (if i.val < 75 then (if i.val < 62 then (if i.val < 56 then (if i.val < 53 then (if
    i.val < 51 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 52 then ⟨[0, 1, 2], [0,
    1], [false, false]⟩ else ⟨[1, 0, 2], [0, 1], [false, false]⟩)) else (if i.val < 54 then ⟨[1,
    0, 2], [0, 1], [false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else (if i.val <
    59 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 60 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else (if i.val < 61 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[1, 0,
    2], [0, 1], [false, false]⟩)))) else (if i.val < 68 then (if i.val < 65 then (if i.val < 63
    then ⟨[1, 0, 2], [0, 1], [false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else ⟨[0,
    1, 2], [0, 1], [false, false]⟩) else (if i.val < 71 then (if i.val < 69 then ⟨[1, 0, 2], [0,
    1], [false, false]⟩ else (if i.val < 70 then ⟨[1, 0, 2], [0, 1], [false, false]⟩ else ⟨[0,
    1, 2], [0, 1], [false, false]⟩)) else ⟨[0, 1, 2], [0, 1], [false, false]⟩))) else ⟨[0, 1,
    2], [0, 1], [false, false]⟩)) else (if i.val < 152 then (if i.val < 126 then (if i.val < 113
    then (if i.val < 107 then (if i.val < 104 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if
    i.val < 105 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 106 then ⟨[0, 1, 2],
    [0, 1], [false, false]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩))) else (if
    i.val < 110 then (if i.val < 108 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else
    (if i.val < 109 then ⟨[1, 0, 2, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[0, 1, 2, 3],
    [0, 1, 2], [false, false, false]⟩)) else (if i.val < 111 then ⟨[0, 1, 2, 3], [0, 1, 2],
    [false, false, false]⟩ else (if i.val < 112 then ⟨[1, 0, 2, 3], [0, 1, 2], [false, false,
    false]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)))) else (if i.val < 119 then
    (if i.val < 116 then (if i.val < 114 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩
    else (if i.val < 115 then ⟨[1, 0, 2, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[0, 1, 2,
    3], [0, 1, 2], [false, false, false]⟩)) else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false,
    false]⟩) else (if i.val < 122 then (if i.val < 120 then ⟨[0, 1, 2, 3], [0, 1, 2], [false,
    false, false]⟩ else (if i.val < 121 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩
    else ⟨[1, 0, 2], [0, 1], [false, false]⟩)) else (if i.val < 124 then ⟨[1, 0, 2], [0, 1],
    [false, false]⟩ else (if i.val < 125 then ⟨[1, 0, 2], [0, 1], [false, false]⟩ else ⟨[0, 1,
    2], [0, 1], [false, false]⟩))))) else (if i.val < 139 then (if i.val < 132 then (if i.val <
    129 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 130 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else ⟨[1, 0, 2], [0, 1], [false, false]⟩)) else (if i.val < 135 then ⟨[1, 0,
    2], [0, 1], [false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else (if i.val < 145
    then (if i.val < 142 then (if i.val < 140 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[1,
    0, 2], [0, 1], [false, false]⟩) else (if i.val < 143 then ⟨[1, 0, 2], [0, 1], [false,
    false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else (if i.val < 148 then (if i.val < 146
    then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 147 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else ⟨[1, 0, 2], [0, 1], [false, false]⟩)) else (if i.val < 150 then ⟨[1, 0,
    2], [0, 1], [false, false]⟩ else (if i.val < 151 then ⟨[1, 0, 2], [0, 1], [false, false]⟩
    else ⟨[0, 1, 2], [0, 1], [false, false]⟩)))))) else (if i.val < 177 then (if i.val < 164
    then (if i.val < 158 then (if i.val < 155 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[1,
    0, 2], [0, 1], [false, false]⟩) else (if i.val < 161 then ⟨[0, 1, 2], [0, 1], [false,
    false]⟩ else (if i.val < 162 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[1, 0, 2], [0,
    1], [false, false]⟩))) else (if i.val < 170 then (if i.val < 167 then (if i.val < 165 then
    ⟨[1, 0, 2], [0, 1], [false, false]⟩ else (if i.val < 166 then ⟨[1, 0, 2], [0, 1], [false,
    false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else ⟨[0, 1, 2], [0, 1], [false, false]⟩)
    else (if i.val < 173 then ⟨[1, 0, 2], [0, 1], [false, false]⟩ else (if i.val < 175 then ⟨[1,
    0, 2], [0, 1], [false, false]⟩ else (if i.val < 176 then ⟨[1, 0, 2], [0, 1], [false, false]⟩
    else ⟨[0, 1, 2], [0, 1], [false, false]⟩))))) else (if i.val < 190 then (if i.val < 183 then
    (if i.val < 180 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 181 then ⟨[0, 1,
    2], [0, 1], [false, false]⟩ else (if i.val < 182 then ⟨[0, 1, 2], [0, 1], [false, false]⟩
    else ⟨[1, 0, 2], [0, 1], [false, false]⟩))) else (if i.val < 186 then ⟨[1, 0, 2], [0, 1],
    [false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else (if i.val < 196 then (if
    i.val < 193 then (if i.val < 191 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[1, 0, 2],
    [0, 1], [false, false]⟩) else ⟨[1, 0, 2], [0, 1], [false, false]⟩) else (if i.val < 199 then
    ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 201 then ⟨[0, 1, 2], [0, 1], [false,
    false]⟩ else ⟨[1, 0, 2], [0, 1], [false, false]⟩))))))) else (if i.val < 305 then (if i.val
    < 254 then (if i.val < 228 then (if i.val < 215 then (if i.val < 209 then (if i.val < 206
    then (if i.val < 204 then ⟨[1, 0, 2], [0, 1], [false, false]⟩ else (if i.val < 205 then ⟨[1,
    0, 2], [0, 1], [false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else ⟨[0, 1, 2],
    [0, 1], [false, false]⟩) else (if i.val < 212 then (if i.val < 210 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else ⟨[1, 0, 2], [0, 1], [false, false]⟩) else ⟨[1, 0, 2], [0, 1], [false,
    false]⟩)) else (if i.val < 221 then (if i.val < 218 then ⟨[0, 1, 2], [0, 1], [false, false]⟩
    else (if i.val < 219 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 220 then ⟨[0,
    1, 2], [0, 1], [false, false]⟩ else ⟨[1, 0, 2], [0, 1], [false, false]⟩))) else (if i.val <
    224 then ⟨[1, 0, 2], [0, 1], [false, false]⟩ else (if i.val < 226 then ⟨[1, 0, 2], [0, 1],
    [false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩)))) else (if i.val < 241 then (if
    i.val < 234 then (if i.val < 231 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val <
    232 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 233 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else ⟨[1, 0, 2], [0, 1], [false, false]⟩))) else (if i.val < 237 then (if
    i.val < 235 then ⟨[1, 0, 2], [0, 1], [false, false]⟩ else (if i.val < 236 then ⟨[1, 0, 2],
    [0, 1], [false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩)) else (if i.val < 239 then
    ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 240 then ⟨[0, 1, 2], [0, 1], [false,
    false]⟩ else ⟨[1, 0, 2], [0, 1], [false, false]⟩)))) else (if i.val < 247 then (if i.val <
    244 then ⟨[1, 0, 2], [0, 1], [false, false]⟩ else ⟨[0, 1, 2], [0, 1], [false, false]⟩) else
    (if i.val < 250 then (if i.val < 248 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else ⟨[1, 0,
    2], [0, 1], [false, false]⟩) else ⟨[1, 0, 2], [0, 1], [false, false]⟩)))) else (if i.val <
    279 then (if i.val < 266 then (if i.val < 260 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else
    ⟨[1, 0, 2], [0, 1], [false, false]⟩) else (if i.val < 272 then ⟨[0, 1, 2], [0, 1], [false,
    false]⟩ else (if i.val < 275 then ⟨[1, 0, 2], [0, 1], [false, false]⟩ else (if i.val < 277
    then (if i.val < 276 then ⟨[1, 0, 2], [0, 1], [false, false]⟩ else ⟨[0, 1, 2], [0, 1],
    [false, false]⟩) else ⟨[0, 1, 2], [0, 1], [false, false]⟩)))) else ⟨[0, 1, 2], [0, 1],
    [false, false]⟩)) else (if i.val < 356 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if
    i.val < 381 then (if i.val < 368 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val <
    374 then ⟨[0, 1, 2], [0, 1], [false, false]⟩ else (if i.val < 377 then ⟨[0, 1, 2], [0, 1],
    [false, false]⟩ else (if i.val < 379 then (if i.val < 378 then ⟨[2, 0, 1, 3], [0, 1, 2],
    [false, false, false]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩) else (if i.val
    < 380 then ⟨[2, 0, 1, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2],
    [false, false, false]⟩))))) else (if i.val < 394 then (if i.val < 387 then (if i.val < 384
    then (if i.val < 382 then ⟨[2, 1, 0, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val <
    383 then ⟨[1, 2, 0, 3], [1, 0, 2], [false, false, false]⟩ else ⟨[2, 0, 1, 3], [0, 1, 2],
    [false, false, false]⟩)) else (if i.val < 385 then ⟨[2, 0, 1, 3], [0, 1, 2], [false, false,
    false]⟩ else (if i.val < 386 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[2,
    0, 1, 3], [0, 1, 2], [false, false, false]⟩))) else (if i.val < 390 then (if i.val < 388
    then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 389 then ⟨[2, 1, 0,
    3], [0, 1, 2], [false, false, false]⟩ else ⟨[1, 2, 0, 3], [1, 0, 2], [false, false,
    false]⟩)) else (if i.val < 392 then ⟨[2, 0, 1, 3], [0, 1, 2], [false, false, false]⟩ else
    (if i.val < 393 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[2, 0, 1, 3],
    [0, 1, 2], [false, false, false]⟩)))) else (if i.val < 400 then (if i.val < 397 then (if
    i.val < 395 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 396 then
    ⟨[2, 1, 0, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[1, 2, 0, 3], [1, 0, 2], [false,
    false, false]⟩)) else ⟨[2, 0, 1, 3], [0, 1, 2], [false, false, false]⟩) else (if i.val < 403
    then (if i.val < 401 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val <
    402 then ⟨[2, 0, 1, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2],
    [false, false, false]⟩)) else (if i.val < 405 then ⟨[2, 0, 1, 3], [0, 1, 2], [false, false,
    false]⟩ else (if i.val < 406 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[2,
    0, 1, 3], [0, 1, 2], [false, false, false]⟩))))))))) else (if i.val < 611 then (if i.val <
    509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if i.val < 413 then
    (if i.val < 410 then (if i.val < 408 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩
    else ⟨[2, 0, 1, 3], [0, 1, 2], [false, false, false]⟩) else (if i.val < 411 then ⟨[2, 0, 1,
    3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 412 then ⟨[0, 1, 2, 3], [0, 1, 2],
    [false, false, false]⟩ else ⟨[2, 0, 1, 3], [0, 1, 2], [false, false, false]⟩))) else (if
    i.val < 416 then (if i.val < 414 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else
    ⟨[2, 0, 1, 3], [0, 1, 2], [false, false, false]⟩) else (if i.val < 417 then ⟨[2, 0, 1, 3],
    [0, 1, 2], [false, false, false]⟩ else (if i.val < 418 then ⟨[1, 0, 2, 3], [0, 1, 2],
    [false, false, false]⟩ else ⟨[1, 2, 0, 3], [1, 0, 2], [false, false, false]⟩)))) else (if
    i.val < 425 then (if i.val < 422 then (if i.val < 420 then ⟨[1, 0, 2, 3], [0, 1, 2], [false,
    false, false]⟩ else (if i.val < 421 then ⟨[1, 2, 0, 3], [1, 0, 2], [false, false, false]⟩
    else ⟨[1, 0, 2, 3], [0, 1, 2], [false, false, false]⟩)) else (if i.val < 423 then ⟨[1, 2, 0,
    3], [1, 0, 2], [false, false, false]⟩ else (if i.val < 424 then ⟨[1, 0, 2, 3], [0, 1, 2],
    [false, false, false]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩))) else (if
    i.val < 428 then (if i.val < 426 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else
    ⟨[1, 0, 2, 3], [0, 1, 2], [false, false, false]⟩) else (if i.val < 430 then (if i.val < 429
    then ⟨[1, 2, 0, 3], [1, 0, 2], [false, false, false]⟩ else ⟨[1, 0, 2, 3], [0, 1, 2], [false,
    false, false]⟩) else (if i.val < 431 then ⟨[1, 2, 0, 3], [1, 0, 2], [false, false, false]⟩
    else ⟨[1, 0, 2, 3], [0, 1, 2], [false, false, false]⟩))))) else (if i.val < 445 then (if
    i.val < 438 then (if i.val < 435 then (if i.val < 433 then ⟨[1, 2, 0, 3], [1, 0, 2], [false,
    false, false]⟩ else (if i.val < 434 then ⟨[1, 0, 2, 3], [0, 1, 2], [false, false, false]⟩
    else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)) else (if i.val < 436 then ⟨[0, 1, 2,
    3], [0, 1, 2], [false, false, false]⟩ else ⟨[1, 0, 2, 3], [0, 1, 2], [false, false,
    false]⟩)) else (if i.val < 441 then (if i.val < 439 then ⟨[1, 2, 0, 3], [1, 0, 2], [false,
    false, false]⟩ else (if i.val < 440 then ⟨[1, 0, 2, 3], [0, 1, 2], [false, false, false]⟩
    else ⟨[1, 2, 0, 3], [1, 0, 2], [false, false, false]⟩)) else (if i.val < 443 then (if i.val
    < 442 then ⟨[1, 0, 2, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[1, 2, 0, 3], [1, 0, 2],
    [false, false, false]⟩) else (if i.val < 444 then ⟨[1, 0, 2, 3], [0, 1, 2], [false, false,
    false]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)))) else (if i.val < 451 then
    (if i.val < 448 then (if i.val < 446 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩
    else ⟨[1, 0, 2, 3], [0, 1, 2], [false, false, false]⟩) else (if i.val < 449 then ⟨[1, 2, 0,
    3], [1, 0, 2], [false, false, false]⟩ else ⟨[1, 0, 2, 3], [0, 1, 2], [false, false,
    false]⟩)) else (if i.val < 454 then (if i.val < 452 then ⟨[1, 2, 0, 3], [1, 0, 2], [false,
    false, false]⟩ else (if i.val < 453 then ⟨[1, 0, 2, 3], [0, 1, 2], [false, false, false]⟩
    else ⟨[1, 2, 0, 3], [1, 0, 2], [false, false, false]⟩)) else (if i.val < 456 then (if i.val
    < 455 then ⟨[1, 0, 2, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[1, 2, 0, 3], [1, 0, 2],
    [false, false, false]⟩) else (if i.val < 457 then ⟨[1, 0, 2, 3], [0, 1, 2], [false, false,
    false]⟩ else ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩)))))) else (if i.val < 483
    then (if i.val < 470 then (if i.val < 464 then (if i.val < 461 then (if i.val < 459 then
    ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[1, 0, 2, 3], [0, 1, 2], [false,
    false, false]⟩) else (if i.val < 462 then ⟨[1, 2, 0, 3], [1, 0, 2], [false, false, false]⟩
    else (if i.val < 463 then ⟨[1, 0, 2, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[1, 2, 0,
    3], [1, 0, 2], [false, false, false]⟩))) else (if i.val < 467 then (if i.val < 465 then ⟨[1,
    0, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 466 then ⟨[1, 2, 0, 3], [1, 0,
    2], [false, false, false]⟩ else ⟨[1, 0, 2, 3], [0, 1, 2], [false, false, false]⟩)) else (if
    i.val < 468 then ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 469 then
    ⟨[0, 1, 2, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[1, 0, 2, 3], [0, 1, 2], [false,
    false, false]⟩)))) else (if i.val < 476 then (if i.val < 473 then (if i.val < 471 then ⟨[1,
    0, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 472 then ⟨[1, 2, 0, 3], [1, 0,
    2], [false, false, false]⟩ else ⟨[1, 0, 2, 3], [0, 1, 2], [false, false, false]⟩)) else (if
    i.val < 474 then ⟨[1, 0, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 475 then
    ⟨[1, 2, 0, 3], [1, 0, 2], [false, false, false]⟩ else ⟨[1, 0, 2, 3], [0, 1, 2], [false,
    false, false]⟩))) else (if i.val < 479 then (if i.val < 477 then ⟨[1, 2, 0, 3], [1, 0, 2],
    [false, false, false]⟩ else (if i.val < 478 then ⟨[1, 0, 2, 3], [0, 1, 2], [false, false,
    false]⟩ else ⟨[1, 2, 0, 3], [1, 0, 2], [false, false, false]⟩)) else (if i.val < 481 then
    (if i.val < 480 then ⟨[1, 0, 2, 3], [0, 1, 2], [false, false, false]⟩ else ⟨[0, 1, 2, 3],
    [0, 1, 2], [false, false, false]⟩) else (if i.val < 482 then ⟨[0, 1, 2, 3], [0, 1, 2],
    [false, false, false]⟩ else ⟨[1, 0, 2, 3], [0, 1, 2], [false, false, false]⟩))))) else (if
    i.val < 496 then (if i.val < 489 then (if i.val < 486 then (if i.val < 484 then ⟨[1, 0, 2,
    3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 485 then ⟨[1, 2, 0, 3], [1, 0, 2],
    [false, false, false]⟩ else ⟨[1, 0, 2, 3], [0, 1, 2], [false, false, false]⟩)) else (if
    i.val < 487 then ⟨[1, 0, 2, 3], [0, 1, 2], [false, false, false]⟩ else (if i.val < 488 then
    ⟨[1, 2, 0, 3], [1, 0, 2], [false, false, false]⟩ else ⟨[1, 0, 2, 3], [0, 1, 2], [false,
    false, false]⟩))) else ⟨[1, 0, 2], [0, 1], [false, false]⟩) else (if i.val < 502 then (if
    i.val < 499 then ⟨[1, 0, 2], [0, 1], [false, false]⟩ else ⟨[0, 1], [1, 0], [false, false]⟩)
    else ⟨[0, 1], [1, 0], [false, false]⟩)))) else (if i.val < 560 then (if i.val < 534 then
    ⟨[0, 1], [1, 0], [false, false]⟩ else (if i.val < 547 then ⟨[0, 1], [1, 0], [false, false]⟩
    else (if i.val < 553 then (if i.val < 550 then (if i.val < 548 then ⟨[0, 1], [1, 0], [false,
    false]⟩ else ⟨[0, 1], [0, 1], [false, false]⟩) else ⟨[0, 1], [0, 1], [false, false]⟩) else
    ⟨[0, 1], [0, 1], [false, false]⟩))) else (if i.val < 585 then ⟨[0, 1], [0, 1], [false,
    false]⟩ else (if i.val < 598 then ⟨[0, 1], [0, 1], [false, false]⟩ else ⟨[0, 1], [1, 0],
    [false, false]⟩)))) else (if i.val < 713 then (if i.val < 662 then ⟨[0, 1], [1, 0], [false,
    false]⟩ else (if i.val < 687 then (if i.val < 674 then (if i.val < 668 then (if i.val < 665
    then (if i.val < 663 then ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩ else (if i.val < 664
    then ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩ else ⟨[1, 0, 2], [1, 2, 0], [false,
    false, false]⟩)) else (if i.val < 666 then ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩
    else ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩)) else (if i.val < 671 then ⟨[0, 1, 2],
    [0, 1, 2], [false, false, false]⟩ else (if i.val < 672 then ⟨[0, 1, 2], [0, 1, 2], [false,
    false, false]⟩ else (if i.val < 673 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else
    ⟨[1, 0, 2], [1, 2, 0], [false, false, false]⟩)))) else (if i.val < 680 then (if i.val < 677
    then (if i.val < 675 then ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩ else (if i.val < 676
    then ⟨[1, 0, 2], [1, 2, 0], [false, false, false]⟩ else ⟨[0, 1, 2], [1, 2, 0], [false,
    false, false]⟩)) else (if i.val < 678 then ⟨[1, 0, 2], [1, 2, 0], [false, false, false]⟩
    else (if i.val < 679 then ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩ else ⟨[1, 0, 2], [1,
    2, 0], [false, false, false]⟩))) else (if i.val < 683 then ⟨[0, 1, 2], [1, 2, 0], [false,
    false, false]⟩ else (if i.val < 685 then (if i.val < 684 then ⟨[1, 0, 2], [1, 2, 0], [false,
    false, false]⟩ else ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩) else ⟨[0, 1, 2], [0, 1,
    2], [false, false, false]⟩)))) else (if i.val < 700 then (if i.val < 693 then (if i.val <
    690 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else (if i.val < 691 then ⟨[0, 1, 2],
    [0, 1, 2], [false, false, false]⟩ else (if i.val < 692 then ⟨[0, 1, 2], [0, 1, 2], [false,
    false, false]⟩ else ⟨[1, 0, 2], [1, 2, 0], [false, false, false]⟩))) else (if i.val < 696
    then (if i.val < 694 then ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩ else (if i.val < 695
    then ⟨[1, 0, 2], [1, 2, 0], [false, false, false]⟩ else ⟨[0, 1, 2], [1, 2, 0], [false,
    false, false]⟩)) else (if i.val < 698 then (if i.val < 697 then ⟨[1, 0, 2], [1, 2, 0],
    [false, false, false]⟩ else ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩) else (if i.val <
    699 then ⟨[1, 0, 2], [1, 2, 0], [false, false, false]⟩ else ⟨[0, 1, 2], [1, 2, 0], [false,
    false, false]⟩)))) else (if i.val < 706 then (if i.val < 703 then (if i.val < 701 then ⟨[0,
    1, 2], [1, 2, 0], [false, false, false]⟩ else (if i.val < 702 then ⟨[0, 1, 2], [1, 2, 0],
    [false, false, false]⟩ else ⟨[1, 0, 2], [1, 2, 0], [false, false, false]⟩)) else (if i.val <
    704 then ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩ else ⟨[0, 1, 2], [0, 1, 2], [false,
    false, false]⟩)) else (if i.val < 709 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩
    else (if i.val < 711 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else (if i.val < 712
    then ⟨[1, 0, 2], [1, 2, 0], [false, false, false]⟩ else ⟨[0, 1, 2], [1, 2, 0], [false,
    false, false]⟩))))))) else (if i.val < 764 then (if i.val < 738 then (if i.val < 725 then
    (if i.val < 719 then (if i.val < 716 then (if i.val < 714 then ⟨[1, 0, 2], [1, 2, 0],
    [false, false, false]⟩ else (if i.val < 715 then ⟨[0, 1, 2], [1, 2, 0], [false, false,
    false]⟩ else ⟨[1, 0, 2], [1, 2, 0], [false, false, false]⟩)) else (if i.val < 717 then ⟨[0,
    1, 2], [1, 2, 0], [false, false, false]⟩ else (if i.val < 718 then ⟨[1, 0, 2], [1, 2, 0],
    [false, false, false]⟩ else ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩))) else (if i.val
    < 722 then (if i.val < 720 then ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩ else ⟨[0, 1,
    2], [0, 1, 2], [false, false, false]⟩) else (if i.val < 723 then ⟨[0, 1, 2], [0, 1, 2],
    [false, false, false]⟩ else (if i.val < 724 then ⟨[1, 0, 2], [1, 2, 0], [false, false,
    false]⟩ else ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩)))) else (if i.val < 731 then (if
    i.val < 728 then (if i.val < 726 then ⟨[1, 0, 2], [1, 2, 0], [false, false, false]⟩ else
    ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩) else (if i.val < 729 then ⟨[0, 1, 2], [1, 2,
    0], [false, false, false]⟩ else (if i.val < 730 then ⟨[0, 1, 2], [1, 2, 0], [false, false,
    false]⟩ else ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩))) else (if i.val < 734 then ⟨[0,
    1, 2], [0, 1, 2], [false, false, false]⟩ else (if i.val < 736 then ⟨[0, 1, 2], [0, 1, 2],
    [false, false, false]⟩ else (if i.val < 737 then ⟨[0, 1, 2], [0, 1, 2], [false, false,
    false]⟩ else ⟨[1, 0, 2], [1, 2, 0], [false, false, false]⟩))))) else (if i.val < 751 then
    (if i.val < 744 then (if i.val < 741 then (if i.val < 739 then ⟨[0, 1, 2], [1, 2, 0],
    [false, false, false]⟩ else (if i.val < 740 then ⟨[1, 0, 2], [1, 2, 0], [false, false,
    false]⟩ else ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩)) else (if i.val < 742 then ⟨[1,
    0, 2], [1, 2, 0], [false, false, false]⟩ else (if i.val < 743 then ⟨[0, 1, 2], [1, 2, 0],
    [false, false, false]⟩ else ⟨[1, 0, 2], [1, 2, 0], [false, false, false]⟩))) else (if i.val
    < 747 then ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩ else (if i.val < 749 then (if i.val
    < 748 then ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩ else ⟨[0, 1, 2], [0, 1, 2], [false,
    false, false]⟩) else ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩))) else (if i.val < 757
    then (if i.val < 754 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else (if i.val < 755
    then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else (if i.val < 756 then ⟨[1, 0, 2], [1,
    2, 0], [false, false, false]⟩ else ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩))) else (if
    i.val < 760 then (if i.val < 758 then ⟨[1, 0, 2], [1, 2, 0], [false, false, false]⟩ else (if
    i.val < 759 then ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩ else ⟨[1, 0, 2], [1, 2, 0],
    [false, false, false]⟩)) else (if i.val < 762 then (if i.val < 761 then ⟨[0, 1, 2], [1, 2,
    0], [false, false, false]⟩ else ⟨[1, 0, 2], [1, 2, 0], [false, false, false]⟩) else ⟨[0, 1,
    2], [1, 2, 0], [false, false, false]⟩))))) else (if i.val < 789 then (if i.val < 776 then
    (if i.val < 770 then (if i.val < 767 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else
    (if i.val < 768 then ⟨[1, 0, 2], [1, 2, 0], [false, false, false]⟩ else (if i.val < 769 then
    ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩ else ⟨[1, 0, 2], [1, 2, 0], [false, false,
    false]⟩))) else (if i.val < 773 then ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩ else (if
    i.val < 774 then ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩ else ⟨[0, 1, 2], [0, 1, 2],
    [false, false, false]⟩))) else (if i.val < 782 then (if i.val < 779 then ⟨[0, 1, 2], [0, 1,
    2], [false, false, false]⟩ else (if i.val < 780 then ⟨[0, 1, 2], [0, 1, 2], [false, false,
    false]⟩ else (if i.val < 781 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else ⟨[1, 0,
    2], [1, 2, 0], [false, false, false]⟩))) else (if i.val < 785 then (if i.val < 783 then ⟨[0,
    1, 2], [1, 2, 0], [false, false, false]⟩ else (if i.val < 784 then ⟨[1, 0, 2], [1, 2, 0],
    [false, false, false]⟩ else ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩)) else (if i.val <
    787 then (if i.val < 786 then ⟨[1, 0, 2], [1, 2, 0], [false, false, false]⟩ else ⟨[0, 1, 2],
    [1, 2, 0], [false, false, false]⟩) else (if i.val < 788 then ⟨[1, 0, 2], [1, 2, 0], [false,
    false, false]⟩ else ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩))))) else (if i.val < 802
    then (if i.val < 795 then (if i.val < 792 then (if i.val < 790 then ⟨[0, 1, 2], [1, 2, 0],
    [false, false, false]⟩ else ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩) else (if i.val <
    793 then ⟨[0, 1, 2], [0, 1, 2], [false, false, false]⟩ else (if i.val < 794 then ⟨[1, 0, 2],
    [1, 2, 0], [false, false, false]⟩ else ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩))) else
    (if i.val < 798 then (if i.val < 796 then ⟨[1, 0, 2], [1, 2, 0], [false, false, false]⟩ else
    ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩) else (if i.val < 800 then ⟨[0, 1, 2], [0, 1,
    2], [false, false, false]⟩ else (if i.val < 801 then ⟨[0, 1, 2], [0, 1, 2], [false, false,
    false]⟩ else ⟨[1, 0, 2], [1, 2, 0], [false, false, false]⟩)))) else (if i.val < 808 then (if
    i.val < 805 then (if i.val < 803 then ⟨[0, 1, 2], [1, 2, 0], [false, false, false]⟩ else (if
    i.val < 804 then ⟨[1, 0, 2], [1, 2, 0], [false, false, false]⟩ else ⟨[0, 1, 2], [1, 2, 0],
    [false, false, false]⟩)) else ⟨[0, 1], [2, 0, 1], [false, false, false]⟩) else ⟨[0, 1], [2,
    0, 1], [false, false, false]⟩)))))))

/-- The kernel checks all decorations and node branches in every constructed graph. -/
theorem hints_valid : ∀ i, (hint i).check
    ((term i).expression.decoratedGraph (term i).decoration) (L24Graphs.graph i) = true := by
  decide +kernel

/-- Each constructed term denotes precisely the held raw graph class. -/
theorem term_stratum (i : Fin 815) :
    (term i).expression.decoratedStratum (term i).decoration = L24Graphs.columns i := by
  apply Quotient.sound
  exact (DecoratedStableGraph.isomorphic?_eq_true_iff _ _).mp
    (GraphIsomorphismHint.check_sound (hint i) _ _ (hints_valid i))

end AxiomaticGW.L24Gluing

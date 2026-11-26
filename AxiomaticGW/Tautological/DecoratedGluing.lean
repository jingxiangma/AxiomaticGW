/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GluingExpression
public import AxiomaticGW.Tautological.LegPsi

/-!
# Cotangent decorations on existing gluing expressions

Cotangent powers are attached to the labelled markings of each original
component. The existing raw gluings then turn the distinguished markings
into decorated node branches. This is data indexed by the existing expression,
not a second graph syntax. No kappa decoration or automorphism division is added.
-/

@[expose] public section

namespace AxiomaticGW.GluingExpression

/-- Powers at the original component markings, including future node branches. -/
@[reducible] def CotangentDecoration {g : ℕ} {S : Type} [Fintype S] : GluingExpression g S → Type
  | @fundamental _ S _ _ => S → ℕ
  | @relabel _ _ _ _ _ _ x => x.CotangentDecoration
  | @separating _ _ _ _ _ _ x y => x.CotangentDecoration × y.CotangentDecoration
  | @nonseparating _ _ _ x => x.CotangentDecoration

/-- Zero decoration on every original component. -/
def zeroDecoration {g : ℕ} {S : Type} [Fintype S] :
    (x : GluingExpression g S) → x.CotangentDecoration
  | @fundamental _ _ _ _ => fun _ ↦ 0
  | @relabel _ _ _ _ _ _ x => x.zeroDecoration
  | @separating _ _ _ _ _ _ x y => (x.zeroDecoration, y.zeroDecoration)
  | @nonseparating _ _ _ x => x.zeroDecoration

/-- Raw gluings transport all original cotangent factors to the actual graph flags. -/
def decoratedGraph {g : ℕ} {S : Type} [Fintype S] :
    (x : GluingExpression g S) → x.CotangentDecoration → DecoratedStableGraph S
  | @fundamental g S _ h, d => DecoratedStableGraph.oneVertex g S h 0 d
  | @relabel _ _ _ _ _ e x, d => (x.decoratedGraph d).relabel e
  | @separating _ _ _ _ _ _ x y, d =>
      (x.decoratedGraph d.1).separating (y.decoratedGraph d.2)
  | @nonseparating _ _ _ x, d => (x.decoratedGraph d).nonseparating

/-- Cotangent decorations preserve the arithmetic genus. -/
theorem decoratedGraph_totalGenus {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (d : x.CotangentDecoration) :
    (x.decoratedGraph d).graph.totalGenus = g := by
  induction x with
  | fundamental g S h => exact DecoratedStableGraph.oneVertex_totalGenus g S h 0 d
  | relabel e x ih =>
    simpa only [decoratedGraph, DecoratedStableGraph.relabel,
      StableGraphCode.relabel_totalGenus] using ih d
  | separating x y ihx ihy =>
    simp only [decoratedGraph, DecoratedStableGraph.separating,
      StableGraphCode.separating_totalGenus, ihx, ihy]
  | nonseparating x ih =>
    simp only [decoratedGraph, DecoratedStableGraph.nonseparating,
      StableGraphCode.nonseparating_totalGenus, ih]

/-- The actual decorated stratum in the existing graph-isomorphism quotient. -/
def decoratedStratum {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (d : x.CotangentDecoration) : TautologicalStratum g S :=
  .mk (x.decoratedGraph d) (x.decoratedGraph_totalGenus d)

/-- A terminal component is the existing fundamental class times its psi monomial. -/
theorem decoratedStratum_fundamental {g : ℕ} {S : Type} [Fintype S]
    (h : StableArity g S) (d : S → ℕ) :
    (fundamental g S h).decoratedStratum d =
      (TautologicalStratum.fundamental g S h).addLegPsi d := by
  rw [TautologicalStratum.fundamental, TautologicalStratum.addLegPsi_oneVertex]
  change TautologicalStratum.oneVertex g S h 0 d =
    TautologicalStratum.oneVertex g S h 0 ((0 : S → ℕ) + d)
  rw [zero_add]

/-- External label transport is the existing decorated quotient operation. -/
theorem decoratedStratum_relabel {g : ℕ} {S T : Type} [Fintype S] [Fintype T]
    (e : S ≃ T) (x : GluingExpression g S) (d : x.CotangentDecoration) :
    (x.relabel e).decoratedStratum d = (x.decoratedStratum d).relabel e := rfl

/-- Separating gluing retains both original branch powers. -/
theorem decoratedStratum_separating {g₁ g₂ : ℕ} {S T : Type} [Fintype S] [Fintype T]
    (x : GluingExpression g₁ (Option S)) (y : GluingExpression g₂ (Option T))
    (d : x.CotangentDecoration × y.CotangentDecoration) :
    (x.separating y).decoratedStratum d =
      (x.decoratedStratum d.1).separating (y.decoratedStratum d.2) := rfl

/-- Nonseparating gluing retains both ordered cotangent decorations at the loop. -/
theorem decoratedStratum_nonseparating {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g (Option (Option S))) (d : x.CotangentDecoration) :
    x.nonseparating.decoratedStratum d = (x.decoratedStratum d).nonseparating := rfl

/-- The previous undecorated graph is recovered without any change of presentation. -/
theorem decoratedGraph_zero {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) :
    x.decoratedGraph x.zeroDecoration = x.graph := by
  induction x with
  | fundamental g S h => rfl
  | relabel e x ih => simp only [decoratedGraph, zeroDecoration, graph, ih]
  | separating x y ihx ihy => simp only [decoratedGraph, zeroDecoration, graph, ihx, ihy]
  | nonseparating x ih => simp only [decoratedGraph, zeroDecoration, graph, ih]

/-- Zero decoration preserves the old public stratum. -/
theorem decoratedStratum_zero {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) :
    x.decoratedStratum x.zeroDecoration = x.stratum := by
  unfold decoratedStratum stratum
  congr 1
  exact decoratedGraph_zero x

/-- Largest genus of an original component, excluding graph cycles. -/
def maxComponentGenus {g : ℕ} {S : Type} [Fintype S] : GluingExpression g S → ℕ
  | @fundamental g _ _ _ => g
  | @relabel _ _ _ _ _ _ x => x.maxComponentGenus
  | @separating _ _ _ _ _ _ x y => max x.maxComponentGenus y.maxComponentGenus
  | @nonseparating _ _ _ x => x.maxComponentGenus

end AxiomaticGW.GluingExpression

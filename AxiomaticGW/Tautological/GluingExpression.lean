/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.BasicStrata
public import AxiomaticGW.Tautological.Relabel
public import AxiomaticGW.Tautological.SeparatingGluing
public import AxiomaticGW.Tautological.NonseparatingGluing

/-!
# Explicit compositions of raw graph gluings

An expression records how a labelled graph is built from stable one-vertex
components, separating and nonseparating gluings, and actual label bijections.
It supplies a compositional witness for graph evaluation; it does not identify
different expressions or assert independence of a chosen decomposition.

The first consumer is the seven Getzler graph families. All operations are raw
pushforward operations: automorphism and marking-orbit factors belong to the
relation coordinates, not to this syntax.
-/

@[expose] public section

namespace AxiomaticGW

/-- A finite, typed construction of an undecorated stable graph. -/
inductive GluingExpression : (g : ℕ) → (S : Type) → [Fintype S] → Type 1 where
  /-- A stable component before any nodes are glued. -/
  | fundamental (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) :
      GluingExpression g S
  /-- Covariant external label transport. -/
  | relabel {g : ℕ} {S T : Type} [Fintype S] [Fintype T]
      (e : S ≃ T) (x : GluingExpression g S) : GluingExpression g T
  /-- Glue the distinguished `none` labels of two connected expressions. -/
  | separating {g₁ g₂ : ℕ} {S T : Type} [Fintype S] [Fintype T]
      (x : GluingExpression g₁ (Option S)) (y : GluingExpression g₂ (Option T)) :
      GluingExpression (g₁ + g₂) (S ⊕ T)
  /-- Glue `none` and `some none`, retaining the other external labels. -/
  | nonseparating {g : ℕ} {S : Type} [Fintype S]
      (x : GluingExpression g (Option (Option S))) : GluingExpression (g + 1) S

namespace GluingExpression

/-- Stability follows from the component stability and the elementary operations. -/
theorem stable {g : ℕ} {S : Type} [Fintype S] :
    (x : GluingExpression g S) → StableArity g S
  | @fundamental _ _ _ h => h
  | @relabel _ _ _ _ _ e x => (StableArity.equiv e).mp x.stable
  | @separating _ _ _ _ _ _ x y => StableArity.separating x.stable y.stable
  | @nonseparating _ _ _ x => StableArity.double_option_iff.mp x.stable

/-- The actual finite graph, rather than a name for a supplied stratum. -/
def graph {g : ℕ} {S : Type} [Fintype S] : GluingExpression g S → DecoratedStableGraph S
  | @fundamental g S _ h => DecoratedStableGraph.oneVertex g S h 0 (fun _ ↦ 0)
  | @relabel _ _ _ _ _ e x => x.graph.relabel e
  | @separating _ _ _ _ _ _ x y => x.graph.separating y.graph
  | @nonseparating _ _ _ x => x.graph.nonseparating

variable {g : ℕ} {S : Type} [Fintype S]

/-- The expression's genus index agrees with the arithmetic genus of its graph. -/
theorem graph_totalGenus (x : GluingExpression g S) : x.graph.graph.totalGenus = g := by
  induction x with
  | fundamental g S h => exact DecoratedStableGraph.oneVertex_totalGenus g S h 0 _
  | relabel e x ih =>
    simpa only [graph, DecoratedStableGraph.relabel,
      StableGraphCode.relabel_totalGenus] using ih
  | separating x y ihx ihy =>
    simp only [graph, DecoratedStableGraph.separating,
      StableGraphCode.separating_totalGenus, ihx, ihy]
  | nonseparating x ih =>
    simp only [graph, DecoratedStableGraph.nonseparating,
      StableGraphCode.nonseparating_totalGenus, ih]

/-- The graph's existing isomorphism class in the free strata module. -/
def stratum (x : GluingExpression g S) : TautologicalStratum g S :=
  TautologicalStratum.mk x.graph x.graph_totalGenus

/-- The one-vertex expression is the existing fundamental stratum. -/
theorem stratum_fundamental (h : StableArity g S) :
    (fundamental g S h).stratum = TautologicalStratum.fundamental g S h := rfl

/-- Expression relabelling is exactly the existing quotient operation. -/
theorem stratum_relabel {T : Type} [Fintype T] (e : S ≃ T)
    (x : GluingExpression g S) : (x.relabel e).stratum = x.stratum.relabel e := rfl

/-- Expression gluing is exactly the existing raw separating operation. -/
theorem stratum_separating {g₁ g₂ : ℕ} {S T : Type} [Fintype S] [Fintype T]
    (x : GluingExpression g₁ (Option S)) (y : GluingExpression g₂ (Option T)) :
    (x.separating y).stratum = x.stratum.separating y.stratum := rfl

/-- The self-gluing expression uses both actual distinguished source labels. -/
theorem stratum_nonseparating (x : GluingExpression g (Option (Option S))) :
    x.nonseparating.stratum = x.stratum.nonseparating := rfl

end GluingExpression

end AxiomaticGW

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.Relabel
public import AxiomaticGW.Tautological.SeparatingGluing
public import AxiomaticGW.Tautological.BasicStrata
public import AxiomaticGW.Tautological.RelationCertificate
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Explicit four-point genus-zero boundary relations

The three raw graph columns have partitions `01|23`, `02|13`, `03|12`.
They are distinct formal strata of codimension one, not three names for
the same quotient graph. The two rows impose their geometric equality;
the row-span calculation does not prove that geometric input.
-/

@[expose] public section

namespace AxiomaticGW.WDVV

/-- The fixed four-point target belongs to the full stable-curve locus. -/
theorem stableArity : StableArity 0 (Fin 4) := by norm_num [StableArity]

/-- The stable rational three-point component, with `none` as its node label. -/
def component : DecoratedStableGraph (Option (Fin 2)) :=
  DecoratedStableGraph.oneVertex 0 _ StableArity.zero_option_fin_two 0 (fun _ ↦ 0)

/-- Ordered raw gluing before changing its external label type. -/
def sourceGraph : DecoratedStableGraph (Fin 2 ⊕ Fin 2) := component.separating component

/-- Covariant label maps for the three four-point boundary partitions. -/
def labels (i : Fin 3) : (Fin 2 ⊕ Fin 2) ≃ Fin 4 :=
  finSumFinEquiv.trans (![Equiv.refl _, Equiv.swap 1 2, Equiv.swap 1 3] i)

/-- A channel is the actual graph operation followed by external relabelling. -/
def graph (i : Fin 3) : DecoratedStableGraph (Fin 4) := sourceGraph.relabel (labels i)

/-- Every channel has total genus zero. -/
theorem graph_totalGenus (i : Fin 3) : (graph i).graph.totalGenus = 0 := by
  rw [graph, DecoratedStableGraph.relabel, StableGraphCode.relabel_totalGenus]
  simp only [sourceGraph, DecoratedStableGraph.separating,
    StableGraphCode.separating_totalGenus, component, DecoratedStableGraph.oneVertex_totalGenus]

/-- Every raw channel is a divisor, with no psi or kappa decoration. -/
theorem graph_codimension (i : Fin 3) : (graph i).codimension = 1 := by
  rw [graph, DecoratedStableGraph.relabel_codimension, sourceGraph,
    DecoratedStableGraph.separating_codimension]
  simp only [component, DecoratedStableGraph.oneVertex_codimension,
    Finsupp.sum_zero_index, Finset.sum_const_zero, Nat.zero_add]

/-- The three labelled graph classes used by the certificate frame. -/
def columns (i : Fin 3) : TautologicalStratum 0 (Fin 4) :=
  TautologicalStratum.mk (graph i) (graph_totalGenus i)

/-- The quotient columns retain their explicit gluing and label transport. -/
theorem columns_eq_relabel_separating (i : Fin 3) :
    columns i = ((TautologicalStratum.fundamental 0 (Option (Fin 2))
      StableArity.zero_option_fin_two).separating
        (TautologicalStratum.fundamental 0 (Option (Fin 2))
          StableArity.zero_option_fin_two)).relabel (labels i) := rfl

/-- Raw coefficients need no automorphism conversion for these labelled channels. -/
theorem graph_automorphismCount (i : Fin 3) : (graph i).automorphismCount = 1 := by
  fin_cases i <;> decide

/-- Distinct channel partitions are not label-fixing graph isomorphisms. -/
theorem graph_isomorphic?_iff :
    ∀ i j : Fin 3, (graph i).isomorphic? (graph j) = true ↔ i = j := by decide

/-- The fixed coordinate frame has distinct semantic graph columns. -/
theorem columns_injective : Function.Injective columns := by
  intro i j h
  obtain ⟨e⟩ := Quotient.exact h
  apply (graph_isomorphic?_iff i j).mp
  exact (DecoratedStableGraph.isomorphic?_eq_true_iff _ _).mpr ⟨e⟩

/-- The two independent raw boundary-equality rows. -/
def rows : Fin 2 → RelationCertificate.Coordinates 3 := ![![1,-1,0], ![0,1,-1]]

/-- A fixed searched consequence, using both rows. -/
def requested : RelationCertificate.Coordinates 3 := ![1,0,-1]

/-- Exact row combination for the separately fixed requested consequence. -/
def certificate : RelationCertificate.Certificate 2 := ⟨![1,1]⟩

/-- Kernel arithmetic verifies the proposed two-row witness. -/
theorem check_requested : RelationCertificate.check rows requested certificate = true := by
  rw [RelationCertificate.check_eq_true_iff]
  funext i
  fin_cases i <;>
    norm_num [RelationCertificate.combination, rows, requested, certificate, Fin.sum_univ_two]

/-- The explicit formal graph relation corresponding to each original row. -/
noncomputable def relation (i : Fin 2) : StrataModule 0 (Fin 4) :=
  RelationCertificate.interpret columns (rows i)

/-- The chosen rows are homogeneous of codimension one. -/
theorem relation_mem_degree (i : Fin 2) : relation i ∈ StrataModule.degree 1 := by
  apply RelationCertificate.interpret_mem_degree
  intro j
  exact graph_codimension j

/-- The requested consequence is a nonzero formal combination, so replay
does not succeed because the three graph columns were identified. -/
theorem requested_ne_zero : RelationCertificate.interpret columns requested ≠ 0 := by
  intro h
  have he := congrArg (fun r ↦ r (columns 0)) h
  rw [RelationCertificate.interpret_apply_column columns columns_injective] at he
  exact (by decide : (1 : ℚ) ≠ 0) he

/-- A proposed presentation must match the fixed graph frame, normalization,
original boundary rows, and independently held requested consequence. -/
abbrev AcceptsExchange (p : RelationCertificate.Presentation 0 (Fin 4) 2 3) : Prop :=
  RelationCertificate.AcceptsPresentation columns rows requested p

end AxiomaticGW.WDVV

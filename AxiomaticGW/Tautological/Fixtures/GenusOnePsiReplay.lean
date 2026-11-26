/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GenusOnePsi

/-!
# Candidate replay of the held genus-one psi relation

Input SHA256: 61d59f804e3d891906288149ebfcecd7f03fb0eb115c62b509194606f7fb2c85
Digest is provenance only. Geometric row validity remains an input.
-/

@[expose] public section

namespace AxiomaticGW.GenusOnePsiReplay

/-- Raw incidence and vertex genera exported for column 0. -/
def incomingGraph0Candidate : StableGraphCode.Candidate (Fin 1) 1 0 where
  legVertex := ![0]
  endpoint := Fin.elim0
  genus := ![1]

/-- The incoming graph satisfies stability and total genus one. -/
theorem incomingGraph0Valid : incomingGraph0Candidate.Valid 1 := by decide +kernel

/-- Incoming kappa, external psi and node psi exponents. -/
def incomingGraph0Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 1 → ℕ
  | .inl (vertex, index) => (![![1]] : Fin 1 → Fin 1 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- The actual incoming decorated graph in the strata quotient. -/
def incomingGraph0 : TautologicalStratum 1 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph0Candidate incomingGraph0Valid incomingGraph0Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph0Candidate incomingGraph0Valid incomingGraph0Exponents)

/-- The incoming decorated graph agrees with the independently held column. -/
theorem incomingGraph0_eq : incomingGraph0 = GenusOnePsi.columns 0 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph0Candidate incomingGraph0Valid incomingGraph0Exponents)
    (GenusOnePsi.graph_totalGenus 0)
    (by simp only [GenusOnePsi.graph, DecoratedStableGraph.toDecoration_eq_mk];
        decide +kernel)

/-- Raw incidence and vertex genera exported for column 1. -/
def incomingGraph1Candidate : StableGraphCode.Candidate (Fin 1) 1 0 where
  legVertex := ![0]
  endpoint := Fin.elim0
  genus := ![1]

/-- The incoming graph satisfies stability and total genus one. -/
theorem incomingGraph1Valid : incomingGraph1Candidate.Valid 1 := by decide +kernel

/-- Incoming kappa, external psi and node psi exponents. -/
def incomingGraph1Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 1 → ℕ
  | .inl (vertex, index) => (![![0]] : Fin 1 → Fin 1 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- The actual incoming decorated graph in the strata quotient. -/
def incomingGraph1 : TautologicalStratum 1 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph1Candidate incomingGraph1Valid incomingGraph1Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph1Candidate incomingGraph1Valid incomingGraph1Exponents)

/-- The incoming decorated graph agrees with the independently held column. -/
theorem incomingGraph1_eq : incomingGraph1 = GenusOnePsi.columns 1 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph1Candidate incomingGraph1Valid incomingGraph1Exponents)
    (GenusOnePsi.graph_totalGenus 1)
    (by simp only [GenusOnePsi.graph, DecoratedStableGraph.toDecoration_eq_mk];
        decide +kernel)

/-- Raw incidence and vertex genera exported for column 2. -/
def incomingGraph2Candidate : StableGraphCode.Candidate (Fin 1) 1 1 where
  legVertex := ![0]
  endpoint := ![![0, 0]]
  genus := ![0]

/-- The incoming graph satisfies stability and total genus one. -/
theorem incomingGraph2Valid : incomingGraph2Candidate.Valid 1 := by decide +kernel

/-- Incoming kappa, external psi and node psi exponents. -/
def incomingGraph2Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 1 → ℕ
  | .inl (vertex, index) => (![![0]] : Fin 1 → Fin 1 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

/-- The actual incoming decorated graph in the strata quotient. -/
def incomingGraph2 : TautologicalStratum 1 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph2Candidate incomingGraph2Valid incomingGraph2Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph2Candidate incomingGraph2Valid incomingGraph2Exponents)

/-- The incoming decorated graph agrees with the independently held column. -/
theorem incomingGraph2_eq : incomingGraph2 = GenusOnePsi.columns 2 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph2Candidate incomingGraph2Valid incomingGraph2Exponents)
    (GenusOnePsi.graph_totalGenus 2)
    (by simp only [GenusOnePsi.graph, DecoratedStableGraph.toDecoration_eq_mk];
        decide +kernel)

/-- Incoming columns in the original source order. -/
def incomingColumns : Fin 3 → TautologicalStratum 1 (Fin 1) :=
  ![incomingGraph0, incomingGraph1, incomingGraph2]

/-- Reported raw graph automorphism counts. -/
def incomingAutomorphisms : Fin 3 → ℕ :=
  ![1, 1, 2]

/-- Each reported automorphism count is checked against its held graph. -/
theorem automorphisms_correct : ∀ i, incomingAutomorphisms i =
    (GenusOnePsi.graph i).automorphismCount := by
  simp only [GenusOnePsi.graph, DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Original rows, normalization, requested equation and rational witness. -/
def presentation : RelationCertificate.Presentation 1 (Fin 1) 2 3 where
  columns := incomingColumns
  columnFactors := ![1, 1, 1]
  rows := ![![102, -30, -3],
    ![30, 42, -3]]
  claimedRequest := ![0, 1, (-1 / 24)]
  certificate := ⟨![(-5 / 864), (17 / 864)]⟩

/-- All incoming data agree with the held frame and satisfy its exact equation. -/
theorem accepted : GenusOnePsi.AcceptsExchange presentation := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change incomingColumns = GenusOnePsi.columns
      funext i
      fin_cases i
      · exact incomingGraph0_eq
      · exact incomingGraph1_eq
      · exact incomingGraph2_eq
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · decide +kernel

/-- The accepted requested relation lies in the span of the original rows. -/
theorem requested_mem_relationSpan :
    RelationCertificate.interpret GenusOnePsi.columns GenusOnePsi.requested ∈
      RelationCertificate.relationSpan GenusOnePsi.columns GenusOnePsi.rows :=
  RelationCertificate.acceptsPresentation_sound _ _ _ presentation accepted

end AxiomaticGW.GenusOnePsiReplay

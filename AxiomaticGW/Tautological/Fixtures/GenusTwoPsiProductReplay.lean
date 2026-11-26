/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GenusTwoPsiProduct

/-!
# Incoming replay of the held marked genus-two psi-product relation

Input SHA256: b22e8c432358044fec84188b96a5747cdf3ff14d4317686ebe6c661d62fe85b0
The digest records provenance only. Geometric validity remains explicit.
-/

@[expose] public section

namespace AxiomaticGW.GenusTwoPsiProductReplay

/-- Actual incoming incidence and genera for column 0. -/
def incomingGraph0Candidate : StableGraphCode.Candidate (Fin 2) 1 0 where
  legVertex := ![0, 0]
  endpoint := Fin.elim0
  genus := ![2]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph0Valid : incomingGraph0Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph0Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 1 0 2 → ℕ
  | .inl (vertex, index) => (![![0, 1]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph0 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph0Candidate incomingGraph0Valid incomingGraph0Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph0Candidate incomingGraph0Valid incomingGraph0Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph0_eq : incomingGraph0 = GenusTwoPsiProduct.columns 0 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph0Candidate incomingGraph0Valid incomingGraph0Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 0)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 1. -/
def incomingGraph1Candidate : StableGraphCode.Candidate (Fin 2) 1 0 where
  legVertex := ![0, 0]
  endpoint := Fin.elim0
  genus := ![2]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph1Valid : incomingGraph1Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph1Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 1 0 2 → ℕ
  | .inl (vertex, index) => (![![2, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph1 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph1Candidate incomingGraph1Valid incomingGraph1Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph1Candidate incomingGraph1Valid incomingGraph1Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph1_eq : incomingGraph1 = GenusTwoPsiProduct.columns 1 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph1Candidate incomingGraph1Valid incomingGraph1Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 1)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 2. -/
def incomingGraph2Candidate : StableGraphCode.Candidate (Fin 2) 1 0 where
  legVertex := ![0, 0]
  endpoint := Fin.elim0
  genus := ![2]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph2Valid : incomingGraph2Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph2Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 1 0 2 → ℕ
  | .inl (vertex, index) => (![![1, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![1, 0]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph2 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph2Candidate incomingGraph2Valid incomingGraph2Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph2Candidate incomingGraph2Valid incomingGraph2Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph2_eq : incomingGraph2 = GenusTwoPsiProduct.columns 2 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph2Candidate incomingGraph2Valid incomingGraph2Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 2)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 3. -/
def incomingGraph3Candidate : StableGraphCode.Candidate (Fin 2) 1 0 where
  legVertex := ![0, 0]
  endpoint := Fin.elim0
  genus := ![2]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph3Valid : incomingGraph3Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph3Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 1 0 2 → ℕ
  | .inl (vertex, index) => (![![1, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 1]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph3 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph3Candidate incomingGraph3Valid incomingGraph3Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph3Candidate incomingGraph3Valid incomingGraph3Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph3_eq : incomingGraph3 = GenusTwoPsiProduct.columns 3 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph3Candidate incomingGraph3Valid incomingGraph3Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 3)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 4. -/
def incomingGraph4Candidate : StableGraphCode.Candidate (Fin 2) 1 0 where
  legVertex := ![0, 0]
  endpoint := Fin.elim0
  genus := ![2]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph4Valid : incomingGraph4Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph4Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 1 0 2 → ℕ
  | .inl (vertex, index) => (![![0, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![2, 0]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph4 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph4Candidate incomingGraph4Valid incomingGraph4Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph4Candidate incomingGraph4Valid incomingGraph4Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph4_eq : incomingGraph4 = GenusTwoPsiProduct.columns 4 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph4Candidate incomingGraph4Valid incomingGraph4Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 4)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 5. -/
def incomingGraph5Candidate : StableGraphCode.Candidate (Fin 2) 1 0 where
  legVertex := ![0, 0]
  endpoint := Fin.elim0
  genus := ![2]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph5Valid : incomingGraph5Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph5Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 1 0 2 → ℕ
  | .inl (vertex, index) => (![![0, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![1, 1]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph5 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph5Candidate incomingGraph5Valid incomingGraph5Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph5Candidate incomingGraph5Valid incomingGraph5Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph5_eq : incomingGraph5 = GenusTwoPsiProduct.columns 5 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph5Candidate incomingGraph5Valid incomingGraph5Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 5)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 6. -/
def incomingGraph6Candidate : StableGraphCode.Candidate (Fin 2) 1 0 where
  legVertex := ![0, 0]
  endpoint := Fin.elim0
  genus := ![2]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph6Valid : incomingGraph6Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph6Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 1 0 2 → ℕ
  | .inl (vertex, index) => (![![0, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 2]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph6 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph6Candidate incomingGraph6Valid incomingGraph6Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph6Candidate incomingGraph6Valid incomingGraph6Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph6_eq : incomingGraph6 = GenusTwoPsiProduct.columns 6 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph6Candidate incomingGraph6Valid incomingGraph6Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 6)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 7. -/
def incomingGraph7Candidate : StableGraphCode.Candidate (Fin 2) 2 1 where
  legVertex := ![0, 0]
  endpoint := ![![0, 1]]
  genus := ![0, 2]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph7Valid : incomingGraph7Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph7Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![1, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph7 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph7Candidate incomingGraph7Valid incomingGraph7Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph7Candidate incomingGraph7Valid incomingGraph7Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph7_eq : incomingGraph7 = GenusTwoPsiProduct.columns 7 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph7Candidate incomingGraph7Valid incomingGraph7Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 7)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 8. -/
def incomingGraph8Candidate : StableGraphCode.Candidate (Fin 2) 2 1 where
  legVertex := ![0, 0]
  endpoint := ![![0, 1]]
  genus := ![0, 2]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph8Valid : incomingGraph8Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph8Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 1]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph8 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph8Candidate incomingGraph8Valid incomingGraph8Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph8Candidate incomingGraph8Valid incomingGraph8Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph8_eq : incomingGraph8 = GenusTwoPsiProduct.columns 8 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph8Candidate incomingGraph8Valid incomingGraph8Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 8)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 9. -/
def incomingGraph9Candidate : StableGraphCode.Candidate (Fin 2) 2 1 where
  legVertex := ![1, 1]
  endpoint := ![![0, 1]]
  genus := ![1, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph9Valid : incomingGraph9Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph9Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![1, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph9 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph9Candidate incomingGraph9Valid incomingGraph9Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph9Candidate incomingGraph9Valid incomingGraph9Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph9_eq : incomingGraph9 = GenusTwoPsiProduct.columns 9 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph9Candidate incomingGraph9Valid incomingGraph9Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 9)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 10. -/
def incomingGraph10Candidate : StableGraphCode.Candidate (Fin 2) 2 1 where
  legVertex := ![1, 1]
  endpoint := ![![0, 1]]
  genus := ![1, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph10Valid : incomingGraph10Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph10Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![1, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph10 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph10Candidate incomingGraph10Valid incomingGraph10Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph10Candidate incomingGraph10Valid incomingGraph10Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph10_eq : incomingGraph10 = GenusTwoPsiProduct.columns 10 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph10Candidate incomingGraph10Valid incomingGraph10Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 10)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 11. -/
def incomingGraph11Candidate : StableGraphCode.Candidate (Fin 2) 2 1 where
  legVertex := ![1, 1]
  endpoint := ![![0, 1]]
  genus := ![1, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph11Valid : incomingGraph11Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph11Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 1]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph11 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph11Candidate incomingGraph11Valid incomingGraph11Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph11Candidate incomingGraph11Valid incomingGraph11Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph11_eq : incomingGraph11 = GenusTwoPsiProduct.columns 11 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph11Candidate incomingGraph11Valid incomingGraph11Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 11)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 12. -/
def incomingGraph12Candidate : StableGraphCode.Candidate (Fin 2) 2 1 where
  legVertex := ![1, 1]
  endpoint := ![![0, 1]]
  genus := ![1, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph12Valid : incomingGraph12Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph12Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 1]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph12 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph12Candidate incomingGraph12Valid incomingGraph12Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph12Candidate incomingGraph12Valid incomingGraph12Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph12_eq : incomingGraph12 = GenusTwoPsiProduct.columns 12 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph12Candidate incomingGraph12Valid incomingGraph12Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 12)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 13. -/
def incomingGraph13Candidate : StableGraphCode.Candidate (Fin 2) 2 1 where
  legVertex := ![1, 0]
  endpoint := ![![0, 1]]
  genus := ![1, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph13Valid : incomingGraph13Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph13Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![1, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph13 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph13Candidate incomingGraph13Valid incomingGraph13Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph13Candidate incomingGraph13Valid incomingGraph13Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph13_eq : incomingGraph13 = GenusTwoPsiProduct.columns 13 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph13Candidate incomingGraph13Valid incomingGraph13Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 13)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 14. -/
def incomingGraph14Candidate : StableGraphCode.Candidate (Fin 2) 2 1 where
  legVertex := ![1, 0]
  endpoint := ![![0, 1]]
  genus := ![1, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph14Valid : incomingGraph14Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph14Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![1, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph14 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph14Candidate incomingGraph14Valid incomingGraph14Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph14Candidate incomingGraph14Valid incomingGraph14Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph14_eq : incomingGraph14 = GenusTwoPsiProduct.columns 14 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph14Candidate incomingGraph14Valid incomingGraph14Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 14)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 15. -/
def incomingGraph15Candidate : StableGraphCode.Candidate (Fin 2) 2 1 where
  legVertex := ![1, 0]
  endpoint := ![![0, 1]]
  genus := ![1, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph15Valid : incomingGraph15Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph15Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 1]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph15 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph15Candidate incomingGraph15Valid incomingGraph15Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph15Candidate incomingGraph15Valid incomingGraph15Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph15_eq : incomingGraph15 = GenusTwoPsiProduct.columns 15 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph15Candidate incomingGraph15Valid incomingGraph15Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 15)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 16. -/
def incomingGraph16Candidate : StableGraphCode.Candidate (Fin 2) 2 1 where
  legVertex := ![1, 0]
  endpoint := ![![0, 1]]
  genus := ![1, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph16Valid : incomingGraph16Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph16Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![1, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph16 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph16Candidate incomingGraph16Valid incomingGraph16Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph16Candidate incomingGraph16Valid incomingGraph16Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph16_eq : incomingGraph16 = GenusTwoPsiProduct.columns 16 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph16Candidate incomingGraph16Valid incomingGraph16Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 16)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 17. -/
def incomingGraph17Candidate : StableGraphCode.Candidate (Fin 2) 2 1 where
  legVertex := ![1, 0]
  endpoint := ![![0, 1]]
  genus := ![1, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph17Valid : incomingGraph17Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph17Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![1, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph17 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph17Candidate incomingGraph17Valid incomingGraph17Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph17Candidate incomingGraph17Valid incomingGraph17Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph17_eq : incomingGraph17 = GenusTwoPsiProduct.columns 17 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph17Candidate incomingGraph17Valid incomingGraph17Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 17)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 18. -/
def incomingGraph18Candidate : StableGraphCode.Candidate (Fin 2) 2 1 where
  legVertex := ![1, 0]
  endpoint := ![![0, 1]]
  genus := ![1, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph18Valid : incomingGraph18Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph18Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 1]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph18 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph18Candidate incomingGraph18Valid incomingGraph18Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph18Candidate incomingGraph18Valid incomingGraph18Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph18_eq : incomingGraph18 = GenusTwoPsiProduct.columns 18 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph18Candidate incomingGraph18Valid incomingGraph18Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 18)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 19. -/
def incomingGraph19Candidate : StableGraphCode.Candidate (Fin 2) 3 2 where
  legVertex := ![0, 0]
  endpoint := ![![0, 2], ![1, 2]]
  genus := ![0, 1, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph19Valid : incomingGraph19Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph19Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph19 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph19Candidate incomingGraph19Valid incomingGraph19Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph19Candidate incomingGraph19Valid incomingGraph19Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph19_eq : incomingGraph19 = GenusTwoPsiProduct.columns 19 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph19Candidate incomingGraph19Valid incomingGraph19Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 19)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 20. -/
def incomingGraph20Candidate : StableGraphCode.Candidate (Fin 2) 3 2 where
  legVertex := ![2, 1]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph20Valid : incomingGraph20Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph20Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph20 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph20Candidate incomingGraph20Valid incomingGraph20Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph20Candidate incomingGraph20Valid incomingGraph20Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph20_eq : incomingGraph20 = GenusTwoPsiProduct.columns 20 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph20Candidate incomingGraph20Valid incomingGraph20Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 20)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 21. -/
def incomingGraph21Candidate : StableGraphCode.Candidate (Fin 2) 3 2 where
  legVertex := ![1, 2]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph21Valid : incomingGraph21Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph21Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph21 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph21Candidate incomingGraph21Valid incomingGraph21Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph21Candidate incomingGraph21Valid incomingGraph21Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph21_eq : incomingGraph21 = GenusTwoPsiProduct.columns 21 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph21Candidate incomingGraph21Valid incomingGraph21Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 21)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 22. -/
def incomingGraph22Candidate : StableGraphCode.Candidate (Fin 2) 3 2 where
  legVertex := ![1, 1]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph22Valid : incomingGraph22Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph22Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph22 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph22Candidate incomingGraph22Valid incomingGraph22Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph22Candidate incomingGraph22Valid incomingGraph22Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph22_eq : incomingGraph22 = GenusTwoPsiProduct.columns 22 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph22Candidate incomingGraph22Valid incomingGraph22Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 22)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 23. -/
def incomingGraph23Candidate : StableGraphCode.Candidate (Fin 2) 2 1 where
  legVertex := ![1, 1]
  endpoint := ![![0, 1]]
  genus := ![1, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph23Valid : incomingGraph23Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph23Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![1, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph23 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph23Candidate incomingGraph23Valid incomingGraph23Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph23Candidate incomingGraph23Valid incomingGraph23Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph23_eq : incomingGraph23 = GenusTwoPsiProduct.columns 23 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph23Candidate incomingGraph23Valid incomingGraph23Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 23)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 24. -/
def incomingGraph24Candidate : StableGraphCode.Candidate (Fin 2) 2 1 where
  legVertex := ![1, 1]
  endpoint := ![![0, 1]]
  genus := ![1, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph24Valid : incomingGraph24Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph24Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![1, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph24 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph24Candidate incomingGraph24Valid incomingGraph24Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph24Candidate incomingGraph24Valid incomingGraph24Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph24_eq : incomingGraph24 = GenusTwoPsiProduct.columns 24 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph24Candidate incomingGraph24Valid incomingGraph24Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 24)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 25. -/
def incomingGraph25Candidate : StableGraphCode.Candidate (Fin 2) 1 1 where
  legVertex := ![0, 0]
  endpoint := ![![0, 0]]
  genus := ![1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph25Valid : incomingGraph25Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph25Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 1 1 2 → ℕ
  | .inl (vertex, index) => (![![1, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph25 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph25Candidate incomingGraph25Valid incomingGraph25Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph25Candidate incomingGraph25Valid incomingGraph25Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph25_eq : incomingGraph25 = GenusTwoPsiProduct.columns 25 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph25Candidate incomingGraph25Valid incomingGraph25Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 25)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 26. -/
def incomingGraph26Candidate : StableGraphCode.Candidate (Fin 2) 1 1 where
  legVertex := ![0, 0]
  endpoint := ![![0, 0]]
  genus := ![1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph26Valid : incomingGraph26Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph26Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 1 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![1, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph26 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph26Candidate incomingGraph26Valid incomingGraph26Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph26Candidate incomingGraph26Valid incomingGraph26Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph26_eq : incomingGraph26 = GenusTwoPsiProduct.columns 26 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph26Candidate incomingGraph26Valid incomingGraph26Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 26)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 27. -/
def incomingGraph27Candidate : StableGraphCode.Candidate (Fin 2) 1 1 where
  legVertex := ![0, 0]
  endpoint := ![![0, 0]]
  genus := ![1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph27Valid : incomingGraph27Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph27Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 1 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![1, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph27 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph27Candidate incomingGraph27Valid incomingGraph27Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph27Candidate incomingGraph27Valid incomingGraph27Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph27_eq : incomingGraph27 = GenusTwoPsiProduct.columns 27 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph27Candidate incomingGraph27Valid incomingGraph27Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 27)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 28. -/
def incomingGraph28Candidate : StableGraphCode.Candidate (Fin 2) 1 1 where
  legVertex := ![0, 0]
  endpoint := ![![0, 0]]
  genus := ![1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph28Valid : incomingGraph28Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph28Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 1 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 1]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph28 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph28Candidate incomingGraph28Valid incomingGraph28Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph28Candidate incomingGraph28Valid incomingGraph28Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph28_eq : incomingGraph28 = GenusTwoPsiProduct.columns 28 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph28Candidate incomingGraph28Valid incomingGraph28Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 28)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 29. -/
def incomingGraph29Candidate : StableGraphCode.Candidate (Fin 2) 2 2 where
  legVertex := ![0, 0]
  endpoint := ![![1, 1], ![0, 1]]
  genus := ![0, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph29Valid : incomingGraph29Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph29Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph29 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph29Candidate incomingGraph29Valid incomingGraph29Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph29Candidate incomingGraph29Valid incomingGraph29Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph29_eq : incomingGraph29 = GenusTwoPsiProduct.columns 29 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph29Candidate incomingGraph29Valid incomingGraph29Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 29)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 30. -/
def incomingGraph30Candidate : StableGraphCode.Candidate (Fin 2) 2 2 where
  legVertex := ![1, 0]
  endpoint := ![![0, 1], ![0, 1]]
  genus := ![0, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph30Valid : incomingGraph30Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph30Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph30 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph30Candidate incomingGraph30Valid incomingGraph30Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph30Candidate incomingGraph30Valid incomingGraph30Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph30_eq : incomingGraph30 = GenusTwoPsiProduct.columns 30 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph30Candidate incomingGraph30Valid incomingGraph30Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 30)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 31. -/
def incomingGraph31Candidate : StableGraphCode.Candidate (Fin 2) 2 2 where
  legVertex := ![0, 1]
  endpoint := ![![0, 1], ![0, 1]]
  genus := ![0, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph31Valid : incomingGraph31Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph31Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph31 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph31Candidate incomingGraph31Valid incomingGraph31Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph31Candidate incomingGraph31Valid incomingGraph31Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph31_eq : incomingGraph31 = GenusTwoPsiProduct.columns 31 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph31Candidate incomingGraph31Valid incomingGraph31Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 31)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 32. -/
def incomingGraph32Candidate : StableGraphCode.Candidate (Fin 2) 2 2 where
  legVertex := ![0, 0]
  endpoint := ![![0, 1], ![0, 1]]
  genus := ![0, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph32Valid : incomingGraph32Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph32Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph32 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph32Candidate incomingGraph32Valid incomingGraph32Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph32Candidate incomingGraph32Valid incomingGraph32Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph32_eq : incomingGraph32 = GenusTwoPsiProduct.columns 32 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph32Candidate incomingGraph32Valid incomingGraph32Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 32)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 33. -/
def incomingGraph33Candidate : StableGraphCode.Candidate (Fin 2) 2 2 where
  legVertex := ![1, 1]
  endpoint := ![![0, 0], ![0, 1]]
  genus := ![0, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph33Valid : incomingGraph33Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph33Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph33 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph33Candidate incomingGraph33Valid incomingGraph33Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph33Candidate incomingGraph33Valid incomingGraph33Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph33_eq : incomingGraph33 = GenusTwoPsiProduct.columns 33 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph33Candidate incomingGraph33Valid incomingGraph33Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 33)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 34. -/
def incomingGraph34Candidate : StableGraphCode.Candidate (Fin 2) 2 2 where
  legVertex := ![1, 0]
  endpoint := ![![0, 0], ![0, 1]]
  genus := ![0, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph34Valid : incomingGraph34Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph34Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph34 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph34Candidate incomingGraph34Valid incomingGraph34Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph34Candidate incomingGraph34Valid incomingGraph34Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph34_eq : incomingGraph34 = GenusTwoPsiProduct.columns 34 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph34Candidate incomingGraph34Valid incomingGraph34Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 34)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 35. -/
def incomingGraph35Candidate : StableGraphCode.Candidate (Fin 2) 2 2 where
  legVertex := ![0, 1]
  endpoint := ![![0, 0], ![0, 1]]
  genus := ![0, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph35Valid : incomingGraph35Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph35Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph35 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph35Candidate incomingGraph35Valid incomingGraph35Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph35Candidate incomingGraph35Valid incomingGraph35Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph35_eq : incomingGraph35 = GenusTwoPsiProduct.columns 35 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph35Candidate incomingGraph35Valid incomingGraph35Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 35)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 36. -/
def incomingGraph36Candidate : StableGraphCode.Candidate (Fin 2) 2 2 where
  legVertex := ![0, 0]
  endpoint := ![![0, 0], ![0, 1]]
  genus := ![0, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph36Valid : incomingGraph36Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph36Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 2 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph36 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph36Candidate incomingGraph36Valid incomingGraph36Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph36Candidate incomingGraph36Valid incomingGraph36Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph36_eq : incomingGraph36 = GenusTwoPsiProduct.columns 36 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph36Candidate incomingGraph36Valid incomingGraph36Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 36)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 37. -/
def incomingGraph37Candidate : StableGraphCode.Candidate (Fin 2) 1 2 where
  legVertex := ![0, 0]
  endpoint := ![![0, 0], ![0, 0]]
  genus := ![0]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph37Valid : incomingGraph37Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph37Exponents : DecoratedStableGraph.DecorationIndex (Fin 2) 1 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph37 : TautologicalStratum 2 (Fin 2) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph37Candidate incomingGraph37Valid incomingGraph37Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph37Candidate incomingGraph37Valid incomingGraph37Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph37_eq : incomingGraph37 = GenusTwoPsiProduct.columns 37 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph37Candidate incomingGraph37Valid incomingGraph37Exponents)
    (GenusTwoPsiProduct.graph_totalGenus 37)
    (by simp only [GenusTwoPsiProduct.graph, BelorousskiPandharipande.tableGraph,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming columns, preserving the original source order. -/
def incomingColumns : Fin 38 → TautologicalStratum 2 (Fin 2) :=
  ![incomingGraph0, incomingGraph1, incomingGraph2, incomingGraph3, incomingGraph4,
    incomingGraph5, incomingGraph6, incomingGraph7, incomingGraph8, incomingGraph9,
    incomingGraph10, incomingGraph11, incomingGraph12, incomingGraph13, incomingGraph14,
    incomingGraph15, incomingGraph16, incomingGraph17, incomingGraph18, incomingGraph19,
    incomingGraph20, incomingGraph21, incomingGraph22, incomingGraph23, incomingGraph24,
    incomingGraph25, incomingGraph26, incomingGraph27, incomingGraph28, incomingGraph29,
    incomingGraph30, incomingGraph31, incomingGraph32, incomingGraph33, incomingGraph34,
    incomingGraph35, incomingGraph36, incomingGraph37]

/-- Incoming mathematical data in both rational coordinate systems. -/
def exchange : GenusTwoPsiProduct.Exchange where
  presentation := {
    columns := incomingColumns
    columnFactors := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    rows := ![![0, -15, 15, 15, 0, 0, 0, -15, 0, 21, 0, 0, 0, 21, 21, 0, 0, 0, 0, 0, 0, 0, 0, 21,
      0, (3 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![308448, -56952, 50400, 50400, -138600, -18000, -138600, -14544, 32760, 34704, -10080,
      -10080, -57960, 17856, 17856, -3600, -12600, -3600, -12600, -720, 5760, 5760, -1656, 11376,
      32760, 5040, -12600, -1800, -1800, 288, 3528, 3528, -360, 288, -360, -360, -1008, -90],
    ![127008, -17892, -27720, 19800, 81900, 12600, -69300, 16056, -36540, 16056, 8568, -6120,
      -36540, -792, 8712, 360, 8820, 5544, -21420, -4680, 4392, -6840, -2340, 2232, 23940, 1980,
      -6300, 1260, -900, -612, 2412, -2772, -1476, 252, 36, -396, -612, -45],
    ![127008, -17892, 19800, -27720, -69300, 12600, 81900, 16056, -36540, 16056, -6120, 8568,
      -36540, 8712, -792, 5544, -21420, 360, 8820, -4680, -6840, 4392, -2340, 2232, 23940, 1980,
      -6300, -900, 1260, -612, -2772, 2412, -1476, 252, -396, 36, -612, -45],
    ![38880, -3960, -8064, -8064, 32760, -7056, 32760, -3600, 12600, 5904, 4032, 4032, -17640,
      -1440, -1440, 1008, -2520, 1008, -2520, -144, -3168, -3168, -504, 1584, 12600, 576, -2520,
      504, 504, 144, -1368, -1368, -72, 144, -72, -72, -288, -18],
    ![0, 0, -15, 0, 15, 15, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3 /
      2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -15, 0, 15, 15, 0, 0, 0, 0, 21, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3
      / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![38880, -3960, 5760, 5760, -27720, -3600, -27720, -3600, 12600, 5904, -2880, -2880, -17640,
      3744, 3744, -720, -2520, -720, -2520, -144, 2016, 2016, -504, 1584, 12600, 576, -2520, -360,
      -360, 144, 1224, 1224, -72, 144, -72, -72, -288, -18],
    ![6480, -450, -1260, 900, 8190, 1260, -6930, 1260, -8190, 1260, 1764, -1260, -8190, -900,
      1260, 900, 6930, 1764, -8190, -1764, 1260, -1764, -882, -900, 6930, 90, -630, 126, -90,
      -126, 630, -666, -666, 90, 90, -126, -126, (-9 / 2)],
    ![6480, -450, 900, -1260, -6930, 1260, 8190, 1260, -8190, 1260, -1260, 1764, -8190, 1260,
      -900, 1764, -8190, 900, 6930, -1764, -1764, 1260, -882, -900, 6930, 90, -630, -90, 126,
      -126, -666, 630, -666, 90, -126, 90, -126, (-9 / 2)],
    ![0, 0, 0, 0, 0, 0, 0, -30, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      3, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 102, -30, 0, 0, 0, 0,
      0, 0, 0, 0, -3, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, (81 / 2), (-45 / 2), (-45 / 2), (-45 / 2), 0, 0, 0, 0, 0, 0, (9 /
      2), (9 / 2), (9 / 2), (-27 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-9 / 4), 0]]
    claimedRequest := ![0, 0, 0, 0, 0, 1, 0, 0, -3, 0, (161 / 90), (161 / 90), (-40 / 9), 0, 0,
      (407 / 180), (-7 / 36), (407 / 180), (-7 / 36), (-25 / 9), (-19 / 90), (-19 / 90), (-13 /
      30), 0, (206 / 51), 0, (-7 / 36), (67 / 720), (67 / 720), (-11 / 72), (-1 / 40), (-1 / 40),
      (-37 / 90), (473 / 12240), (-1 / 180), (-1 / 180), (-37 / 720), (-1 / 720)]
    certificate := ⟨![(7 / 3240), (7 / 248832), (-43 / 746496), (-43 / 746496), (41 / 746496), (91
      / 1296), (91 / 1296), (-83 / 1866240), (799 / 1866240), (799 / 1866240), (-1 / 24), (31 /
      4896), (-5 / 648)]⟩ }
  sourceRows := ![![15, -15, 15, 15, 0, 0, 0, -15, 0, 21, 0, 0, 0, 21, 21, 0, 0, 0, 0, 0, 0, 0, 0,
    21, 0, (3 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![365400, -56952, 50400, 50400, -138600, -18000, -138600, -14544, 32760, 34704, -10080,
      -10080, -57960, 17856, 17856, -3600, -12600, -3600, -12600, -720, 5760, 5760, -1656, 11376,
      32760, 5040, -12600, -1800, -1800, 288, 3528, 3528, -360, 288, -360, -360, -1008, -90],
    ![144900, -17892, -27720, 19800, 81900, 12600, -69300, 16056, -36540, 16056, 8568, -6120,
      -36540, -792, 8712, 360, 8820, 5544, -21420, -4680, 4392, -6840, -2340, 2232, 23940, 1980,
      -6300, 1260, -900, -612, 2412, -2772, -1476, 252, 36, -396, -612, -45],
    ![144900, -17892, 19800, -27720, -69300, 12600, 81900, 16056, -36540, 16056, -6120, 8568,
      -36540, 8712, -792, 5544, -21420, 360, 8820, -4680, -6840, 4392, -2340, 2232, 23940, 1980,
      -6300, -900, 1260, -612, -2772, 2412, -1476, 252, -396, 36, -612, -45],
    ![42840, -3960, -8064, -8064, 32760, -7056, 32760, -3600, 12600, 5904, 4032, 4032, -17640,
      -1440, -1440, 1008, -2520, 1008, -2520, -144, -3168, -3168, -504, 1584, 12600, 576, -2520,
      504, 504, 144, -1368, -1368, -72, 144, -72, -72, -288, -18],
    ![0, 0, -15, 0, 15, 15, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3 /
      2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -15, 0, 15, 15, 0, 0, 0, 0, 21, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3
      / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![42840, -3960, 5760, 5760, -27720, -3600, -27720, -3600, 12600, 5904, -2880, -2880, -17640,
      3744, 3744, -720, -2520, -720, -2520, -144, 2016, 2016, -504, 1584, 12600, 576, -2520, -360,
      -360, 144, 1224, 1224, -72, 144, -72, -72, -288, -18],
    ![6930, -450, -1260, 900, 8190, 1260, -6930, 1260, -8190, 1260, 1764, -1260, -8190, -900,
      1260, 900, 6930, 1764, -8190, -1764, 1260, -1764, -882, -900, 6930, 90, -630, 126, -90,
      -126, 630, -666, -666, 90, 90, -126, -126, (-9 / 2)],
    ![6930, -450, 900, -1260, -6930, 1260, 8190, 1260, -8190, 1260, -1260, 1764, -8190, 1260,
      -900, 1764, -8190, 900, 6930, -1764, -1764, 1260, -882, -900, 6930, 90, -630, -90, 126,
      -126, -666, 630, -666, 90, -126, 90, -126, (-9 / 2)],
    ![0, 0, 0, 0, 0, 0, 0, -30, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      3, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 102, -30, 0, 0, 0, 0,
      0, 0, 0, 0, -3, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, (81 / 2), (-45 / 2), (-45 / 2), (-45 / 2), 0, 0, 0, 0, 0, 0, (9 /
      2), (9 / 2), (9 / 2), (-27 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-9 / 4), 0]]
  sourceToMonomial := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1]]
  monomialToSource := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
      0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 1]]
  claimedBoundary := ![0, 0, 0, 0, 0, 0, 0, 0, 3, 0, (-161 / 90), (-161 / 90), (40 / 9), 0, 0,
    (-407 / 180), (7 / 36), (-407 / 180), (7 / 36), (25 / 9), (19 / 90), (19 / 90), (13 / 30), 0,
    (-206 / 51), 0, (7 / 36), (-67 / 720), (-67 / 720), (11 / 72), (1 / 40), (1 / 40), (37 / 90),
    (-473 / 12240), (1 / 180), (1 / 180), (37 / 720), (1 / 720)]
  automorphisms := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2,
    1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 8]

/-- All incoming fields are bound to the held claim and the witness is checked. -/
theorem accepted : GenusTwoPsiProduct.AcceptsExchange exchange := by
  constructor
  · constructor
    · refine ⟨?_, ?_, ?_, ?_⟩
      · change incomingColumns = GenusTwoPsiProduct.columns
        funext i
        fin_cases i
        · exact incomingGraph0_eq
        · exact incomingGraph1_eq
        · exact incomingGraph2_eq
        · exact incomingGraph3_eq
        · exact incomingGraph4_eq
        · exact incomingGraph5_eq
        · exact incomingGraph6_eq
        · exact incomingGraph7_eq
        · exact incomingGraph8_eq
        · exact incomingGraph9_eq
        · exact incomingGraph10_eq
        · exact incomingGraph11_eq
        · exact incomingGraph12_eq
        · exact incomingGraph13_eq
        · exact incomingGraph14_eq
        · exact incomingGraph15_eq
        · exact incomingGraph16_eq
        · exact incomingGraph17_eq
        · exact incomingGraph18_eq
        · exact incomingGraph19_eq
        · exact incomingGraph20_eq
        · exact incomingGraph21_eq
        · exact incomingGraph22_eq
        · exact incomingGraph23_eq
        · exact incomingGraph24_eq
        · exact incomingGraph25_eq
        · exact incomingGraph26_eq
        · exact incomingGraph27_eq
        · exact incomingGraph28_eq
        · exact incomingGraph29_eq
        · exact incomingGraph30_eq
        · exact incomingGraph31_eq
        · exact incomingGraph32_eq
        · exact incomingGraph33_eq
        · exact incomingGraph34_eq
        · exact incomingGraph35_eq
        · exact incomingGraph36_eq
        · exact incomingGraph37_eq
      · decide +kernel
      · decide +kernel
      · decide +kernel
    · decide +kernel
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · simp only [GenusTwoPsiProduct.automorphismOrders_correct]
      decide +kernel

/-- The actual accepted request is in the span of the held original rows. -/
theorem requested_mem_relationSpan :
    RelationCertificate.interpret GenusTwoPsiProduct.columns GenusTwoPsiProduct.requested ∈
      RelationCertificate.relationSpan GenusTwoPsiProduct.columns GenusTwoPsiProduct.rows :=
  RelationCertificate.acceptsPresentation_sound _ _ _ exchange.presentation accepted.1

end AxiomaticGW.GenusTwoPsiProductReplay

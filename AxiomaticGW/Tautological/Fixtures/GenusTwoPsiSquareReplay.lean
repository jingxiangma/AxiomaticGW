/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GenusTwoPsiSquare

/-!
# Incoming replay of the held marked genus-two psi-square relation

Input SHA256: 6b9c75fd1555575fd036348e943881f6ba5cb8e83b7b7f51e64f7448286e5e1d
The digest records provenance only. Geometric validity remains explicit.
-/

@[expose] public section

namespace AxiomaticGW.GenusTwoPsiSquareReplay

/-- Actual incoming incidence and genera for column 0. -/
def incomingGraph0Candidate : StableGraphCode.Candidate (Fin 1) 1 0 where
  legVertex := ![0]
  endpoint := Fin.elim0
  genus := ![2]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph0Valid : incomingGraph0Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph0Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 2 → ℕ
  | .inl (vertex, index) => (![![0, 1]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph0 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph0Candidate incomingGraph0Valid incomingGraph0Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph0Candidate incomingGraph0Valid incomingGraph0Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph0_eq : incomingGraph0 = GenusTwoPsiSquare.columns 0 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph0Candidate incomingGraph0Valid incomingGraph0Exponents)
    (GenusTwoPsiSquare.graph_totalGenus 0)
    (by simp only [GenusTwoPsiSquare.graph, GenusTwoPsiSquare.decorate,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 1. -/
def incomingGraph1Candidate : StableGraphCode.Candidate (Fin 1) 1 0 where
  legVertex := ![0]
  endpoint := Fin.elim0
  genus := ![2]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph1Valid : incomingGraph1Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph1Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 2 → ℕ
  | .inl (vertex, index) => (![![2, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph1 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph1Candidate incomingGraph1Valid incomingGraph1Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph1Candidate incomingGraph1Valid incomingGraph1Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph1_eq : incomingGraph1 = GenusTwoPsiSquare.columns 1 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph1Candidate incomingGraph1Valid incomingGraph1Exponents)
    (GenusTwoPsiSquare.graph_totalGenus 1)
    (by simp only [GenusTwoPsiSquare.graph, GenusTwoPsiSquare.decorate,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 2. -/
def incomingGraph2Candidate : StableGraphCode.Candidate (Fin 1) 1 0 where
  legVertex := ![0]
  endpoint := Fin.elim0
  genus := ![2]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph2Valid : incomingGraph2Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph2Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 2 → ℕ
  | .inl (vertex, index) => (![![1, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph2 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph2Candidate incomingGraph2Valid incomingGraph2Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph2Candidate incomingGraph2Valid incomingGraph2Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph2_eq : incomingGraph2 = GenusTwoPsiSquare.columns 2 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph2Candidate incomingGraph2Valid incomingGraph2Exponents)
    (GenusTwoPsiSquare.graph_totalGenus 2)
    (by simp only [GenusTwoPsiSquare.graph, GenusTwoPsiSquare.decorate,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 3. -/
def incomingGraph3Candidate : StableGraphCode.Candidate (Fin 1) 1 0 where
  legVertex := ![0]
  endpoint := Fin.elim0
  genus := ![2]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph3Valid : incomingGraph3Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph3Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 2 → ℕ
  | .inl (vertex, index) => (![![0, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![2]) label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph3 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph3Candidate incomingGraph3Valid incomingGraph3Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph3Candidate incomingGraph3Valid incomingGraph3Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph3_eq : incomingGraph3 = GenusTwoPsiSquare.columns 3 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph3Candidate incomingGraph3Valid incomingGraph3Exponents)
    (GenusTwoPsiSquare.graph_totalGenus 3)
    (by simp only [GenusTwoPsiSquare.graph, GenusTwoPsiSquare.decorate,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 4. -/
def incomingGraph4Candidate : StableGraphCode.Candidate (Fin 1) 2 1 where
  legVertex := ![1]
  endpoint := ![![0, 1]]
  genus := ![1, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph4Valid : incomingGraph4Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph4Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![1, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph4 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph4Candidate incomingGraph4Valid incomingGraph4Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph4Candidate incomingGraph4Valid incomingGraph4Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph4_eq : incomingGraph4 = GenusTwoPsiSquare.columns 4 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph4Candidate incomingGraph4Valid incomingGraph4Exponents)
    (GenusTwoPsiSquare.graph_totalGenus 4)
    (by simp only [GenusTwoPsiSquare.graph, GenusTwoPsiSquare.decorate,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 5. -/
def incomingGraph5Candidate : StableGraphCode.Candidate (Fin 1) 2 1 where
  legVertex := ![1]
  endpoint := ![![0, 1]]
  genus := ![1, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph5Valid : incomingGraph5Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph5Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph5 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph5Candidate incomingGraph5Valid incomingGraph5Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph5Candidate incomingGraph5Valid incomingGraph5Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph5_eq : incomingGraph5 = GenusTwoPsiSquare.columns 5 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph5Candidate incomingGraph5Valid incomingGraph5Exponents)
    (GenusTwoPsiSquare.graph_totalGenus 5)
    (by simp only [GenusTwoPsiSquare.graph, GenusTwoPsiSquare.decorate,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 6. -/
def incomingGraph6Candidate : StableGraphCode.Candidate (Fin 1) 2 1 where
  legVertex := ![1]
  endpoint := ![![0, 1]]
  genus := ![1, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph6Valid : incomingGraph6Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph6Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) => (![![0, 1]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph6 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph6Candidate incomingGraph6Valid incomingGraph6Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph6Candidate incomingGraph6Valid incomingGraph6Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph6_eq : incomingGraph6 = GenusTwoPsiSquare.columns 6 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph6Candidate incomingGraph6Valid incomingGraph6Exponents)
    (GenusTwoPsiSquare.graph_totalGenus 6)
    (by simp only [GenusTwoPsiSquare.graph, GenusTwoPsiSquare.decorate,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 7. -/
def incomingGraph7Candidate : StableGraphCode.Candidate (Fin 1) 3 2 where
  legVertex := ![1]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph7Valid : incomingGraph7Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph7Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph7 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph7Candidate incomingGraph7Valid incomingGraph7Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph7Candidate incomingGraph7Valid incomingGraph7Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph7_eq : incomingGraph7 = GenusTwoPsiSquare.columns 7 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph7Candidate incomingGraph7Valid incomingGraph7Exponents)
    (GenusTwoPsiSquare.graph_totalGenus 7)
    (by simp only [GenusTwoPsiSquare.graph, GenusTwoPsiSquare.decorate,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 8. -/
def incomingGraph8Candidate : StableGraphCode.Candidate (Fin 1) 2 1 where
  legVertex := ![1]
  endpoint := ![![0, 1]]
  genus := ![1, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph8Valid : incomingGraph8Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph8Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![1, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph8 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph8Candidate incomingGraph8Valid incomingGraph8Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph8Candidate incomingGraph8Valid incomingGraph8Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph8_eq : incomingGraph8 = GenusTwoPsiSquare.columns 8 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph8Candidate incomingGraph8Valid incomingGraph8Exponents)
    (GenusTwoPsiSquare.graph_totalGenus 8)
    (by simp only [GenusTwoPsiSquare.graph, GenusTwoPsiSquare.decorate,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 9. -/
def incomingGraph9Candidate : StableGraphCode.Candidate (Fin 1) 2 1 where
  legVertex := ![1]
  endpoint := ![![0, 1]]
  genus := ![1, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph9Valid : incomingGraph9Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph9Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) => (![![1, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph9 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph9Candidate incomingGraph9Valid incomingGraph9Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph9Candidate incomingGraph9Valid incomingGraph9Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph9_eq : incomingGraph9 = GenusTwoPsiSquare.columns 9 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph9Candidate incomingGraph9Valid incomingGraph9Exponents)
    (GenusTwoPsiSquare.graph_totalGenus 9)
    (by simp only [GenusTwoPsiSquare.graph, GenusTwoPsiSquare.decorate,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 10. -/
def incomingGraph10Candidate : StableGraphCode.Candidate (Fin 1) 1 1 where
  legVertex := ![0]
  endpoint := ![![0, 0]]
  genus := ![1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph10Valid : incomingGraph10Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph10Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 2 → ℕ
  | .inl (vertex, index) => (![![1, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph10 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph10Candidate incomingGraph10Valid incomingGraph10Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph10Candidate incomingGraph10Valid incomingGraph10Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph10_eq : incomingGraph10 = GenusTwoPsiSquare.columns 10 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph10Candidate incomingGraph10Valid incomingGraph10Exponents)
    (GenusTwoPsiSquare.graph_totalGenus 10)
    (by simp only [GenusTwoPsiSquare.graph, GenusTwoPsiSquare.decorate,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 11. -/
def incomingGraph11Candidate : StableGraphCode.Candidate (Fin 1) 1 1 where
  legVertex := ![0]
  endpoint := ![![0, 0]]
  genus := ![1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph11Valid : incomingGraph11Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph11Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) => (![![1, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph11 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph11Candidate incomingGraph11Valid incomingGraph11Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph11Candidate incomingGraph11Valid incomingGraph11Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph11_eq : incomingGraph11 = GenusTwoPsiSquare.columns 11 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph11Candidate incomingGraph11Valid incomingGraph11Exponents)
    (GenusTwoPsiSquare.graph_totalGenus 11)
    (by simp only [GenusTwoPsiSquare.graph, GenusTwoPsiSquare.decorate,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 12. -/
def incomingGraph12Candidate : StableGraphCode.Candidate (Fin 1) 1 1 where
  legVertex := ![0]
  endpoint := ![![0, 0]]
  genus := ![1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph12Valid : incomingGraph12Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph12Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![1]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph12 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph12Candidate incomingGraph12Valid incomingGraph12Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph12Candidate incomingGraph12Valid incomingGraph12Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph12_eq : incomingGraph12 = GenusTwoPsiSquare.columns 12 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph12Candidate incomingGraph12Valid incomingGraph12Exponents)
    (GenusTwoPsiSquare.graph_totalGenus 12)
    (by simp only [GenusTwoPsiSquare.graph, GenusTwoPsiSquare.decorate,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 13. -/
def incomingGraph13Candidate : StableGraphCode.Candidate (Fin 1) 2 2 where
  legVertex := ![0]
  endpoint := ![![0, 1], ![0, 1]]
  genus := ![0, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph13Valid : incomingGraph13Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph13Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph13 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph13Candidate incomingGraph13Valid incomingGraph13Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph13Candidate incomingGraph13Valid incomingGraph13Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph13_eq : incomingGraph13 = GenusTwoPsiSquare.columns 13 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph13Candidate incomingGraph13Valid incomingGraph13Exponents)
    (GenusTwoPsiSquare.graph_totalGenus 13)
    (by simp only [GenusTwoPsiSquare.graph, GenusTwoPsiSquare.decorate,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 14. -/
def incomingGraph14Candidate : StableGraphCode.Candidate (Fin 1) 2 2 where
  legVertex := ![1]
  endpoint := ![![0, 0], ![0, 1]]
  genus := ![0, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph14Valid : incomingGraph14Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph14Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph14 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph14Candidate incomingGraph14Valid incomingGraph14Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph14Candidate incomingGraph14Valid incomingGraph14Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph14_eq : incomingGraph14 = GenusTwoPsiSquare.columns 14 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph14Candidate incomingGraph14Valid incomingGraph14Exponents)
    (GenusTwoPsiSquare.graph_totalGenus 14)
    (by simp only [GenusTwoPsiSquare.graph, GenusTwoPsiSquare.decorate,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 15. -/
def incomingGraph15Candidate : StableGraphCode.Candidate (Fin 1) 2 2 where
  legVertex := ![0]
  endpoint := ![![0, 0], ![0, 1]]
  genus := ![0, 1]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph15Valid : incomingGraph15Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph15Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph15 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph15Candidate incomingGraph15Valid incomingGraph15Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph15Candidate incomingGraph15Valid incomingGraph15Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph15_eq : incomingGraph15 = GenusTwoPsiSquare.columns 15 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph15Candidate incomingGraph15Valid incomingGraph15Exponents)
    (GenusTwoPsiSquare.graph_totalGenus 15)
    (by simp only [GenusTwoPsiSquare.graph, GenusTwoPsiSquare.decorate,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming incidence and genera for column 16. -/
def incomingGraph16Candidate : StableGraphCode.Candidate (Fin 1) 1 2 where
  legVertex := ![0]
  endpoint := ![![0, 0], ![0, 0]]
  genus := ![0]

/-- Stability and arithmetic genus are kernel checked. -/
theorem incomingGraph16Valid : incomingGraph16Candidate.Valid 2 := by decide +kernel

/-- Incoming kappa powers, external cotangent powers and node branch powers. -/
def incomingGraph16Exponents : DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => (![0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

/-- The incoming decorated graph in the existing isomorphism quotient. -/
def incomingGraph16 : TautologicalStratum 2 (Fin 1) :=
  .mk
    (DecoratedStableGraph.toDecoration
      incomingGraph16Candidate incomingGraph16Valid incomingGraph16Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph16Candidate incomingGraph16Valid incomingGraph16Exponents)

/-- Incoming decorations and incidence agree with the independently held column. -/
theorem incomingGraph16_eq : incomingGraph16 = GenusTwoPsiSquare.columns 16 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph16Candidate incomingGraph16Valid incomingGraph16Exponents)
    (GenusTwoPsiSquare.graph_totalGenus 16)
    (by simp only [GenusTwoPsiSquare.graph, GenusTwoPsiSquare.decorate,
          DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel)

/-- Actual incoming columns, preserving the original source order. -/
def incomingColumns : Fin 17 → TautologicalStratum 2 (Fin 1) :=
  ![incomingGraph0, incomingGraph1, incomingGraph2, incomingGraph3, incomingGraph4,
    incomingGraph5, incomingGraph6, incomingGraph7, incomingGraph8, incomingGraph9,
    incomingGraph10, incomingGraph11, incomingGraph12, incomingGraph13, incomingGraph14,
    incomingGraph15, incomingGraph16]

/-- Incoming mathematical data in both rational coordinate systems. -/
def exchange : GenusTwoPsiSquare.Exchange where
  presentation := {
    columns := incomingColumns
    columnFactors := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    rows := ![![0, -30, 30, 0, 42, 0, 0, 0, 42, 0, 3, 0, 0, 0, 0, 0, 0],
    ![362880, -78120, 61200, -138600, 37296, -7920, -42840, 1368, 18288, 17640, 6120, -12600,
      -1800, 2232, 72, -792, -90],
    ![176256, -27864, -39312, 98280, 20304, 9072, -37800, -3672, 1296, 22680, 2808, -7560, 1512,
      -2808, 216, -648, -54],
    ![0, 0, -30, 30, 0, 42, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0],
    ![64800, -7020, 9720, -41580, 9288, -3240, -18900, 756, 4968, 11340, 972, -3780, -540, 1188,
      108, -324, -27],
    ![12960, -900, -2520, 16380, 2520, 3528, -16380, -1764, -1800, 13860, 180, -1260, 252, -1332,
      180, -252, -9],
    ![0, 0, 0, 0, 0, 0, 0, 0, 102, -30, 0, 0, 0, 0, -3, 0, 0]]
    claimedRequest := ![0, 0, 0, 1, 0, (-155 / 351), (-70 / 351), (-23 / 390), 0, (328 / 1989), 0,
      (-7 / 2808), (-31 / 1404), (-749 / 14040), (-101 / 477360), (-3 / 1040), (-1 / 56160)]
    certificate := ⟨![(7 / 505440), (-19 / 19408896), (305 / 58226688), (-53 / 3744), (-1759 /
      145566720), (161 / 9704448), (47 / 47736)]⟩ }
  sourceRows := ![![30, -30, 30, 0, 42, 0, 0, 0, 42, 0, 3, 0, 0, 0, 0, 0, 0],
    ![441000, -78120, 61200, -138600, 37296, -7920, -42840, 1368, 18288, 17640, 6120, -12600,
      -1800, 2232, 72, -792, -90],
    ![204120, -27864, -39312, 98280, 20304, 9072, -37800, -3672, 1296, 22680, 2808, -7560, 1512,
      -2808, 216, -648, -54],
    ![0, 0, -30, 30, 0, 42, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0],
    ![71820, -7020, 9720, -41580, 9288, -3240, -18900, 756, 4968, 11340, 972, -3780, -540, 1188,
      108, -324, -27],
    ![13860, -900, -2520, 16380, 2520, 3528, -16380, -1764, -1800, 13860, 180, -1260, 252, -1332,
      180, -252, -9],
    ![0, 0, 0, 0, 0, 0, 0, 0, 102, -30, 0, 0, 0, 0, -3, 0, 0]]
  sourceToMonomial := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]
  monomialToSource := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]
  claimedBoundary := ![0, 0, 0, 0, 0, (155 / 351), (70 / 351), (23 / 390), 0, (-328 / 1989), 0, (7
    / 2808), (31 / 1404), (749 / 14040), (101 / 477360), (3 / 1040), (1 / 56160)]
  automorphisms := ![1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 8]

/-- All incoming fields are bound to the held claim and the witness is checked. -/
theorem accepted : GenusTwoPsiSquare.AcceptsExchange exchange := by
  constructor
  · constructor
    · refine ⟨?_, ?_, ?_, ?_⟩
      · change incomingColumns = GenusTwoPsiSquare.columns
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
      · decide +kernel
      · decide +kernel
      · decide +kernel
    · decide +kernel
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · simp only [GenusTwoPsiSquare.automorphismOrders_correct]
      decide +kernel

/-- The actual accepted request is in the span of the held original rows. -/
theorem requested_mem_relationSpan :
    RelationCertificate.interpret GenusTwoPsiSquare.columns GenusTwoPsiSquare.requested ∈
      RelationCertificate.relationSpan GenusTwoPsiSquare.columns GenusTwoPsiSquare.rows :=
  RelationCertificate.acceptsPresentation_sound _ _ _ exchange.presentation accepted.1

end AxiomaticGW.GenusTwoPsiSquareReplay

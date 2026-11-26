/- Candidate Getzler replay. Geometric relation validity remains a hypothesis.
Input SHA256:
ccd8a8f941e9d2d503ec91e29b2be527bf0c91ce111599e6ec56118f6994ecb7
This digest is provenance, not proof. -/
module

public import AxiomaticGW.Tautological.GetzlerRealization

@[expose] public section

namespace AxiomaticGW.GetzlerReplay

def incomingGraph0Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![1, 1, 2, 2]
  endpoint := ![![0, 1], ![0, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph0Valid : incomingGraph0Candidate.Valid 1 := by decide

def incomingGraph0Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph0 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph0Candidate incomingGraph0Valid incomingGraph0Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph0Candidate incomingGraph0Valid incomingGraph0Exponents)

theorem incomingGraph0_eq : incomingGraph0 = GetzlerGraphs.columns 0 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph0Candidate incomingGraph0Valid incomingGraph0Exponents)
    (GetzlerGraphs.graph_totalGenus 0)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph1Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![1, 2, 1, 2]
  endpoint := ![![0, 1], ![0, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph1Valid : incomingGraph1Candidate.Valid 1 := by decide

def incomingGraph1Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph1 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph1Candidate incomingGraph1Valid incomingGraph1Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph1Candidate incomingGraph1Valid incomingGraph1Exponents)

theorem incomingGraph1_eq : incomingGraph1 = GetzlerGraphs.columns 1 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph1Candidate incomingGraph1Valid incomingGraph1Exponents)
    (GetzlerGraphs.graph_totalGenus 1)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph2Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![1, 2, 2, 1]
  endpoint := ![![0, 1], ![0, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph2Valid : incomingGraph2Candidate.Valid 1 := by decide

def incomingGraph2Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph2 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph2Candidate incomingGraph2Valid incomingGraph2Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph2Candidate incomingGraph2Valid incomingGraph2Exponents)

theorem incomingGraph2_eq : incomingGraph2 = GetzlerGraphs.columns 2 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph2Candidate incomingGraph2Valid incomingGraph2Exponents)
    (GetzlerGraphs.graph_totalGenus 2)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph3Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![2, 2, 1, 0]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph3Valid : incomingGraph3Candidate.Valid 1 := by decide

def incomingGraph3Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph3 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph3Candidate incomingGraph3Valid incomingGraph3Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph3Candidate incomingGraph3Valid incomingGraph3Exponents)

theorem incomingGraph3_eq : incomingGraph3 = GetzlerGraphs.columns 3 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph3Candidate incomingGraph3Valid incomingGraph3Exponents)
    (GetzlerGraphs.graph_totalGenus 3)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph4Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![2, 2, 0, 1]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph4Valid : incomingGraph4Candidate.Valid 1 := by decide

def incomingGraph4Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph4 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph4Candidate incomingGraph4Valid incomingGraph4Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph4Candidate incomingGraph4Valid incomingGraph4Exponents)

theorem incomingGraph4_eq : incomingGraph4 = GetzlerGraphs.columns 4 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph4Candidate incomingGraph4Valid incomingGraph4Exponents)
    (GetzlerGraphs.graph_totalGenus 4)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph5Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![2, 1, 2, 0]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph5Valid : incomingGraph5Candidate.Valid 1 := by decide

def incomingGraph5Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph5 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph5Candidate incomingGraph5Valid incomingGraph5Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph5Candidate incomingGraph5Valid incomingGraph5Exponents)

theorem incomingGraph5_eq : incomingGraph5 = GetzlerGraphs.columns 5 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph5Candidate incomingGraph5Valid incomingGraph5Exponents)
    (GetzlerGraphs.graph_totalGenus 5)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph6Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![2, 0, 2, 1]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph6Valid : incomingGraph6Candidate.Valid 1 := by decide

def incomingGraph6Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph6 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph6Candidate incomingGraph6Valid incomingGraph6Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph6Candidate incomingGraph6Valid incomingGraph6Exponents)

theorem incomingGraph6_eq : incomingGraph6 = GetzlerGraphs.columns 6 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph6Candidate incomingGraph6Valid incomingGraph6Exponents)
    (GetzlerGraphs.graph_totalGenus 6)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph7Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![2, 1, 0, 2]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph7Valid : incomingGraph7Candidate.Valid 1 := by decide

def incomingGraph7Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph7 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph7Candidate incomingGraph7Valid incomingGraph7Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph7Candidate incomingGraph7Valid incomingGraph7Exponents)

theorem incomingGraph7_eq : incomingGraph7 = GetzlerGraphs.columns 7 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph7Candidate incomingGraph7Valid incomingGraph7Exponents)
    (GetzlerGraphs.graph_totalGenus 7)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph8Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![2, 0, 1, 2]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph8Valid : incomingGraph8Candidate.Valid 1 := by decide

def incomingGraph8Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph8 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph8Candidate incomingGraph8Valid incomingGraph8Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph8Candidate incomingGraph8Valid incomingGraph8Exponents)

theorem incomingGraph8_eq : incomingGraph8 = GetzlerGraphs.columns 8 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph8Candidate incomingGraph8Valid incomingGraph8Exponents)
    (GetzlerGraphs.graph_totalGenus 8)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph9Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![1, 2, 2, 0]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph9Valid : incomingGraph9Candidate.Valid 1 := by decide

def incomingGraph9Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph9 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph9Candidate incomingGraph9Valid incomingGraph9Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph9Candidate incomingGraph9Valid incomingGraph9Exponents)

theorem incomingGraph9_eq : incomingGraph9 = GetzlerGraphs.columns 9 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph9Candidate incomingGraph9Valid incomingGraph9Exponents)
    (GetzlerGraphs.graph_totalGenus 9)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph10Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![0, 2, 2, 1]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph10Valid : incomingGraph10Candidate.Valid 1 := by decide

def incomingGraph10Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph10 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph10Candidate incomingGraph10Valid incomingGraph10Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph10Candidate incomingGraph10Valid incomingGraph10Exponents)

theorem incomingGraph10_eq : incomingGraph10 = GetzlerGraphs.columns 10 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph10Candidate incomingGraph10Valid incomingGraph10Exponents)
    (GetzlerGraphs.graph_totalGenus 10)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph11Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![1, 2, 0, 2]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph11Valid : incomingGraph11Candidate.Valid 1 := by decide

def incomingGraph11Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph11 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph11Candidate incomingGraph11Valid incomingGraph11Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph11Candidate incomingGraph11Valid incomingGraph11Exponents)

theorem incomingGraph11_eq : incomingGraph11 = GetzlerGraphs.columns 11 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph11Candidate incomingGraph11Valid incomingGraph11Exponents)
    (GetzlerGraphs.graph_totalGenus 11)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph12Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![0, 2, 1, 2]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph12Valid : incomingGraph12Candidate.Valid 1 := by decide

def incomingGraph12Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph12 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph12Candidate incomingGraph12Valid incomingGraph12Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph12Candidate incomingGraph12Valid incomingGraph12Exponents)

theorem incomingGraph12_eq : incomingGraph12 = GetzlerGraphs.columns 12 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph12Candidate incomingGraph12Valid incomingGraph12Exponents)
    (GetzlerGraphs.graph_totalGenus 12)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph13Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![1, 0, 2, 2]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph13Valid : incomingGraph13Candidate.Valid 1 := by decide

def incomingGraph13Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph13 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph13Candidate incomingGraph13Valid incomingGraph13Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph13Candidate incomingGraph13Valid incomingGraph13Exponents)

theorem incomingGraph13_eq : incomingGraph13 = GetzlerGraphs.columns 13 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph13Candidate incomingGraph13Valid incomingGraph13Exponents)
    (GetzlerGraphs.graph_totalGenus 13)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph14Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![0, 1, 2, 2]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph14Valid : incomingGraph14Candidate.Valid 1 := by decide

def incomingGraph14Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph14 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph14Candidate incomingGraph14Valid incomingGraph14Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph14Candidate incomingGraph14Valid incomingGraph14Exponents)

theorem incomingGraph14_eq : incomingGraph14 = GetzlerGraphs.columns 14 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph14Candidate incomingGraph14Valid incomingGraph14Exponents)
    (GetzlerGraphs.graph_totalGenus 14)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph15Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![2, 2, 1, 1]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph15Valid : incomingGraph15Candidate.Valid 1 := by decide

def incomingGraph15Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph15 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph15Candidate incomingGraph15Valid incomingGraph15Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph15Candidate incomingGraph15Valid incomingGraph15Exponents)

theorem incomingGraph15_eq : incomingGraph15 = GetzlerGraphs.columns 15 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph15Candidate incomingGraph15Valid incomingGraph15Exponents)
    (GetzlerGraphs.graph_totalGenus 15)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph16Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![2, 1, 2, 1]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph16Valid : incomingGraph16Candidate.Valid 1 := by decide

def incomingGraph16Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph16 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph16Candidate incomingGraph16Valid incomingGraph16Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph16Candidate incomingGraph16Valid incomingGraph16Exponents)

theorem incomingGraph16_eq : incomingGraph16 = GetzlerGraphs.columns 16 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph16Candidate incomingGraph16Valid incomingGraph16Exponents)
    (GetzlerGraphs.graph_totalGenus 16)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph17Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![2, 1, 1, 2]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph17Valid : incomingGraph17Candidate.Valid 1 := by decide

def incomingGraph17Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph17 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph17Candidate incomingGraph17Valid incomingGraph17Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph17Candidate incomingGraph17Valid incomingGraph17Exponents)

theorem incomingGraph17_eq : incomingGraph17 = GetzlerGraphs.columns 17 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph17Candidate incomingGraph17Valid incomingGraph17Exponents)
    (GetzlerGraphs.graph_totalGenus 17)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph18Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![1, 2, 2, 1]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph18Valid : incomingGraph18Candidate.Valid 1 := by decide

def incomingGraph18Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph18 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph18Candidate incomingGraph18Valid incomingGraph18Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph18Candidate incomingGraph18Valid incomingGraph18Exponents)

theorem incomingGraph18_eq : incomingGraph18 = GetzlerGraphs.columns 18 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph18Candidate incomingGraph18Valid incomingGraph18Exponents)
    (GetzlerGraphs.graph_totalGenus 18)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph19Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![1, 2, 1, 2]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph19Valid : incomingGraph19Candidate.Valid 1 := by decide

def incomingGraph19Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph19 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph19Candidate incomingGraph19Valid incomingGraph19Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph19Candidate incomingGraph19Valid incomingGraph19Exponents)

theorem incomingGraph19_eq : incomingGraph19 = GetzlerGraphs.columns 19 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph19Candidate incomingGraph19Valid incomingGraph19Exponents)
    (GetzlerGraphs.graph_totalGenus 19)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph20Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![1, 1, 2, 2]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph20Valid : incomingGraph20Candidate.Valid 1 := by decide

def incomingGraph20Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph20 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph20Candidate incomingGraph20Valid incomingGraph20Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph20Candidate incomingGraph20Valid incomingGraph20Exponents)

theorem incomingGraph20_eq : incomingGraph20 = GetzlerGraphs.columns 20 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph20Candidate incomingGraph20Valid incomingGraph20Exponents)
    (GetzlerGraphs.graph_totalGenus 20)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph21Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![1, 2, 2, 2]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph21Valid : incomingGraph21Candidate.Valid 1 := by decide

def incomingGraph21Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph21 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph21Candidate incomingGraph21Valid incomingGraph21Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph21Candidate incomingGraph21Valid incomingGraph21Exponents)

theorem incomingGraph21_eq : incomingGraph21 = GetzlerGraphs.columns 21 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph21Candidate incomingGraph21Valid incomingGraph21Exponents)
    (GetzlerGraphs.graph_totalGenus 21)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph22Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![2, 1, 2, 2]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph22Valid : incomingGraph22Candidate.Valid 1 := by decide

def incomingGraph22Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph22 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph22Candidate incomingGraph22Valid incomingGraph22Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph22Candidate incomingGraph22Valid incomingGraph22Exponents)

theorem incomingGraph22_eq : incomingGraph22 = GetzlerGraphs.columns 22 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph22Candidate incomingGraph22Valid incomingGraph22Exponents)
    (GetzlerGraphs.graph_totalGenus 22)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph23Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![2, 2, 1, 2]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph23Valid : incomingGraph23Candidate.Valid 1 := by decide

def incomingGraph23Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph23 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph23Candidate incomingGraph23Valid incomingGraph23Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph23Candidate incomingGraph23Valid incomingGraph23Exponents)

theorem incomingGraph23_eq : incomingGraph23 = GetzlerGraphs.columns 23 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph23Candidate incomingGraph23Valid incomingGraph23Exponents)
    (GetzlerGraphs.graph_totalGenus 23)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph24Candidate : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![2, 2, 2, 1]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

theorem incomingGraph24Valid : incomingGraph24Candidate.Valid 1 := by decide

def incomingGraph24Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 3 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0], ![0, 0]] : Fin 3 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph24 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph24Candidate incomingGraph24Valid incomingGraph24Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph24Candidate incomingGraph24Valid incomingGraph24Exponents)

theorem incomingGraph24_eq : incomingGraph24 = GetzlerGraphs.columns 24 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph24Candidate incomingGraph24Valid incomingGraph24Exponents)
    (GetzlerGraphs.graph_totalGenus 24)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph25Candidate : StableGraphCode.Candidate (Fin 4) 2 2 where
  legVertex := ![0, 1, 1, 1]
  endpoint := ![![0, 0], ![0, 1]]
  genus := ![0, 0]

theorem incomingGraph25Valid : incomingGraph25Candidate.Valid 1 := by decide

def incomingGraph25Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 2 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph25 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph25Candidate incomingGraph25Valid incomingGraph25Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph25Candidate incomingGraph25Valid incomingGraph25Exponents)

theorem incomingGraph25_eq : incomingGraph25 = GetzlerGraphs.columns 25 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph25Candidate incomingGraph25Valid incomingGraph25Exponents)
    (GetzlerGraphs.graph_totalGenus 25)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph26Candidate : StableGraphCode.Candidate (Fin 4) 2 2 where
  legVertex := ![1, 0, 1, 1]
  endpoint := ![![0, 0], ![0, 1]]
  genus := ![0, 0]

theorem incomingGraph26Valid : incomingGraph26Candidate.Valid 1 := by decide

def incomingGraph26Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 2 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph26 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph26Candidate incomingGraph26Valid incomingGraph26Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph26Candidate incomingGraph26Valid incomingGraph26Exponents)

theorem incomingGraph26_eq : incomingGraph26 = GetzlerGraphs.columns 26 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph26Candidate incomingGraph26Valid incomingGraph26Exponents)
    (GetzlerGraphs.graph_totalGenus 26)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph27Candidate : StableGraphCode.Candidate (Fin 4) 2 2 where
  legVertex := ![1, 1, 0, 1]
  endpoint := ![![0, 0], ![0, 1]]
  genus := ![0, 0]

theorem incomingGraph27Valid : incomingGraph27Candidate.Valid 1 := by decide

def incomingGraph27Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 2 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph27 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph27Candidate incomingGraph27Valid incomingGraph27Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph27Candidate incomingGraph27Valid incomingGraph27Exponents)

theorem incomingGraph27_eq : incomingGraph27 = GetzlerGraphs.columns 27 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph27Candidate incomingGraph27Valid incomingGraph27Exponents)
    (GetzlerGraphs.graph_totalGenus 27)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph28Candidate : StableGraphCode.Candidate (Fin 4) 2 2 where
  legVertex := ![1, 1, 1, 0]
  endpoint := ![![0, 0], ![0, 1]]
  genus := ![0, 0]

theorem incomingGraph28Valid : incomingGraph28Candidate.Valid 1 := by decide

def incomingGraph28Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 2 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph28 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph28Candidate incomingGraph28Valid incomingGraph28Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph28Candidate incomingGraph28Valid incomingGraph28Exponents)

theorem incomingGraph28_eq : incomingGraph28 = GetzlerGraphs.columns 28 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph28Candidate incomingGraph28Valid incomingGraph28Exponents)
    (GetzlerGraphs.graph_totalGenus 28)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph29Candidate : StableGraphCode.Candidate (Fin 4) 2 2 where
  legVertex := ![1, 1, 1, 1]
  endpoint := ![![0, 0], ![0, 1]]
  genus := ![0, 0]

theorem incomingGraph29Valid : incomingGraph29Candidate.Valid 1 := by decide

def incomingGraph29Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 2 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph29 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph29Candidate incomingGraph29Valid incomingGraph29Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph29Candidate incomingGraph29Valid incomingGraph29Exponents)

theorem incomingGraph29_eq : incomingGraph29 = GetzlerGraphs.columns 29 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph29Candidate incomingGraph29Valid incomingGraph29Exponents)
    (GetzlerGraphs.graph_totalGenus 29)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph30Candidate : StableGraphCode.Candidate (Fin 4) 2 2 where
  legVertex := ![0, 0, 1, 1]
  endpoint := ![![0, 1], ![0, 1]]
  genus := ![0, 0]

theorem incomingGraph30Valid : incomingGraph30Candidate.Valid 1 := by decide

def incomingGraph30Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 2 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph30 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph30Candidate incomingGraph30Valid incomingGraph30Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph30Candidate incomingGraph30Valid incomingGraph30Exponents)

theorem incomingGraph30_eq : incomingGraph30 = GetzlerGraphs.columns 30 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph30Candidate incomingGraph30Valid incomingGraph30Exponents)
    (GetzlerGraphs.graph_totalGenus 30)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph31Candidate : StableGraphCode.Candidate (Fin 4) 2 2 where
  legVertex := ![0, 1, 0, 1]
  endpoint := ![![0, 1], ![0, 1]]
  genus := ![0, 0]

theorem incomingGraph31Valid : incomingGraph31Candidate.Valid 1 := by decide

def incomingGraph31Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 2 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph31 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph31Candidate incomingGraph31Valid incomingGraph31Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph31Candidate incomingGraph31Valid incomingGraph31Exponents)

theorem incomingGraph31_eq : incomingGraph31 = GetzlerGraphs.columns 31 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph31Candidate incomingGraph31Valid incomingGraph31Exponents)
    (GetzlerGraphs.graph_totalGenus 31)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph32Candidate : StableGraphCode.Candidate (Fin 4) 2 2 where
  legVertex := ![0, 1, 1, 0]
  endpoint := ![![0, 1], ![0, 1]]
  genus := ![0, 0]

theorem incomingGraph32Valid : incomingGraph32Candidate.Valid 1 := by decide

def incomingGraph32Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 2 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]]) edge branch

def incomingGraph32 : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph32Candidate incomingGraph32Valid incomingGraph32Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph32Candidate incomingGraph32Valid incomingGraph32Exponents)

theorem incomingGraph32_eq : incomingGraph32 = GetzlerGraphs.columns 32 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph32Candidate incomingGraph32Valid incomingGraph32Exponents)
    (GetzlerGraphs.graph_totalGenus 32)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingColumns : Fin 33 → TautologicalStratum 1 (Fin 4) :=
  ![
    incomingGraph0,
    incomingGraph1,
    incomingGraph2,
    incomingGraph3,
    incomingGraph4,
    incomingGraph5,
    incomingGraph6,
    incomingGraph7,
    incomingGraph8,
    incomingGraph9,
    incomingGraph10,
    incomingGraph11,
    incomingGraph12,
    incomingGraph13,
    incomingGraph14,
    incomingGraph15,
    incomingGraph16,
    incomingGraph17,
    incomingGraph18,
    incomingGraph19,
    incomingGraph20,
    incomingGraph21,
    incomingGraph22,
    incomingGraph23,
    incomingGraph24,
    incomingGraph25,
    incomingGraph26,
    incomingGraph27,
    incomingGraph28,
    incomingGraph29,
    incomingGraph30,
    incomingGraph31,
    incomingGraph32]

def incomingNames : Fin 33 → GetzlerStratum :=
  ![
    .delta22,
    .delta22,
    .delta22,
    .delta23,
    .delta23,
    .delta23,
    .delta23,
    .delta23,
    .delta23,
    .delta23,
    .delta23,
    .delta23,
    .delta23,
    .delta23,
    .delta23,
    .delta24,
    .delta24,
    .delta24,
    .delta24,
    .delta24,
    .delta24,
    .delta34,
    .delta34,
    .delta34,
    .delta34,
    .delta03,
    .delta03,
    .delta03,
    .delta03,
    .delta04,
    .deltaBeta,
    .deltaBeta,
    .deltaBeta]

def incomingOrbifoldFactors : RelationCertificate.Coordinates 33 :=
  ![1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    (1 / 2),
    (1 / 2),
    (1 / 2),
    (1 / 2),
    (1 / 2),
    (1 / 2),
    (1 / 2),
    (1 / 2)]

theorem names_correct : incomingNames = GetzlerGraphs.kind := by
  funext i
  fin_cases i <;> decide

theorem conversion_correct : incomingOrbifoldFactors = GetzlerGraphs.normalization := by
  funext i
  fin_cases i <;>
    norm_num [incomingOrbifoldFactors, GetzlerGraphs.normalization,
      Matrix.cons_val_two]

def presentation : RelationCertificate.Presentation 1 (Fin 4) 1 33 where
  columns := incomingColumns
  columnFactors := ![1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1]
  rows := ![![12,
    12,
    12,
    -4,
    -4,
    -4,
    -4,
    -4,
    -4,
    -4,
    -4,
    -4,
    -4,
    -4,
    -4,
    -2,
    -2,
    -2,
    -2,
    -2,
    -2,
    6,
    6,
    6,
    6,
    (1 / 2),
    (1 / 2),
    (1 / 2),
    (1 / 2),
    (1 / 2),
    -1,
    -1,
    -1]]
  claimedRequest := ![-3,
    -3,
    -3,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    (1 / 2),
    (1 / 2),
    (1 / 2),
    (1 / 2),
    (1 / 2),
    (1 / 2),
    (-3 / 2),
    (-3 / 2),
    (-3 / 2),
    (-3 / 2),
    (-1 / 8),
    (-1 / 8),
    (-1 / 8),
    (-1 / 8),
    (-1 / 8),
    (1 / 4),
    (1 / 4),
    (1 / 4)]
  certificate := ⟨![(-1 / 4)]⟩

theorem accepted : GetzlerGraphs.AcceptsExchange presentation := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change incomingColumns = GetzlerGraphs.columns
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
    · funext i
      fin_cases i <;> norm_num [presentation, Matrix.cons_val_two]
    · funext r i
      fin_cases r
      fin_cases i <;>
        norm_num [presentation, GetzlerGraphs.rows, GetzlerGraphs.row,
          GetzlerGraphs.kind, GetzlerGraphs.normalization, GetzlerStratum.coefficient,
          Matrix.cons_val_two]
    · funext i
      fin_cases i <;>
        norm_num [presentation, GetzlerGraphs.requested, GetzlerGraphs.kind,
          GetzlerGraphs.normalization, Matrix.cons_val_two]
  · funext i
    fin_cases i <;>
      norm_num [RelationCertificate.combination, presentation, GetzlerGraphs.rows,
        GetzlerGraphs.row, GetzlerGraphs.kind, GetzlerGraphs.normalization,
        GetzlerStratum.coefficient, GetzlerGraphs.requested, Fin.sum_univ_one,
        Matrix.cons_val_two]

/-- Offline replay certifies the held delta23 consequence in the fixed relation span. -/
theorem requested_mem_relationSpan :
    RelationCertificate.interpret GetzlerGraphs.columns GetzlerGraphs.requested ∈
      RelationCertificate.relationSpan GetzlerGraphs.columns GetzlerGraphs.rows :=
  RelationCertificate.acceptsPresentation_sound _ _ _ presentation accepted

end AxiomaticGW.GetzlerReplay

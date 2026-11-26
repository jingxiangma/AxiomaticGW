/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GenusOnePsi
public import AxiomaticGW.Tautological.RelabelRealization

/-!
# The published Belorousski--Pandharipande graph equation

Theorem 1, equation (4), page 4 of arXiv:math/9803072 has twenty diagrams.
They denote stack fundamental classes summed over all six marking assignments,
including repetitions. Each stack stratum is the raw pushforward divided by
its label-fixing graph automorphism order. The two unmarked elliptic tails in
term 4 can be exchanged; loop branches and parallel edges also contribute a
factor two. No generic elliptic stack stabilizer is divided out again.

The fixed frame has 100 raw codimension-two decorated graphs on Mbar(2,3).
External labels are 0,1,2. The three cotangent terms are on the genus-two
component: terms 1 and 3 at the node, term 2 at its external marking. In the
parallel-edge drawings, the dotted left arc ends at the genus-zero label.
This file checks graph meanings, the sixfold sum and the exact published
request; geometric vanishing is a separate input to the certificate layer.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open RelationCertificate

/-- Shared table syntax for the existing decoration constructor; no new graph type. -/
def tableGraph (g : ℕ) {n v e : ℕ} (c : StableGraphCode.Candidate (Fin n) v e)
    (h : c.Valid g) (k : Fin v → Fin 2 → ℕ) (p : Fin n → ℕ)
    (q : Fin e → Fin 2 → ℕ) : DecoratedStableGraph (Fin n) :=
  DecoratedStableGraph.toDecoration c h (fun
    | .inl (vertex, index) => k vertex index
    | .inr (.inl label) => p label
    | .inr (.inr (edge, branch)) => q edge branch)

/-- The stable curve arity of the published relation. -/
theorem stableArity : StableArity 2 (Fin 3) := by norm_num [StableArity]

/-- Held raw columns, with monomial kappa, external psi and branch psi powers. -/
def graph : Fin 100 → DecoratedStableGraph (Fin 3) :=
  ![tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![2] } :
    StableGraphCode.Candidate (Fin 3) 1 0) (by decide +kernel)
      ![![0, 1]] ![0, 0, 0] Fin.elim0,
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![2] } :
      StableGraphCode.Candidate (Fin 3) 1 0) (by decide +kernel)
      ![![2, 0]] ![0, 0, 0] Fin.elim0,
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![2] } :
      StableGraphCode.Candidate (Fin 3) 1 0) (by decide +kernel)
      ![![1, 0]] ![1, 0, 0] Fin.elim0,
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![2] } :
      StableGraphCode.Candidate (Fin 3) 1 0) (by decide +kernel)
      ![![1, 0]] ![0, 1, 0] Fin.elim0,
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![2] } :
      StableGraphCode.Candidate (Fin 3) 1 0) (by decide +kernel)
      ![![1, 0]] ![0, 0, 1] Fin.elim0,
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![2] } :
      StableGraphCode.Candidate (Fin 3) 1 0) (by decide +kernel)
      ![![0, 0]] ![2, 0, 0] Fin.elim0,
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![2] } :
      StableGraphCode.Candidate (Fin 3) 1 0) (by decide +kernel)
      ![![0, 0]] ![1, 1, 0] Fin.elim0,
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![2] } :
      StableGraphCode.Candidate (Fin 3) 1 0) (by decide +kernel)
      ![![0, 0]] ![1, 0, 1] Fin.elim0,
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![2] } :
      StableGraphCode.Candidate (Fin 3) 1 0) (by decide +kernel)
      ![![0, 0]] ![0, 2, 0] Fin.elim0,
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![2] } :
      StableGraphCode.Candidate (Fin 3) 1 0) (by decide +kernel)
      ![![0, 0]] ![0, 1, 1] Fin.elim0,
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![2] } :
      StableGraphCode.Candidate (Fin 3) 1 0) (by decide +kernel)
      ![![0, 0]] ![0, 0, 2] Fin.elim0,
    tableGraph 2 ({ legVertex := ![1, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![1, 0]] ![0, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![1, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 1]],
    tableGraph 2 ({ legVertex := ![0, 1, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![1, 0]] ![0, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 1, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 1, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 1, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 1]],
    tableGraph 2 ({ legVertex := ![0, 0, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![1, 0]] ![0, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 1] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 1]],
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![1, 0], ![0, 0]] ![0, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![1, 0]] ![0, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![1, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 1, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 1] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![1, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 1]],
    tableGraph 2 ({ legVertex := ![1, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![1, 0]] ![0, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![1, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 1, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 1] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 1]],
    tableGraph 2 ({ legVertex := ![1, 1, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![1, 0], ![0, 0]] ![0, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![1, 0]] ![0, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 1] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![1, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![1, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 1, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 1]],
    tableGraph 2 ({ legVertex := ![1, 0, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![1, 0], ![0, 0]] ![0, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 0, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![1, 0]] ![0, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 0, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 1, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 0, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![1, 0]],
    tableGraph 2 ({ legVertex := ![1, 0, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![1, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 0, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 1] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 0, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 1]],
    tableGraph 2 ({ legVertex := ![1, 0, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![1, 0], ![0, 0]] ![0, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 0, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![1, 0]] ![0, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 0, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 1, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 0, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 1] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 0, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![1, 0]],
    tableGraph 2 ({ legVertex := ![1, 0, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![1, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 0, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 1]],
    tableGraph 2 ({ legVertex := ![2, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![2, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 2, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![2, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![2, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![2, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![2, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![2, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![1, 0], ![0, 0]] ![0, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![1, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := ![![0, 0]], genus := ![1] } :
      StableGraphCode.Candidate (Fin 3) 1 1) (by decide +kernel)
      ![![1, 0]] ![0, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := ![![0, 0]], genus := ![1] } :
      StableGraphCode.Candidate (Fin 3) 1 1) (by decide +kernel)
      ![![0, 0]] ![0, 0, 0] ![![1, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := ![![0, 0]], genus := ![1] } :
      StableGraphCode.Candidate (Fin 3) 1 1) (by decide +kernel)
      ![![0, 0]] ![1, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := ![![0, 0]], genus := ![1] } :
      StableGraphCode.Candidate (Fin 3) 1 1) (by decide +kernel)
      ![![0, 0]] ![0, 1, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := ![![0, 0]], genus := ![1] } :
      StableGraphCode.Candidate (Fin 3) 1 1) (by decide +kernel)
      ![![0, 0]] ![0, 0, 1] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 1, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 1], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 0, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 0, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 1, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 1, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 0, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 0, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 1, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := ![![0, 0], ![0, 0]], genus := ![0] } :
      StableGraphCode.Candidate (Fin 3) 1 2) (by decide +kernel)
      ![![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]]]

/-- All columns have the prescribed arithmetic genus. -/
theorem graph_totalGenus (i : Fin 100) : (graph i).graph.totalGenus = 2 := by
  fin_cases i <;> decide +kernel

/-- The existing quotient identifies equivalent decorated presentations. -/
def columns (i : Fin 100) : TautologicalStratum 2 (Fin 3) :=
  .mk (graph i) (graph_totalGenus i)

/-- Every column has codimension two. -/
theorem columns_codimension : ∀ i, (columns i).codimension = 2 := by
  simp only [columns, graph, tableGraph, DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The raw labelled frame has no repeated decorated stratum. -/
theorem columns_injective : Function.Injective columns := by
  simp only [Function.Injective, columns, graph, tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Decorated graph orders, computed before any orbit summation. -/
def automorphismOrders : Fin 100 → ℕ :=
  ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 8]

/-- Decorations can break a loop-branch symmetry; the full decorated graph is checked. -/
theorem automorphismOrders_correct : ∀ i, (graph i).automorphismCount = automorphismOrders i := by
  simp only [graph, tableGraph, DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Covariant relabellings; their inverses give the table's order of new labels. -/
def labelPermutation (p : Fin 6) : Equiv.Perm (Fin 3) where
  toFun := ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![2, 0, 1], ![1, 2, 0], ![2, 1, 0]] p
  invFun := ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]] p
  left_inv := by fin_cases p <;> decide +kernel
  right_inv := by fin_cases p <;> decide +kernel

/-- Exactly all six marking assignments occur, with no orbit averaging. -/
theorem labelPermutation_bijective : Function.Bijective labelPermutation := by decide +kernel

/-- Each marking permutation acts on the entire held raw frame. -/
def permutationDestinations : Fin 6 → Fin 100 → Fin 100 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
    25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
    48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70,
    71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93,
    94, 95, 96, 97, 98, 99], ![0, 1, 2, 4, 3, 5, 7, 6, 10, 9, 8, 11, 12, 13, 17, 18, 19, 14, 15,
    16, 20, 21, 22, 24, 23, 25, 26, 27, 29, 28, 30, 31, 33, 32, 34, 42, 43, 44, 45, 46, 47, 48,
    35, 36, 37, 38, 39, 40, 41, 49, 50, 52, 51, 53, 54, 55, 56, 57, 60, 61, 58, 59, 62, 64, 63,
    65, 66, 68, 67, 69, 72, 71, 70, 73, 74, 75, 76, 77, 79, 78, 80, 82, 81, 83, 85, 84, 86, 87,
    89, 88, 90, 91, 93, 92, 94, 95, 97, 96, 98, 99], ![0, 1, 3, 2, 4, 8, 6, 9, 5, 7, 10, 14, 15,
    16, 11, 12, 13, 17, 18, 19, 20, 21, 23, 22, 24, 25, 26, 28, 27, 29, 30, 32, 31, 33, 34, 35,
    36, 37, 38, 40, 39, 41, 50, 49, 54, 55, 51, 52, 53, 43, 42, 46, 47, 48, 44, 45, 58, 59, 56,
    57, 60, 61, 62, 63, 66, 67, 64, 65, 68, 69, 71, 70, 72, 73, 74, 75, 76, 78, 77, 79, 81, 80,
    82, 83, 84, 87, 88, 85, 86, 89, 90, 91, 92, 95, 96, 93, 94, 97, 98, 99], ![0, 1, 4, 2, 3, 10,
    7, 9, 5, 6, 8, 17, 18, 19, 11, 12, 13, 14, 15, 16, 20, 21, 24, 22, 23, 25, 26, 29, 27, 28, 30,
    33, 31, 32, 34, 42, 43, 44, 45, 47, 46, 48, 50, 49, 54, 55, 52, 51, 53, 36, 35, 39, 40, 41,
    37, 38, 60, 61, 56, 57, 58, 59, 62, 64, 66, 68, 63, 65, 67, 69, 71, 72, 70, 73, 74, 75, 76,
    79, 77, 78, 82, 80, 81, 83, 85, 87, 89, 84, 86, 88, 90, 91, 93, 95, 97, 92, 94, 96, 98, 99],
    ![0, 1, 3, 4, 2, 8, 9, 6, 10, 7, 5, 14, 15, 16, 17, 18, 19, 11, 12, 13, 20, 21, 23, 24, 22,
    25, 26, 28, 29, 27, 30, 32, 33, 31, 34, 50, 49, 54, 55, 51, 52, 53, 35, 36, 37, 38, 40, 39,
    41, 43, 42, 47, 46, 48, 44, 45, 58, 59, 60, 61, 56, 57, 62, 66, 63, 67, 64, 68, 65, 69, 72,
    70, 71, 73, 74, 75, 76, 78, 79, 77, 81, 82, 80, 83, 87, 84, 88, 85, 89, 86, 90, 91, 95, 92,
    96, 93, 97, 94, 98, 99], ![0, 1, 4, 3, 2, 10, 9, 7, 8, 6, 5, 17, 18, 19, 14, 15, 16, 11, 12,
    13, 20, 21, 24, 23, 22, 25, 26, 29, 28, 27, 30, 33, 32, 31, 34, 50, 49, 54, 55, 52, 51, 53,
    42, 43, 44, 45, 47, 46, 48, 36, 35, 40, 39, 41, 37, 38, 60, 61, 58, 59, 56, 57, 62, 66, 64,
    68, 63, 67, 65, 69, 70, 72, 71, 73, 74, 75, 76, 79, 78, 77, 82, 81, 80, 83, 87, 85, 89, 84,
    88, 86, 90, 91, 95, 93, 97, 92, 96, 94, 98, 99]]

/-- The induced permutation of columns, including all decorations. -/
def columnPermutation (p : Fin 6) : Equiv.Perm (Fin 100) where
  toFun := permutationDestinations p
  invFun := permutationDestinations (![0, 1, 2, 4, 3, 5] p)
  left_inv := by fin_cases p <;> decide +kernel
  right_inv := by fin_cases p <;> decide +kernel

/-- Actual graph relabelling gives the tabulated column action. -/
theorem columns_relabel (p : Fin 6) (i : Fin 100) :
    (columns i).relabel (labelPermutation p) = columns (columnPermutation p i) := by
  have h : ∀ p i, ((graph i).relabel (labelPermutation p)).isomorphic?
      (graph (columnPermutation p i)) = true := by
    simp only [graph, tableGraph, DecoratedStableGraph.toDecoration_eq_mk]
    decide +kernel
  apply Quotient.sound
  apply (DecoratedStableGraph.isomorphic?_eq_true_iff _ _).mp
  exact h p i

/-- All six covariant label actions on a coordinate expression, retaining repetitions. -/
def symmetrize (x : Coordinates 100) : Coordinates 100 :=
  ∑ p, fun i ↦ x ((columnPermutation p).symm i)

/-- Coordinate symmetrization is the actual sum of six formal graph relabellings. -/
theorem interpret_symmetrize (x : Coordinates 100) :
    interpret columns (symmetrize x) =
      ∑ p, StrataModule.relabel (labelPermutation p) (interpret columns x) := by
  rw [symmetrize, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [relabel_interpret, interpret_apply, interpret_apply]
  have h := Equiv.sum_comp (columnPermutation p)
    (fun i ↦ x ((columnPermutation p).symm i) • StrataModule.basis (columns i))
  simpa only [Equiv.symm_apply_apply, columns_relabel] using h.symm

/-- The twenty diagrams in the paper, in reading order, with one explicit labelling. -/
def paperGraph : Fin 20 → DecoratedStableGraph (Fin 3) :=
  ![tableGraph 2 ({ legVertex := ![1, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![2, 0, 0]
    } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 1], endpoint := ![![0, 1]], genus := ![2, 0] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![1, 0]],
    tableGraph 2 ({ legVertex := ![0, 1, 1], endpoint := ![![0, 1]], genus := ![2, 0] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![1, 0, 0] ![![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 1, 1], endpoint := ![![0, 1]], genus := ![2, 0] } :
      StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![1, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![2, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 1, 0]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 1, 0]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 1, 0]
      } : StableGraphCode.Candidate (Fin 3) 3 2) (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 0, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 1, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![1, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![1, 0] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
    tableGraph 2 ({ legVertex := ![0, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![1, 0] } :
      StableGraphCode.Candidate (Fin 3) 2 2) (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]]]

/-- Every diagram is a stable genus-two graph. -/
theorem paperGraph_totalGenus (i : Fin 20) : (paperGraph i).graph.totalGenus = 2 := by
  fin_cases i <;> decide +kernel

/-- The published representatives as actual decorated strata. -/
def paperStratum (i : Fin 20) : TautologicalStratum 2 (Fin 3) :=
  .mk (paperGraph i) (paperGraph_totalGenus i)

/-- Their slots in the independently held raw frame. -/
def representative : Fin 20 → Fin 100 := ![27, 26, 12, 13, 69, 68, 66, 70, 62, 57, 56, 98, 97, 95,
  91, 90, 89, 87, 83, 80]

/-- Branch powers and label placements of every published diagram are checked. -/
theorem paperStratum_eq (i : Fin 20) : paperStratum i = columns (representative i) := by
  apply Quotient.sound
  apply (DecoratedStableGraph.isomorphic?_eq_true_iff _ _).mp
  simp only [paperGraph, graph, tableGraph, DecoratedStableGraph.toDecoration_eq_mk]
  fin_cases i <;> decide +kernel

/-- Coefficients of equation (4), before stack-to-raw conversion or marking summation. -/
def paperCoefficient : Fin 20 → ℚ := ![-2, 2, 3, -3, (2 / 5), (-6 / 5), (12 / 5), (-18 / 5), (-6 /
  5), (9 / 5), (-6 / 5), (1 / 60), (-3 / 20), (3 / 20), (-1 / 60), (1 / 5), (-3 / 5), (1 / 5), (-1
  / 10), (-1 / 10)]

/-- Inverse label-fixing graph order, distinct from an elliptic point stabilizer. -/
def paperNormalization (i : Fin 20) : ℚ := (automorphismOrders (representative i) : ℚ)⁻¹

/-- Every paper normalization is proved from the actual decorated graph. -/
theorem paperNormalization_correct (i : Fin 20) :
    paperNormalization i = ((paperGraph i).automorphismCount : ℚ)⁻¹ := by
  have h : ∀ i, (paperGraph i).automorphismCount = automorphismOrders (representative i) := by
    simp only [paperGraph, tableGraph, DecoratedStableGraph.toDecoration_eq_mk]
    decide +kernel
  rw [paperNormalization, h]

/-- The complete published relation, with repetitions from all marking assignments. -/
noncomputable def paperRelation : StrataModule 2 (Fin 3) :=
  ∑ i, (paperCoefficient i * paperNormalization i) •
    ∑ p, StrataModule.basis ((paperStratum i).relabel (labelPermutation p))

/-- The separately fixed raw coordinate request, with all lower-genus terms retained. -/
def requested : Coordinates 100 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, -6, 0, 6, -6, 0, 6,
  -6, 0, 0, 0, 0, 0, 0, 12, -4, -4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, (-12 / 5), (18 / 5), (-12 / 5), (18 / 5), (-12 / 5), (18 / 5), (-36 / 5),
  (24 / 5), (24 / 5), (-12 / 5), (24 / 5), (-12 / 5), (-12 / 5), (6 / 5), (-36 / 5), (-36 / 5),
  (-36 / 5), 0, 0, 0, 0, 0, 0, 0, (-1 / 10), (-1 / 10), (-1 / 10), (-3 / 10), (1 / 5), (1 / 5),
  (-3 / 5), (1 / 5), (-3 / 5), (-3 / 5), (3 / 5), (-1 / 20), (3 / 20), (3 / 20), (-3 / 20), (3 /
  20), (-3 / 20), (-3 / 20), (1 / 20), 0]

/-- The finite conversion includes the automorphism divisor and all six assignments. -/
theorem requested_coordinates : requested = symmetrize
    (∑ i, Pi.single (representative i) (paperCoefficient i * paperNormalization i)) := by
  decide +kernel

/-- The held request is exactly the published full equation in the free strata module. -/
theorem interpret_request : interpret columns requested = paperRelation := by
  rw [requested_coordinates, interpret_symmetrize]
  simp only [interpret, map_sum, Fintype.linearCombination_apply_single,
    StrataModule.relabel_basis, map_smul, paperRelation, paperStratum_eq]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum]

/-- The equation is nonzero as a formal expression before geometric relations. -/
theorem requested_ne_zero : interpret columns requested ≠ 0 := by
  intro h
  have hi := congrArg (fun r ↦ r (columns 12)) h
  rw [interpret_apply_column columns columns_injective] at hi
  exact (by norm_num : (6 : ℚ) ≠ 0) hi

end AxiomaticGW.BelorousskiPandharipande

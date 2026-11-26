/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.BelorousskiPandharipande

/-!
# Offline incoming replay for the complete published BP equation

Input SHA256: 5868b2f3ef1e5a45e6175b6349566b72c778f4ab028ef941b43498fd0ee8d1bc
The digest records provenance; graph and rational equalities are kernel obligations.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipandeReplay

/-- Actual incoming graph incidence and all decoration powers. -/
def incomingGraphs : Fin 100 → DecoratedStableGraph (Fin 3) :=
  ![BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], Fin.elim0, ![2]⟩ : StableGraphCode.Candidate (Fin 3) 1 0)
      (by decide +kernel)
      ![![0, 1]] ![0, 0, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], Fin.elim0, ![2]⟩ : StableGraphCode.Candidate (Fin 3) 1 0)
      (by decide +kernel)
      ![![2, 0]] ![0, 0, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], Fin.elim0, ![2]⟩ : StableGraphCode.Candidate (Fin 3) 1 0)
      (by decide +kernel)
      ![![1, 0]] ![1, 0, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], Fin.elim0, ![2]⟩ : StableGraphCode.Candidate (Fin 3) 1 0)
      (by decide +kernel)
      ![![1, 0]] ![0, 1, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], Fin.elim0, ![2]⟩ : StableGraphCode.Candidate (Fin 3) 1 0)
      (by decide +kernel)
      ![![1, 0]] ![0, 0, 1] Fin.elim0, BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], Fin.elim0, ![2]⟩ : StableGraphCode.Candidate (Fin 3) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![2, 0, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], Fin.elim0, ![2]⟩ : StableGraphCode.Candidate (Fin 3) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![1, 1, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], Fin.elim0, ![2]⟩ : StableGraphCode.Candidate (Fin 3) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![1, 0, 1] Fin.elim0, BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], Fin.elim0, ![2]⟩ : StableGraphCode.Candidate (Fin 3) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![0, 2, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], Fin.elim0, ![2]⟩ : StableGraphCode.Candidate (Fin 3) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![0, 1, 1] Fin.elim0, BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], Fin.elim0, ![2]⟩ : StableGraphCode.Candidate (Fin 3) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![0, 0, 2] Fin.elim0, BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 0], ![![0, 1]], ![0, 2]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![1, 0]] ![0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 0], ![![0, 1]], ![0, 2]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![1, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 0], ![![0, 1]], ![0, 2]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 1]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 1, 0], ![![0, 1]], ![0, 2]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![1, 0]] ![0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 1, 0], ![![0, 1]], ![0, 2]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 1, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 1, 0], ![![0, 1]], ![0, 2]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 1]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 1], ![![0, 1]], ![0, 2]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![1, 0]] ![0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 1], ![![0, 1]], ![0, 2]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 1] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 1], ![![0, 1]], ![0, 2]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 1]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], ![![0, 1]], ![0, 2]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![1, 0], ![0, 0]] ![0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], ![![0, 1]], ![0, 2]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![1, 0]] ![0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], ![![0, 1]], ![0, 2]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![1, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], ![![0, 1]], ![0, 2]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 1, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], ![![0, 1]], ![0, 2]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 1] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], ![![0, 1]], ![0, 2]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![1, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], ![![0, 1]], ![0, 2]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 1]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 0], ![![0, 1], ![1, 2]], ![0, 0, 2]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![0, 1, 0], ![![0, 1], ![1, 2]], ![0, 0, 2]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 1], ![![0, 1], ![1, 2]], ![0, 0, 2]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 1], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![1, 0]] ![0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 1], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![1, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 1], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 1, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 1], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 1] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 1], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 1]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 0], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![1, 0], ![0, 0]] ![0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 0], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![1, 0]] ![0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 0], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 1] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 0], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![1, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 0], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![1, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 0], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 1, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 0], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 1]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 1], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![1, 0], ![0, 0]] ![0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 1], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![1, 0]] ![0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 1], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 1, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 1], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![1, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 1], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![1, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 1], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 1] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 1], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 1]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 0], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![1, 0], ![0, 0]] ![0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 0], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![1, 0]] ![0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 0], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 1, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 0], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 1] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 0], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![1, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 0], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![1, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 0], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 1]], BelorousskiPandharipande.tableGraph 2
      (⟨![2, 0, 0], ![![0, 2], ![1, 2]], ![0, 1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![2, 0, 0], ![![0, 1], ![1, 2]], ![0, 1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![0, 2, 0], ![![0, 2], ![1, 2]], ![0, 1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![0, 2, 0], ![![0, 1], ![1, 2]], ![0, 1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 2], ![![0, 2], ![1, 2]], ![0, 1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 2], ![![0, 1], ![1, 2]], ![0, 1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], ![![0, 2], ![1, 2]], ![0, 1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![2, 2, 1], ![![0, 1], ![1, 2]], ![1, 0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![2, 1, 2], ![![0, 1], ![1, 2]], ![1, 0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![2, 1, 1], ![![0, 1], ![1, 2]], ![1, 0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![1, 2, 2], ![![0, 1], ![1, 2]], ![1, 0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![1, 2, 1], ![![0, 1], ![1, 2]], ![1, 0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 2], ![![0, 1], ![1, 2]], ![1, 0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 1], ![![0, 1], ![1, 2]], ![1, 0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![2, 1, 0], ![![0, 1], ![1, 2]], ![1, 0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![1, 2, 0], ![![0, 1], ![1, 2]], ![1, 0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![2, 0, 1], ![![0, 1], ![1, 2]], ![1, 0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 1], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![1, 0], ![0, 0]] ![0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 1], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![1, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], ![![0, 0]], ![1]⟩ : StableGraphCode.Candidate (Fin 3) 1 1)
      (by decide +kernel)
      ![![1, 0]] ![0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], ![![0, 0]], ![1]⟩ : StableGraphCode.Candidate (Fin 3) 1 1)
      (by decide +kernel)
      ![![0, 0]] ![0, 0, 0] ![![1, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], ![![0, 0]], ![1]⟩ : StableGraphCode.Candidate (Fin 3) 1 1)
      (by decide +kernel)
      ![![0, 0]] ![1, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], ![![0, 0]], ![1]⟩ : StableGraphCode.Candidate (Fin 3) 1 1)
      (by decide +kernel)
      ![![0, 0]] ![0, 1, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], ![![0, 0]], ![1]⟩ : StableGraphCode.Candidate (Fin 3) 1 1)
      (by decide +kernel)
      ![![0, 0]] ![0, 0, 1] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 0], ![![1, 1], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 1, 0], ![![1, 1], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 1], ![![1, 1], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], ![![1, 1], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 0], ![![0, 1], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 1], ![![0, 1], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 0], ![![0, 1], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 1, 1], ![![0, 1], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 1, 0], ![![0, 1], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 1], ![![0, 1], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], ![![0, 1], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 1], ![![0, 0], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 0], ![![0, 0], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 1], ![![0, 0], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0, 0], ![![0, 0], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 1, 1], ![![0, 0], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 1, 0], ![![0, 0], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 1], ![![0, 0], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], ![![0, 0], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], ![![0, 0], ![0, 0]], ![0]⟩ : StableGraphCode.Candidate (Fin 3) 1 2)
      (by decide +kernel)
      ![![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]]]

/-- Connectedness and stability were checked by each constructor; genus is retained. -/
theorem incomingGenus (i : Fin 100) : (incomingGraphs i).graph.totalGenus = 2 := by
  fin_cases i <;> decide +kernel

/-- Incoming graph classes use the existing semantic quotient. -/
def incomingColumns (i : Fin 100) : TautologicalStratum 2 (Fin 3) :=
  .mk (incomingGraphs i) (incomingGenus i)

-- The diagnostic branch is exercised by the negative exchange tests.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- Semantic equality is checked against the independently held frame. -/
theorem incomingColumns_eq : incomingColumns = BelorousskiPandharipande.columns := by
  simp only [funext_iff, incomingColumns, BelorousskiPandharipande.columns, incomingGraphs,
    BelorousskiPandharipande.graph,
    BelorousskiPandharipande.tableGraph, DecoratedStableGraph.toDecoration_eq_mk]
  first
  | decide +kernel
  | fail "BP incoming graph frame check did not close"

/-- Actual incoming graph incidence and all decoration powers. -/
def paperGraphs : Fin 20 → DecoratedStableGraph (Fin 3) :=
  ![BelorousskiPandharipande.tableGraph 2
      (⟨![1, 2, 2], ![![0, 1], ![1, 2]], ![2, 0, 0]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 1], ![![0, 1]], ![2, 0]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![1, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 1, 1], ![![0, 1]], ![2, 0]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![1, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 1, 1], ![![0, 1]], ![2, 0]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![1, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 1], ![![0, 1], ![1, 2]], ![1, 0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 2], ![![0, 1], ![1, 2]], ![1, 0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![1, 2, 2], ![![0, 1], ![1, 2]], ![1, 0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![0, 1, 2], ![![0, 1], ![1, 2]], ![1, 0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![2, 2, 2], ![![0, 1], ![1, 2]], ![1, 1, 0]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![0, 2, 2], ![![0, 1], ![1, 2]], ![1, 1, 0]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![1, 2, 2], ![![0, 1], ![1, 2]], ![1, 1, 0]⟩ : StableGraphCode.Candidate (Fin 3) 3 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]],
        BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], ![![0, 0], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 1], ![![0, 0], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 1, 1], ![![0, 0], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 1], ![![0, 0], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 0], ![![0, 1], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0, 1], ![![0, 1], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 1, 1], ![![0, 1], ![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1, 1], ![![0, 0], ![0, 1]], ![1, 0]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 1, 1], ![![0, 0], ![0, 1]], ![1, 0]⟩ : StableGraphCode.Candidate (Fin 3) 2 2)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0], ![0, 0]]]

/-- Connectedness and stability were checked by each constructor; genus is retained. -/
theorem paperGenus (i : Fin 20) : (paperGraphs i).graph.totalGenus = 2 := by
  fin_cases i <;> decide +kernel

/-- Incoming graph classes use the existing semantic quotient. -/
def paperColumns (i : Fin 20) : TautologicalStratum 2 (Fin 3) :=
  .mk (paperGraphs i) (paperGenus i)

-- The diagnostic branch is exercised by the negative exchange tests.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- Semantic equality is checked against the independently held frame. -/
theorem paperColumns_eq : paperColumns = BelorousskiPandharipande.paperStratum := by
  simp only [funext_iff, paperColumns, BelorousskiPandharipande.paperStratum, paperGraphs,
    BelorousskiPandharipande.paperGraph,
    BelorousskiPandharipande.tableGraph, DecoratedStableGraph.toDecoration_eq_mk]
  first
  | decide +kernel
  | fail "BP incoming graph frame check did not close"

/-- Actual incoming component graph frames, including the one-point elliptic input. -/
def sourceGraphs : (b : Fin 7) → Fin (BelorousskiPandharipande.sourceSize b) →
    DecoratedStableGraph (Fin (BelorousskiPandharipande.sourceArity b)) :=
  Fin.cases (![BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0], Fin.elim0, ![2]⟩ : StableGraphCode.Candidate (Fin 2) 1 0)
      (by decide +kernel)
      ![![1, 0]] ![0, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0], Fin.elim0, ![2]⟩ : StableGraphCode.Candidate (Fin 2) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![1, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0], Fin.elim0, ![2]⟩ : StableGraphCode.Candidate (Fin 2) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![0, 1] Fin.elim0, BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0], ![![0, 1]], ![0, 2]⟩ : StableGraphCode.Candidate (Fin 2) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 1], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 2) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![1, 0], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 2) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0, 0], ![![0, 0]], ![1]⟩ : StableGraphCode.Candidate (Fin 2) 1 1)
      (by decide +kernel)
      ![![0, 0]] ![0, 0] ![![0, 0]]]) (
    Fin.cases (![BelorousskiPandharipande.tableGraph 0
      (⟨![0, 0, 0, 0], Fin.elim0, ![0]⟩ : StableGraphCode.Candidate (Fin 4) 1 0)
      (by decide +kernel)
      ![![1, 0]] ![0, 0, 0, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 0
      (⟨![0, 0, 0, 0], Fin.elim0, ![0]⟩ : StableGraphCode.Candidate (Fin 4) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![1, 0, 0, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 0
      (⟨![0, 0, 0, 0], Fin.elim0, ![0]⟩ : StableGraphCode.Candidate (Fin 4) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![0, 1, 0, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 0
      (⟨![0, 0, 0, 0], Fin.elim0, ![0]⟩ : StableGraphCode.Candidate (Fin 4) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![0, 0, 1, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 0
      (⟨![0, 0, 0, 0], Fin.elim0, ![0]⟩ : StableGraphCode.Candidate (Fin 4) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![0, 0, 0, 1] Fin.elim0, BelorousskiPandharipande.tableGraph 0
      (⟨![1, 1, 0, 0], ![![0, 1]], ![0, 0]⟩ : StableGraphCode.Candidate (Fin 4) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 0
      (⟨![1, 0, 1, 0], ![![0, 1]], ![0, 0]⟩ : StableGraphCode.Candidate (Fin 4) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 0
      (⟨![1, 0, 0, 1], ![![0, 1]], ![0, 0]⟩ : StableGraphCode.Candidate (Fin 4) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]]]) (
    Fin.cases (![BelorousskiPandharipande.tableGraph 2
      (⟨![0], Fin.elim0, ![2]⟩ : StableGraphCode.Candidate (Fin 1) 1 0)
      (by decide +kernel)
      ![![1, 0]] ![0] Fin.elim0, BelorousskiPandharipande.tableGraph 2
      (⟨![0], Fin.elim0, ![2]⟩ : StableGraphCode.Candidate (Fin 1) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![1] Fin.elim0, BelorousskiPandharipande.tableGraph 2
      (⟨![1], ![![0, 1]], ![1, 1]⟩ : StableGraphCode.Candidate (Fin 1) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0] ![![0, 0]], BelorousskiPandharipande.tableGraph 2
      (⟨![0], ![![0, 0]], ![1]⟩ : StableGraphCode.Candidate (Fin 1) 1 1)
      (by decide +kernel)
      ![![0, 0]] ![0] ![![0, 0]]]) (
    Fin.cases (![BelorousskiPandharipande.tableGraph 1
      (⟨![0], Fin.elim0, ![1]⟩ : StableGraphCode.Candidate (Fin 1) 1 0)
      (by decide +kernel)
      ![![1, 0]] ![0] Fin.elim0, BelorousskiPandharipande.tableGraph 1
      (⟨![0], Fin.elim0, ![1]⟩ : StableGraphCode.Candidate (Fin 1) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![1] Fin.elim0, BelorousskiPandharipande.tableGraph 1
      (⟨![0], ![![0, 0]], ![0]⟩ : StableGraphCode.Candidate (Fin 1) 1 1)
      (by decide +kernel)
      ![![0, 0]] ![0] ![![0, 0]]]) (
    Fin.cases (![BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0, 0, 0], Fin.elim0, ![1]⟩ : StableGraphCode.Candidate (Fin 4) 1 0)
      (by decide +kernel)
      ![![1, 0]] ![0, 0, 0, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0, 0, 0], Fin.elim0, ![1]⟩ : StableGraphCode.Candidate (Fin 4) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![1, 0, 0, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0, 0, 0], Fin.elim0, ![1]⟩ : StableGraphCode.Candidate (Fin 4) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![0, 1, 0, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0, 0, 0], Fin.elim0, ![1]⟩ : StableGraphCode.Candidate (Fin 4) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![0, 0, 1, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0, 0, 0], Fin.elim0, ![1]⟩ : StableGraphCode.Candidate (Fin 4) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![0, 0, 0, 1] Fin.elim0, BelorousskiPandharipande.tableGraph 1
      (⟨![1, 1, 0, 0], ![![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 4) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 1
      (⟨![1, 0, 1, 0], ![![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 4) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 1
      (⟨![1, 0, 0, 1], ![![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 4) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 1
      (⟨![1, 0, 0, 0], ![![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 4) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 1
      (⟨![0, 1, 1, 0], ![![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 4) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 1
      (⟨![0, 1, 0, 1], ![![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 4) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 1
      (⟨![0, 1, 0, 0], ![![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 4) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0, 1, 1], ![![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 4) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0, 1, 0], ![![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 4) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0, 0, 1], ![![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 4) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0, 0, 0], ![![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 4) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0, 0, 0], ![![0, 0]], ![0]⟩ : StableGraphCode.Candidate (Fin 4) 1 1)
      (by decide +kernel)
      ![![0, 0]] ![0, 0, 0, 0] ![![0, 0]]]) (
    Fin.cases (![BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0], Fin.elim0, ![1]⟩ : StableGraphCode.Candidate (Fin 2) 1 0)
      (by decide +kernel)
      ![![1, 0]] ![0, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0], Fin.elim0, ![1]⟩ : StableGraphCode.Candidate (Fin 2) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![1, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0], Fin.elim0, ![1]⟩ : StableGraphCode.Candidate (Fin 2) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![0, 1] Fin.elim0, BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0], ![![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 2) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0], ![![0, 0]], ![0]⟩ : StableGraphCode.Candidate (Fin 2) 1 1)
      (by decide +kernel)
      ![![0, 0]] ![0, 0] ![![0, 0]]]) (
    Fin.cases (![BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0, 0], Fin.elim0, ![1]⟩ : StableGraphCode.Candidate (Fin 3) 1 0)
      (by decide +kernel)
      ![![1, 0]] ![0, 0, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0, 0], Fin.elim0, ![1]⟩ : StableGraphCode.Candidate (Fin 3) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![1, 0, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0, 0], Fin.elim0, ![1]⟩ : StableGraphCode.Candidate (Fin 3) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![0, 1, 0] Fin.elim0, BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0, 0], Fin.elim0, ![1]⟩ : StableGraphCode.Candidate (Fin 3) 1 0)
      (by decide +kernel)
      ![![0, 0]] ![0, 0, 1] Fin.elim0, BelorousskiPandharipande.tableGraph 1
      (⟨![1, 0, 0], ![![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 1
      (⟨![0, 1, 0], ![![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0, 1], ![![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0, 0], ![![0, 1]], ![0, 1]⟩ : StableGraphCode.Candidate (Fin 3) 2 1)
      (by decide +kernel)
      ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0]], BelorousskiPandharipande.tableGraph 1
      (⟨![0, 0, 0], ![![0, 0]], ![0]⟩ : StableGraphCode.Candidate (Fin 3) 1 1)
      (by decide +kernel)
      ![![0, 0]] ![0, 0, 0] ![![0, 0]]]) (
    fun i ↦ Fin.elim0 i)))))))

/-- Arithmetic genus is checked for every incoming component column. -/
theorem sourceGraphs_genus (b : Fin 7) (i : Fin (BelorousskiPandharipande.sourceSize b)) :
    (sourceGraphs b i).graph.totalGenus = BelorousskiPandharipande.sourceGenus b := by
  fin_cases b <;> fin_cases i <;> decide +kernel

/-- Actual incoming source graph classes. -/
def sourceColumns (b : Fin 7) (i : Fin (BelorousskiPandharipande.sourceSize b)) :
    TautologicalStratum (BelorousskiPandharipande.sourceGenus b) (Fin
      (BelorousskiPandharipande.sourceArity b)) :=
  .mk (sourceGraphs b i) (sourceGraphs_genus b i)

-- The diagnostic branch is exercised by the negative exchange tests.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- Source incidence and decorations agree semantically with the held component frames. -/
theorem sourceColumns_eq : sourceColumns = BelorousskiPandharipande.sourceColumns := by
  simp only [funext_iff, sourceColumns, BelorousskiPandharipande.sourceColumns, sourceGraphs,
    BelorousskiPandharipande.sourceGraph,
    BelorousskiPandharipande.tableGraph, GenusOnePsi.graph, DecoratedStableGraph.toDecoration_eq_mk]
  first
  | decide +kernel
  | fail "BP incoming source graph check did not close"

/-- Incoming component rows, preserving their separately held source families. -/
def sourceRows : (i : Fin 16) → RelationCertificate.Coordinates
  (BelorousskiPandharipande.sourceSize (BelorousskiPandharipande.sourceFamily i)) :=
  Fin.cases (![-15, 15, 15, -15, 21, 21, (3 / 2)]) (
    Fin.cases (![(-153 / 4), (45 / 4), (45 / 4), (45 / 4), (45 / 4), (-9 / 4), (-9 / 4), (-9 /
      4)]) (
    Fin.cases (![(-33 / 2), (-21 / 2), (15 / 2), (15 / 2), (15 / 2), (3 / 2), (3 / 2), (3 / 2)]) (
    Fin.cases (![(-33 / 2), (15 / 2), (15 / 2), (15 / 2), (-21 / 2), (3 / 2), (3 / 2), (3 / 2)]) (
    Fin.cases (![-30, 30, 42, 3]) (
    Fin.cases (![102, -30, -3]) (
    Fin.cases (![30, 42, -3]) (
    Fin.cases (![24, -15, -15, -15, -15, 6, 6, 6, -3, 6, 6, -3, 6, -3, -3, -12, (-3 / 2)]) (
    Fin.cases (![(15 / 4), (21 / 4), (-15 / 4), (-15 / 4), (-15 / 4), (15 / 4), (15 / 4), (15 /
      4), (15 / 4), (-21 / 4), (-21 / 4), (-21 / 4), (-21 / 4), (-21 / 4), (-21 / 4), (-21 / 4),
      (-3 / 8)]) (
    Fin.cases (![(15 / 4), (-15 / 4), (-15 / 4), (-15 / 4), (21 / 4), (-21 / 4), (-21 / 4), (15 /
      4), (-21 / 4), (-21 / 4), (15 / 4), (-21 / 4), (15 / 4), (-21 / 4), (15 / 4), (-21 / 4), (-3
      / 8)]) (
    Fin.cases (![66, -30, -30, -6, -3]) (
    Fin.cases (![15, 21, -15, -21, (-3 / 2)]) (
    Fin.cases (![15, -15, 21, -21, (-3 / 2)]) (
    Fin.cases (![(81 / 2), (-45 / 2), (-45 / 2), (-45 / 2), (9 / 2), (9 / 2), (9 / 2), (-27 / 2),
      (-9 / 4)]) (
    Fin.cases (![(15 / 2), (21 / 2), (-15 / 2), (-15 / 2), (15 / 2), (-21 / 2), (-21 / 2), (-21 /
      2), (-3 / 4)]) (
    Fin.cases (![(15 / 2), (-15 / 2), (-15 / 2), (21 / 2), (-21 / 2), (-21 / 2), (15 / 2), (-21 /
      2), (-3 / 4)]) (
    fun i ↦ Fin.elim0 i))))))))))))))))

/-- Incoming source operation tables. -/
def sourceDestinations : (b : Fin 7) → Fin (BelorousskiPandharipande.sourceSize b) → Fin 100 :=
  Fin.cases (![11, 12, 13, 27, 56, 57, 80]) (
    Fin.cases (![20, 22, 23, 24, 25, 29, 28, 27]) (
    Fin.cases (![21, 26, 62, 83]) (
    Fin.cases (![73, 74, 91]) (
    Fin.cases (![30, 31, 32, 33, 34, 63, 64, 56, 65, 66, 58, 67, 60, 68, 62, 69, 98]) (
    Fin.cases (![35, 37, 38, 63, 92]) (
    Fin.cases (![36, 39, 40, 41, 70, 71, 61, 68, 97]) (
    fun i ↦ Fin.elim0 i)))))))

/-- Actual incoming symmetric row coordinates. -/
def incomingRows : Fin 20 → RelationCertificate.Coordinates 100 := ![![1442448, -237762, 230580,
  230580, 230580, -727650, -94500, -94500, -727650, -94500, -727650, -81540, 23220, 228690,
  -81540, 23220, 228690, -81540, 23220, 228690, 32508, -2484, -28620, -28620, -28620, -134190,
  1890, 53244, 53244, 53244, 173772, -61020, -61020, -61020, -360990, 59724, 94716, -9180, 1890,
  -28620, -28620, -134190, 59724, 94716, -9180, 1890, -28620, -28620, -134190, 94716, 59724,
  -28620, -28620, -134190, -9180, 1890, 7884, -8964, 7884, -8964, 7884, -8964, -21924, 40284,
  40284, -2484, 40284, -2484, -2484, -16146, 42876, 42876, 42876, 42876, 228690, 23058, -66150,
  -9450, -9450, -9450, 2322, 2322, 2322, -918, 23382, 23382, 3942, 23382, 3942, 3942, -7722, 2322,
  -918, -918, -2862, -918, -2862, -2862, -6102, (-945 / 2)],
    ![517104, -66906, 15876, 15876, 15876, -85050, 24300, 24300, -85050, 24300, -85050, 33804,
      -27324, -81270, 33804, -27324, -81270, 33804, -27324, -81270, 6156, 41148, 324, 324, 324,
      39690, -96390, 7884, 7884, 7884, 69660, -6156, -6156, -6156, -187110, 12636, 24300, 9396,
      -5670, 2916, 2916, -51030, 12636, 24300, 9396, -5670, 2916, 2916, -51030, 24300, 12636,
      2916, 2916, -51030, 9396, -5670, -11556, -15444, -11556, -15444, -11556, -15444, -19764,
      3564, 3564, -10692, 3564, -10692, -10692, -11178, 6156, 6156, 6156, 8748, 130410, 7938,
      -28350, -810, -810, -810, -1566, -1566, -1566, -1782, 3726, 3726, -2754, 3726, -2754, -2754,
      -6642, 1458, -486, -486, -1134, -486, -1134, -1134, -3078, (-405 / 2)],
    ![136080, -13230, -11988, -11988, -11988, 47250, 3780, 3780, 47250, 3780, 47250, 9828, 13932,
      -32130, 9828, 13932, -32130, 9828, 13932, -32130, -540, -7020, 3564, 3564, 3564, -32130,
      13230, -5724, -5724, -5724, 21492, 7452, 7452, 7452, -77490, 2484, 324, 5724, -17010, 2700,
      2700, -1890, 2484, 324, 5724, -17010, 2700, 2700, -1890, 324, 2484, 2700, 2700, -1890, 5724,
      -17010, -4428, -4860, -4428, -4860, -4428, -4860, -5724, -6588, -6588, -3564, -6588, -3564,
      -3564, -4158, -3996, -3996, -3996, 2052, 58590, 1998, -9450, 810, 810, 810, -594, -594,
      -594, 54, -2214, -2214, -918, -2214, -918, -918, -2214, 702, -378, -378, -162, -378, -162,
      -162, -1242, (-135 / 2)],
    ![19440, -1350, -3780, -3780, -3780, 24570, -5292, -5292, 24570, -5292, 24570, -2700, -3780,
      20790, -2700, -3780, 20790, -2700, -3780, 20790, -2700, 3780, -3780, -3780, -3780, 20790,
      -24570, -2700, -2700, -2700, 3780, 5292, 5292, 5292, -24570, 3780, -2700, 5292, -24570,
      -3780, -3780, 20790, 3780, -2700, 5292, -24570, -3780, -3780, 20790, -2700, 3780, -3780,
      -3780, 20790, 5292, -24570, 3780, -2700, 3780, -2700, 3780, -2700, -5292, -5292, -5292,
      3780, -5292, 3780, 3780, -2646, -2700, -2700, -2700, -2700, 20790, 270, -1890, 378, 378,
      378, 270, 270, 270, -378, -1998, -1998, 1890, -1998, 1890, 1890, -1998, 270, -378, -378,
      270, -378, 270, 270, -378, (-27 / 2)],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -30, 30, 30, -30, 30, 30, -30, 30, 30, 0, 0, 0, 0, 0, 0, 0,
      -30, -30, -30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      42, 42, 42, 42, 42, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 3, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-459 / 2), 0, (135 / 2), (135 /
      2), (135 / 2), (135 / 2), 0, (-27 / 2), (-27 / 2), (-27 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -99, 0, 9, 9, 9, 45, 0, 9, 9, 9,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -99, 0, 45, 45, 45, -63, 0, 9,
      9, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -180, 0, 0, 0, 0, 180, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 252, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 612, -180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -18, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 180, 252, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -18, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      144, -90, -90, -90, -90, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36,
      0, 36, 0, 36, 0, -18, 36, 36, -18, 36, -18, -18, -72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -9, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      (45 / 2), (-9 / 2), (-9 / 2), (-9 / 2), (-45 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, (-27 / 2), 0, (-27 / 2), 0, (-27 / 2), 0, (-63 / 2), (9 / 2), (9 / 2),
      (-27 / 2), (9 / 2), (-27 / 2), (-27 / 2), (-63 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-9 / 4), 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      (45 / 2), (-45 / 2), (-45 / 2), (-45 / 2), (63 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, (45 / 2), 0, (45 / 2), 0, (45 / 2), 0, (45 / 2), (-63 / 2), (-63 /
      2), (-63 / 2), (-63 / 2), (-63 / 2), (-63 / 2), (-63 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-9 / 4), 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 132, 0, -60, -60, 0, 0, 0, 132, 0, -60, -60, 0, 0, 0, 0, 132, 0, 0, 0, -60, -60,
      0, 0, 0, 0, 0, 0, 0, -12, -12, 0, -12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -6, -6, 0, -6, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 30, 0, 42, -30, 0, 0, 0, 30, 0, 42, -30, 0, 0, 0, 0, 30, 0, 0, 0, 42, -30, 0, 0,
      0, 0, 0, 0, 0, -42, -42, 0, -42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, -3, -3, 0, -3, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 30, 0, -30, 42, 0, 0, 0, 30, 0, -30, 42, 0, 0, 0, 0, 30, 0, 0, 0, -30, 42, 0, 0,
      0, 0, 0, 0, 0, -42, -42, 0, -42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, -3, -3, 0, -3, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 81, 0, 0, -45, -45, -45, 0, 81, 0, 0, -45, -45, -45, 81, 0, -45, -45, -45, 0,
      0, 0, 9, 0, 9, 0, 9, 0, 0, 0, -27, 0, -27, -27, 0, 18, 18, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-9 / 2), 0, (-9 / 2), (-9 / 2), 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 15, 0, 0, 3, 3, -15, 0, 15, 0, 0, 3, 3, -15, 15, 0, 3, 3, -15, 0, 0, 0, -21,
      0, -21, 0, -21, 0, 0, 0, -21, 0, -21, -21, 0, -6, -6, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3 / 2), 0, (-3 / 2), (-3 / 2), 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 15, 0, 0, -15, -15, 21, 0, 15, 0, 0, -15, -15, 21, 15, 0, -15, -15, 21, 0, 0,
      0, 15, 0, 15, 0, 15, 0, 0, 0, -21, 0, -21, -21, 0, -42, -42, -42, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3 / 2), 0, (-3 / 2), (-3 / 2), 0, 0]]

/-- Actual original pushforward-kappa coordinates. -/
def incomingOriginalRows : Fin 20 → RelationCertificate.Coordinates 100 := ![![280035, -39627,
  38430, 38430, 38430, -121275, -15750, -15750, -121275, -15750, -121275, -13590, 3870, 38115,
  -13590, 3870, 38115, -13590, 3870, 38115, 5418, -414, -4770, -4770, -4770, -22365, 315, 8874,
  8874, 8874, 28962, -10170, -10170, -10170, -60165, 9954, 15786, -1530, 315, -4770, -4770,
  -22365, 9954, 15786, -1530, 315, -4770, -4770, -22365, 15786, 9954, -4770, -4770, -22365, -1530,
  315, 1314, -1494, 1314, -1494, 1314, -1494, -3654, 6714, 6714, -414, 6714, -414, -414, -2691,
  7146, 7146, 7146, 7146, 38115, 3843, -11025, -1575, -1575, -1575, 387, 387, 387, -153, 3897,
  3897, 657, 3897, 657, 657, -1287, 387, -153, -153, -477, -153, -477, -477, -1017, (-315 / 4)],
    ![97335, -11151, -18522, 13230, 13230, 61425, 9450, 9450, -51975, -6750, -51975, -6318, -3402,
      21735, 11610, -5130, -31185, 11610, -5130, -31185, 1026, 6858, -378, 270, 270, 6615, -16065,
      -3726, 3834, 3834, 11610, 7182, -5130, -5130, -31185, 1026, 6858, 270, 6615, 4158, -2970,
      -16065, 1026, 6858, 270, 6615, 4158, -2970, -16065, -1566, 4266, 270, 270, 6615, 4158,
      -16065, 1674, -1134, -3726, -3294, -3726, -3294, -3294, 3834, 3834, 1242, -5886, -3294,
      -3294, -1863, 4266, -5454, 4266, 1458, 21735, 1323, -4725, 945, -675, -675, 243, -513, -513,
      -297, 2133, 2133, 837, -2403, -1107, -1107, -1107, 243, 27, 27, 27, -297, -297, -297, -513,
      (-135 / 4)],
    ![24885, -2205, -4662, -4662, 3330, 20475, -4410, 3150, 20475, 3150, -17325, 3582, 2898,
      -12915, 3582, 2898, -12915, -2250, 1170, 9765, -90, -1170, 1386, 1386, -990, -5355, 2205,
      -2466, -2466, 2070, 3582, 2898, 2898, -2070, -12915, 1422, 2502, 90, 2205, 1386, 1386,
      -5355, -90, -1170, 1386, -5355, -126, 90, 2205, -1170, -90, -126, 90, 2205, 1386, -5355,
      -1386, -954, -1386, -954, 558, -522, -954, 1638, -2466, -954, -2466, -954, 126, -693, -2034,
      -2034, 2070, 342, 9765, 333, -1575, 315, 315, -225, -207, -207, 117, 9, 927, -1017, -369,
      -1017, -369, 279, -369, 117, 9, -99, 9, -99, 9, -99, -207, (-45 / 4)],
    ![3465, -225, -630, -630, -630, 4095, -882, -882, 4095, -882, 4095, -450, -630, 3465, -450,
      -630, 3465, -450, -630, 3465, -450, 630, -630, -630, -630, 3465, -4095, -450, -450, -450,
      630, 882, 882, 882, -4095, 630, -450, 882, -4095, -630, -630, 3465, 630, -450, 882, -4095,
      -630, -630, 3465, -450, 630, -630, -630, 3465, 882, -4095, 630, -450, 630, -450, 630, -450,
      -882, -882, -882, 630, -882, 630, 630, -441, -450, -450, -450, -450, 3465, 45, -315, 63, 63,
      63, 45, 45, 45, -63, -333, -333, 315, -333, 315, 315, -333, 45, -63, -63, 45, -63, 45, 45,
      -63, (-9 / 4)],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -15, 15, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -15, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 21, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3 / 2), 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-153 / 4), 0, (45 / 4), (45 /
      4), (45 / 4), (45 / 4), 0, (-9 / 4), (-9 / 4), (-9 / 4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-33 / 2), 0, (-21 / 2), (15 /
      2), (15 / 2), (15 / 2), 0, (3 / 2), (3 / 2), (3 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-33 / 2), 0, (15 / 2), (15 /
      2), (15 / 2), (-21 / 2), 0, (3 / 2), (3 / 2), (3 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -30, 0, 0, 0, 0, 30, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 102, -30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -3, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3,
      0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      24, -15, -15, -15, -15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0,
      6, 0, 6, 0, -3, 6, 6, -3, 6, -3, -3, -12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3 / 2), 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      (15 / 4), (21 / 4), (-15 / 4), (-15 / 4), (-15 / 4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, (15 / 4), 0, (-21 / 4), 0, (-21 / 4), 0, (-21 / 4), (15 / 4), (15 /
      4), (15 / 4), (-21 / 4), (-21 / 4), (-21 / 4), (-21 / 4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3 / 8), 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      (15 / 4), (-15 / 4), (-15 / 4), (-15 / 4), (21 / 4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, (15 / 4), 0, (15 / 4), 0, (15 / 4), 0, (15 / 4), (-21 / 4), (-21 /
      4), (-21 / 4), (-21 / 4), (-21 / 4), (-21 / 4), (-21 / 4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3 / 8), 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 66, 0, -30, -30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -3, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 15, 0, 21, -15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, -21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, (-3 / 2), 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 15, 0, -15, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, -21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, (-3 / 2), 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, (81 / 2), 0, 0, (-45 / 2), (-45 / 2), (-45 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (9 / 2), 0, 0, 0, 0, 0, 0, (-27 / 2), 0, (9 / 2), (9 / 2), 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-9 / 4), 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, (15 / 2), 0, 0, (21 / 2), (-15 / 2), (-15 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, (-21 / 2), 0, 0, 0, 0, 0, 0, (-21 / 2), 0, (15 / 2), (-21 / 2),
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3 / 4), 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, (15 / 2), 0, 0, (-15 / 2), (-15 / 2), (21 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, (15 / 2), 0, 0, 0, 0, 0, 0, (-21 / 2), 0, (-21 / 2), (-21 / 2),
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3 / 4), 0, 0]]

/-- Actual unsymmetrized monomial-kappa coordinates. -/
def incomingUnsymmetrizedRows : Fin 20 → RelationCertificate.Coordinates 100 := ![![240408,
  -39627, 38430, 38430, 38430, -121275, -15750, -15750, -121275, -15750, -121275, -13590, 3870,
  38115, -13590, 3870, 38115, -13590, 3870, 38115, 5418, -414, -4770, -4770, -4770, -22365, 315,
  8874, 8874, 8874, 28962, -10170, -10170, -10170, -60165, 9954, 15786, -1530, 315, -4770, -4770,
  -22365, 9954, 15786, -1530, 315, -4770, -4770, -22365, 15786, 9954, -4770, -4770, -22365, -1530,
  315, 1314, -1494, 1314, -1494, 1314, -1494, -3654, 6714, 6714, -414, 6714, -414, -414, -2691,
  7146, 7146, 7146, 7146, 38115, 3843, -11025, -1575, -1575, -1575, 387, 387, 387, -153, 3897,
  3897, 657, 3897, 657, 657, -1287, 387, -153, -153, -477, -153, -477, -477, -1017, (-315 / 4)],
    ![86184, -11151, -18522, 13230, 13230, 61425, 9450, 9450, -51975, -6750, -51975, -6318, -3402,
      21735, 11610, -5130, -31185, 11610, -5130, -31185, 1026, 6858, -378, 270, 270, 6615, -16065,
      -3726, 3834, 3834, 11610, 7182, -5130, -5130, -31185, 1026, 6858, 270, 6615, 4158, -2970,
      -16065, 1026, 6858, 270, 6615, 4158, -2970, -16065, -1566, 4266, 270, 270, 6615, 4158,
      -16065, 1674, -1134, -3726, -3294, -3726, -3294, -3294, 3834, 3834, 1242, -5886, -3294,
      -3294, -1863, 4266, -5454, 4266, 1458, 21735, 1323, -4725, 945, -675, -675, 243, -513, -513,
      -297, 2133, 2133, 837, -2403, -1107, -1107, -1107, 243, 27, 27, 27, -297, -297, -297, -513,
      (-135 / 4)],
    ![22680, -2205, -4662, -4662, 3330, 20475, -4410, 3150, 20475, 3150, -17325, 3582, 2898,
      -12915, 3582, 2898, -12915, -2250, 1170, 9765, -90, -1170, 1386, 1386, -990, -5355, 2205,
      -2466, -2466, 2070, 3582, 2898, 2898, -2070, -12915, 1422, 2502, 90, 2205, 1386, 1386,
      -5355, -90, -1170, 1386, -5355, -126, 90, 2205, -1170, -90, -126, 90, 2205, 1386, -5355,
      -1386, -954, -1386, -954, 558, -522, -954, 1638, -2466, -954, -2466, -954, 126, -693, -2034,
      -2034, 2070, 342, 9765, 333, -1575, 315, 315, -225, -207, -207, 117, 9, 927, -1017, -369,
      -1017, -369, 279, -369, 117, 9, -99, 9, -99, 9, -99, -207, (-45 / 4)],
    ![3240, -225, -630, -630, -630, 4095, -882, -882, 4095, -882, 4095, -450, -630, 3465, -450,
      -630, 3465, -450, -630, 3465, -450, 630, -630, -630, -630, 3465, -4095, -450, -450, -450,
      630, 882, 882, 882, -4095, 630, -450, 882, -4095, -630, -630, 3465, 630, -450, 882, -4095,
      -630, -630, 3465, -450, 630, -630, -630, 3465, 882, -4095, 630, -450, 630, -450, 630, -450,
      -882, -882, -882, 630, -882, 630, 630, -441, -450, -450, -450, -450, 3465, 45, -315, 63, 63,
      63, 45, 45, 45, -63, -333, -333, 315, -333, 315, 315, -333, 45, -63, -63, 45, -63, 45, 45,
      -63, (-9 / 4)],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -15, 15, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -15, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 21, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3 / 2), 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-153 / 4), 0, (45 / 4), (45 /
      4), (45 / 4), (45 / 4), 0, (-9 / 4), (-9 / 4), (-9 / 4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-33 / 2), 0, (-21 / 2), (15 /
      2), (15 / 2), (15 / 2), 0, (3 / 2), (3 / 2), (3 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-33 / 2), 0, (15 / 2), (15 /
      2), (15 / 2), (-21 / 2), 0, (3 / 2), (3 / 2), (3 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -30, 0, 0, 0, 0, 30, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 102, -30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      -3, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3,
      0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      24, -15, -15, -15, -15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0,
      6, 0, 6, 0, -3, 6, 6, -3, 6, -3, -3, -12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3 / 2), 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      (15 / 4), (21 / 4), (-15 / 4), (-15 / 4), (-15 / 4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, (15 / 4), 0, (-21 / 4), 0, (-21 / 4), 0, (-21 / 4), (15 / 4), (15 /
      4), (15 / 4), (-21 / 4), (-21 / 4), (-21 / 4), (-21 / 4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3 / 8), 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      (15 / 4), (-15 / 4), (-15 / 4), (-15 / 4), (21 / 4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, (15 / 4), 0, (15 / 4), 0, (15 / 4), 0, (15 / 4), (-21 / 4), (-21 /
      4), (-21 / 4), (-21 / 4), (-21 / 4), (-21 / 4), (-21 / 4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3 / 8), 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 66, 0, -30, -30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -3, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 15, 0, 21, -15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, -21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, (-3 / 2), 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 15, 0, -15, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, -21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, (-3 / 2), 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, (81 / 2), 0, 0, (-45 / 2), (-45 / 2), (-45 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (9 / 2), 0, 0, 0, 0, 0, 0, (-27 / 2), 0, (9 / 2), (9 / 2), 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-9 / 4), 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, (15 / 2), 0, 0, (21 / 2), (-15 / 2), (-15 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, (-21 / 2), 0, 0, 0, 0, 0, 0, (-21 / 2), 0, (15 / 2), (-21 / 2),
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3 / 4), 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, (15 / 2), 0, 0, (-15 / 2), (-15 / 2), (21 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, (15 / 2), 0, 0, 0, 0, 0, 0, (-21 / 2), 0, (-21 / 2), (-21 / 2),
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3 / 4), 0, 0]]

/-- Every incoming mathematical field is retained for acceptance checking. -/
def exchange : BelorousskiPandharipande.Exchange where
  presentation := {
    columns := incomingColumns
    columnFactors := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    rows := incomingRows
    claimedRequest := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, -6, 0, 6, -6, 0, 6, -6, 0, 0, 0, 0,
      0, 0, 12, -4, -4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, (-12 / 5), (18 / 5), (-12 / 5), (18 / 5), (-12 / 5), (18 / 5), (-36 / 5), (24 / 5),
      (24 / 5), (-12 / 5), (24 / 5), (-12 / 5), (-12 / 5), (6 / 5), (-36 / 5), (-36 / 5), (-36 /
      5), 0, 0, 0, 0, 0, 0, 0, (-1 / 10), (-1 / 10), (-1 / 10), (-3 / 10), (1 / 5), (1 / 5), (-3 /
      5), (1 / 5), (-3 / 5), (-3 / 5), (3 / 5), (-1 / 20), (3 / 20), (3 / 20), (-3 / 20), (3 /
      20), (-3 / 20), (-3 / 20), (1 / 20), 0]
    certificate := ⟨![(1 / 103680), (-7 / 103680), (7 / 34560), (-7 / 20736), (-1 / 180), (109 /
      945), (-13 / 210), (-25 / 126), (-11 / 360), (-7 / 2160), (1 / 216), (1 / 270), (1 / 90),
      (-1 / 27), (1 / 40), (1 / 120), (-1 / 12), (-1 / 36), (-1 / 30), (1 / 6)]⟩ }
  originalRows := incomingOriginalRows
  unsymmetrizedRows := incomingUnsymmetrizedRows
  conversionSource := 1
  conversionTarget := 0
  forwardCoefficient := 1
  backwardCoefficient := -1
  automorphisms := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 8]
  paperColumns := paperColumns
  paperCoefficients := ![-2, 2, 3, -3, (2 / 5), (-6 / 5), (12 / 5), (-18 / 5), (-6 / 5), (9 / 5),
    (-6 / 5), (1 / 60), (-3 / 20), (3 / 20), (-1 / 60), (1 / 5), (-3 / 5), (1 / 5), (-1 / 10), (-1
    / 10)]
  paperOrders := ![1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2]
  paperDestinations := ![![27, 27, 28, 29, 28, 29], ![26, 26, 26, 26, 26, 26], ![12, 12, 15, 18,
    15, 18], ![13, 13, 16, 19, 16, 19], ![69, 69, 69, 69, 69, 69], ![68, 67, 68, 67, 65, 65],
    ![66, 66, 64, 63, 64, 63], ![70, 72, 71, 71, 72, 70], ![62, 62, 62, 62, 62, 62], ![57, 57, 59,
    61, 59, 61], ![56, 56, 58, 60, 58, 60], ![98, 98, 98, 98, 98, 98], ![97, 96, 97, 96, 94, 94],
    ![95, 95, 93, 92, 93, 92], ![91, 91, 91, 91, 91, 91], ![90, 90, 90, 90, 90, 90], ![89, 88, 89,
    88, 86, 86], ![87, 87, 85, 84, 85, 84], ![83, 83, 83, 83, 83, 83], ![80, 80, 81, 82, 81, 82]]
  permutationDestinations := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
    19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41,
    42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64,
    65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87,
    88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99], ![0, 1, 2, 4, 3, 5, 7, 6, 10, 9, 8, 11, 12,
    13, 17, 18, 19, 14, 15, 16, 20, 21, 22, 24, 23, 25, 26, 27, 29, 28, 30, 31, 33, 32, 34, 42,
    43, 44, 45, 46, 47, 48, 35, 36, 37, 38, 39, 40, 41, 49, 50, 52, 51, 53, 54, 55, 56, 57, 60,
    61, 58, 59, 62, 64, 63, 65, 66, 68, 67, 69, 72, 71, 70, 73, 74, 75, 76, 77, 79, 78, 80, 82,
    81, 83, 85, 84, 86, 87, 89, 88, 90, 91, 93, 92, 94, 95, 97, 96, 98, 99], ![0, 1, 3, 2, 4, 8,
    6, 9, 5, 7, 10, 14, 15, 16, 11, 12, 13, 17, 18, 19, 20, 21, 23, 22, 24, 25, 26, 28, 27, 29,
    30, 32, 31, 33, 34, 35, 36, 37, 38, 40, 39, 41, 50, 49, 54, 55, 51, 52, 53, 43, 42, 46, 47,
    48, 44, 45, 58, 59, 56, 57, 60, 61, 62, 63, 66, 67, 64, 65, 68, 69, 71, 70, 72, 73, 74, 75,
    76, 78, 77, 79, 81, 80, 82, 83, 84, 87, 88, 85, 86, 89, 90, 91, 92, 95, 96, 93, 94, 97, 98,
    99], ![0, 1, 4, 2, 3, 10, 7, 9, 5, 6, 8, 17, 18, 19, 11, 12, 13, 14, 15, 16, 20, 21, 24, 22,
    23, 25, 26, 29, 27, 28, 30, 33, 31, 32, 34, 42, 43, 44, 45, 47, 46, 48, 50, 49, 54, 55, 52,
    51, 53, 36, 35, 39, 40, 41, 37, 38, 60, 61, 56, 57, 58, 59, 62, 64, 66, 68, 63, 65, 67, 69,
    71, 72, 70, 73, 74, 75, 76, 79, 77, 78, 82, 80, 81, 83, 85, 87, 89, 84, 86, 88, 90, 91, 93,
    95, 97, 92, 94, 96, 98, 99], ![0, 1, 3, 4, 2, 8, 9, 6, 10, 7, 5, 14, 15, 16, 17, 18, 19, 11,
    12, 13, 20, 21, 23, 24, 22, 25, 26, 28, 29, 27, 30, 32, 33, 31, 34, 50, 49, 54, 55, 51, 52,
    53, 35, 36, 37, 38, 40, 39, 41, 43, 42, 47, 46, 48, 44, 45, 58, 59, 60, 61, 56, 57, 62, 66,
    63, 67, 64, 68, 65, 69, 72, 70, 71, 73, 74, 75, 76, 78, 79, 77, 81, 82, 80, 83, 87, 84, 88,
    85, 89, 86, 90, 91, 95, 92, 96, 93, 97, 94, 98, 99], ![0, 1, 4, 3, 2, 10, 9, 7, 8, 6, 5, 17,
    18, 19, 14, 15, 16, 11, 12, 13, 20, 21, 24, 23, 22, 25, 26, 29, 28, 27, 30, 33, 32, 31, 34,
    50, 49, 54, 55, 52, 51, 53, 42, 43, 44, 45, 47, 46, 48, 36, 35, 40, 39, 41, 37, 38, 60, 61,
    58, 59, 56, 57, 62, 66, 64, 68, 63, 67, 65, 69, 70, 72, 71, 73, 74, 75, 76, 79, 78, 77, 82,
    81, 80, 83, 87, 85, 89, 84, 88, 86, 90, 91, 95, 93, 97, 92, 96, 94, 98, 99]]
  sourceColumns := sourceColumns
  sourceRows := sourceRows
  sourceDestinations := sourceDestinations
  generatorReferences := ![1, 2, 5, 9, 16, 19, 20, 23, 31, 32, 33, 34, 35, 38, 39, 40, 41, 42, 43,
    45]

set_option maxHeartbeats 2000000 in
-- Kernel acceptance compares the complete three 20-by-100 tables and all operation data.
-- The diagnostic branch is exercised by the negative exchange tests.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- Incoming graphs and exact arithmetic prove acceptance for the caller-held published claim. -/
theorem accepted : BelorousskiPandharipande.AcceptsExchange exchange := by
  refine ⟨⟨⟨incomingColumns_eq, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    paperColumns_eq, ?_, ?_, ?_, ?_, sourceColumns_eq, ?_, ?_, ?_⟩ <;>
    first
    | decide +kernel
    | fail "BP incoming coordinate check did not close"

/-- Offline replay proves the original published equation belongs to the fixed row span. -/
theorem requested_mem_relationSpan :
    RelationCertificate.interpret BelorousskiPandharipande.columns
      BelorousskiPandharipande.requested ∈
      RelationCertificate.relationSpan BelorousskiPandharipande.columns
        BelorousskiPandharipande.rows :=
  RelationCertificate.acceptsPresentation_sound _ _ _ exchange.presentation accepted.1

end AxiomaticGW.BelorousskiPandharipandeReplay

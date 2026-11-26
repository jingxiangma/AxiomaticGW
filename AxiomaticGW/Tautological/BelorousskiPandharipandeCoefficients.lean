/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.BelorousskiPandharipandeGraphs

/-!
# Direct computation of the twenty raw BP coefficients

The original normalization accesses a hundred-column finite vector. Native
profiling showed that traversing its nested `Fin` recursors dominates even a
zero-class contraction. This direct twenty-case lookup is proved equal to the
original coefficient times graph normalization at every published term.
The graph data, automorphism proofs and original public definitions are unchanged.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande

/-- Published coefficient divided by the proved decorated graph order. -/
def rawPaperCoefficient (i : Fin 20) : ℚ :=
  match i with
  | ⟨0, _⟩ => -2
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => -3
  | ⟨4, _⟩ => 1 / 5
  | ⟨5, _⟩ => -6 / 5
  | ⟨6, _⟩ => 12 / 5
  | ⟨7, _⟩ => -18 / 5
  | ⟨8, _⟩ => -6 / 5
  | ⟨9, _⟩ => 9 / 5
  | ⟨10, _⟩ => -6 / 5
  | ⟨11, _⟩ => 1 / 120
  | ⟨12, _⟩ => -3 / 40
  | ⟨13, _⟩ => 3 / 40
  | ⟨14, _⟩ => -1 / 120
  | ⟨15, _⟩ => 1 / 10
  | ⟨16, _⟩ => -3 / 10
  | ⟨17, _⟩ => 1 / 10
  | ⟨18, _⟩ => -1 / 20
  | ⟨19, _⟩ => -1 / 20
  | ⟨n + 20, h⟩ => False.elim (by omega)

/-- Kernel verification binds every fast entry to the existing BP claim. -/
theorem rawPaperCoefficient_eq (i : Fin 20) :
    rawPaperCoefficient i = paperCoefficient i * paperNormalization i := by
  fin_cases i <;> decide +kernel

end AxiomaticGW.BelorousskiPandharipande

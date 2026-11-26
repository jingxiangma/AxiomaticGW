/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Transfer

/-! # Outer-marking transports for the Bl₂ strict-line contraction

Each proof compares the original decorated graph before the two external
permutations. The three equal exceptional insertions have identical
pullbacks wherever a representative is reused.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoLineH.Frame
open GluingExpression
set_option maxRecDepth 20000

private abbrev core121 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term121.expression).2.2

theorem same140 : unweighted 121 = unweighted 140 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core121 L24Gluing.term121.decoration L24Gluing.term121.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same155 : unweighted 121 = unweighted 155 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core121 L24Gluing.term121.decoration L24Gluing.term121.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core122 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term122.expression).2.2

theorem same141 : unweighted 122 = unweighted 141 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core122 L24Gluing.term122.decoration L24Gluing.term122.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same156 : unweighted 122 = unweighted 156 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core122 L24Gluing.term122.decoration L24Gluing.term122.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core124 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term124.expression).2.2

theorem same142 : unweighted 124 = unweighted 142 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core124 L24Gluing.term124.decoration L24Gluing.term124.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same157 : unweighted 124 = unweighted 157 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core124 L24Gluing.term124.decoration L24Gluing.term124.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core126 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term126.expression).2.2

theorem same143 : unweighted 126 = unweighted 143 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core126 L24Gluing.term126.decoration L24Gluing.term126.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same158 : unweighted 126 = unweighted 158 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core126 L24Gluing.term126.decoration L24Gluing.term126.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core127 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term127.expression).2.2

theorem same144 : unweighted 127 = unweighted 144 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core127 L24Gluing.term127.decoration L24Gluing.term127.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same159 : unweighted 127 = unweighted 159 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core127 L24Gluing.term127.decoration L24Gluing.term127.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core128 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term128.expression).2.2

theorem same145 : unweighted 128 = unweighted 145 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core128 L24Gluing.term128.decoration L24Gluing.term128.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same160 : unweighted 128 = unweighted 160 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core128 L24Gluing.term128.decoration L24Gluing.term128.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core129 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term129.expression).2.2

theorem same146 : unweighted 129 = unweighted 146 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core129 L24Gluing.term129.decoration L24Gluing.term129.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same161 : unweighted 129 = unweighted 161 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core129 L24Gluing.term129.decoration L24Gluing.term129.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core130 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term130.expression).2.2

theorem same147 : unweighted 130 = unweighted 147 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core130 L24Gluing.term130.decoration L24Gluing.term130.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation11 shifted 0 labels (by decide +kernel)

theorem same162 : unweighted 130 = unweighted 162 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core130 L24Gluing.term130.decoration L24Gluing.term130.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation12 shifted 0 labels (by decide +kernel)

private abbrev core131 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term131.expression).2.2

theorem same148 : unweighted 131 = unweighted 148 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core131 L24Gluing.term131.decoration L24Gluing.term131.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation11 shifted 0 labels (by decide +kernel)

theorem same163 : unweighted 131 = unweighted 163 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core131 L24Gluing.term131.decoration L24Gluing.term131.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation12 shifted 0 labels (by decide +kernel)

private abbrev core132 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term132.expression).2.2

theorem same149 : unweighted 132 = unweighted 149 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core132 L24Gluing.term132.decoration L24Gluing.term132.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation11 shifted 0 labels (by decide +kernel)

theorem same164 : unweighted 132 = unweighted 164 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core132 L24Gluing.term132.decoration L24Gluing.term132.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation12 shifted 0 labels (by decide +kernel)

private abbrev core134 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term134.expression).2.2

theorem same150 : unweighted 134 = unweighted 150 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core134 L24Gluing.term134.decoration L24Gluing.term134.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation11 shifted 0 labels (by decide +kernel)

theorem same165 : unweighted 134 = unweighted 165 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core134 L24Gluing.term134.decoration L24Gluing.term134.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation12 shifted 0 labels (by decide +kernel)

private abbrev core135 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term135.expression).2.2

theorem same151 : unweighted 135 = unweighted 151 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core135 L24Gluing.term135.decoration L24Gluing.term135.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 shifted 0 labels (by decide +kernel)

theorem same166 : unweighted 135 = unweighted 166 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core135 L24Gluing.term135.decoration L24Gluing.term135.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 shifted 0 labels (by decide +kernel)

private abbrev core137 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term137.expression).2.2

theorem same152 : unweighted 137 = unweighted 152 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core137 L24Gluing.term137.decoration L24Gluing.term137.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 shifted 0 labels (by decide +kernel)

theorem same167 : unweighted 137 = unweighted 167 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core137 L24Gluing.term137.decoration L24Gluing.term137.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 shifted 0 labels (by decide +kernel)

private abbrev core138 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term138.expression).2.2

theorem same153 : unweighted 138 = unweighted 153 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core138 L24Gluing.term138.decoration L24Gluing.term138.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 shifted 0 labels (by decide +kernel)

theorem same168 : unweighted 138 = unweighted 168 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core138 L24Gluing.term138.decoration L24Gluing.term138.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 shifted 0 labels (by decide +kernel)

private abbrev core139 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term139.expression).2.2

theorem same154 : unweighted 139 = unweighted 154 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core139 L24Gluing.term139.decoration L24Gluing.term139.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 shifted 0 labels (by decide +kernel)

theorem same169 : unweighted 139 = unweighted 169 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core139 L24Gluing.term139.decoration L24Gluing.term139.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 shifted 0 labels (by decide +kernel)

end AxiomaticGW.BlowupTwoLineH.Frame

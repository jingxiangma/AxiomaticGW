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

private abbrev core230 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term230.expression).2.2

theorem same257 : unweighted 230 = unweighted 257 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core230 L24Gluing.term230.decoration L24Gluing.term230.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same269 : unweighted 230 = unweighted 269 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core230 L24Gluing.term230.decoration L24Gluing.term230.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core231 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term231.expression).2.2

theorem same258 : unweighted 231 = unweighted 258 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core231 L24Gluing.term231.decoration L24Gluing.term231.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same270 : unweighted 231 = unweighted 270 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core231 L24Gluing.term231.decoration L24Gluing.term231.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core232 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term232.expression).2.2

theorem same259 : unweighted 232 = unweighted 259 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core232 L24Gluing.term232.decoration L24Gluing.term232.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same271 : unweighted 232 = unweighted 271 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core232 L24Gluing.term232.decoration L24Gluing.term232.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core276 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term276.expression).2.2

theorem same277 : unweighted 276 = unweighted 277 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core276 L24Gluing.term276.decoration L24Gluing.term276.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation16 shifted 0 labels (by decide +kernel)

theorem same283 : unweighted 276 = unweighted 283 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core276 L24Gluing.term276.decoration L24Gluing.term276.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation17 shifted 0 labels (by decide +kernel)

private abbrev core279 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term279.expression).2.2

theorem same285 : unweighted 279 = unweighted 285 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core279 L24Gluing.term279.decoration L24Gluing.term279.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same288 : unweighted 279 = unweighted 288 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core279 L24Gluing.term279.decoration L24Gluing.term279.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core280 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term280.expression).2.2

theorem same286 : unweighted 280 = unweighted 286 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core280 L24Gluing.term280.decoration L24Gluing.term280.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same289 : unweighted 280 = unweighted 289 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core280 L24Gluing.term280.decoration L24Gluing.term280.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core281 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term281.expression).2.2

theorem same287 : unweighted 281 = unweighted 287 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core281 L24Gluing.term281.decoration L24Gluing.term281.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same290 : unweighted 281 = unweighted 290 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core281 L24Gluing.term281.decoration L24Gluing.term281.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core296 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term296.expression).2.2

theorem same300 : unweighted 296 = unweighted 300 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core296 L24Gluing.term296.decoration L24Gluing.term296.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same308 : unweighted 296 = unweighted 308 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core296 L24Gluing.term296.decoration L24Gluing.term296.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

end AxiomaticGW.BlowupTwoLineH.Frame

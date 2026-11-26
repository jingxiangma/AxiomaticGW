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

private abbrev core517 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term517.expression).2.2

theorem same521 : unweighted 517 = unweighted 521 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core517 L24Gluing.term517.decoration L24Gluing.term517.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same531 : unweighted 517 = unweighted 531 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core517 L24Gluing.term517.decoration L24Gluing.term517.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core518 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term518.expression).2.2

theorem same522 : unweighted 518 = unweighted 522 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core518 L24Gluing.term518.decoration L24Gluing.term518.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

private abbrev core523 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term523.expression).2.2

theorem same532 : unweighted 523 = unweighted 532 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core523 L24Gluing.term523.decoration L24Gluing.term523.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same538 : unweighted 523 = unweighted 538 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core523 L24Gluing.term523.decoration L24Gluing.term523.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core524 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term524.expression).2.2

theorem same533 : unweighted 524 = unweighted 533 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core524 L24Gluing.term524.decoration L24Gluing.term524.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same539 : unweighted 524 = unweighted 539 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core524 L24Gluing.term524.decoration L24Gluing.term524.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core525 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term525.expression).2.2

theorem same534 : unweighted 525 = unweighted 534 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core525 L24Gluing.term525.decoration L24Gluing.term525.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same540 : unweighted 525 = unweighted 540 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core525 L24Gluing.term525.decoration L24Gluing.term525.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core526 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term526.expression).2.2

theorem same535 : unweighted 526 = unweighted 535 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core526 L24Gluing.term526.decoration L24Gluing.term526.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same541 : unweighted 526 = unweighted 541 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core526 L24Gluing.term526.decoration L24Gluing.term526.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core527 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term527.expression).2.2

theorem same536 : unweighted 527 = unweighted 536 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core527 L24Gluing.term527.decoration L24Gluing.term527.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same542 : unweighted 527 = unweighted 542 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core527 L24Gluing.term527.decoration L24Gluing.term527.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core528 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term528.expression).2.2

theorem same537 : unweighted 528 = unweighted 537 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core528 L24Gluing.term528.decoration L24Gluing.term528.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same543 : unweighted 528 = unweighted 543 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core528 L24Gluing.term528.decoration L24Gluing.term528.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core548 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term548.expression).2.2

theorem same549 : unweighted 548 = unweighted 549 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core548 L24Gluing.term548.decoration L24Gluing.term548.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation16 shifted 0 labels (by decide +kernel)

theorem same555 : unweighted 548 = unweighted 555 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core548 L24Gluing.term548.decoration L24Gluing.term548.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation17 shifted 0 labels (by decide +kernel)

private abbrev core550 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term550.expression).2.2

theorem same557 : unweighted 550 = unweighted 557 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core550 L24Gluing.term550.decoration L24Gluing.term550.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same561 : unweighted 550 = unweighted 561 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core550 L24Gluing.term550.decoration L24Gluing.term550.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core551 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term551.expression).2.2

theorem same558 : unweighted 551 = unweighted 558 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core551 L24Gluing.term551.decoration L24Gluing.term551.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same562 : unweighted 551 = unweighted 562 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core551 L24Gluing.term551.decoration L24Gluing.term551.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core552 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term552.expression).2.2

theorem same559 : unweighted 552 = unweighted 559 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core552 L24Gluing.term552.decoration L24Gluing.term552.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same563 : unweighted 552 = unweighted 563 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core552 L24Gluing.term552.decoration L24Gluing.term552.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core553 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term553.expression).2.2

theorem same560 : unweighted 553 = unweighted 560 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core553 L24Gluing.term553.decoration L24Gluing.term553.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same564 : unweighted 553 = unweighted 564 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core553 L24Gluing.term553.decoration L24Gluing.term553.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

end AxiomaticGW.BlowupTwoLineH.Frame

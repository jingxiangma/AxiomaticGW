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

private abbrev core459 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term459.expression).2.2

theorem same469 : unweighted 459 = unweighted 469 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core459 L24Gluing.term459.decoration L24Gluing.term459.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation14 shifted 0 labels (by decide +kernel)

theorem same482 : unweighted 459 = unweighted 482 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core459 L24Gluing.term459.decoration L24Gluing.term459.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation15 shifted 0 labels (by decide +kernel)

private abbrev core470 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term470.expression).2.2

theorem same483 : unweighted 470 = unweighted 483 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core470 L24Gluing.term470.decoration L24Gluing.term470.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same486 : unweighted 470 = unweighted 486 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core470 L24Gluing.term470.decoration L24Gluing.term470.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core471 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term471.expression).2.2

theorem same484 : unweighted 471 = unweighted 484 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core471 L24Gluing.term471.decoration L24Gluing.term471.labels
    L24Gluing.flagPermutation17 L24Gluing.flagPermutation16 shifted 0 labels (by decide +kernel)

theorem same487 : unweighted 471 = unweighted 487 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core471 L24Gluing.term471.decoration L24Gluing.term471.labels
    L24Gluing.flagPermutation17 L24Gluing.flagPermutation15 shifted 0 labels (by decide +kernel)

private abbrev core472 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term472.expression).2.2

theorem same485 : unweighted 472 = unweighted 485 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core472 L24Gluing.term472.decoration L24Gluing.term472.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same488 : unweighted 472 = unweighted 488 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core472 L24Gluing.term472.decoration L24Gluing.term472.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core489 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term489.expression).2.2

theorem same490 : unweighted 489 = unweighted 490 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core489 L24Gluing.term489.decoration L24Gluing.term489.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same491 : unweighted 489 = unweighted 491 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core489 L24Gluing.term489.decoration L24Gluing.term489.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core493 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term493.expression).2.2

theorem same494 : unweighted 493 = unweighted 494 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core493 L24Gluing.term493.decoration L24Gluing.term493.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same496 : unweighted 493 = unweighted 496 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core493 L24Gluing.term493.decoration L24Gluing.term493.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core495 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term495.expression).2.2

theorem same497 : unweighted 495 = unweighted 497 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core495 L24Gluing.term495.decoration L24Gluing.term495.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same498 : unweighted 495 = unweighted 498 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core495 L24Gluing.term495.decoration L24Gluing.term495.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core499 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term499.expression).2.2

theorem same503 : unweighted 499 = unweighted 503 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core499 L24Gluing.term499.decoration L24Gluing.term499.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same506 : unweighted 499 = unweighted 506 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core499 L24Gluing.term499.decoration L24Gluing.term499.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core500 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term500.expression).2.2

theorem same504 : unweighted 500 = unweighted 504 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core500 L24Gluing.term500.decoration L24Gluing.term500.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same507 : unweighted 500 = unweighted 507 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core500 L24Gluing.term500.decoration L24Gluing.term500.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core501 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term501.expression).2.2

theorem same505 : unweighted 501 = unweighted 505 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core501 L24Gluing.term501.decoration L24Gluing.term501.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same508 : unweighted 501 = unweighted 508 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core501 L24Gluing.term501.decoration L24Gluing.term501.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core515 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term515.expression).2.2

theorem same519 : unweighted 515 = unweighted 519 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core515 L24Gluing.term515.decoration L24Gluing.term515.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same529 : unweighted 515 = unweighted 529 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core515 L24Gluing.term515.decoration L24Gluing.term515.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core516 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term516.expression).2.2

theorem same520 : unweighted 516 = unweighted 520 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core516 L24Gluing.term516.decoration L24Gluing.term516.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same530 : unweighted 516 = unweighted 530 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core516 L24Gluing.term516.decoration L24Gluing.term516.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

end AxiomaticGW.BlowupTwoLineH.Frame

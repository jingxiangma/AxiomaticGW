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

private abbrev core409 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term409.expression).2.2

theorem same415 : unweighted 409 = unweighted 415 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core409 L24Gluing.term409.decoration L24Gluing.term409.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same416 : unweighted 409 = unweighted 416 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core409 L24Gluing.term409.decoration L24Gluing.term409.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core417 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term417.expression).2.2

theorem same427 : unweighted 417 = unweighted 427 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core417 L24Gluing.term417.decoration L24Gluing.term417.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same437 : unweighted 417 = unweighted 437 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core417 L24Gluing.term417.decoration L24Gluing.term417.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core418 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term418.expression).2.2

theorem same428 : unweighted 418 = unweighted 428 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core418 L24Gluing.term418.decoration L24Gluing.term418.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation11 shifted 0 labels (by decide +kernel)

theorem same438 : unweighted 418 = unweighted 438 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core418 L24Gluing.term418.decoration L24Gluing.term418.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation12 shifted 0 labels (by decide +kernel)

private abbrev core419 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term419.expression).2.2

theorem same429 : unweighted 419 = unweighted 429 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core419 L24Gluing.term419.decoration L24Gluing.term419.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 shifted 0 labels (by decide +kernel)

theorem same439 : unweighted 419 = unweighted 439 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core419 L24Gluing.term419.decoration L24Gluing.term419.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 shifted 0 labels (by decide +kernel)

private abbrev core420 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term420.expression).2.2

theorem same430 : unweighted 420 = unweighted 430 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core420 L24Gluing.term420.decoration L24Gluing.term420.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same440 : unweighted 420 = unweighted 440 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core420 L24Gluing.term420.decoration L24Gluing.term420.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core421 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term421.expression).2.2

theorem same431 : unweighted 421 = unweighted 431 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core421 L24Gluing.term421.decoration L24Gluing.term421.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same441 : unweighted 421 = unweighted 441 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core421 L24Gluing.term421.decoration L24Gluing.term421.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core422 : GluingExpression 2 (Fin 4) :=
  L24Gluing.term422.expression

theorem same432 : unweighted 422 = unweighted 432 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core422 L24Gluing.term422.decoration L24Gluing.term422.labels
    (Equiv.refl (Fin 4)) L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same442 : unweighted 422 = unweighted 442 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core422 L24Gluing.term422.decoration L24Gluing.term422.labels
    (Equiv.refl (Fin 4)) L24Gluing.flagPermutation4 shifted 0 labels (by decide +kernel)

private abbrev core423 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term423.expression).2.2

theorem same433 : unweighted 423 = unweighted 433 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core423 L24Gluing.term423.decoration L24Gluing.term423.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same443 : unweighted 423 = unweighted 443 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core423 L24Gluing.term423.decoration L24Gluing.term423.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core424 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term424.expression).2.2

theorem same434 : unweighted 424 = unweighted 434 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core424 L24Gluing.term424.decoration L24Gluing.term424.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 shifted 0 labels (by decide +kernel)

theorem same444 : unweighted 424 = unweighted 444 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core424 L24Gluing.term424.decoration L24Gluing.term424.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 shifted 0 labels (by decide +kernel)

private abbrev core425 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term425.expression).2.2

theorem same435 : unweighted 425 = unweighted 435 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core425 L24Gluing.term425.decoration L24Gluing.term425.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same445 : unweighted 425 = unweighted 445 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core425 L24Gluing.term425.decoration L24Gluing.term425.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core426 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term426.expression).2.2

theorem same436 : unweighted 426 = unweighted 436 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core426 L24Gluing.term426.decoration L24Gluing.term426.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation11 shifted 0 labels (by decide +kernel)

theorem same446 : unweighted 426 = unweighted 446 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core426 L24Gluing.term426.decoration L24Gluing.term426.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation12 shifted 0 labels (by decide +kernel)

private abbrev core450 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term450.expression).2.2

theorem same460 : unweighted 450 = unweighted 460 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core450 L24Gluing.term450.decoration L24Gluing.term450.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same473 : unweighted 450 = unweighted 473 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core450 L24Gluing.term450.decoration L24Gluing.term450.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core451 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term451.expression).2.2

theorem same453 : unweighted 451 = unweighted 453 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core451 L24Gluing.term451.decoration L24Gluing.term451.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation21 shifted 0 labels (by decide +kernel)

theorem same461 : unweighted 451 = unweighted 461 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core451 L24Gluing.term451.decoration L24Gluing.term451.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation14 shifted 0 labels (by decide +kernel)

theorem same463 : unweighted 451 = unweighted 463 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core451 L24Gluing.term451.decoration L24Gluing.term451.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation17 shifted 0 labels (by decide +kernel)

theorem same474 : unweighted 451 = unweighted 474 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core451 L24Gluing.term451.decoration L24Gluing.term451.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation15 shifted 0 labels (by decide +kernel)

theorem same476 : unweighted 451 = unweighted 476 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core451 L24Gluing.term451.decoration L24Gluing.term451.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation16 shifted 0 labels (by decide +kernel)

private abbrev core452 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term452.expression).2.2

theorem same454 : unweighted 452 = unweighted 454 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core452 L24Gluing.term452.decoration L24Gluing.term452.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation4 shifted 0 labels (by decide +kernel)

theorem same462 : unweighted 452 = unweighted 462 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core452 L24Gluing.term452.decoration L24Gluing.term452.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 shifted 0 labels (by decide +kernel)

theorem same464 : unweighted 452 = unweighted 464 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core452 L24Gluing.term452.decoration L24Gluing.term452.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same475 : unweighted 452 = unweighted 475 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core452 L24Gluing.term452.decoration L24Gluing.term452.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same477 : unweighted 452 = unweighted 477 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core452 L24Gluing.term452.decoration L24Gluing.term452.labels
    L24Gluing.flagPermutation10 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core455 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term455.expression).2.2

theorem same465 : unweighted 455 = unweighted 465 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core455 L24Gluing.term455.decoration L24Gluing.term455.labels
    L24Gluing.flagPermutation2 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same478 : unweighted 455 = unweighted 478 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core455 L24Gluing.term455.decoration L24Gluing.term455.labels
    L24Gluing.flagPermutation2 L24Gluing.flagPermutation0 shifted 0 labels (by decide +kernel)

private abbrev core456 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term456.expression).2.2

theorem same466 : unweighted 456 = unweighted 466 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core456 L24Gluing.term456.decoration L24Gluing.term456.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same479 : unweighted 456 = unweighted 479 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core456 L24Gluing.term456.decoration L24Gluing.term456.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core457 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term457.expression).2.2

theorem same458 : unweighted 457 = unweighted 458 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core457 L24Gluing.term457.decoration L24Gluing.term457.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation4 shifted 0 labels (by decide +kernel)

theorem same467 : unweighted 457 = unweighted 467 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core457 L24Gluing.term457.decoration L24Gluing.term457.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 shifted 0 labels (by decide +kernel)

theorem same468 : unweighted 457 = unweighted 468 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core457 L24Gluing.term457.decoration L24Gluing.term457.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same480 : unweighted 457 = unweighted 480 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core457 L24Gluing.term457.decoration L24Gluing.term457.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same481 : unweighted 457 = unweighted 481 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core457 L24Gluing.term457.decoration L24Gluing.term457.labels
    L24Gluing.flagPermutation10 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

end AxiomaticGW.BlowupTwoLineH.Frame

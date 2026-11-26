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

private abbrev core642 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term642.expression).2.2

theorem same650 : unweighted 642 = unweighted 650 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core642 L24Gluing.term642.decoration L24Gluing.term642.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same654 : unweighted 642 = unweighted 654 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core642 L24Gluing.term642.decoration L24Gluing.term642.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core643 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term643.expression).2.2

theorem same651 : unweighted 643 = unweighted 651 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core643 L24Gluing.term643.decoration L24Gluing.term643.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same655 : unweighted 643 = unweighted 655 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core643 L24Gluing.term643.decoration L24Gluing.term643.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core644 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term644.expression).2.2

theorem same652 : unweighted 644 = unweighted 652 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core644 L24Gluing.term644.decoration L24Gluing.term644.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same656 : unweighted 644 = unweighted 656 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core644 L24Gluing.term644.decoration L24Gluing.term644.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core645 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term645.expression).2.2

theorem same653 : unweighted 645 = unweighted 653 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core645 L24Gluing.term645.decoration L24Gluing.term645.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same657 : unweighted 645 = unweighted 657 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core645 L24Gluing.term645.decoration L24Gluing.term645.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core662 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term662.expression).2.2

theorem same681 : unweighted 662 = unweighted 681 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core662 L24Gluing.term662.decoration L24Gluing.term662.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 shifted 0 labels (by decide +kernel)

theorem same700 : unweighted 662 = unweighted 700 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core662 L24Gluing.term662.decoration L24Gluing.term662.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 shifted 0 labels (by decide +kernel)

private abbrev core663 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term663.expression).2.2

theorem same682 : unweighted 663 = unweighted 682 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core663 L24Gluing.term663.decoration L24Gluing.term663.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same701 : unweighted 663 = unweighted 701 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core663 L24Gluing.term663.decoration L24Gluing.term663.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core664 : GluingExpression 2 (Fin 4) :=
  L24Gluing.term664.expression

theorem same683 : unweighted 664 = unweighted 683 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core664 L24Gluing.term664.decoration L24Gluing.term664.labels
    (Equiv.refl (Fin 4)) L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same702 : unweighted 664 = unweighted 702 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core664 L24Gluing.term664.decoration L24Gluing.term664.labels
    (Equiv.refl (Fin 4)) L24Gluing.flagPermutation4 shifted 0 labels (by decide +kernel)

private abbrev core665 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term665.expression).2.2

theorem same684 : unweighted 665 = unweighted 684 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core665 L24Gluing.term665.decoration L24Gluing.term665.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same703 : unweighted 665 = unweighted 703 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core665 L24Gluing.term665.decoration L24Gluing.term665.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core666 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term666.expression).2.2

theorem same685 : unweighted 666 = unweighted 685 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core666 L24Gluing.term666.decoration L24Gluing.term666.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same704 : unweighted 666 = unweighted 704 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core666 L24Gluing.term666.decoration L24Gluing.term666.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core667 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term667.expression).2.2

theorem same686 : unweighted 667 = unweighted 686 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core667 L24Gluing.term667.decoration L24Gluing.term667.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 shifted 0 labels (by decide +kernel)

theorem same705 : unweighted 667 = unweighted 705 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core667 L24Gluing.term667.decoration L24Gluing.term667.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 shifted 0 labels (by decide +kernel)

private abbrev core668 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term668.expression).2.2

theorem same687 : unweighted 668 = unweighted 687 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core668 L24Gluing.term668.decoration L24Gluing.term668.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 shifted 0 labels (by decide +kernel)

theorem same706 : unweighted 668 = unweighted 706 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core668 L24Gluing.term668.decoration L24Gluing.term668.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 shifted 0 labels (by decide +kernel)

private abbrev core669 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term669.expression).2.2

theorem same688 : unweighted 669 = unweighted 688 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core669 L24Gluing.term669.decoration L24Gluing.term669.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same707 : unweighted 669 = unweighted 707 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core669 L24Gluing.term669.decoration L24Gluing.term669.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core670 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term670.expression).2.2

theorem same689 : unweighted 670 = unweighted 689 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core670 L24Gluing.term670.decoration L24Gluing.term670.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same708 : unweighted 670 = unweighted 708 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core670 L24Gluing.term670.decoration L24Gluing.term670.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core671 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term671.expression).2.2

theorem same690 : unweighted 671 = unweighted 690 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core671 L24Gluing.term671.decoration L24Gluing.term671.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same709 : unweighted 671 = unweighted 709 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core671 L24Gluing.term671.decoration L24Gluing.term671.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core672 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term672.expression).2.2

theorem same691 : unweighted 672 = unweighted 691 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core672 L24Gluing.term672.decoration L24Gluing.term672.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same710 : unweighted 672 = unweighted 710 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core672 L24Gluing.term672.decoration L24Gluing.term672.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core673 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term673.expression).2.2

theorem same692 : unweighted 673 = unweighted 692 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core673 L24Gluing.term673.decoration L24Gluing.term673.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same711 : unweighted 673 = unweighted 711 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core673 L24Gluing.term673.decoration L24Gluing.term673.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

end AxiomaticGW.BlowupTwoLineH.Frame

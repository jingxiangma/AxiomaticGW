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

private abbrev core674 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term674.expression).2.2

theorem same693 : unweighted 674 = unweighted 693 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core674 L24Gluing.term674.decoration L24Gluing.term674.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same712 : unweighted 674 = unweighted 712 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core674 L24Gluing.term674.decoration L24Gluing.term674.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core675 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term675.expression).2.2

theorem same694 : unweighted 675 = unweighted 694 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core675 L24Gluing.term675.decoration L24Gluing.term675.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation11 shifted 0 labels (by decide +kernel)

theorem same713 : unweighted 675 = unweighted 713 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core675 L24Gluing.term675.decoration L24Gluing.term675.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation12 shifted 0 labels (by decide +kernel)

private abbrev core676 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term676.expression).2.2

theorem same695 : unweighted 676 = unweighted 695 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core676 L24Gluing.term676.decoration L24Gluing.term676.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 shifted 0 labels (by decide +kernel)

theorem same714 : unweighted 676 = unweighted 714 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core676 L24Gluing.term676.decoration L24Gluing.term676.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 shifted 0 labels (by decide +kernel)

private abbrev core677 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term677.expression).2.2

theorem same696 : unweighted 677 = unweighted 696 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core677 L24Gluing.term677.decoration L24Gluing.term677.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same715 : unweighted 677 = unweighted 715 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core677 L24Gluing.term677.decoration L24Gluing.term677.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core678 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term678.expression).2.2

theorem same697 : unweighted 678 = unweighted 697 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core678 L24Gluing.term678.decoration L24Gluing.term678.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same716 : unweighted 678 = unweighted 716 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core678 L24Gluing.term678.decoration L24Gluing.term678.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core679 : GluingExpression 2 (Fin 4) :=
  L24Gluing.term679.expression

theorem same698 : unweighted 679 = unweighted 698 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core679 L24Gluing.term679.decoration L24Gluing.term679.labels
    (Equiv.refl (Fin 4)) L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same717 : unweighted 679 = unweighted 717 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core679 L24Gluing.term679.decoration L24Gluing.term679.labels
    (Equiv.refl (Fin 4)) L24Gluing.flagPermutation4 shifted 0 labels (by decide +kernel)

private abbrev core680 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term680.expression).2.2

theorem same699 : unweighted 680 = unweighted 699 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core680 L24Gluing.term680.decoration L24Gluing.term680.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same718 : unweighted 680 = unweighted 718 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core680 L24Gluing.term680.decoration L24Gluing.term680.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core727 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term727.expression).2.2

theorem same728 : unweighted 727 = unweighted 728 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core727 L24Gluing.term727.decoration L24Gluing.term727.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation4 shifted 0 labels (by decide +kernel)

theorem same745 : unweighted 727 = unweighted 745 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core727 L24Gluing.term727.decoration L24Gluing.term727.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 shifted 0 labels (by decide +kernel)

theorem same746 : unweighted 727 = unweighted 746 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core727 L24Gluing.term727.decoration L24Gluing.term727.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same771 : unweighted 727 = unweighted 771 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core727 L24Gluing.term727.decoration L24Gluing.term727.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same772 : unweighted 727 = unweighted 772 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core727 L24Gluing.term727.decoration L24Gluing.term727.labels
    L24Gluing.flagPermutation10 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core729 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term729.expression).2.2

theorem same747 : unweighted 729 = unweighted 747 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core729 L24Gluing.term729.decoration L24Gluing.term729.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same773 : unweighted 729 = unweighted 773 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core729 L24Gluing.term729.decoration L24Gluing.term729.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core730 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term730.expression).2.2

theorem same748 : unweighted 730 = unweighted 748 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core730 L24Gluing.term730.decoration L24Gluing.term730.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same774 : unweighted 730 = unweighted 774 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core730 L24Gluing.term730.decoration L24Gluing.term730.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core731 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term731.expression).2.2

theorem same733 : unweighted 731 = unweighted 733 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core731 L24Gluing.term731.decoration L24Gluing.term731.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation4 shifted 0 labels (by decide +kernel)

theorem same749 : unweighted 731 = unweighted 749 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core731 L24Gluing.term731.decoration L24Gluing.term731.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 shifted 0 labels (by decide +kernel)

theorem same751 : unweighted 731 = unweighted 751 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core731 L24Gluing.term731.decoration L24Gluing.term731.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same775 : unweighted 731 = unweighted 775 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core731 L24Gluing.term731.decoration L24Gluing.term731.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same777 : unweighted 731 = unweighted 777 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core731 L24Gluing.term731.decoration L24Gluing.term731.labels
    L24Gluing.flagPermutation10 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core732 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term732.expression).2.2

theorem same734 : unweighted 732 = unweighted 734 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core732 L24Gluing.term732.decoration L24Gluing.term732.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation4 shifted 0 labels (by decide +kernel)

theorem same750 : unweighted 732 = unweighted 750 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core732 L24Gluing.term732.decoration L24Gluing.term732.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 shifted 0 labels (by decide +kernel)

theorem same752 : unweighted 732 = unweighted 752 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core732 L24Gluing.term732.decoration L24Gluing.term732.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same776 : unweighted 732 = unweighted 776 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core732 L24Gluing.term732.decoration L24Gluing.term732.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same778 : unweighted 732 = unweighted 778 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core732 L24Gluing.term732.decoration L24Gluing.term732.labels
    L24Gluing.flagPermutation10 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

end AxiomaticGW.BlowupTwoLineH.Frame

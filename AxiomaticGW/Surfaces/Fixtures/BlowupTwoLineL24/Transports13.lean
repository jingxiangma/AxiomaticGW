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

private abbrev core735 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term735.expression).2.2

theorem same753 : unweighted 735 = unweighted 753 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core735 L24Gluing.term735.decoration L24Gluing.term735.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same779 : unweighted 735 = unweighted 779 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core735 L24Gluing.term735.decoration L24Gluing.term735.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core736 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term736.expression).2.2

theorem same754 : unweighted 736 = unweighted 754 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core736 L24Gluing.term736.decoration L24Gluing.term736.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same780 : unweighted 736 = unweighted 780 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core736 L24Gluing.term736.decoration L24Gluing.term736.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core737 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term737.expression).2.2

theorem same755 : unweighted 737 = unweighted 755 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core737 L24Gluing.term737.decoration L24Gluing.term737.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same781 : unweighted 737 = unweighted 781 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core737 L24Gluing.term737.decoration L24Gluing.term737.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core738 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term738.expression).2.2

theorem same756 : unweighted 738 = unweighted 756 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core738 L24Gluing.term738.decoration L24Gluing.term738.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same782 : unweighted 738 = unweighted 782 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core738 L24Gluing.term738.decoration L24Gluing.term738.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core739 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term739.expression).2.2

theorem same741 : unweighted 739 = unweighted 741 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core739 L24Gluing.term739.decoration L24Gluing.term739.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation21 shifted 0 labels (by decide +kernel)

theorem same757 : unweighted 739 = unweighted 757 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core739 L24Gluing.term739.decoration L24Gluing.term739.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation14 shifted 0 labels (by decide +kernel)

theorem same759 : unweighted 739 = unweighted 759 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core739 L24Gluing.term739.decoration L24Gluing.term739.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation17 shifted 0 labels (by decide +kernel)

theorem same783 : unweighted 739 = unweighted 783 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core739 L24Gluing.term739.decoration L24Gluing.term739.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation15 shifted 0 labels (by decide +kernel)

theorem same785 : unweighted 739 = unweighted 785 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core739 L24Gluing.term739.decoration L24Gluing.term739.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation16 shifted 0 labels (by decide +kernel)

private abbrev core740 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term740.expression).2.2

theorem same742 : unweighted 740 = unweighted 742 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core740 L24Gluing.term740.decoration L24Gluing.term740.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation4 shifted 0 labels (by decide +kernel)

theorem same758 : unweighted 740 = unweighted 758 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core740 L24Gluing.term740.decoration L24Gluing.term740.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 shifted 0 labels (by decide +kernel)

theorem same760 : unweighted 740 = unweighted 760 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core740 L24Gluing.term740.decoration L24Gluing.term740.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same784 : unweighted 740 = unweighted 784 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core740 L24Gluing.term740.decoration L24Gluing.term740.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same786 : unweighted 740 = unweighted 786 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core740 L24Gluing.term740.decoration L24Gluing.term740.labels
    L24Gluing.flagPermutation10 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core743 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term743.expression).2.2

theorem same761 : unweighted 743 = unweighted 761 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core743 L24Gluing.term743.decoration L24Gluing.term743.labels
    L24Gluing.flagPermutation2 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same787 : unweighted 743 = unweighted 787 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core743 L24Gluing.term743.decoration L24Gluing.term743.labels
    L24Gluing.flagPermutation2 L24Gluing.flagPermutation0 shifted 0 labels (by decide +kernel)

private abbrev core744 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term744.expression).2.2

theorem same762 : unweighted 744 = unweighted 762 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core744 L24Gluing.term744.decoration L24Gluing.term744.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same788 : unweighted 744 = unweighted 788 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core744 L24Gluing.term744.decoration L24Gluing.term744.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core763 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term763.expression).2.2

theorem same789 : unweighted 763 = unweighted 789 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core763 L24Gluing.term763.decoration L24Gluing.term763.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same797 : unweighted 763 = unweighted 797 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core763 L24Gluing.term763.decoration L24Gluing.term763.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core764 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term764.expression).2.2

theorem same790 : unweighted 764 = unweighted 790 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core764 L24Gluing.term764.decoration L24Gluing.term764.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same798 : unweighted 764 = unweighted 798 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core764 L24Gluing.term764.decoration L24Gluing.term764.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core765 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term765.expression).2.2

theorem same791 : unweighted 765 = unweighted 791 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core765 L24Gluing.term765.decoration L24Gluing.term765.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same799 : unweighted 765 = unweighted 799 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core765 L24Gluing.term765.decoration L24Gluing.term765.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core766 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term766.expression).2.2

theorem same792 : unweighted 766 = unweighted 792 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core766 L24Gluing.term766.decoration L24Gluing.term766.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same800 : unweighted 766 = unweighted 800 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core766 L24Gluing.term766.decoration L24Gluing.term766.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core767 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term767.expression).2.2

theorem same793 : unweighted 767 = unweighted 793 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core767 L24Gluing.term767.decoration L24Gluing.term767.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same801 : unweighted 767 = unweighted 801 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core767 L24Gluing.term767.decoration L24Gluing.term767.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core768 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term768.expression).2.2

theorem same794 : unweighted 768 = unweighted 794 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core768 L24Gluing.term768.decoration L24Gluing.term768.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same802 : unweighted 768 = unweighted 802 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core768 L24Gluing.term768.decoration L24Gluing.term768.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core769 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term769.expression).2.2

theorem same795 : unweighted 769 = unweighted 795 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core769 L24Gluing.term769.decoration L24Gluing.term769.labels
    L24Gluing.flagPermutation17 L24Gluing.flagPermutation16 shifted 0 labels (by decide +kernel)

theorem same803 : unweighted 769 = unweighted 803 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core769 L24Gluing.term769.decoration L24Gluing.term769.labels
    L24Gluing.flagPermutation17 L24Gluing.flagPermutation15 shifted 0 labels (by decide +kernel)

private abbrev core770 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term770.expression).2.2

theorem same796 : unweighted 770 = unweighted 796 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core770 L24Gluing.term770.decoration L24Gluing.term770.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same804 : unweighted 770 = unweighted 804 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core770 L24Gluing.term770.decoration L24Gluing.term770.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core805 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term805.expression).2.2

theorem same806 : unweighted 805 = unweighted 806 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core805 L24Gluing.term805.decoration L24Gluing.term805.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same807 : unweighted 805 = unweighted 807 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core805 L24Gluing.term805.decoration L24Gluing.term805.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core809 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term809.expression).2.2

theorem same810 : unweighted 809 = unweighted 810 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core809 L24Gluing.term809.decoration L24Gluing.term809.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same812 : unweighted 809 = unweighted 812 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core809 L24Gluing.term809.decoration L24Gluing.term809.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core811 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term811.expression).2.2

theorem same813 : unweighted 811 = unweighted 813 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core811 L24Gluing.term811.decoration L24Gluing.term811.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same814 : unweighted 811 = unweighted 814 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core811 L24Gluing.term811.decoration L24Gluing.term811.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

end AxiomaticGW.BlowupTwoLineH.Frame

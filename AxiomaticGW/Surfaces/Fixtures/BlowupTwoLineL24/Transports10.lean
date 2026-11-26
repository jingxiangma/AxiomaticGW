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

private abbrev core602 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term602.expression).2.2

theorem same606 : unweighted 602 = unweighted 606 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core602 L24Gluing.term602.decoration L24Gluing.term602.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation16 shifted 0 labels (by decide +kernel)

theorem same614 : unweighted 602 = unweighted 614 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core602 L24Gluing.term602.decoration L24Gluing.term602.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation17 shifted 0 labels (by decide +kernel)

private abbrev core603 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term603.expression).2.2

theorem same607 : unweighted 603 = unweighted 607 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core603 L24Gluing.term603.decoration L24Gluing.term603.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation16 shifted 0 labels (by decide +kernel)

theorem same615 : unweighted 603 = unweighted 615 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core603 L24Gluing.term603.decoration L24Gluing.term603.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation17 shifted 0 labels (by decide +kernel)

private abbrev core604 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term604.expression).2.2

theorem same608 : unweighted 604 = unweighted 608 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core604 L24Gluing.term604.decoration L24Gluing.term604.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation16 shifted 0 labels (by decide +kernel)

theorem same616 : unweighted 604 = unweighted 616 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core604 L24Gluing.term604.decoration L24Gluing.term604.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation17 shifted 0 labels (by decide +kernel)

private abbrev core605 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term605.expression).2.2

theorem same609 : unweighted 605 = unweighted 609 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core605 L24Gluing.term605.decoration L24Gluing.term605.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation16 shifted 0 labels (by decide +kernel)

theorem same617 : unweighted 605 = unweighted 617 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core605 L24Gluing.term605.decoration L24Gluing.term605.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation17 shifted 0 labels (by decide +kernel)

private abbrev core610 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term610.expression).2.2

theorem same618 : unweighted 610 = unweighted 618 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core610 L24Gluing.term610.decoration L24Gluing.term610.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same622 : unweighted 610 = unweighted 622 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core610 L24Gluing.term610.decoration L24Gluing.term610.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core611 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term611.expression).2.2

theorem same619 : unweighted 611 = unweighted 619 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core611 L24Gluing.term611.decoration L24Gluing.term611.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same623 : unweighted 611 = unweighted 623 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core611 L24Gluing.term611.decoration L24Gluing.term611.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core612 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term612.expression).2.2

theorem same620 : unweighted 612 = unweighted 620 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core612 L24Gluing.term612.decoration L24Gluing.term612.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same624 : unweighted 612 = unweighted 624 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core612 L24Gluing.term612.decoration L24Gluing.term612.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core613 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term613.expression).2.2

theorem same621 : unweighted 613 = unweighted 621 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core613 L24Gluing.term613.decoration L24Gluing.term613.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same625 : unweighted 613 = unweighted 625 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core613 L24Gluing.term613.decoration L24Gluing.term613.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core634 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term634.expression).2.2

theorem same638 : unweighted 634 = unweighted 638 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core634 L24Gluing.term634.decoration L24Gluing.term634.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same646 : unweighted 634 = unweighted 646 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core634 L24Gluing.term634.decoration L24Gluing.term634.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core635 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term635.expression).2.2

theorem same639 : unweighted 635 = unweighted 639 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core635 L24Gluing.term635.decoration L24Gluing.term635.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same647 : unweighted 635 = unweighted 647 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core635 L24Gluing.term635.decoration L24Gluing.term635.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core636 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term636.expression).2.2

theorem same640 : unweighted 636 = unweighted 640 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core636 L24Gluing.term636.decoration L24Gluing.term636.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same648 : unweighted 636 = unweighted 648 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core636 L24Gluing.term636.decoration L24Gluing.term636.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core637 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term637.expression).2.2

theorem same641 : unweighted 637 = unweighted 641 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core637 L24Gluing.term637.decoration L24Gluing.term637.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same649 : unweighted 637 = unweighted 649 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core637 L24Gluing.term637.decoration L24Gluing.term637.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

end AxiomaticGW.BlowupTwoLineH.Frame

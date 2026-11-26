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

private abbrev core570 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term570.expression).2.2

theorem same574 : unweighted 570 = unweighted 574 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core570 L24Gluing.term570.decoration L24Gluing.term570.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same582 : unweighted 570 = unweighted 582 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core570 L24Gluing.term570.decoration L24Gluing.term570.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core571 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term571.expression).2.2

theorem same575 : unweighted 571 = unweighted 575 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core571 L24Gluing.term571.decoration L24Gluing.term571.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same583 : unweighted 571 = unweighted 583 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core571 L24Gluing.term571.decoration L24Gluing.term571.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core572 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term572.expression).2.2

theorem same576 : unweighted 572 = unweighted 576 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core572 L24Gluing.term572.decoration L24Gluing.term572.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same584 : unweighted 572 = unweighted 584 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core572 L24Gluing.term572.decoration L24Gluing.term572.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core573 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term573.expression).2.2

theorem same577 : unweighted 573 = unweighted 577 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core573 L24Gluing.term573.decoration L24Gluing.term573.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same585 : unweighted 573 = unweighted 585 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core573 L24Gluing.term573.decoration L24Gluing.term573.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core578 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term578.expression).2.2

theorem same586 : unweighted 578 = unweighted 586 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core578 L24Gluing.term578.decoration L24Gluing.term578.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same590 : unweighted 578 = unweighted 590 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core578 L24Gluing.term578.decoration L24Gluing.term578.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core579 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term579.expression).2.2

theorem same587 : unweighted 579 = unweighted 587 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core579 L24Gluing.term579.decoration L24Gluing.term579.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same591 : unweighted 579 = unweighted 591 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core579 L24Gluing.term579.decoration L24Gluing.term579.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core580 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term580.expression).2.2

theorem same588 : unweighted 580 = unweighted 588 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core580 L24Gluing.term580.decoration L24Gluing.term580.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same592 : unweighted 580 = unweighted 592 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core580 L24Gluing.term580.decoration L24Gluing.term580.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core581 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term581.expression).2.2

theorem same589 : unweighted 581 = unweighted 589 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core581 L24Gluing.term581.decoration L24Gluing.term581.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same593 : unweighted 581 = unweighted 593 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core581 L24Gluing.term581.decoration L24Gluing.term581.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

end AxiomaticGW.BlowupTwoLineH.Frame

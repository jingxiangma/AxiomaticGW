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

private abbrev core182 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term182.expression).2.2

theorem same201 : unweighted 182 = unweighted 201 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core182 L24Gluing.term182.decoration L24Gluing.term182.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same233 : unweighted 182 = unweighted 233 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core182 L24Gluing.term182.decoration L24Gluing.term182.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core183 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term183.expression).2.2

theorem same202 : unweighted 183 = unweighted 202 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core183 L24Gluing.term183.decoration L24Gluing.term183.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same234 : unweighted 183 = unweighted 234 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core183 L24Gluing.term183.decoration L24Gluing.term183.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core184 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term184.expression).2.2

theorem same203 : unweighted 184 = unweighted 203 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core184 L24Gluing.term184.decoration L24Gluing.term184.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

private abbrev core185 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term185.expression).2.2

theorem same204 : unweighted 185 = unweighted 204 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core185 L24Gluing.term185.decoration L24Gluing.term185.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same235 : unweighted 185 = unweighted 235 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core185 L24Gluing.term185.decoration L24Gluing.term185.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core186 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term186.expression).2.2

theorem same205 : unweighted 186 = unweighted 205 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core186 L24Gluing.term186.decoration L24Gluing.term186.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

private abbrev core187 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term187.expression).2.2

theorem same206 : unweighted 187 = unweighted 206 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core187 L24Gluing.term187.decoration L24Gluing.term187.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same236 : unweighted 187 = unweighted 236 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core187 L24Gluing.term187.decoration L24Gluing.term187.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core188 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term188.expression).2.2

theorem same207 : unweighted 188 = unweighted 207 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core188 L24Gluing.term188.decoration L24Gluing.term188.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same237 : unweighted 188 = unweighted 237 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core188 L24Gluing.term188.decoration L24Gluing.term188.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core189 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term189.expression).2.2

theorem same208 : unweighted 189 = unweighted 208 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core189 L24Gluing.term189.decoration L24Gluing.term189.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same238 : unweighted 189 = unweighted 238 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core189 L24Gluing.term189.decoration L24Gluing.term189.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core190 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term190.expression).2.2

theorem same209 : unweighted 190 = unweighted 209 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core190 L24Gluing.term190.decoration L24Gluing.term190.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same239 : unweighted 190 = unweighted 239 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core190 L24Gluing.term190.decoration L24Gluing.term190.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

end AxiomaticGW.BlowupTwoLineH.Frame

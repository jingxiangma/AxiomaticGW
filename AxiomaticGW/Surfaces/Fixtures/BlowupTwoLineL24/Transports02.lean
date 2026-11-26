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

private abbrev core191 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term191.expression).2.2

theorem same210 : unweighted 191 = unweighted 210 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core191 L24Gluing.term191.decoration L24Gluing.term191.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation14 shifted 0 labels (by decide +kernel)

theorem same240 : unweighted 191 = unweighted 240 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core191 L24Gluing.term191.decoration L24Gluing.term191.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation15 shifted 0 labels (by decide +kernel)

private abbrev core192 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term192.expression).2.2

theorem same211 : unweighted 192 = unweighted 211 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core192 L24Gluing.term192.decoration L24Gluing.term192.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation14 shifted 0 labels (by decide +kernel)

theorem same241 : unweighted 192 = unweighted 241 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core192 L24Gluing.term192.decoration L24Gluing.term192.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation15 shifted 0 labels (by decide +kernel)

private abbrev core193 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term193.expression).2.2

theorem same212 : unweighted 193 = unweighted 212 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core193 L24Gluing.term193.decoration L24Gluing.term193.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation14 shifted 0 labels (by decide +kernel)

theorem same242 : unweighted 193 = unweighted 242 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core193 L24Gluing.term193.decoration L24Gluing.term193.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation15 shifted 0 labels (by decide +kernel)

private abbrev core194 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term194.expression).2.2

theorem same213 : unweighted 194 = unweighted 213 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core194 L24Gluing.term194.decoration L24Gluing.term194.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation14 shifted 0 labels (by decide +kernel)

private abbrev core195 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term195.expression).2.2

theorem same214 : unweighted 195 = unweighted 214 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core195 L24Gluing.term195.decoration L24Gluing.term195.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation14 shifted 0 labels (by decide +kernel)

theorem same243 : unweighted 195 = unweighted 243 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core195 L24Gluing.term195.decoration L24Gluing.term195.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation15 shifted 0 labels (by decide +kernel)

private abbrev core196 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term196.expression).2.2

theorem same215 : unweighted 196 = unweighted 215 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core196 L24Gluing.term196.decoration L24Gluing.term196.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 shifted 0 labels (by decide +kernel)

theorem same244 : unweighted 196 = unweighted 244 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core196 L24Gluing.term196.decoration L24Gluing.term196.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

private abbrev core197 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term197.expression).2.2

theorem same216 : unweighted 197 = unweighted 216 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core197 L24Gluing.term197.decoration L24Gluing.term197.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 shifted 0 labels (by decide +kernel)

private abbrev core198 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term198.expression).2.2

theorem same217 : unweighted 198 = unweighted 217 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core198 L24Gluing.term198.decoration L24Gluing.term198.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 shifted 0 labels (by decide +kernel)

theorem same245 : unweighted 198 = unweighted 245 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core198 L24Gluing.term198.decoration L24Gluing.term198.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

private abbrev core199 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term199.expression).2.2

theorem same218 : unweighted 199 = unweighted 218 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core199 L24Gluing.term199.decoration L24Gluing.term199.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 shifted 0 labels (by decide +kernel)

theorem same246 : unweighted 199 = unweighted 246 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core199 L24Gluing.term199.decoration L24Gluing.term199.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

private abbrev core200 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term200.expression).2.2

theorem same219 : unweighted 200 = unweighted 219 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core200 L24Gluing.term200.decoration L24Gluing.term200.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 shifted 0 labels (by decide +kernel)

theorem same247 : unweighted 200 = unweighted 247 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core200 L24Gluing.term200.decoration L24Gluing.term200.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

private abbrev core220 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term220.expression).2.2

theorem same248 : unweighted 220 = unweighted 248 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core220 L24Gluing.term220.decoration L24Gluing.term220.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same260 : unweighted 220 = unweighted 260 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core220 L24Gluing.term220.decoration L24Gluing.term220.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core221 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term221.expression).2.2

theorem same249 : unweighted 221 = unweighted 249 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core221 L24Gluing.term221.decoration L24Gluing.term221.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same261 : unweighted 221 = unweighted 261 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core221 L24Gluing.term221.decoration L24Gluing.term221.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core222 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term222.expression).2.2

theorem same250 : unweighted 222 = unweighted 250 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core222 L24Gluing.term222.decoration L24Gluing.term222.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same262 : unweighted 222 = unweighted 262 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core222 L24Gluing.term222.decoration L24Gluing.term222.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core223 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term223.expression).2.2

theorem same251 : unweighted 223 = unweighted 251 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core223 L24Gluing.term223.decoration L24Gluing.term223.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same263 : unweighted 223 = unweighted 263 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core223 L24Gluing.term223.decoration L24Gluing.term223.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core224 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term224.expression).2.2

theorem same252 : unweighted 224 = unweighted 252 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core224 L24Gluing.term224.decoration L24Gluing.term224.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same264 : unweighted 224 = unweighted 264 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core224 L24Gluing.term224.decoration L24Gluing.term224.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core225 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term225.expression).2.2

theorem same253 : unweighted 225 = unweighted 253 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core225 L24Gluing.term225.decoration L24Gluing.term225.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same265 : unweighted 225 = unweighted 265 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core225 L24Gluing.term225.decoration L24Gluing.term225.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core226 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term226.expression).2.2

theorem same254 : unweighted 226 = unweighted 254 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core226 L24Gluing.term226.decoration L24Gluing.term226.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same266 : unweighted 226 = unweighted 266 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core226 L24Gluing.term226.decoration L24Gluing.term226.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core228 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term228.expression).2.2

theorem same255 : unweighted 228 = unweighted 255 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core228 L24Gluing.term228.decoration L24Gluing.term228.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same267 : unweighted 228 = unweighted 267 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core228 L24Gluing.term228.decoration L24Gluing.term228.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core229 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term229.expression).2.2

theorem same256 : unweighted 229 = unweighted 256 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core229 L24Gluing.term229.decoration L24Gluing.term229.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same268 : unweighted 229 = unweighted 268 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core229 L24Gluing.term229.decoration L24Gluing.term229.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

end AxiomaticGW.BlowupTwoLineH.Frame

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

private abbrev core297 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term297.expression).2.2

theorem same301 : unweighted 297 = unweighted 301 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core297 L24Gluing.term297.decoration L24Gluing.term297.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

private abbrev core298 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term298.expression).2.2

theorem same302 : unweighted 298 = unweighted 302 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core298 L24Gluing.term298.decoration L24Gluing.term298.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same309 : unweighted 298 = unweighted 309 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core298 L24Gluing.term298.decoration L24Gluing.term298.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core299 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term299.expression).2.2

theorem same303 : unweighted 299 = unweighted 303 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core299 L24Gluing.term299.decoration L24Gluing.term299.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same310 : unweighted 299 = unweighted 310 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core299 L24Gluing.term299.decoration L24Gluing.term299.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core304 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term304.expression).2.2

theorem same311 : unweighted 304 = unweighted 311 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core304 L24Gluing.term304.decoration L24Gluing.term304.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same315 : unweighted 304 = unweighted 315 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core304 L24Gluing.term304.decoration L24Gluing.term304.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core305 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term305.expression).2.2

theorem same312 : unweighted 305 = unweighted 312 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core305 L24Gluing.term305.decoration L24Gluing.term305.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same316 : unweighted 305 = unweighted 316 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core305 L24Gluing.term305.decoration L24Gluing.term305.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core306 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term306.expression).2.2

theorem same313 : unweighted 306 = unweighted 313 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core306 L24Gluing.term306.decoration L24Gluing.term306.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same317 : unweighted 306 = unweighted 317 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core306 L24Gluing.term306.decoration L24Gluing.term306.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core307 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term307.expression).2.2

theorem same314 : unweighted 307 = unweighted 314 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core307 L24Gluing.term307.decoration L24Gluing.term307.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same318 : unweighted 307 = unweighted 318 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core307 L24Gluing.term307.decoration L24Gluing.term307.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core323 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term323.expression).2.2

theorem same326 : unweighted 323 = unweighted 326 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core323 L24Gluing.term323.decoration L24Gluing.term323.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation19 shifted 0 labels (by decide +kernel)

theorem same344 : unweighted 323 = unweighted 344 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core323 L24Gluing.term323.decoration L24Gluing.term323.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation0 shifted 0 labels (by decide +kernel)

theorem same347 : unweighted 323 = unweighted 347 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core323 L24Gluing.term323.decoration L24Gluing.term323.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation20 shifted 0 labels (by decide +kernel)

theorem same365 : unweighted 323 = unweighted 365 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core323 L24Gluing.term323.decoration L24Gluing.term323.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same366 : unweighted 323 = unweighted 366 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core323 L24Gluing.term323.decoration L24Gluing.term323.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core324 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term324.expression).2.2

theorem same327 : unweighted 324 = unweighted 327 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core324 L24Gluing.term324.decoration L24Gluing.term324.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation19 shifted 0 labels (by decide +kernel)

theorem same345 : unweighted 324 = unweighted 345 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core324 L24Gluing.term324.decoration L24Gluing.term324.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation0 shifted 0 labels (by decide +kernel)

theorem same348 : unweighted 324 = unweighted 348 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core324 L24Gluing.term324.decoration L24Gluing.term324.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation20 shifted 0 labels (by decide +kernel)

private abbrev core325 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term325.expression).2.2

theorem same328 : unweighted 325 = unweighted 328 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core325 L24Gluing.term325.decoration L24Gluing.term325.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation19 shifted 0 labels (by decide +kernel)

theorem same346 : unweighted 325 = unweighted 346 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core325 L24Gluing.term325.decoration L24Gluing.term325.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation0 shifted 0 labels (by decide +kernel)

theorem same349 : unweighted 325 = unweighted 349 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core325 L24Gluing.term325.decoration L24Gluing.term325.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation20 shifted 0 labels (by decide +kernel)

private abbrev core329 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term329.expression).2.2

theorem same350 : unweighted 329 = unweighted 350 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core329 L24Gluing.term329.decoration L24Gluing.term329.labels
    L24Gluing.flagPermutation12 L24Gluing.flagPermutation11 shifted 0 labels (by decide +kernel)

theorem same367 : unweighted 329 = unweighted 367 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core329 L24Gluing.term329.decoration L24Gluing.term329.labels
    L24Gluing.flagPermutation12 L24Gluing.flagPermutation3 shifted 0 labels (by decide +kernel)

private abbrev core330 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term330.expression).2.2

theorem same351 : unweighted 330 = unweighted 351 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core330 L24Gluing.term330.decoration L24Gluing.term330.labels
    L24Gluing.flagPermutation12 L24Gluing.flagPermutation11 shifted 0 labels (by decide +kernel)

theorem same368 : unweighted 330 = unweighted 368 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core330 L24Gluing.term330.decoration L24Gluing.term330.labels
    L24Gluing.flagPermutation12 L24Gluing.flagPermutation3 shifted 0 labels (by decide +kernel)

private abbrev core331 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term331.expression).2.2

theorem same352 : unweighted 331 = unweighted 352 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core331 L24Gluing.term331.decoration L24Gluing.term331.labels
    L24Gluing.flagPermutation12 L24Gluing.flagPermutation11 shifted 0 labels (by decide +kernel)

theorem same369 : unweighted 331 = unweighted 369 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core331 L24Gluing.term331.decoration L24Gluing.term331.labels
    L24Gluing.flagPermutation12 L24Gluing.flagPermutation3 shifted 0 labels (by decide +kernel)

private abbrev core332 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term332.expression).2.2

theorem same353 : unweighted 332 = unweighted 353 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core332 L24Gluing.term332.decoration L24Gluing.term332.labels
    L24Gluing.flagPermutation12 L24Gluing.flagPermutation11 shifted 0 labels (by decide +kernel)

theorem same370 : unweighted 332 = unweighted 370 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core332 L24Gluing.term332.decoration L24Gluing.term332.labels
    L24Gluing.flagPermutation12 L24Gluing.flagPermutation3 shifted 0 labels (by decide +kernel)

private abbrev core333 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term333.expression).2.2

theorem same354 : unweighted 333 = unweighted 354 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core333 L24Gluing.term333.decoration L24Gluing.term333.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation16 shifted 0 labels (by decide +kernel)

private abbrev core334 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term334.expression).2.2

theorem same355 : unweighted 334 = unweighted 355 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core334 L24Gluing.term334.decoration L24Gluing.term334.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation16 shifted 0 labels (by decide +kernel)

end AxiomaticGW.BlowupTwoLineH.Frame

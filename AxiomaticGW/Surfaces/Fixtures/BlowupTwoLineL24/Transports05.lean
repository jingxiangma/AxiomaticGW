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

private abbrev core335 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term335.expression).2.2

theorem same356 : unweighted 335 = unweighted 356 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core335 L24Gluing.term335.decoration L24Gluing.term335.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation16 shifted 0 labels (by decide +kernel)

private abbrev core336 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term336.expression).2.2

theorem same340 : unweighted 336 = unweighted 340 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core336 L24Gluing.term336.decoration L24Gluing.term336.labels
    L24Gluing.flagPermutation14 L24Gluing.flagPermutation15 shifted 0 labels (by decide +kernel)

theorem same357 : unweighted 336 = unweighted 357 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core336 L24Gluing.term336.decoration L24Gluing.term336.labels
    L24Gluing.flagPermutation14 L24Gluing.flagPermutation13 shifted 0 labels (by decide +kernel)

private abbrev core337 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term337.expression).2.2

theorem same341 : unweighted 337 = unweighted 341 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core337 L24Gluing.term337.decoration L24Gluing.term337.labels
    L24Gluing.flagPermutation14 L24Gluing.flagPermutation15 shifted 0 labels (by decide +kernel)

theorem same358 : unweighted 337 = unweighted 358 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core337 L24Gluing.term337.decoration L24Gluing.term337.labels
    L24Gluing.flagPermutation14 L24Gluing.flagPermutation13 shifted 0 labels (by decide +kernel)

private abbrev core338 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term338.expression).2.2

theorem same342 : unweighted 338 = unweighted 342 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core338 L24Gluing.term338.decoration L24Gluing.term338.labels
    L24Gluing.flagPermutation14 L24Gluing.flagPermutation15 shifted 0 labels (by decide +kernel)

theorem same359 : unweighted 338 = unweighted 359 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core338 L24Gluing.term338.decoration L24Gluing.term338.labels
    L24Gluing.flagPermutation14 L24Gluing.flagPermutation13 shifted 0 labels (by decide +kernel)

private abbrev core339 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term339.expression).2.2

theorem same343 : unweighted 339 = unweighted 343 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core339 L24Gluing.term339.decoration L24Gluing.term339.labels
    L24Gluing.flagPermutation14 L24Gluing.flagPermutation15 shifted 0 labels (by decide +kernel)

theorem same360 : unweighted 339 = unweighted 360 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core339 L24Gluing.term339.decoration L24Gluing.term339.labels
    L24Gluing.flagPermutation14 L24Gluing.flagPermutation13 shifted 0 labels (by decide +kernel)

private abbrev core361 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term361.expression).2.2

theorem same371 : unweighted 361 = unweighted 371 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core361 L24Gluing.term361.decoration L24Gluing.term361.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 shifted 0 labels (by decide +kernel)

theorem same374 : unweighted 361 = unweighted 374 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core361 L24Gluing.term361.decoration L24Gluing.term361.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 shifted 0 labels (by decide +kernel)

private abbrev core362 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term362.expression).2.2

theorem same372 : unweighted 362 = unweighted 372 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core362 L24Gluing.term362.decoration L24Gluing.term362.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 shifted 0 labels (by decide +kernel)

theorem same375 : unweighted 362 = unweighted 375 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core362 L24Gluing.term362.decoration L24Gluing.term362.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 shifted 0 labels (by decide +kernel)

private abbrev core363 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term363.expression).2.2

theorem same373 : unweighted 363 = unweighted 373 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core363 L24Gluing.term363.decoration L24Gluing.term363.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 shifted 0 labels (by decide +kernel)

theorem same376 : unweighted 363 = unweighted 376 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core363 L24Gluing.term363.decoration L24Gluing.term363.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 shifted 0 labels (by decide +kernel)

private abbrev core377 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term377.expression).2.2

theorem same384 : unweighted 377 = unweighted 384 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core377 L24Gluing.term377.decoration L24Gluing.term377.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 shifted 0 labels (by decide +kernel)

theorem same391 : unweighted 377 = unweighted 391 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core377 L24Gluing.term377.decoration L24Gluing.term377.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 shifted 0 labels (by decide +kernel)

private abbrev core378 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term378.expression).2.2

theorem same385 : unweighted 378 = unweighted 385 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core378 L24Gluing.term378.decoration L24Gluing.term378.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 shifted 0 labels (by decide +kernel)

theorem same392 : unweighted 378 = unweighted 392 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core378 L24Gluing.term378.decoration L24Gluing.term378.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 shifted 0 labels (by decide +kernel)

private abbrev core379 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term379.expression).2.2

theorem same386 : unweighted 379 = unweighted 386 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core379 L24Gluing.term379.decoration L24Gluing.term379.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same393 : unweighted 379 = unweighted 393 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core379 L24Gluing.term379.decoration L24Gluing.term379.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core380 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term380.expression).2.2

theorem same387 : unweighted 380 = unweighted 387 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core380 L24Gluing.term380.decoration L24Gluing.term380.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same394 : unweighted 380 = unweighted 394 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core380 L24Gluing.term380.decoration L24Gluing.term380.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core381 : GluingExpression 2 (Fin 4) :=
  L24Gluing.term381.expression

theorem same388 : unweighted 381 = unweighted 388 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core381 L24Gluing.term381.decoration L24Gluing.term381.labels
    (Equiv.refl (Fin 4)) L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same395 : unweighted 381 = unweighted 395 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core381 L24Gluing.term381.decoration L24Gluing.term381.labels
    (Equiv.refl (Fin 4)) L24Gluing.flagPermutation4 shifted 0 labels (by decide +kernel)

private abbrev core382 : GluingExpression 2 (Fin 4) :=
  L24Gluing.term382.expression

theorem same389 : unweighted 382 = unweighted 389 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core382 L24Gluing.term382.decoration L24Gluing.term382.labels
    (Equiv.refl (Fin 4)) L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same396 : unweighted 382 = unweighted 396 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core382 L24Gluing.term382.decoration L24Gluing.term382.labels
    (Equiv.refl (Fin 4)) L24Gluing.flagPermutation4 shifted 0 labels (by decide +kernel)

private abbrev core383 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term383.expression).2.2

theorem same390 : unweighted 383 = unweighted 390 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core383 L24Gluing.term383.decoration L24Gluing.term383.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 shifted 0 labels (by decide +kernel)

theorem same397 : unweighted 383 = unweighted 397 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core383 L24Gluing.term383.decoration L24Gluing.term383.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 shifted 0 labels (by decide +kernel)

private abbrev core399 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term399.expression).2.2

theorem same401 : unweighted 399 = unweighted 401 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core399 L24Gluing.term399.decoration L24Gluing.term399.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation4 shifted 0 labels (by decide +kernel)

theorem same404 : unweighted 399 = unweighted 404 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core399 L24Gluing.term399.decoration L24Gluing.term399.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 shifted 0 labels (by decide +kernel)

theorem same406 : unweighted 399 = unweighted 406 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core399 L24Gluing.term399.decoration L24Gluing.term399.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same410 : unweighted 399 = unweighted 410 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core399 L24Gluing.term399.decoration L24Gluing.term399.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same412 : unweighted 399 = unweighted 412 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core399 L24Gluing.term399.decoration L24Gluing.term399.labels
    L24Gluing.flagPermutation10 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core400 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term400.expression).2.2

theorem same402 : unweighted 400 = unweighted 402 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core400 L24Gluing.term400.decoration L24Gluing.term400.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation4 shifted 0 labels (by decide +kernel)

theorem same405 : unweighted 400 = unweighted 405 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core400 L24Gluing.term400.decoration L24Gluing.term400.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 shifted 0 labels (by decide +kernel)

theorem same407 : unweighted 400 = unweighted 407 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core400 L24Gluing.term400.decoration L24Gluing.term400.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same411 : unweighted 400 = unweighted 411 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core400 L24Gluing.term400.decoration L24Gluing.term400.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 shifted 0 labels (by decide +kernel)

theorem same413 : unweighted 400 = unweighted 413 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core400 L24Gluing.term400.decoration L24Gluing.term400.labels
    L24Gluing.flagPermutation10 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

private abbrev core403 : GluingExpression 2 (Fin 4) :=
  (underlying L24Gluing.term403.expression).2.2

theorem same408 : unweighted 403 = unweighted 408 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core403 L24Gluing.term403.decoration L24Gluing.term403.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 shifted 0 labels (by decide +kernel)

theorem same414 : unweighted 403 = unweighted 414 :=
  scalarPointContraction_relabel_eq_of_labels .blowupTwo (fun _ ↦ lowerVertex)
    core403 L24Gluing.term403.decoration L24Gluing.term403.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) shifted 0 labels (by decide +kernel)

end AxiomaticGW.BlowupTwoLineH.Frame

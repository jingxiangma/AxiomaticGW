/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.ScalarPointRelabel
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly

/-!
# Source-bound reuse of original F1 external assignments

Only identical gluing cores, cotangent decorations and label decisions are
shared. The actual pulled-back HEEE assignments are checked at all four labels.
Original relation coordinates remain outside each contraction. Component
backends and sampled slot values are never evaluated or assumed here.
-/

@[expose] public section
set_option Elab.async false

namespace AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05

open BlowupF1RootAssembly SurfaceGenusTwo GetzlerGraphs L24Gluing

private def core330 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core331 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core332 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core333 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 1) (n := 2) 1 1
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core334 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 1) (n := 2) 1 1
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core335 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 1) (n := 2) 1 1
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core336 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core337 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core338 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core339 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core361 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core362 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core363 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core377 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

private def core378 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

theorem coefficient330 : L24CorrectionsReplay.fullClaim 330 =
    (-1 / 1 : ℚ) := by decide +kernel

theorem coefficient331 : L24CorrectionsReplay.fullClaim 331 =
    (1 / 15 : ℚ) := by decide +kernel

theorem coefficient332 : L24CorrectionsReplay.fullClaim 332 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient333 : L24CorrectionsReplay.fullClaim 333 =
    (-1 / 3 : ℚ) := by decide +kernel

theorem coefficient334 : L24CorrectionsReplay.fullClaim 334 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient335 : L24CorrectionsReplay.fullClaim 335 =
    (1 / 3 : ℚ) := by decide +kernel

theorem coefficient336 : L24CorrectionsReplay.fullClaim 336 =
    (-1 / 3 : ℚ) := by decide +kernel

theorem coefficient337 : L24CorrectionsReplay.fullClaim 337 =
    (-1 / 15 : ℚ) := by decide +kernel

theorem coefficient338 : L24CorrectionsReplay.fullClaim 338 =
    (-1 / 15 : ℚ) := by decide +kernel

theorem coefficient339 : L24CorrectionsReplay.fullClaim 339 =
    (-7 / 5 : ℚ) := by decide +kernel

theorem coefficient340 : L24CorrectionsReplay.fullClaim 340 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient341 : L24CorrectionsReplay.fullClaim 341 =
    (1 / 15 : ℚ) := by decide +kernel

theorem coefficient342 : L24CorrectionsReplay.fullClaim 342 =
    (-1 / 1 : ℚ) := by decide +kernel

theorem coefficient343 : L24CorrectionsReplay.fullClaim 343 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient352 : L24CorrectionsReplay.fullClaim 352 =
    (1 / 15 : ℚ) := by decide +kernel

theorem coefficient353 : L24CorrectionsReplay.fullClaim 353 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient354 : L24CorrectionsReplay.fullClaim 354 =
    (-1 / 3 : ℚ) := by decide +kernel

theorem coefficient355 : L24CorrectionsReplay.fullClaim 355 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient356 : L24CorrectionsReplay.fullClaim 356 =
    (1 / 3 : ℚ) := by decide +kernel

theorem coefficient357 : L24CorrectionsReplay.fullClaim 357 =
    (-1 / 3 : ℚ) := by decide +kernel

theorem coefficient358 : L24CorrectionsReplay.fullClaim 358 =
    (-1 / 15 : ℚ) := by decide +kernel

theorem coefficient359 : L24CorrectionsReplay.fullClaim 359 =
    (-1 / 15 : ℚ) := by decide +kernel

theorem coefficient360 : L24CorrectionsReplay.fullClaim 360 =
    (-7 / 5 : ℚ) := by decide +kernel

theorem coefficient361 : L24CorrectionsReplay.fullClaim 361 =
    (2 / 15 : ℚ) := by decide +kernel

theorem coefficient362 : L24CorrectionsReplay.fullClaim 362 =
    (2 / 15 : ℚ) := by decide +kernel

theorem coefficient363 : L24CorrectionsReplay.fullClaim 363 =
    (-8 / 15 : ℚ) := by decide +kernel

theorem coefficient368 : L24CorrectionsReplay.fullClaim 368 =
    (-1 / 15 : ℚ) := by decide +kernel

theorem coefficient369 : L24CorrectionsReplay.fullClaim 369 =
    (-1 / 15 : ℚ) := by decide +kernel

theorem coefficient370 : L24CorrectionsReplay.fullClaim 370 =
    (-1 / 3 : ℚ) := by decide +kernel

theorem coefficient371 : L24CorrectionsReplay.fullClaim 371 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient372 : L24CorrectionsReplay.fullClaim 372 =
    (1 / 3 : ℚ) := by decide +kernel

theorem coefficient373 : L24CorrectionsReplay.fullClaim 373 =
    (-1 / 3 : ℚ) := by decide +kernel

theorem coefficient374 : L24CorrectionsReplay.fullClaim 374 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient375 : L24CorrectionsReplay.fullClaim 375 =
    (1 / 3 : ℚ) := by decide +kernel

theorem coefficient376 : L24CorrectionsReplay.fullClaim 376 =
    (-1 / 3 : ℚ) := by decide +kernel

theorem coefficient377 : L24CorrectionsReplay.fullClaim 377 =
    (-565 / 351 : ℚ) := by decide +kernel

theorem coefficient378 : L24CorrectionsReplay.fullClaim 378 =
    (-565 / 351 : ℚ) := by decide +kernel

theorem coefficient384 : L24CorrectionsReplay.fullClaim 384 =
    (-3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient385 : L24CorrectionsReplay.fullClaim 385 =
    (-17423 / 21060 : ℚ) := by decide +kernel

theorem coefficient391 : L24CorrectionsReplay.fullClaim 391 =
    (-3527 / 5265 : ℚ) := by decide +kernel

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels330_368 :
    insertions ∘ L24Gluing.flagPermutation12 =
      insertions ∘ L24Gluing.flagPermutation3 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar330_eq368 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 330).expression.scalarPointContraction X v
      (L24Gluing.term 330).decoration (L24Gluing.term 330).labels beta n insertions =
    (L24Gluing.term 368).expression.scalarPointContraction X v
      (L24Gluing.term 368).decoration (L24Gluing.term 368).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core330 L24Gluing.term330.decoration L24Gluing.term330.labels
    L24Gluing.flagPermutation12 L24Gluing.flagPermutation3 beta n insertions labels330_368

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded330_eq368 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 330) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 368) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 330) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 368) (by decide +kernel)]
  exact scalar330_eq368 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted368_eq330 : originalWeighted 368 =
    (1 / 15 : ℚ) * originalWeighted 330 := by
  rw [originalWeighted, originalWeighted, ← guarded330_eq368,
    coefficient368, coefficient330]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels331_352 :
    insertions ∘ L24Gluing.flagPermutation12 =
      insertions ∘ L24Gluing.flagPermutation11 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar331_eq352 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 331).expression.scalarPointContraction X v
      (L24Gluing.term 331).decoration (L24Gluing.term 331).labels beta n insertions =
    (L24Gluing.term 352).expression.scalarPointContraction X v
      (L24Gluing.term 352).decoration (L24Gluing.term 352).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core331 L24Gluing.term331.decoration L24Gluing.term331.labels
    L24Gluing.flagPermutation12 L24Gluing.flagPermutation11 beta n insertions labels331_352

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded331_eq352 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 331) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 352) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 331) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 352) (by decide +kernel)]
  exact scalar331_eq352 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted352_eq331 : originalWeighted 352 =
    (1 / 1 : ℚ) * originalWeighted 331 := by
  rw [originalWeighted, originalWeighted, ← guarded331_eq352,
    coefficient352, coefficient331]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels331_369 :
    insertions ∘ L24Gluing.flagPermutation12 =
      insertions ∘ L24Gluing.flagPermutation3 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar331_eq369 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 331).expression.scalarPointContraction X v
      (L24Gluing.term 331).decoration (L24Gluing.term 331).labels beta n insertions =
    (L24Gluing.term 369).expression.scalarPointContraction X v
      (L24Gluing.term 369).decoration (L24Gluing.term 369).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core331 L24Gluing.term331.decoration L24Gluing.term331.labels
    L24Gluing.flagPermutation12 L24Gluing.flagPermutation3 beta n insertions labels331_369

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded331_eq369 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 331) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 369) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 331) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 369) (by decide +kernel)]
  exact scalar331_eq369 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted369_eq331 : originalWeighted 369 =
    (-1 / 1 : ℚ) * originalWeighted 331 := by
  rw [originalWeighted, originalWeighted, ← guarded331_eq369,
    coefficient369, coefficient331]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels332_353 :
    insertions ∘ L24Gluing.flagPermutation12 =
      insertions ∘ L24Gluing.flagPermutation11 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar332_eq353 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 332).expression.scalarPointContraction X v
      (L24Gluing.term 332).decoration (L24Gluing.term 332).labels beta n insertions =
    (L24Gluing.term 353).expression.scalarPointContraction X v
      (L24Gluing.term 353).decoration (L24Gluing.term 353).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core332 L24Gluing.term332.decoration L24Gluing.term332.labels
    L24Gluing.flagPermutation12 L24Gluing.flagPermutation11 beta n insertions labels332_353

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded332_eq353 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 332) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 353) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 332) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 353) (by decide +kernel)]
  exact scalar332_eq353 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted353_eq332 : originalWeighted 353 =
    (1 / 1 : ℚ) * originalWeighted 332 := by
  rw [originalWeighted, originalWeighted, ← guarded332_eq353,
    coefficient353, coefficient332]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels332_370 :
    insertions ∘ L24Gluing.flagPermutation12 =
      insertions ∘ L24Gluing.flagPermutation3 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar332_eq370 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 332).expression.scalarPointContraction X v
      (L24Gluing.term 332).decoration (L24Gluing.term 332).labels beta n insertions =
    (L24Gluing.term 370).expression.scalarPointContraction X v
      (L24Gluing.term 370).decoration (L24Gluing.term 370).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core332 L24Gluing.term332.decoration L24Gluing.term332.labels
    L24Gluing.flagPermutation12 L24Gluing.flagPermutation3 beta n insertions labels332_370

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded332_eq370 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 332) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 370) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 332) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 370) (by decide +kernel)]
  exact scalar332_eq370 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted370_eq332 : originalWeighted 370 =
    (5 / 3 : ℚ) * originalWeighted 332 := by
  rw [originalWeighted, originalWeighted, ← guarded332_eq370,
    coefficient370, coefficient332]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels333_354 :
    insertions ∘ L24Gluing.flagPermutation15 =
      insertions ∘ L24Gluing.flagPermutation16 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar333_eq354 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 333).expression.scalarPointContraction X v
      (L24Gluing.term 333).decoration (L24Gluing.term 333).labels beta n insertions =
    (L24Gluing.term 354).expression.scalarPointContraction X v
      (L24Gluing.term 354).decoration (L24Gluing.term 354).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core333 L24Gluing.term333.decoration L24Gluing.term333.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation16 beta n insertions labels333_354

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded333_eq354 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 333) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 354) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 333) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 354) (by decide +kernel)]
  exact scalar333_eq354 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted354_eq333 : originalWeighted 354 =
    (1 / 1 : ℚ) * originalWeighted 333 := by
  rw [originalWeighted, originalWeighted, ← guarded333_eq354,
    coefficient354, coefficient333]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels334_355 :
    insertions ∘ L24Gluing.flagPermutation15 =
      insertions ∘ L24Gluing.flagPermutation16 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar334_eq355 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 334).expression.scalarPointContraction X v
      (L24Gluing.term 334).decoration (L24Gluing.term 334).labels beta n insertions =
    (L24Gluing.term 355).expression.scalarPointContraction X v
      (L24Gluing.term 355).decoration (L24Gluing.term 355).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core334 L24Gluing.term334.decoration L24Gluing.term334.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation16 beta n insertions labels334_355

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded334_eq355 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 334) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 355) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 334) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 355) (by decide +kernel)]
  exact scalar334_eq355 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted355_eq334 : originalWeighted 355 =
    (1 / 1 : ℚ) * originalWeighted 334 := by
  rw [originalWeighted, originalWeighted, ← guarded334_eq355,
    coefficient355, coefficient334]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels335_356 :
    insertions ∘ L24Gluing.flagPermutation15 =
      insertions ∘ L24Gluing.flagPermutation16 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar335_eq356 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 335).expression.scalarPointContraction X v
      (L24Gluing.term 335).decoration (L24Gluing.term 335).labels beta n insertions =
    (L24Gluing.term 356).expression.scalarPointContraction X v
      (L24Gluing.term 356).decoration (L24Gluing.term 356).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core335 L24Gluing.term335.decoration L24Gluing.term335.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation16 beta n insertions labels335_356

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded335_eq356 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 335) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 356) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 335) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 356) (by decide +kernel)]
  exact scalar335_eq356 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted356_eq335 : originalWeighted 356 =
    (1 / 1 : ℚ) * originalWeighted 335 := by
  rw [originalWeighted, originalWeighted, ← guarded335_eq356,
    coefficient356, coefficient335]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels336_340 :
    insertions ∘ L24Gluing.flagPermutation14 =
      insertions ∘ L24Gluing.flagPermutation15 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar336_eq340 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 336).expression.scalarPointContraction X v
      (L24Gluing.term 336).decoration (L24Gluing.term 336).labels beta n insertions =
    (L24Gluing.term 340).expression.scalarPointContraction X v
      (L24Gluing.term 340).decoration (L24Gluing.term 340).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core336 L24Gluing.term336.decoration L24Gluing.term336.labels
    L24Gluing.flagPermutation14 L24Gluing.flagPermutation15 beta n insertions labels336_340

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded336_eq340 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 336) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 340) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 336) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 340) (by decide +kernel)]
  exact scalar336_eq340 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted340_eq336 : originalWeighted 340 =
    (3 / 5 : ℚ) * originalWeighted 336 := by
  rw [originalWeighted, originalWeighted, ← guarded336_eq340,
    coefficient340, coefficient336]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels336_357 :
    insertions ∘ L24Gluing.flagPermutation14 =
      insertions ∘ L24Gluing.flagPermutation13 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar336_eq357 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 336).expression.scalarPointContraction X v
      (L24Gluing.term 336).decoration (L24Gluing.term 336).labels beta n insertions =
    (L24Gluing.term 357).expression.scalarPointContraction X v
      (L24Gluing.term 357).decoration (L24Gluing.term 357).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core336 L24Gluing.term336.decoration L24Gluing.term336.labels
    L24Gluing.flagPermutation14 L24Gluing.flagPermutation13 beta n insertions labels336_357

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded336_eq357 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 336) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 357) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 336) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 357) (by decide +kernel)]
  exact scalar336_eq357 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted357_eq336 : originalWeighted 357 =
    (1 / 1 : ℚ) * originalWeighted 336 := by
  rw [originalWeighted, originalWeighted, ← guarded336_eq357,
    coefficient357, coefficient336]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels337_341 :
    insertions ∘ L24Gluing.flagPermutation14 =
      insertions ∘ L24Gluing.flagPermutation15 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar337_eq341 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 337).expression.scalarPointContraction X v
      (L24Gluing.term 337).decoration (L24Gluing.term 337).labels beta n insertions =
    (L24Gluing.term 341).expression.scalarPointContraction X v
      (L24Gluing.term 341).decoration (L24Gluing.term 341).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core337 L24Gluing.term337.decoration L24Gluing.term337.labels
    L24Gluing.flagPermutation14 L24Gluing.flagPermutation15 beta n insertions labels337_341

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded337_eq341 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 337) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 341) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 337) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 341) (by decide +kernel)]
  exact scalar337_eq341 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted341_eq337 : originalWeighted 341 =
    (-1 / 1 : ℚ) * originalWeighted 337 := by
  rw [originalWeighted, originalWeighted, ← guarded337_eq341,
    coefficient341, coefficient337]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels337_358 :
    insertions ∘ L24Gluing.flagPermutation14 =
      insertions ∘ L24Gluing.flagPermutation13 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar337_eq358 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 337).expression.scalarPointContraction X v
      (L24Gluing.term 337).decoration (L24Gluing.term 337).labels beta n insertions =
    (L24Gluing.term 358).expression.scalarPointContraction X v
      (L24Gluing.term 358).decoration (L24Gluing.term 358).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core337 L24Gluing.term337.decoration L24Gluing.term337.labels
    L24Gluing.flagPermutation14 L24Gluing.flagPermutation13 beta n insertions labels337_358

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded337_eq358 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 337) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 358) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 337) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 358) (by decide +kernel)]
  exact scalar337_eq358 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted358_eq337 : originalWeighted 358 =
    (1 / 1 : ℚ) * originalWeighted 337 := by
  rw [originalWeighted, originalWeighted, ← guarded337_eq358,
    coefficient358, coefficient337]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels338_342 :
    insertions ∘ L24Gluing.flagPermutation14 =
      insertions ∘ L24Gluing.flagPermutation15 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar338_eq342 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 338).expression.scalarPointContraction X v
      (L24Gluing.term 338).decoration (L24Gluing.term 338).labels beta n insertions =
    (L24Gluing.term 342).expression.scalarPointContraction X v
      (L24Gluing.term 342).decoration (L24Gluing.term 342).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core338 L24Gluing.term338.decoration L24Gluing.term338.labels
    L24Gluing.flagPermutation14 L24Gluing.flagPermutation15 beta n insertions labels338_342

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded338_eq342 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 338) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 342) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 338) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 342) (by decide +kernel)]
  exact scalar338_eq342 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted342_eq338 : originalWeighted 342 =
    (15 / 1 : ℚ) * originalWeighted 338 := by
  rw [originalWeighted, originalWeighted, ← guarded338_eq342,
    coefficient342, coefficient338]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels338_359 :
    insertions ∘ L24Gluing.flagPermutation14 =
      insertions ∘ L24Gluing.flagPermutation13 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar338_eq359 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 338).expression.scalarPointContraction X v
      (L24Gluing.term 338).decoration (L24Gluing.term 338).labels beta n insertions =
    (L24Gluing.term 359).expression.scalarPointContraction X v
      (L24Gluing.term 359).decoration (L24Gluing.term 359).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core338 L24Gluing.term338.decoration L24Gluing.term338.labels
    L24Gluing.flagPermutation14 L24Gluing.flagPermutation13 beta n insertions labels338_359

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded338_eq359 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 338) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 359) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 338) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 359) (by decide +kernel)]
  exact scalar338_eq359 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted359_eq338 : originalWeighted 359 =
    (1 / 1 : ℚ) * originalWeighted 338 := by
  rw [originalWeighted, originalWeighted, ← guarded338_eq359,
    coefficient359, coefficient338]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels339_343 :
    insertions ∘ L24Gluing.flagPermutation14 =
      insertions ∘ L24Gluing.flagPermutation15 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar339_eq343 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 339).expression.scalarPointContraction X v
      (L24Gluing.term 339).decoration (L24Gluing.term 339).labels beta n insertions =
    (L24Gluing.term 343).expression.scalarPointContraction X v
      (L24Gluing.term 343).decoration (L24Gluing.term 343).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core339 L24Gluing.term339.decoration L24Gluing.term339.labels
    L24Gluing.flagPermutation14 L24Gluing.flagPermutation15 beta n insertions labels339_343

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded339_eq343 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 339) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 343) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 339) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 343) (by decide +kernel)]
  exact scalar339_eq343 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted343_eq339 : originalWeighted 343 =
    (1 / 7 : ℚ) * originalWeighted 339 := by
  rw [originalWeighted, originalWeighted, ← guarded339_eq343,
    coefficient343, coefficient339]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels339_360 :
    insertions ∘ L24Gluing.flagPermutation14 =
      insertions ∘ L24Gluing.flagPermutation13 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar339_eq360 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 339).expression.scalarPointContraction X v
      (L24Gluing.term 339).decoration (L24Gluing.term 339).labels beta n insertions =
    (L24Gluing.term 360).expression.scalarPointContraction X v
      (L24Gluing.term 360).decoration (L24Gluing.term 360).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core339 L24Gluing.term339.decoration L24Gluing.term339.labels
    L24Gluing.flagPermutation14 L24Gluing.flagPermutation13 beta n insertions labels339_360

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded339_eq360 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 339) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 360) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 339) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 360) (by decide +kernel)]
  exact scalar339_eq360 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted360_eq339 : originalWeighted 360 =
    (1 / 1 : ℚ) * originalWeighted 339 := by
  rw [originalWeighted, originalWeighted, ← guarded339_eq360,
    coefficient360, coefficient339]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels361_371 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation9 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar361_eq371 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 361).expression.scalarPointContraction X v
      (L24Gluing.term 361).decoration (L24Gluing.term 361).labels beta n insertions =
    (L24Gluing.term 371).expression.scalarPointContraction X v
      (L24Gluing.term 371).decoration (L24Gluing.term 371).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core361 L24Gluing.term361.decoration L24Gluing.term361.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 beta n insertions labels361_371

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded361_eq371 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 361) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 371) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 361) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 371) (by decide +kernel)]
  exact scalar361_eq371 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted371_eq361 : originalWeighted 371 =
    (-3 / 2 : ℚ) * originalWeighted 361 := by
  rw [originalWeighted, originalWeighted, ← guarded361_eq371,
    coefficient371, coefficient361]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels361_374 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation3 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar361_eq374 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 361).expression.scalarPointContraction X v
      (L24Gluing.term 361).decoration (L24Gluing.term 361).labels beta n insertions =
    (L24Gluing.term 374).expression.scalarPointContraction X v
      (L24Gluing.term 374).decoration (L24Gluing.term 374).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core361 L24Gluing.term361.decoration L24Gluing.term361.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 beta n insertions labels361_374

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded361_eq374 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 361) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 374) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 361) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 374) (by decide +kernel)]
  exact scalar361_eq374 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted374_eq361 : originalWeighted 374 =
    (-3 / 2 : ℚ) * originalWeighted 361 := by
  rw [originalWeighted, originalWeighted, ← guarded361_eq374,
    coefficient374, coefficient361]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels362_372 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation9 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar362_eq372 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 362).expression.scalarPointContraction X v
      (L24Gluing.term 362).decoration (L24Gluing.term 362).labels beta n insertions =
    (L24Gluing.term 372).expression.scalarPointContraction X v
      (L24Gluing.term 372).decoration (L24Gluing.term 372).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core362 L24Gluing.term362.decoration L24Gluing.term362.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 beta n insertions labels362_372

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded362_eq372 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 362) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 372) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 362) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 372) (by decide +kernel)]
  exact scalar362_eq372 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted372_eq362 : originalWeighted 372 =
    (5 / 2 : ℚ) * originalWeighted 362 := by
  rw [originalWeighted, originalWeighted, ← guarded362_eq372,
    coefficient372, coefficient362]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels362_375 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation3 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar362_eq375 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 362).expression.scalarPointContraction X v
      (L24Gluing.term 362).decoration (L24Gluing.term 362).labels beta n insertions =
    (L24Gluing.term 375).expression.scalarPointContraction X v
      (L24Gluing.term 375).decoration (L24Gluing.term 375).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core362 L24Gluing.term362.decoration L24Gluing.term362.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 beta n insertions labels362_375

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded362_eq375 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 362) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 375) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 362) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 375) (by decide +kernel)]
  exact scalar362_eq375 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted375_eq362 : originalWeighted 375 =
    (5 / 2 : ℚ) * originalWeighted 362 := by
  rw [originalWeighted, originalWeighted, ← guarded362_eq375,
    coefficient375, coefficient362]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels363_373 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation9 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar363_eq373 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 363).expression.scalarPointContraction X v
      (L24Gluing.term 363).decoration (L24Gluing.term 363).labels beta n insertions =
    (L24Gluing.term 373).expression.scalarPointContraction X v
      (L24Gluing.term 373).decoration (L24Gluing.term 373).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core363 L24Gluing.term363.decoration L24Gluing.term363.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 beta n insertions labels363_373

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded363_eq373 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 363) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 373) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 363) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 373) (by decide +kernel)]
  exact scalar363_eq373 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted373_eq363 : originalWeighted 373 =
    (5 / 8 : ℚ) * originalWeighted 363 := by
  rw [originalWeighted, originalWeighted, ← guarded363_eq373,
    coefficient373, coefficient363]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels363_376 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation3 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar363_eq376 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 363).expression.scalarPointContraction X v
      (L24Gluing.term 363).decoration (L24Gluing.term 363).labels beta n insertions =
    (L24Gluing.term 376).expression.scalarPointContraction X v
      (L24Gluing.term 376).decoration (L24Gluing.term 376).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core363 L24Gluing.term363.decoration L24Gluing.term363.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 beta n insertions labels363_376

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded363_eq376 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 363) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 376) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 363) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 376) (by decide +kernel)]
  exact scalar363_eq376 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted376_eq363 : originalWeighted 376 =
    (5 / 8 : ℚ) * originalWeighted 363 := by
  rw [originalWeighted, originalWeighted, ← guarded363_eq376,
    coefficient376, coefficient363]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels377_384 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation9 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar377_eq384 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 377).expression.scalarPointContraction X v
      (L24Gluing.term 377).decoration (L24Gluing.term 377).labels beta n insertions =
    (L24Gluing.term 384).expression.scalarPointContraction X v
      (L24Gluing.term 384).decoration (L24Gluing.term 384).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core377 L24Gluing.term377.decoration L24Gluing.term377.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 beta n insertions labels377_384

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded377_eq384 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 377) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 384) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 377) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 384) (by decide +kernel)]
  exact scalar377_eq384 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted384_eq377 : originalWeighted 384 =
    (3527 / 8475 : ℚ) * originalWeighted 377 := by
  rw [originalWeighted, originalWeighted, ← guarded377_eq384,
    coefficient384, coefficient377]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels377_391 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation3 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar377_eq391 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 377).expression.scalarPointContraction X v
      (L24Gluing.term 377).decoration (L24Gluing.term 377).labels beta n insertions =
    (L24Gluing.term 391).expression.scalarPointContraction X v
      (L24Gluing.term 391).decoration (L24Gluing.term 391).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core377 L24Gluing.term377.decoration L24Gluing.term377.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 beta n insertions labels377_391

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded377_eq391 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 377) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 391) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 377) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 391) (by decide +kernel)]
  exact scalar377_eq391 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted391_eq377 : originalWeighted 391 =
    (3527 / 8475 : ℚ) * originalWeighted 377 := by
  rw [originalWeighted, originalWeighted, ← guarded377_eq391,
    coefficient391, coefficient377]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels378_385 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation9 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar378_eq385 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 378).expression.scalarPointContraction X v
      (L24Gluing.term 378).decoration (L24Gluing.term 378).labels beta n insertions =
    (L24Gluing.term 385).expression.scalarPointContraction X v
      (L24Gluing.term 385).decoration (L24Gluing.term 385).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core378 L24Gluing.term378.decoration L24Gluing.term378.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 beta n insertions labels378_385

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded378_eq385 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 378) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 385) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 378) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 385) (by decide +kernel)]
  exact scalar378_eq385 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted385_eq378 : originalWeighted 385 =
    (17423 / 33900 : ℚ) * originalWeighted 378 := by
  rw [originalWeighted, originalWeighted, ← guarded378_eq385,
    coefficient385, coefficient378]
  ring

end AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05

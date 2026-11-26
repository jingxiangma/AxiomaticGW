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

namespace AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06

open BlowupF1RootAssembly SurfaceGenusTwo GetzlerGraphs L24Gluing

private def core378 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core379 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

private def core380 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core381 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))))

private def core382 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))

private def core383 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 4 0
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))

private def core399 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))

private def core400 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core403 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 4 0
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))

private def core409 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 4 0
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))

theorem coefficient378 : L24CorrectionsReplay.fullClaim 378 =
    (-565 / 351 : ℚ) := by decide +kernel

theorem coefficient379 : L24CorrectionsReplay.fullClaim 379 =
    (-197 / 270 : ℚ) := by decide +kernel

theorem coefficient380 : L24CorrectionsReplay.fullClaim 380 =
    (-47 / 45 : ℚ) := by decide +kernel

theorem coefficient381 : L24CorrectionsReplay.fullClaim 381 =
    (-24779 / 10530 : ℚ) := by decide +kernel

theorem coefficient382 : L24CorrectionsReplay.fullClaim 382 =
    (-52873 / 21060 : ℚ) := by decide +kernel

theorem coefficient383 : L24CorrectionsReplay.fullClaim 383 =
    (-565 / 351 : ℚ) := by decide +kernel

theorem coefficient386 : L24CorrectionsReplay.fullClaim 386 =
    (-3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient387 : L24CorrectionsReplay.fullClaim 387 =
    (-17423 / 21060 : ℚ) := by decide +kernel

theorem coefficient388 : L24CorrectionsReplay.fullClaim 388 =
    (-24779 / 10530 : ℚ) := by decide +kernel

theorem coefficient389 : L24CorrectionsReplay.fullClaim 389 =
    (-52873 / 21060 : ℚ) := by decide +kernel

theorem coefficient390 : L24CorrectionsReplay.fullClaim 390 =
    (-1130 / 1053 : ℚ) := by decide +kernel

theorem coefficient392 : L24CorrectionsReplay.fullClaim 392 =
    (-17423 / 21060 : ℚ) := by decide +kernel

theorem coefficient393 : L24CorrectionsReplay.fullClaim 393 =
    (-3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient394 : L24CorrectionsReplay.fullClaim 394 =
    (-17423 / 21060 : ℚ) := by decide +kernel

theorem coefficient395 : L24CorrectionsReplay.fullClaim 395 =
    (-24779 / 10530 : ℚ) := by decide +kernel

theorem coefficient396 : L24CorrectionsReplay.fullClaim 396 =
    (-52873 / 21060 : ℚ) := by decide +kernel

theorem coefficient397 : L24CorrectionsReplay.fullClaim 397 =
    (-1130 / 1053 : ℚ) := by decide +kernel

theorem coefficient399 : L24CorrectionsReplay.fullClaim 399 =
    (-197 / 270 : ℚ) := by decide +kernel

theorem coefficient400 : L24CorrectionsReplay.fullClaim 400 =
    (-47 / 45 : ℚ) := by decide +kernel

theorem coefficient401 : L24CorrectionsReplay.fullClaim 401 =
    (-565 / 351 : ℚ) := by decide +kernel

theorem coefficient402 : L24CorrectionsReplay.fullClaim 402 =
    (-565 / 351 : ℚ) := by decide +kernel

theorem coefficient403 : L24CorrectionsReplay.fullClaim 403 =
    (-565 / 351 : ℚ) := by decide +kernel

theorem coefficient404 : L24CorrectionsReplay.fullClaim 404 =
    (-197 / 270 : ℚ) := by decide +kernel

theorem coefficient405 : L24CorrectionsReplay.fullClaim 405 =
    (-47 / 45 : ℚ) := by decide +kernel

theorem coefficient406 : L24CorrectionsReplay.fullClaim 406 =
    (-565 / 351 : ℚ) := by decide +kernel

theorem coefficient407 : L24CorrectionsReplay.fullClaim 407 =
    (-565 / 351 : ℚ) := by decide +kernel

theorem coefficient408 : L24CorrectionsReplay.fullClaim 408 =
    (-565 / 351 : ℚ) := by decide +kernel

theorem coefficient409 : L24CorrectionsReplay.fullClaim 409 =
    (-565 / 117 : ℚ) := by decide +kernel

theorem coefficient410 : L24CorrectionsReplay.fullClaim 410 =
    (-3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient411 : L24CorrectionsReplay.fullClaim 411 =
    (-17423 / 21060 : ℚ) := by decide +kernel

theorem coefficient412 : L24CorrectionsReplay.fullClaim 412 =
    (-3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient413 : L24CorrectionsReplay.fullClaim 413 =
    (-17423 / 21060 : ℚ) := by decide +kernel

theorem coefficient414 : L24CorrectionsReplay.fullClaim 414 =
    (-1130 / 1053 : ℚ) := by decide +kernel

theorem coefficient415 : L24CorrectionsReplay.fullClaim 415 =
    (-2105 / 1053 : ℚ) := by decide +kernel

theorem coefficient416 : L24CorrectionsReplay.fullClaim 416 =
    (-2105 / 1053 : ℚ) := by decide +kernel

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels378_392 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation3 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar378_eq392 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 378).expression.scalarPointContraction X v
      (L24Gluing.term 378).decoration (L24Gluing.term 378).labels beta n insertions =
    (L24Gluing.term 392).expression.scalarPointContraction X v
      (L24Gluing.term 392).decoration (L24Gluing.term 392).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core378 L24Gluing.term378.decoration L24Gluing.term378.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 beta n insertions labels378_392

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded378_eq392 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 378) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 392) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 378) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 392) (by decide +kernel)]
  exact scalar378_eq392 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted392_eq378 : originalWeighted 392 =
    (17423 / 33900 : ℚ) * originalWeighted 378 := by
  rw [originalWeighted, originalWeighted, ← guarded378_eq392,
    coefficient392, coefficient378]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels379_386 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar379_eq386 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 379).expression.scalarPointContraction X v
      (L24Gluing.term 379).decoration (L24Gluing.term 379).labels beta n insertions =
    (L24Gluing.term 386).expression.scalarPointContraction X v
      (L24Gluing.term 386).decoration (L24Gluing.term 386).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core379 L24Gluing.term379.decoration L24Gluing.term379.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels379_386

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded379_eq386 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 379) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 386) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 379) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 386) (by decide +kernel)]
  exact scalar379_eq386 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted386_eq379 : originalWeighted 386 =
    (7054 / 7683 : ℚ) * originalWeighted 379 := by
  rw [originalWeighted, originalWeighted, ← guarded379_eq386,
    coefficient386, coefficient379]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels379_393 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar379_eq393 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 379).expression.scalarPointContraction X v
      (L24Gluing.term 379).decoration (L24Gluing.term 379).labels beta n insertions =
    (L24Gluing.term 393).expression.scalarPointContraction X v
      (L24Gluing.term 393).decoration (L24Gluing.term 393).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core379 L24Gluing.term379.decoration L24Gluing.term379.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels379_393

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded379_eq393 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 379) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 393) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 379) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 393) (by decide +kernel)]
  exact scalar379_eq393 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted393_eq379 : originalWeighted 393 =
    (7054 / 7683 : ℚ) * originalWeighted 379 := by
  rw [originalWeighted, originalWeighted, ← guarded379_eq393,
    coefficient393, coefficient379]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels380_387 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar380_eq387 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 380).expression.scalarPointContraction X v
      (L24Gluing.term 380).decoration (L24Gluing.term 380).labels beta n insertions =
    (L24Gluing.term 387).expression.scalarPointContraction X v
      (L24Gluing.term 387).decoration (L24Gluing.term 387).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core380 L24Gluing.term380.decoration L24Gluing.term380.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels380_387

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded380_eq387 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 380) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 387) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 380) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 387) (by decide +kernel)]
  exact scalar380_eq387 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted387_eq380 : originalWeighted 387 =
    (17423 / 21996 : ℚ) * originalWeighted 380 := by
  rw [originalWeighted, originalWeighted, ← guarded380_eq387,
    coefficient387, coefficient380]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels380_394 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar380_eq394 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 380).expression.scalarPointContraction X v
      (L24Gluing.term 380).decoration (L24Gluing.term 380).labels beta n insertions =
    (L24Gluing.term 394).expression.scalarPointContraction X v
      (L24Gluing.term 394).decoration (L24Gluing.term 394).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core380 L24Gluing.term380.decoration L24Gluing.term380.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels380_394

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded380_eq394 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 380) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 394) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 380) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 394) (by decide +kernel)]
  exact scalar380_eq394 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted394_eq380 : originalWeighted 394 =
    (17423 / 21996 : ℚ) * originalWeighted 380 := by
  rw [originalWeighted, originalWeighted, ← guarded380_eq394,
    coefficient394, coefficient380]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels381_388 :
    insertions ∘ (Equiv.refl (Fin 4)) =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar381_eq388 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 381).expression.scalarPointContraction X v
      (L24Gluing.term 381).decoration (L24Gluing.term 381).labels beta n insertions =
    (L24Gluing.term 388).expression.scalarPointContraction X v
      (L24Gluing.term 388).decoration (L24Gluing.term 388).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core381 L24Gluing.term381.decoration L24Gluing.term381.labels
    (Equiv.refl (Fin 4)) L24Gluing.flagPermutation5 beta n insertions labels381_388

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded381_eq388 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 381) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 388) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 381) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 388) (by decide +kernel)]
  exact scalar381_eq388 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted388_eq381 : originalWeighted 388 =
    (1 / 1 : ℚ) * originalWeighted 381 := by
  rw [originalWeighted, originalWeighted, ← guarded381_eq388,
    coefficient388, coefficient381]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels381_395 :
    insertions ∘ (Equiv.refl (Fin 4)) =
      insertions ∘ L24Gluing.flagPermutation4 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar381_eq395 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 381).expression.scalarPointContraction X v
      (L24Gluing.term 381).decoration (L24Gluing.term 381).labels beta n insertions =
    (L24Gluing.term 395).expression.scalarPointContraction X v
      (L24Gluing.term 395).decoration (L24Gluing.term 395).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core381 L24Gluing.term381.decoration L24Gluing.term381.labels
    (Equiv.refl (Fin 4)) L24Gluing.flagPermutation4 beta n insertions labels381_395

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded381_eq395 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 381) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 395) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 381) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 395) (by decide +kernel)]
  exact scalar381_eq395 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted395_eq381 : originalWeighted 395 =
    (1 / 1 : ℚ) * originalWeighted 381 := by
  rw [originalWeighted, originalWeighted, ← guarded381_eq395,
    coefficient395, coefficient381]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels382_389 :
    insertions ∘ (Equiv.refl (Fin 4)) =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar382_eq389 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 382).expression.scalarPointContraction X v
      (L24Gluing.term 382).decoration (L24Gluing.term 382).labels beta n insertions =
    (L24Gluing.term 389).expression.scalarPointContraction X v
      (L24Gluing.term 389).decoration (L24Gluing.term 389).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core382 L24Gluing.term382.decoration L24Gluing.term382.labels
    (Equiv.refl (Fin 4)) L24Gluing.flagPermutation5 beta n insertions labels382_389

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded382_eq389 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 382) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 389) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 382) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 389) (by decide +kernel)]
  exact scalar382_eq389 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted389_eq382 : originalWeighted 389 =
    (1 / 1 : ℚ) * originalWeighted 382 := by
  rw [originalWeighted, originalWeighted, ← guarded382_eq389,
    coefficient389, coefficient382]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels382_396 :
    insertions ∘ (Equiv.refl (Fin 4)) =
      insertions ∘ L24Gluing.flagPermutation4 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar382_eq396 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 382).expression.scalarPointContraction X v
      (L24Gluing.term 382).decoration (L24Gluing.term 382).labels beta n insertions =
    (L24Gluing.term 396).expression.scalarPointContraction X v
      (L24Gluing.term 396).decoration (L24Gluing.term 396).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core382 L24Gluing.term382.decoration L24Gluing.term382.labels
    (Equiv.refl (Fin 4)) L24Gluing.flagPermutation4 beta n insertions labels382_396

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded382_eq396 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 382) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 396) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 382) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 396) (by decide +kernel)]
  exact scalar382_eq396 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted396_eq382 : originalWeighted 396 =
    (1 / 1 : ℚ) * originalWeighted 382 := by
  rw [originalWeighted, originalWeighted, ← guarded382_eq396,
    coefficient396, coefficient382]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels383_390 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar383_eq390 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 383).expression.scalarPointContraction X v
      (L24Gluing.term 383).decoration (L24Gluing.term 383).labels beta n insertions =
    (L24Gluing.term 390).expression.scalarPointContraction X v
      (L24Gluing.term 390).decoration (L24Gluing.term 390).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core383 L24Gluing.term383.decoration L24Gluing.term383.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels383_390

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded383_eq390 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 383) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 390) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 383) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 390) (by decide +kernel)]
  exact scalar383_eq390 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted390_eq383 : originalWeighted 390 =
    (2 / 3 : ℚ) * originalWeighted 383 := by
  rw [originalWeighted, originalWeighted, ← guarded383_eq390,
    coefficient390, coefficient383]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels383_397 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar383_eq397 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 383).expression.scalarPointContraction X v
      (L24Gluing.term 383).decoration (L24Gluing.term 383).labels beta n insertions =
    (L24Gluing.term 397).expression.scalarPointContraction X v
      (L24Gluing.term 397).decoration (L24Gluing.term 397).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core383 L24Gluing.term383.decoration L24Gluing.term383.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels383_397

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded383_eq397 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 383) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 397) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 383) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 397) (by decide +kernel)]
  exact scalar383_eq397 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted397_eq383 : originalWeighted 397 =
    (2 / 3 : ℚ) * originalWeighted 383 := by
  rw [originalWeighted, originalWeighted, ← guarded383_eq397,
    coefficient397, coefficient383]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels399_401 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation4 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar399_eq401 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 399).expression.scalarPointContraction X v
      (L24Gluing.term 399).decoration (L24Gluing.term 399).labels beta n insertions =
    (L24Gluing.term 401).expression.scalarPointContraction X v
      (L24Gluing.term 401).decoration (L24Gluing.term 401).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core399 L24Gluing.term399.decoration L24Gluing.term399.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation4 beta n insertions labels399_401

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded399_eq401 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 399) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 401) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 399) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 401) (by decide +kernel)]
  exact scalar399_eq401 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted401_eq399 : originalWeighted 401 =
    (5650 / 2561 : ℚ) * originalWeighted 399 := by
  rw [originalWeighted, originalWeighted, ← guarded399_eq401,
    coefficient401, coefficient399]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels399_404 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation6 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar399_eq404 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 399).expression.scalarPointContraction X v
      (L24Gluing.term 399).decoration (L24Gluing.term 399).labels beta n insertions =
    (L24Gluing.term 404).expression.scalarPointContraction X v
      (L24Gluing.term 404).decoration (L24Gluing.term 404).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core399 L24Gluing.term399.decoration L24Gluing.term399.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 beta n insertions labels399_404

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded399_eq404 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 399) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 404) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 399) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 404) (by decide +kernel)]
  exact scalar399_eq404 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted404_eq399 : originalWeighted 404 =
    (1 / 1 : ℚ) * originalWeighted 399 := by
  rw [originalWeighted, originalWeighted, ← guarded399_eq404,
    coefficient404, coefficient399]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels399_406 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar399_eq406 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 399).expression.scalarPointContraction X v
      (L24Gluing.term 399).decoration (L24Gluing.term 399).labels beta n insertions =
    (L24Gluing.term 406).expression.scalarPointContraction X v
      (L24Gluing.term 406).decoration (L24Gluing.term 406).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core399 L24Gluing.term399.decoration L24Gluing.term399.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation5 beta n insertions labels399_406

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded399_eq406 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 399) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 406) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 399) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 406) (by decide +kernel)]
  exact scalar399_eq406 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted406_eq399 : originalWeighted 406 =
    (5650 / 2561 : ℚ) * originalWeighted 399 := by
  rw [originalWeighted, originalWeighted, ← guarded399_eq406,
    coefficient406, coefficient399]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels399_410 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar399_eq410 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 399).expression.scalarPointContraction X v
      (L24Gluing.term 399).decoration (L24Gluing.term 399).labels beta n insertions =
    (L24Gluing.term 410).expression.scalarPointContraction X v
      (L24Gluing.term 410).decoration (L24Gluing.term 410).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core399 L24Gluing.term399.decoration L24Gluing.term399.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 beta n insertions labels399_410

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded399_eq410 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 399) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 410) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 399) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 410) (by decide +kernel)]
  exact scalar399_eq410 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted410_eq399 : originalWeighted 410 =
    (7054 / 7683 : ℚ) * originalWeighted 399 := by
  rw [originalWeighted, originalWeighted, ← guarded399_eq410,
    coefficient410, coefficient399]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels399_412 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar399_eq412 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 399).expression.scalarPointContraction X v
      (L24Gluing.term 399).decoration (L24Gluing.term 399).labels beta n insertions =
    (L24Gluing.term 412).expression.scalarPointContraction X v
      (L24Gluing.term 412).decoration (L24Gluing.term 412).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core399 L24Gluing.term399.decoration L24Gluing.term399.labels
    L24Gluing.flagPermutation10 (Equiv.refl (Fin 4)) beta n insertions labels399_412

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded399_eq412 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 399) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 412) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 399) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 412) (by decide +kernel)]
  exact scalar399_eq412 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted412_eq399 : originalWeighted 412 =
    (7054 / 7683 : ℚ) * originalWeighted 399 := by
  rw [originalWeighted, originalWeighted, ← guarded399_eq412,
    coefficient412, coefficient399]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels400_402 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation4 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar400_eq402 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 400).expression.scalarPointContraction X v
      (L24Gluing.term 400).decoration (L24Gluing.term 400).labels beta n insertions =
    (L24Gluing.term 402).expression.scalarPointContraction X v
      (L24Gluing.term 402).decoration (L24Gluing.term 402).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core400 L24Gluing.term400.decoration L24Gluing.term400.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation4 beta n insertions labels400_402

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded400_eq402 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 400) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 402) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 400) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 402) (by decide +kernel)]
  exact scalar400_eq402 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted402_eq400 : originalWeighted 402 =
    (2825 / 1833 : ℚ) * originalWeighted 400 := by
  rw [originalWeighted, originalWeighted, ← guarded400_eq402,
    coefficient402, coefficient400]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels400_405 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation6 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar400_eq405 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 400).expression.scalarPointContraction X v
      (L24Gluing.term 400).decoration (L24Gluing.term 400).labels beta n insertions =
    (L24Gluing.term 405).expression.scalarPointContraction X v
      (L24Gluing.term 405).decoration (L24Gluing.term 405).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core400 L24Gluing.term400.decoration L24Gluing.term400.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 beta n insertions labels400_405

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded400_eq405 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 400) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 405) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 400) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 405) (by decide +kernel)]
  exact scalar400_eq405 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted405_eq400 : originalWeighted 405 =
    (1 / 1 : ℚ) * originalWeighted 400 := by
  rw [originalWeighted, originalWeighted, ← guarded400_eq405,
    coefficient405, coefficient400]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels400_407 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar400_eq407 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 400).expression.scalarPointContraction X v
      (L24Gluing.term 400).decoration (L24Gluing.term 400).labels beta n insertions =
    (L24Gluing.term 407).expression.scalarPointContraction X v
      (L24Gluing.term 407).decoration (L24Gluing.term 407).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core400 L24Gluing.term400.decoration L24Gluing.term400.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation5 beta n insertions labels400_407

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded400_eq407 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 400) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 407) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 400) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 407) (by decide +kernel)]
  exact scalar400_eq407 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted407_eq400 : originalWeighted 407 =
    (2825 / 1833 : ℚ) * originalWeighted 400 := by
  rw [originalWeighted, originalWeighted, ← guarded400_eq407,
    coefficient407, coefficient400]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels400_411 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar400_eq411 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 400).expression.scalarPointContraction X v
      (L24Gluing.term 400).decoration (L24Gluing.term 400).labels beta n insertions =
    (L24Gluing.term 411).expression.scalarPointContraction X v
      (L24Gluing.term 411).decoration (L24Gluing.term 411).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core400 L24Gluing.term400.decoration L24Gluing.term400.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 beta n insertions labels400_411

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded400_eq411 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 400) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 411) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 400) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 411) (by decide +kernel)]
  exact scalar400_eq411 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted411_eq400 : originalWeighted 411 =
    (17423 / 21996 : ℚ) * originalWeighted 400 := by
  rw [originalWeighted, originalWeighted, ← guarded400_eq411,
    coefficient411, coefficient400]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels400_413 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar400_eq413 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 400).expression.scalarPointContraction X v
      (L24Gluing.term 400).decoration (L24Gluing.term 400).labels beta n insertions =
    (L24Gluing.term 413).expression.scalarPointContraction X v
      (L24Gluing.term 413).decoration (L24Gluing.term 413).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core400 L24Gluing.term400.decoration L24Gluing.term400.labels
    L24Gluing.flagPermutation10 (Equiv.refl (Fin 4)) beta n insertions labels400_413

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded400_eq413 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 400) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 413) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 400) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 413) (by decide +kernel)]
  exact scalar400_eq413 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted413_eq400 : originalWeighted 413 =
    (17423 / 21996 : ℚ) * originalWeighted 400 := by
  rw [originalWeighted, originalWeighted, ← guarded400_eq413,
    coefficient413, coefficient400]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels403_408 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar403_eq408 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 403).expression.scalarPointContraction X v
      (L24Gluing.term 403).decoration (L24Gluing.term 403).labels beta n insertions =
    (L24Gluing.term 408).expression.scalarPointContraction X v
      (L24Gluing.term 408).decoration (L24Gluing.term 408).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core403 L24Gluing.term403.decoration L24Gluing.term403.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels403_408

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded403_eq408 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 403) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 408) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 403) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 408) (by decide +kernel)]
  exact scalar403_eq408 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted408_eq403 : originalWeighted 408 =
    (1 / 1 : ℚ) * originalWeighted 403 := by
  rw [originalWeighted, originalWeighted, ← guarded403_eq408,
    coefficient408, coefficient403]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels403_414 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar403_eq414 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 403).expression.scalarPointContraction X v
      (L24Gluing.term 403).decoration (L24Gluing.term 403).labels beta n insertions =
    (L24Gluing.term 414).expression.scalarPointContraction X v
      (L24Gluing.term 414).decoration (L24Gluing.term 414).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core403 L24Gluing.term403.decoration L24Gluing.term403.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels403_414

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded403_eq414 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 403) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 414) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 403) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 414) (by decide +kernel)]
  exact scalar403_eq414 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted414_eq403 : originalWeighted 414 =
    (2 / 3 : ℚ) * originalWeighted 403 := by
  rw [originalWeighted, originalWeighted, ← guarded403_eq414,
    coefficient414, coefficient403]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels409_415 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar409_eq415 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 409).expression.scalarPointContraction X v
      (L24Gluing.term 409).decoration (L24Gluing.term 409).labels beta n insertions =
    (L24Gluing.term 415).expression.scalarPointContraction X v
      (L24Gluing.term 415).decoration (L24Gluing.term 415).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core409 L24Gluing.term409.decoration L24Gluing.term409.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels409_415

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded409_eq415 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 409) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 415) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 409) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 415) (by decide +kernel)]
  exact scalar409_eq415 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted415_eq409 : originalWeighted 415 =
    (421 / 1017 : ℚ) * originalWeighted 409 := by
  rw [originalWeighted, originalWeighted, ← guarded409_eq415,
    coefficient415, coefficient409]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels409_416 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar409_eq416 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 409).expression.scalarPointContraction X v
      (L24Gluing.term 409).decoration (L24Gluing.term 409).labels beta n insertions =
    (L24Gluing.term 416).expression.scalarPointContraction X v
      (L24Gluing.term 416).decoration (L24Gluing.term 416).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core409 L24Gluing.term409.decoration L24Gluing.term409.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels409_416

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded409_eq416 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 409) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 416) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 409) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 416) (by decide +kernel)]
  exact scalar409_eq416 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted416_eq409 : originalWeighted 416 =
    (421 / 1017 : ℚ) * originalWeighted 409 := by
  rw [originalWeighted, originalWeighted, ← guarded409_eq416,
    coefficient416, coefficient409]
  ring

end AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06

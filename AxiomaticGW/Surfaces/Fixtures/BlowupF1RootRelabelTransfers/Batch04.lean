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

namespace AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04

open BlowupF1RootAssembly SurfaceGenusTwo GetzlerGraphs L24Gluing

private def core298 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core299 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core304 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core305 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core306 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core307 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core323 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 1) (n := 2) 1 1
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core324 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 1) (n := 2) 1 1
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core325 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 1) (n := 2) 1 1
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core329 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core330 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

theorem coefficient298 : L24CorrectionsReplay.fullClaim 298 =
    (3 / 5 : ℚ) := by decide +kernel

theorem coefficient299 : L24CorrectionsReplay.fullClaim 299 =
    (1 / 3 : ℚ) := by decide +kernel

theorem coefficient303 : L24CorrectionsReplay.fullClaim 303 =
    (1 / 3 : ℚ) := by decide +kernel

theorem coefficient304 : L24CorrectionsReplay.fullClaim 304 =
    (-1 / 15 : ℚ) := by decide +kernel

theorem coefficient305 : L24CorrectionsReplay.fullClaim 305 =
    (-1 / 15 : ℚ) := by decide +kernel

theorem coefficient306 : L24CorrectionsReplay.fullClaim 306 =
    (-1 / 15 : ℚ) := by decide +kernel

theorem coefficient307 : L24CorrectionsReplay.fullClaim 307 =
    (-3 / 5 : ℚ) := by decide +kernel

theorem coefficient309 : L24CorrectionsReplay.fullClaim 309 =
    (2 / 15 : ℚ) := by decide +kernel

theorem coefficient310 : L24CorrectionsReplay.fullClaim 310 =
    (2 / 15 : ℚ) := by decide +kernel

theorem coefficient311 : L24CorrectionsReplay.fullClaim 311 =
    (1 / 15 : ℚ) := by decide +kernel

theorem coefficient312 : L24CorrectionsReplay.fullClaim 312 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient313 : L24CorrectionsReplay.fullClaim 313 =
    (1 / 15 : ℚ) := by decide +kernel

theorem coefficient314 : L24CorrectionsReplay.fullClaim 314 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient315 : L24CorrectionsReplay.fullClaim 315 =
    (1 / 15 : ℚ) := by decide +kernel

theorem coefficient316 : L24CorrectionsReplay.fullClaim 316 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient317 : L24CorrectionsReplay.fullClaim 317 =
    (1 / 15 : ℚ) := by decide +kernel

theorem coefficient318 : L24CorrectionsReplay.fullClaim 318 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient323 : L24CorrectionsReplay.fullClaim 323 =
    (-1 / 3 : ℚ) := by decide +kernel

theorem coefficient324 : L24CorrectionsReplay.fullClaim 324 =
    (1 / 3 : ℚ) := by decide +kernel

theorem coefficient325 : L24CorrectionsReplay.fullClaim 325 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient326 : L24CorrectionsReplay.fullClaim 326 =
    (-8 / 15 : ℚ) := by decide +kernel

theorem coefficient327 : L24CorrectionsReplay.fullClaim 327 =
    (2 / 15 : ℚ) := by decide +kernel

theorem coefficient328 : L24CorrectionsReplay.fullClaim 328 =
    (2 / 15 : ℚ) := by decide +kernel

theorem coefficient329 : L24CorrectionsReplay.fullClaim 329 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient330 : L24CorrectionsReplay.fullClaim 330 =
    (-1 / 1 : ℚ) := by decide +kernel

theorem coefficient344 : L24CorrectionsReplay.fullClaim 344 =
    (-1 / 3 : ℚ) := by decide +kernel

theorem coefficient345 : L24CorrectionsReplay.fullClaim 345 =
    (1 / 3 : ℚ) := by decide +kernel

theorem coefficient346 : L24CorrectionsReplay.fullClaim 346 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient347 : L24CorrectionsReplay.fullClaim 347 =
    (-8 / 15 : ℚ) := by decide +kernel

theorem coefficient348 : L24CorrectionsReplay.fullClaim 348 =
    (2 / 15 : ℚ) := by decide +kernel

theorem coefficient349 : L24CorrectionsReplay.fullClaim 349 =
    (2 / 15 : ℚ) := by decide +kernel

theorem coefficient350 : L24CorrectionsReplay.fullClaim 350 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient351 : L24CorrectionsReplay.fullClaim 351 =
    (-1 / 1 : ℚ) := by decide +kernel

theorem coefficient365 : L24CorrectionsReplay.fullClaim 365 =
    (-6 / 5 : ℚ) := by decide +kernel

theorem coefficient366 : L24CorrectionsReplay.fullClaim 366 =
    (-6 / 5 : ℚ) := by decide +kernel

theorem coefficient367 : L24CorrectionsReplay.fullClaim 367 =
    (-7 / 5 : ℚ) := by decide +kernel

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels298_309 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar298_eq309 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 298).expression.scalarPointContraction X v
      (L24Gluing.term 298).decoration (L24Gluing.term 298).labels beta n insertions =
    (L24Gluing.term 309).expression.scalarPointContraction X v
      (L24Gluing.term 309).decoration (L24Gluing.term 309).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core298 L24Gluing.term298.decoration L24Gluing.term298.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels298_309

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded298_eq309 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 298) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 309) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 298) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 309) (by decide +kernel)]
  exact scalar298_eq309 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted309_eq298 : originalWeighted 309 =
    (2 / 9 : ℚ) * originalWeighted 298 := by
  rw [originalWeighted, originalWeighted, ← guarded298_eq309,
    coefficient309, coefficient298]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels299_303 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar299_eq303 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 299).expression.scalarPointContraction X v
      (L24Gluing.term 299).decoration (L24Gluing.term 299).labels beta n insertions =
    (L24Gluing.term 303).expression.scalarPointContraction X v
      (L24Gluing.term 303).decoration (L24Gluing.term 303).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core299 L24Gluing.term299.decoration L24Gluing.term299.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels299_303

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded299_eq303 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 299) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 303) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 299) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 303) (by decide +kernel)]
  exact scalar299_eq303 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted303_eq299 : originalWeighted 303 =
    (1 / 1 : ℚ) * originalWeighted 299 := by
  rw [originalWeighted, originalWeighted, ← guarded299_eq303,
    coefficient303, coefficient299]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels299_310 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar299_eq310 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 299).expression.scalarPointContraction X v
      (L24Gluing.term 299).decoration (L24Gluing.term 299).labels beta n insertions =
    (L24Gluing.term 310).expression.scalarPointContraction X v
      (L24Gluing.term 310).decoration (L24Gluing.term 310).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core299 L24Gluing.term299.decoration L24Gluing.term299.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels299_310

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded299_eq310 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 299) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 310) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 299) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 310) (by decide +kernel)]
  exact scalar299_eq310 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted310_eq299 : originalWeighted 310 =
    (2 / 5 : ℚ) * originalWeighted 299 := by
  rw [originalWeighted, originalWeighted, ← guarded299_eq310,
    coefficient310, coefficient299]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels304_311 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar304_eq311 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 304).expression.scalarPointContraction X v
      (L24Gluing.term 304).decoration (L24Gluing.term 304).labels beta n insertions =
    (L24Gluing.term 311).expression.scalarPointContraction X v
      (L24Gluing.term 311).decoration (L24Gluing.term 311).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core304 L24Gluing.term304.decoration L24Gluing.term304.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels304_311

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded304_eq311 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 304) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 311) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 304) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 311) (by decide +kernel)]
  exact scalar304_eq311 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted311_eq304 : originalWeighted 311 =
    (-1 / 1 : ℚ) * originalWeighted 304 := by
  rw [originalWeighted, originalWeighted, ← guarded304_eq311,
    coefficient311, coefficient304]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels304_315 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar304_eq315 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 304).expression.scalarPointContraction X v
      (L24Gluing.term 304).decoration (L24Gluing.term 304).labels beta n insertions =
    (L24Gluing.term 315).expression.scalarPointContraction X v
      (L24Gluing.term 315).decoration (L24Gluing.term 315).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core304 L24Gluing.term304.decoration L24Gluing.term304.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels304_315

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded304_eq315 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 304) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 315) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 304) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 315) (by decide +kernel)]
  exact scalar304_eq315 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted315_eq304 : originalWeighted 315 =
    (-1 / 1 : ℚ) * originalWeighted 304 := by
  rw [originalWeighted, originalWeighted, ← guarded304_eq315,
    coefficient315, coefficient304]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels305_312 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar305_eq312 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 305).expression.scalarPointContraction X v
      (L24Gluing.term 305).decoration (L24Gluing.term 305).labels beta n insertions =
    (L24Gluing.term 312).expression.scalarPointContraction X v
      (L24Gluing.term 312).decoration (L24Gluing.term 312).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core305 L24Gluing.term305.decoration L24Gluing.term305.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels305_312

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded305_eq312 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 305) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 312) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 305) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 312) (by decide +kernel)]
  exact scalar305_eq312 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted312_eq305 : originalWeighted 312 =
    (3 / 1 : ℚ) * originalWeighted 305 := by
  rw [originalWeighted, originalWeighted, ← guarded305_eq312,
    coefficient312, coefficient305]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels305_316 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar305_eq316 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 305).expression.scalarPointContraction X v
      (L24Gluing.term 305).decoration (L24Gluing.term 305).labels beta n insertions =
    (L24Gluing.term 316).expression.scalarPointContraction X v
      (L24Gluing.term 316).decoration (L24Gluing.term 316).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core305 L24Gluing.term305.decoration L24Gluing.term305.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels305_316

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded305_eq316 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 305) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 316) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 305) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 316) (by decide +kernel)]
  exact scalar305_eq316 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted316_eq305 : originalWeighted 316 =
    (3 / 1 : ℚ) * originalWeighted 305 := by
  rw [originalWeighted, originalWeighted, ← guarded305_eq316,
    coefficient316, coefficient305]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels306_313 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar306_eq313 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 306).expression.scalarPointContraction X v
      (L24Gluing.term 306).decoration (L24Gluing.term 306).labels beta n insertions =
    (L24Gluing.term 313).expression.scalarPointContraction X v
      (L24Gluing.term 313).decoration (L24Gluing.term 313).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core306 L24Gluing.term306.decoration L24Gluing.term306.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels306_313

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded306_eq313 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 306) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 313) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 306) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 313) (by decide +kernel)]
  exact scalar306_eq313 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted313_eq306 : originalWeighted 313 =
    (-1 / 1 : ℚ) * originalWeighted 306 := by
  rw [originalWeighted, originalWeighted, ← guarded306_eq313,
    coefficient313, coefficient306]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels306_317 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar306_eq317 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 306).expression.scalarPointContraction X v
      (L24Gluing.term 306).decoration (L24Gluing.term 306).labels beta n insertions =
    (L24Gluing.term 317).expression.scalarPointContraction X v
      (L24Gluing.term 317).decoration (L24Gluing.term 317).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core306 L24Gluing.term306.decoration L24Gluing.term306.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels306_317

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded306_eq317 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 306) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 317) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 306) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 317) (by decide +kernel)]
  exact scalar306_eq317 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted317_eq306 : originalWeighted 317 =
    (-1 / 1 : ℚ) * originalWeighted 306 := by
  rw [originalWeighted, originalWeighted, ← guarded306_eq317,
    coefficient317, coefficient306]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels307_314 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar307_eq314 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 307).expression.scalarPointContraction X v
      (L24Gluing.term 307).decoration (L24Gluing.term 307).labels beta n insertions =
    (L24Gluing.term 314).expression.scalarPointContraction X v
      (L24Gluing.term 314).decoration (L24Gluing.term 314).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core307 L24Gluing.term307.decoration L24Gluing.term307.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels307_314

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded307_eq314 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 307) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 314) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 307) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 314) (by decide +kernel)]
  exact scalar307_eq314 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted314_eq307 : originalWeighted 314 =
    (1 / 3 : ℚ) * originalWeighted 307 := by
  rw [originalWeighted, originalWeighted, ← guarded307_eq314,
    coefficient314, coefficient307]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels307_318 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar307_eq318 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 307).expression.scalarPointContraction X v
      (L24Gluing.term 307).decoration (L24Gluing.term 307).labels beta n insertions =
    (L24Gluing.term 318).expression.scalarPointContraction X v
      (L24Gluing.term 318).decoration (L24Gluing.term 318).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core307 L24Gluing.term307.decoration L24Gluing.term307.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels307_318

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded307_eq318 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 307) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 318) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 307) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 318) (by decide +kernel)]
  exact scalar307_eq318 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted318_eq307 : originalWeighted 318 =
    (1 / 3 : ℚ) * originalWeighted 307 := by
  rw [originalWeighted, originalWeighted, ← guarded307_eq318,
    coefficient318, coefficient307]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels323_326 :
    insertions ∘ L24Gluing.flagPermutation18 =
      insertions ∘ L24Gluing.flagPermutation19 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar323_eq326 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 323).expression.scalarPointContraction X v
      (L24Gluing.term 323).decoration (L24Gluing.term 323).labels beta n insertions =
    (L24Gluing.term 326).expression.scalarPointContraction X v
      (L24Gluing.term 326).decoration (L24Gluing.term 326).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core323 L24Gluing.term323.decoration L24Gluing.term323.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation19 beta n insertions labels323_326

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded323_eq326 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 323) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 326) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 323) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 326) (by decide +kernel)]
  exact scalar323_eq326 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted326_eq323 : originalWeighted 326 =
    (8 / 5 : ℚ) * originalWeighted 323 := by
  rw [originalWeighted, originalWeighted, ← guarded323_eq326,
    coefficient326, coefficient323]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels323_344 :
    insertions ∘ L24Gluing.flagPermutation18 =
      insertions ∘ L24Gluing.flagPermutation0 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar323_eq344 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 323).expression.scalarPointContraction X v
      (L24Gluing.term 323).decoration (L24Gluing.term 323).labels beta n insertions =
    (L24Gluing.term 344).expression.scalarPointContraction X v
      (L24Gluing.term 344).decoration (L24Gluing.term 344).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core323 L24Gluing.term323.decoration L24Gluing.term323.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation0 beta n insertions labels323_344

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded323_eq344 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 323) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 344) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 323) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 344) (by decide +kernel)]
  exact scalar323_eq344 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted344_eq323 : originalWeighted 344 =
    (1 / 1 : ℚ) * originalWeighted 323 := by
  rw [originalWeighted, originalWeighted, ← guarded323_eq344,
    coefficient344, coefficient323]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels323_347 :
    insertions ∘ L24Gluing.flagPermutation18 =
      insertions ∘ L24Gluing.flagPermutation20 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar323_eq347 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 323).expression.scalarPointContraction X v
      (L24Gluing.term 323).decoration (L24Gluing.term 323).labels beta n insertions =
    (L24Gluing.term 347).expression.scalarPointContraction X v
      (L24Gluing.term 347).decoration (L24Gluing.term 347).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core323 L24Gluing.term323.decoration L24Gluing.term323.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation20 beta n insertions labels323_347

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded323_eq347 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 323) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 347) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 323) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 347) (by decide +kernel)]
  exact scalar323_eq347 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted347_eq323 : originalWeighted 347 =
    (8 / 5 : ℚ) * originalWeighted 323 := by
  rw [originalWeighted, originalWeighted, ← guarded323_eq347,
    coefficient347, coefficient323]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels323_365 :
    insertions ∘ L24Gluing.flagPermutation18 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar323_eq365 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 323).expression.scalarPointContraction X v
      (L24Gluing.term 323).decoration (L24Gluing.term 323).labels beta n insertions =
    (L24Gluing.term 365).expression.scalarPointContraction X v
      (L24Gluing.term 365).decoration (L24Gluing.term 365).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core323 L24Gluing.term323.decoration L24Gluing.term323.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation1 beta n insertions labels323_365

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded323_eq365 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 323) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 365) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 323) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 365) (by decide +kernel)]
  exact scalar323_eq365 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted365_eq323 : originalWeighted 365 =
    (18 / 5 : ℚ) * originalWeighted 323 := by
  rw [originalWeighted, originalWeighted, ← guarded323_eq365,
    coefficient365, coefficient323]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels323_366 :
    insertions ∘ L24Gluing.flagPermutation18 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar323_eq366 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 323).expression.scalarPointContraction X v
      (L24Gluing.term 323).decoration (L24Gluing.term 323).labels beta n insertions =
    (L24Gluing.term 366).expression.scalarPointContraction X v
      (L24Gluing.term 366).decoration (L24Gluing.term 366).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core323 L24Gluing.term323.decoration L24Gluing.term323.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation2 beta n insertions labels323_366

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded323_eq366 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 323) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 366) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 323) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 366) (by decide +kernel)]
  exact scalar323_eq366 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted366_eq323 : originalWeighted 366 =
    (18 / 5 : ℚ) * originalWeighted 323 := by
  rw [originalWeighted, originalWeighted, ← guarded323_eq366,
    coefficient366, coefficient323]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels324_327 :
    insertions ∘ L24Gluing.flagPermutation18 =
      insertions ∘ L24Gluing.flagPermutation19 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar324_eq327 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 324).expression.scalarPointContraction X v
      (L24Gluing.term 324).decoration (L24Gluing.term 324).labels beta n insertions =
    (L24Gluing.term 327).expression.scalarPointContraction X v
      (L24Gluing.term 327).decoration (L24Gluing.term 327).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core324 L24Gluing.term324.decoration L24Gluing.term324.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation19 beta n insertions labels324_327

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded324_eq327 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 324) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 327) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 324) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 327) (by decide +kernel)]
  exact scalar324_eq327 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted327_eq324 : originalWeighted 327 =
    (2 / 5 : ℚ) * originalWeighted 324 := by
  rw [originalWeighted, originalWeighted, ← guarded324_eq327,
    coefficient327, coefficient324]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels324_345 :
    insertions ∘ L24Gluing.flagPermutation18 =
      insertions ∘ L24Gluing.flagPermutation0 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar324_eq345 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 324).expression.scalarPointContraction X v
      (L24Gluing.term 324).decoration (L24Gluing.term 324).labels beta n insertions =
    (L24Gluing.term 345).expression.scalarPointContraction X v
      (L24Gluing.term 345).decoration (L24Gluing.term 345).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core324 L24Gluing.term324.decoration L24Gluing.term324.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation0 beta n insertions labels324_345

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded324_eq345 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 324) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 345) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 324) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 345) (by decide +kernel)]
  exact scalar324_eq345 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted345_eq324 : originalWeighted 345 =
    (1 / 1 : ℚ) * originalWeighted 324 := by
  rw [originalWeighted, originalWeighted, ← guarded324_eq345,
    coefficient345, coefficient324]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels324_348 :
    insertions ∘ L24Gluing.flagPermutation18 =
      insertions ∘ L24Gluing.flagPermutation20 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar324_eq348 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 324).expression.scalarPointContraction X v
      (L24Gluing.term 324).decoration (L24Gluing.term 324).labels beta n insertions =
    (L24Gluing.term 348).expression.scalarPointContraction X v
      (L24Gluing.term 348).decoration (L24Gluing.term 348).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core324 L24Gluing.term324.decoration L24Gluing.term324.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation20 beta n insertions labels324_348

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded324_eq348 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 324) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 348) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 324) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 348) (by decide +kernel)]
  exact scalar324_eq348 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted348_eq324 : originalWeighted 348 =
    (2 / 5 : ℚ) * originalWeighted 324 := by
  rw [originalWeighted, originalWeighted, ← guarded324_eq348,
    coefficient348, coefficient324]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels325_328 :
    insertions ∘ L24Gluing.flagPermutation18 =
      insertions ∘ L24Gluing.flagPermutation19 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar325_eq328 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 325).expression.scalarPointContraction X v
      (L24Gluing.term 325).decoration (L24Gluing.term 325).labels beta n insertions =
    (L24Gluing.term 328).expression.scalarPointContraction X v
      (L24Gluing.term 328).decoration (L24Gluing.term 328).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core325 L24Gluing.term325.decoration L24Gluing.term325.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation19 beta n insertions labels325_328

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded325_eq328 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 325) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 328) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 325) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 328) (by decide +kernel)]
  exact scalar325_eq328 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted328_eq325 : originalWeighted 328 =
    (-2 / 3 : ℚ) * originalWeighted 325 := by
  rw [originalWeighted, originalWeighted, ← guarded325_eq328,
    coefficient328, coefficient325]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels325_346 :
    insertions ∘ L24Gluing.flagPermutation18 =
      insertions ∘ L24Gluing.flagPermutation0 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar325_eq346 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 325).expression.scalarPointContraction X v
      (L24Gluing.term 325).decoration (L24Gluing.term 325).labels beta n insertions =
    (L24Gluing.term 346).expression.scalarPointContraction X v
      (L24Gluing.term 346).decoration (L24Gluing.term 346).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core325 L24Gluing.term325.decoration L24Gluing.term325.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation0 beta n insertions labels325_346

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded325_eq346 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 325) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 346) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 325) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 346) (by decide +kernel)]
  exact scalar325_eq346 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted346_eq325 : originalWeighted 346 =
    (1 / 1 : ℚ) * originalWeighted 325 := by
  rw [originalWeighted, originalWeighted, ← guarded325_eq346,
    coefficient346, coefficient325]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels325_349 :
    insertions ∘ L24Gluing.flagPermutation18 =
      insertions ∘ L24Gluing.flagPermutation20 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar325_eq349 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 325).expression.scalarPointContraction X v
      (L24Gluing.term 325).decoration (L24Gluing.term 325).labels beta n insertions =
    (L24Gluing.term 349).expression.scalarPointContraction X v
      (L24Gluing.term 349).decoration (L24Gluing.term 349).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core325 L24Gluing.term325.decoration L24Gluing.term325.labels
    L24Gluing.flagPermutation18 L24Gluing.flagPermutation20 beta n insertions labels325_349

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded325_eq349 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 325) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 349) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 325) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 349) (by decide +kernel)]
  exact scalar325_eq349 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted349_eq325 : originalWeighted 349 =
    (-2 / 3 : ℚ) * originalWeighted 325 := by
  rw [originalWeighted, originalWeighted, ← guarded325_eq349,
    coefficient349, coefficient325]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels329_350 :
    insertions ∘ L24Gluing.flagPermutation12 =
      insertions ∘ L24Gluing.flagPermutation11 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar329_eq350 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 329).expression.scalarPointContraction X v
      (L24Gluing.term 329).decoration (L24Gluing.term 329).labels beta n insertions =
    (L24Gluing.term 350).expression.scalarPointContraction X v
      (L24Gluing.term 350).decoration (L24Gluing.term 350).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core329 L24Gluing.term329.decoration L24Gluing.term329.labels
    L24Gluing.flagPermutation12 L24Gluing.flagPermutation11 beta n insertions labels329_350

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded329_eq350 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 329) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 350) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 329) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 350) (by decide +kernel)]
  exact scalar329_eq350 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted350_eq329 : originalWeighted 350 =
    (1 / 1 : ℚ) * originalWeighted 329 := by
  rw [originalWeighted, originalWeighted, ← guarded329_eq350,
    coefficient350, coefficient329]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels329_367 :
    insertions ∘ L24Gluing.flagPermutation12 =
      insertions ∘ L24Gluing.flagPermutation3 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar329_eq367 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 329).expression.scalarPointContraction X v
      (L24Gluing.term 329).decoration (L24Gluing.term 329).labels beta n insertions =
    (L24Gluing.term 367).expression.scalarPointContraction X v
      (L24Gluing.term 367).decoration (L24Gluing.term 367).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core329 L24Gluing.term329.decoration L24Gluing.term329.labels
    L24Gluing.flagPermutation12 L24Gluing.flagPermutation3 beta n insertions labels329_367

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded329_eq367 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 329) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 367) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 329) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 367) (by decide +kernel)]
  exact scalar329_eq367 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted367_eq329 : originalWeighted 367 =
    (7 / 1 : ℚ) * originalWeighted 329 := by
  rw [originalWeighted, originalWeighted, ← guarded329_eq367,
    coefficient367, coefficient329]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels330_351 :
    insertions ∘ L24Gluing.flagPermutation12 =
      insertions ∘ L24Gluing.flagPermutation11 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar330_eq351 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 330).expression.scalarPointContraction X v
      (L24Gluing.term 330).decoration (L24Gluing.term 330).labels beta n insertions =
    (L24Gluing.term 351).expression.scalarPointContraction X v
      (L24Gluing.term 351).decoration (L24Gluing.term 351).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core330 L24Gluing.term330.decoration L24Gluing.term330.labels
    L24Gluing.flagPermutation12 L24Gluing.flagPermutation11 beta n insertions labels330_351

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded330_eq351 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 330) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 351) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 330) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 351) (by decide +kernel)]
  exact scalar330_eq351 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted351_eq330 : originalWeighted 351 =
    (1 / 1 : ℚ) * originalWeighted 330 := by
  rw [originalWeighted, originalWeighted, ← guarded330_eq351,
    coefficient351, coefficient330]
  ring

end AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04

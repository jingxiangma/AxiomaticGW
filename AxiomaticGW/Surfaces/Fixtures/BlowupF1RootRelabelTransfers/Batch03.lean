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

namespace AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03

open BlowupF1RootAssembly SurfaceGenusTwo GetzlerGraphs L24Gluing

private def core225 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

private def core226 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core228 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core229 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core230 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core231 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core232 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 3) (n := 1) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core276 : GluingExpression 2 (Fin 4) :=
  join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]))

private def core279 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core280 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core281 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core296 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core297 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core298 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

theorem coefficient225 : L24CorrectionsReplay.fullClaim 225 =
    (-745 / 117 : ℚ) := by decide +kernel

theorem coefficient226 : L24CorrectionsReplay.fullClaim 226 =
    (1 / 10 : ℚ) := by decide +kernel

theorem coefficient228 : L24CorrectionsReplay.fullClaim 228 =
    (1 / 10 : ℚ) := by decide +kernel

theorem coefficient229 : L24CorrectionsReplay.fullClaim 229 =
    (407 / 120 : ℚ) := by decide +kernel

theorem coefficient230 : L24CorrectionsReplay.fullClaim 230 =
    (-953 / 1768 : ℚ) := by decide +kernel

theorem coefficient231 : L24CorrectionsReplay.fullClaim 231 =
    (4637 / 936 : ℚ) := by decide +kernel

theorem coefficient232 : L24CorrectionsReplay.fullClaim 232 =
    (7 / 936 : ℚ) := by decide +kernel

theorem coefficient254 : L24CorrectionsReplay.fullClaim 254 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient255 : L24CorrectionsReplay.fullClaim 255 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient256 : L24CorrectionsReplay.fullClaim 256 =
    (407 / 270 : ℚ) := by decide +kernel

theorem coefficient257 : L24CorrectionsReplay.fullClaim 257 =
    (-2203 / 11934 : ℚ) := by decide +kernel

theorem coefficient258 : L24CorrectionsReplay.fullClaim 258 =
    (4327 / 2106 : ℚ) := by decide +kernel

theorem coefficient259 : L24CorrectionsReplay.fullClaim 259 =
    (-133 / 2106 : ℚ) := by decide +kernel

theorem coefficient265 : L24CorrectionsReplay.fullClaim 265 =
    (-3050 / 1053 : ℚ) := by decide +kernel

theorem coefficient266 : L24CorrectionsReplay.fullClaim 266 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient267 : L24CorrectionsReplay.fullClaim 267 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient268 : L24CorrectionsReplay.fullClaim 268 =
    (407 / 270 : ℚ) := by decide +kernel

theorem coefficient269 : L24CorrectionsReplay.fullClaim 269 =
    (-2203 / 11934 : ℚ) := by decide +kernel

theorem coefficient270 : L24CorrectionsReplay.fullClaim 270 =
    (4327 / 2106 : ℚ) := by decide +kernel

theorem coefficient271 : L24CorrectionsReplay.fullClaim 271 =
    (-133 / 2106 : ℚ) := by decide +kernel

theorem coefficient276 : L24CorrectionsReplay.fullClaim 276 =
    (4 / 5 : ℚ) := by decide +kernel

theorem coefficient277 : L24CorrectionsReplay.fullClaim 277 =
    (4 / 5 : ℚ) := by decide +kernel

theorem coefficient279 : L24CorrectionsReplay.fullClaim 279 =
    (-1 / 15 : ℚ) := by decide +kernel

theorem coefficient280 : L24CorrectionsReplay.fullClaim 280 =
    (1 / 3 : ℚ) := by decide +kernel

theorem coefficient281 : L24CorrectionsReplay.fullClaim 281 =
    (3 / 5 : ℚ) := by decide +kernel

theorem coefficient283 : L24CorrectionsReplay.fullClaim 283 =
    (2 / 15 : ℚ) := by decide +kernel

theorem coefficient285 : L24CorrectionsReplay.fullClaim 285 =
    (-4 / 15 : ℚ) := by decide +kernel

theorem coefficient286 : L24CorrectionsReplay.fullClaim 286 =
    (2 / 15 : ℚ) := by decide +kernel

theorem coefficient287 : L24CorrectionsReplay.fullClaim 287 =
    (2 / 15 : ℚ) := by decide +kernel

theorem coefficient288 : L24CorrectionsReplay.fullClaim 288 =
    (-4 / 15 : ℚ) := by decide +kernel

theorem coefficient289 : L24CorrectionsReplay.fullClaim 289 =
    (2 / 15 : ℚ) := by decide +kernel

theorem coefficient290 : L24CorrectionsReplay.fullClaim 290 =
    (2 / 15 : ℚ) := by decide +kernel

theorem coefficient296 : L24CorrectionsReplay.fullClaim 296 =
    (-1 / 15 : ℚ) := by decide +kernel

theorem coefficient297 : L24CorrectionsReplay.fullClaim 297 =
    (-1 / 15 : ℚ) := by decide +kernel

theorem coefficient298 : L24CorrectionsReplay.fullClaim 298 =
    (3 / 5 : ℚ) := by decide +kernel

theorem coefficient300 : L24CorrectionsReplay.fullClaim 300 =
    (-1 / 15 : ℚ) := by decide +kernel

theorem coefficient301 : L24CorrectionsReplay.fullClaim 301 =
    (-1 / 15 : ℚ) := by decide +kernel

theorem coefficient302 : L24CorrectionsReplay.fullClaim 302 =
    (3 / 5 : ℚ) := by decide +kernel

theorem coefficient308 : L24CorrectionsReplay.fullClaim 308 =
    (-4 / 15 : ℚ) := by decide +kernel

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels225_265 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar225_eq265 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 225).expression.scalarPointContraction X v
      (L24Gluing.term 225).decoration (L24Gluing.term 225).labels beta n insertions =
    (L24Gluing.term 265).expression.scalarPointContraction X v
      (L24Gluing.term 265).decoration (L24Gluing.term 265).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core225 L24Gluing.term225.decoration L24Gluing.term225.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels225_265

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded225_eq265 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 225) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 265) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 225) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 265) (by decide +kernel)]
  exact scalar225_eq265 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted265_eq225 : originalWeighted 265 =
    (610 / 1341 : ℚ) * originalWeighted 225 := by
  rw [originalWeighted, originalWeighted, ← guarded225_eq265,
    coefficient265, coefficient225]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels226_254 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar226_eq254 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 226).expression.scalarPointContraction X v
      (L24Gluing.term 226).decoration (L24Gluing.term 226).labels beta n insertions =
    (L24Gluing.term 254).expression.scalarPointContraction X v
      (L24Gluing.term 254).decoration (L24Gluing.term 254).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core226 L24Gluing.term226.decoration L24Gluing.term226.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels226_254

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded226_eq254 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 226) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 254) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 226) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 254) (by decide +kernel)]
  exact scalar226_eq254 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted254_eq226 : originalWeighted 254 =
    (-2 / 1 : ℚ) * originalWeighted 226 := by
  rw [originalWeighted, originalWeighted, ← guarded226_eq254,
    coefficient254, coefficient226]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels226_266 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar226_eq266 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 226).expression.scalarPointContraction X v
      (L24Gluing.term 226).decoration (L24Gluing.term 226).labels beta n insertions =
    (L24Gluing.term 266).expression.scalarPointContraction X v
      (L24Gluing.term 266).decoration (L24Gluing.term 266).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core226 L24Gluing.term226.decoration L24Gluing.term226.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels226_266

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded226_eq266 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 226) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 266) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 226) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 266) (by decide +kernel)]
  exact scalar226_eq266 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted266_eq226 : originalWeighted 266 =
    (-2 / 1 : ℚ) * originalWeighted 226 := by
  rw [originalWeighted, originalWeighted, ← guarded226_eq266,
    coefficient266, coefficient226]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels228_255 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar228_eq255 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 228).expression.scalarPointContraction X v
      (L24Gluing.term 228).decoration (L24Gluing.term 228).labels beta n insertions =
    (L24Gluing.term 255).expression.scalarPointContraction X v
      (L24Gluing.term 255).decoration (L24Gluing.term 255).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core228 L24Gluing.term228.decoration L24Gluing.term228.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels228_255

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded228_eq255 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 228) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 255) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 228) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 255) (by decide +kernel)]
  exact scalar228_eq255 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted255_eq228 : originalWeighted 255 =
    (-2 / 1 : ℚ) * originalWeighted 228 := by
  rw [originalWeighted, originalWeighted, ← guarded228_eq255,
    coefficient255, coefficient228]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels228_267 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar228_eq267 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 228).expression.scalarPointContraction X v
      (L24Gluing.term 228).decoration (L24Gluing.term 228).labels beta n insertions =
    (L24Gluing.term 267).expression.scalarPointContraction X v
      (L24Gluing.term 267).decoration (L24Gluing.term 267).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core228 L24Gluing.term228.decoration L24Gluing.term228.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels228_267

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded228_eq267 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 228) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 267) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 228) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 267) (by decide +kernel)]
  exact scalar228_eq267 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted267_eq228 : originalWeighted 267 =
    (-2 / 1 : ℚ) * originalWeighted 228 := by
  rw [originalWeighted, originalWeighted, ← guarded228_eq267,
    coefficient267, coefficient228]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels229_256 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar229_eq256 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 229).expression.scalarPointContraction X v
      (L24Gluing.term 229).decoration (L24Gluing.term 229).labels beta n insertions =
    (L24Gluing.term 256).expression.scalarPointContraction X v
      (L24Gluing.term 256).decoration (L24Gluing.term 256).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core229 L24Gluing.term229.decoration L24Gluing.term229.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels229_256

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded229_eq256 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 229) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 256) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 229) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 256) (by decide +kernel)]
  exact scalar229_eq256 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted256_eq229 : originalWeighted 256 =
    (4 / 9 : ℚ) * originalWeighted 229 := by
  rw [originalWeighted, originalWeighted, ← guarded229_eq256,
    coefficient256, coefficient229]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels229_268 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar229_eq268 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 229).expression.scalarPointContraction X v
      (L24Gluing.term 229).decoration (L24Gluing.term 229).labels beta n insertions =
    (L24Gluing.term 268).expression.scalarPointContraction X v
      (L24Gluing.term 268).decoration (L24Gluing.term 268).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core229 L24Gluing.term229.decoration L24Gluing.term229.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels229_268

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded229_eq268 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 229) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 268) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 229) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 268) (by decide +kernel)]
  exact scalar229_eq268 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted268_eq229 : originalWeighted 268 =
    (4 / 9 : ℚ) * originalWeighted 229 := by
  rw [originalWeighted, originalWeighted, ← guarded229_eq268,
    coefficient268, coefficient229]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels230_257 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar230_eq257 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 230).expression.scalarPointContraction X v
      (L24Gluing.term 230).decoration (L24Gluing.term 230).labels beta n insertions =
    (L24Gluing.term 257).expression.scalarPointContraction X v
      (L24Gluing.term 257).decoration (L24Gluing.term 257).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core230 L24Gluing.term230.decoration L24Gluing.term230.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels230_257

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded230_eq257 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 230) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 257) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 230) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 257) (by decide +kernel)]
  exact scalar230_eq257 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted257_eq230 : originalWeighted 257 =
    (8812 / 25731 : ℚ) * originalWeighted 230 := by
  rw [originalWeighted, originalWeighted, ← guarded230_eq257,
    coefficient257, coefficient230]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels230_269 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar230_eq269 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 230).expression.scalarPointContraction X v
      (L24Gluing.term 230).decoration (L24Gluing.term 230).labels beta n insertions =
    (L24Gluing.term 269).expression.scalarPointContraction X v
      (L24Gluing.term 269).decoration (L24Gluing.term 269).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core230 L24Gluing.term230.decoration L24Gluing.term230.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels230_269

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded230_eq269 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 230) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 269) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 230) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 269) (by decide +kernel)]
  exact scalar230_eq269 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted269_eq230 : originalWeighted 269 =
    (8812 / 25731 : ℚ) * originalWeighted 230 := by
  rw [originalWeighted, originalWeighted, ← guarded230_eq269,
    coefficient269, coefficient230]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels231_258 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar231_eq258 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 231).expression.scalarPointContraction X v
      (L24Gluing.term 231).decoration (L24Gluing.term 231).labels beta n insertions =
    (L24Gluing.term 258).expression.scalarPointContraction X v
      (L24Gluing.term 258).decoration (L24Gluing.term 258).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core231 L24Gluing.term231.decoration L24Gluing.term231.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels231_258

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded231_eq258 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 231) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 258) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 231) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 258) (by decide +kernel)]
  exact scalar231_eq258 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted258_eq231 : originalWeighted 258 =
    (17308 / 41733 : ℚ) * originalWeighted 231 := by
  rw [originalWeighted, originalWeighted, ← guarded231_eq258,
    coefficient258, coefficient231]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels231_270 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar231_eq270 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 231).expression.scalarPointContraction X v
      (L24Gluing.term 231).decoration (L24Gluing.term 231).labels beta n insertions =
    (L24Gluing.term 270).expression.scalarPointContraction X v
      (L24Gluing.term 270).decoration (L24Gluing.term 270).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core231 L24Gluing.term231.decoration L24Gluing.term231.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels231_270

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded231_eq270 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 231) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 270) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 231) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 270) (by decide +kernel)]
  exact scalar231_eq270 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted270_eq231 : originalWeighted 270 =
    (17308 / 41733 : ℚ) * originalWeighted 231 := by
  rw [originalWeighted, originalWeighted, ← guarded231_eq270,
    coefficient270, coefficient231]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels232_259 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar232_eq259 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 232).expression.scalarPointContraction X v
      (L24Gluing.term 232).decoration (L24Gluing.term 232).labels beta n insertions =
    (L24Gluing.term 259).expression.scalarPointContraction X v
      (L24Gluing.term 259).decoration (L24Gluing.term 259).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core232 L24Gluing.term232.decoration L24Gluing.term232.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels232_259

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded232_eq259 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 232) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 259) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 232) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 259) (by decide +kernel)]
  exact scalar232_eq259 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted259_eq232 : originalWeighted 259 =
    (-76 / 9 : ℚ) * originalWeighted 232 := by
  rw [originalWeighted, originalWeighted, ← guarded232_eq259,
    coefficient259, coefficient232]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels232_271 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar232_eq271 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 232).expression.scalarPointContraction X v
      (L24Gluing.term 232).decoration (L24Gluing.term 232).labels beta n insertions =
    (L24Gluing.term 271).expression.scalarPointContraction X v
      (L24Gluing.term 271).decoration (L24Gluing.term 271).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core232 L24Gluing.term232.decoration L24Gluing.term232.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels232_271

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded232_eq271 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 232) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 271) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 232) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 271) (by decide +kernel)]
  exact scalar232_eq271 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted271_eq232 : originalWeighted 271 =
    (-76 / 9 : ℚ) * originalWeighted 232 := by
  rw [originalWeighted, originalWeighted, ← guarded232_eq271,
    coefficient271, coefficient232]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels276_277 :
    insertions ∘ L24Gluing.flagPermutation15 =
      insertions ∘ L24Gluing.flagPermutation16 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar276_eq277 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 276).expression.scalarPointContraction X v
      (L24Gluing.term 276).decoration (L24Gluing.term 276).labels beta n insertions =
    (L24Gluing.term 277).expression.scalarPointContraction X v
      (L24Gluing.term 277).decoration (L24Gluing.term 277).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core276 L24Gluing.term276.decoration L24Gluing.term276.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation16 beta n insertions labels276_277

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded276_eq277 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 276) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 277) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 276) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 277) (by decide +kernel)]
  exact scalar276_eq277 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted277_eq276 : originalWeighted 277 =
    (1 / 1 : ℚ) * originalWeighted 276 := by
  rw [originalWeighted, originalWeighted, ← guarded276_eq277,
    coefficient277, coefficient276]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels276_283 :
    insertions ∘ L24Gluing.flagPermutation15 =
      insertions ∘ L24Gluing.flagPermutation17 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar276_eq283 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 276).expression.scalarPointContraction X v
      (L24Gluing.term 276).decoration (L24Gluing.term 276).labels beta n insertions =
    (L24Gluing.term 283).expression.scalarPointContraction X v
      (L24Gluing.term 283).decoration (L24Gluing.term 283).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core276 L24Gluing.term276.decoration L24Gluing.term276.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation17 beta n insertions labels276_283

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded276_eq283 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 276) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 283) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 276) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 283) (by decide +kernel)]
  exact scalar276_eq283 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted283_eq276 : originalWeighted 283 =
    (1 / 6 : ℚ) * originalWeighted 276 := by
  rw [originalWeighted, originalWeighted, ← guarded276_eq283,
    coefficient283, coefficient276]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels279_285 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar279_eq285 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 279).expression.scalarPointContraction X v
      (L24Gluing.term 279).decoration (L24Gluing.term 279).labels beta n insertions =
    (L24Gluing.term 285).expression.scalarPointContraction X v
      (L24Gluing.term 285).decoration (L24Gluing.term 285).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core279 L24Gluing.term279.decoration L24Gluing.term279.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels279_285

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded279_eq285 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 279) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 285) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 279) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 285) (by decide +kernel)]
  exact scalar279_eq285 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted285_eq279 : originalWeighted 285 =
    (4 / 1 : ℚ) * originalWeighted 279 := by
  rw [originalWeighted, originalWeighted, ← guarded279_eq285,
    coefficient285, coefficient279]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels279_288 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar279_eq288 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 279).expression.scalarPointContraction X v
      (L24Gluing.term 279).decoration (L24Gluing.term 279).labels beta n insertions =
    (L24Gluing.term 288).expression.scalarPointContraction X v
      (L24Gluing.term 288).decoration (L24Gluing.term 288).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core279 L24Gluing.term279.decoration L24Gluing.term279.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels279_288

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded279_eq288 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 279) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 288) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 279) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 288) (by decide +kernel)]
  exact scalar279_eq288 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted288_eq279 : originalWeighted 288 =
    (4 / 1 : ℚ) * originalWeighted 279 := by
  rw [originalWeighted, originalWeighted, ← guarded279_eq288,
    coefficient288, coefficient279]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels280_286 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar280_eq286 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 280).expression.scalarPointContraction X v
      (L24Gluing.term 280).decoration (L24Gluing.term 280).labels beta n insertions =
    (L24Gluing.term 286).expression.scalarPointContraction X v
      (L24Gluing.term 286).decoration (L24Gluing.term 286).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core280 L24Gluing.term280.decoration L24Gluing.term280.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels280_286

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded280_eq286 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 280) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 286) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 280) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 286) (by decide +kernel)]
  exact scalar280_eq286 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted286_eq280 : originalWeighted 286 =
    (2 / 5 : ℚ) * originalWeighted 280 := by
  rw [originalWeighted, originalWeighted, ← guarded280_eq286,
    coefficient286, coefficient280]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels280_289 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar280_eq289 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 280).expression.scalarPointContraction X v
      (L24Gluing.term 280).decoration (L24Gluing.term 280).labels beta n insertions =
    (L24Gluing.term 289).expression.scalarPointContraction X v
      (L24Gluing.term 289).decoration (L24Gluing.term 289).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core280 L24Gluing.term280.decoration L24Gluing.term280.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels280_289

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded280_eq289 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 280) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 289) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 280) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 289) (by decide +kernel)]
  exact scalar280_eq289 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted289_eq280 : originalWeighted 289 =
    (2 / 5 : ℚ) * originalWeighted 280 := by
  rw [originalWeighted, originalWeighted, ← guarded280_eq289,
    coefficient289, coefficient280]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels281_287 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar281_eq287 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 281).expression.scalarPointContraction X v
      (L24Gluing.term 281).decoration (L24Gluing.term 281).labels beta n insertions =
    (L24Gluing.term 287).expression.scalarPointContraction X v
      (L24Gluing.term 287).decoration (L24Gluing.term 287).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core281 L24Gluing.term281.decoration L24Gluing.term281.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels281_287

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded281_eq287 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 281) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 287) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 281) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 287) (by decide +kernel)]
  exact scalar281_eq287 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted287_eq281 : originalWeighted 287 =
    (2 / 9 : ℚ) * originalWeighted 281 := by
  rw [originalWeighted, originalWeighted, ← guarded281_eq287,
    coefficient287, coefficient281]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels281_290 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar281_eq290 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 281).expression.scalarPointContraction X v
      (L24Gluing.term 281).decoration (L24Gluing.term 281).labels beta n insertions =
    (L24Gluing.term 290).expression.scalarPointContraction X v
      (L24Gluing.term 290).decoration (L24Gluing.term 290).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core281 L24Gluing.term281.decoration L24Gluing.term281.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels281_290

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded281_eq290 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 281) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 290) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 281) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 290) (by decide +kernel)]
  exact scalar281_eq290 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted290_eq281 : originalWeighted 290 =
    (2 / 9 : ℚ) * originalWeighted 281 := by
  rw [originalWeighted, originalWeighted, ← guarded281_eq290,
    coefficient290, coefficient281]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels296_300 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar296_eq300 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 296).expression.scalarPointContraction X v
      (L24Gluing.term 296).decoration (L24Gluing.term 296).labels beta n insertions =
    (L24Gluing.term 300).expression.scalarPointContraction X v
      (L24Gluing.term 300).decoration (L24Gluing.term 300).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core296 L24Gluing.term296.decoration L24Gluing.term296.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels296_300

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded296_eq300 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 296) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 300) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 296) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 300) (by decide +kernel)]
  exact scalar296_eq300 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted300_eq296 : originalWeighted 300 =
    (1 / 1 : ℚ) * originalWeighted 296 := by
  rw [originalWeighted, originalWeighted, ← guarded296_eq300,
    coefficient300, coefficient296]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels296_308 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar296_eq308 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 296).expression.scalarPointContraction X v
      (L24Gluing.term 296).decoration (L24Gluing.term 296).labels beta n insertions =
    (L24Gluing.term 308).expression.scalarPointContraction X v
      (L24Gluing.term 308).decoration (L24Gluing.term 308).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core296 L24Gluing.term296.decoration L24Gluing.term296.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels296_308

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded296_eq308 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 296) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 308) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 296) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 308) (by decide +kernel)]
  exact scalar296_eq308 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted308_eq296 : originalWeighted 308 =
    (4 / 1 : ℚ) * originalWeighted 296 := by
  rw [originalWeighted, originalWeighted, ← guarded296_eq308,
    coefficient308, coefficient296]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels297_301 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar297_eq301 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 297).expression.scalarPointContraction X v
      (L24Gluing.term 297).decoration (L24Gluing.term 297).labels beta n insertions =
    (L24Gluing.term 301).expression.scalarPointContraction X v
      (L24Gluing.term 301).decoration (L24Gluing.term 301).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core297 L24Gluing.term297.decoration L24Gluing.term297.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels297_301

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded297_eq301 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 297) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 301) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 297) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 301) (by decide +kernel)]
  exact scalar297_eq301 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted301_eq297 : originalWeighted 301 =
    (1 / 1 : ℚ) * originalWeighted 297 := by
  rw [originalWeighted, originalWeighted, ← guarded297_eq301,
    coefficient301, coefficient297]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels298_302 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar298_eq302 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 298).expression.scalarPointContraction X v
      (L24Gluing.term 298).decoration (L24Gluing.term 298).labels beta n insertions =
    (L24Gluing.term 302).expression.scalarPointContraction X v
      (L24Gluing.term 302).decoration (L24Gluing.term 302).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core298 L24Gluing.term298.decoration L24Gluing.term298.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels298_302

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded298_eq302 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 298) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 302) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 298) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 302) (by decide +kernel)]
  exact scalar298_eq302 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted302_eq298 : originalWeighted 302 =
    (1 / 1 : ℚ) * originalWeighted 298 := by
  rw [originalWeighted, originalWeighted, ← guarded298_eq302,
    coefficient302, coefficient298]
  ring

end AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03

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

namespace AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02

open BlowupF1RootAssembly SurfaceGenusTwo GetzlerGraphs L24Gluing

private def core193 : GluingExpression 2 (Fin 4) :=
  join (m := 1) (n := 3) 1 3
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))

private def core194 : GluingExpression 2 (Fin 4) :=
  join (m := 1) (n := 3) 1 3
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))

private def core195 : GluingExpression 2 (Fin 4) :=
  join (m := 1) (n := 3) 1 3
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))

private def core196 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core197 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core198 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core199 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core200 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core220 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

private def core221 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

private def core222 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

private def core223 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

private def core224 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

private def core225 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

theorem coefficient193 : L24CorrectionsReplay.fullClaim 193 =
    (6047 / 4680 : ℚ) := by decide +kernel

theorem coefficient194 : L24CorrectionsReplay.fullClaim 194 =
    (559 / 1080 : ℚ) := by decide +kernel

theorem coefficient195 : L24CorrectionsReplay.fullClaim 195 =
    (-745 / 351 : ℚ) := by decide +kernel

theorem coefficient196 : L24CorrectionsReplay.fullClaim 196 =
    (-23 / 1080 : ℚ) := by decide +kernel

theorem coefficient197 : L24CorrectionsReplay.fullClaim 197 =
    (899 / 1080 : ℚ) := by decide +kernel

theorem coefficient198 : L24CorrectionsReplay.fullClaim 198 =
    (701 / 1326 : ℚ) := by decide +kernel

theorem coefficient199 : L24CorrectionsReplay.fullClaim 199 =
    (791 / 390 : ℚ) := by decide +kernel

theorem coefficient200 : L24CorrectionsReplay.fullClaim 200 =
    (-2797 / 3978 : ℚ) := by decide +kernel

theorem coefficient212 : L24CorrectionsReplay.fullClaim 212 =
    (6047 / 4680 : ℚ) := by decide +kernel

theorem coefficient213 : L24CorrectionsReplay.fullClaim 213 =
    (559 / 1080 : ℚ) := by decide +kernel

theorem coefficient214 : L24CorrectionsReplay.fullClaim 214 =
    (-745 / 351 : ℚ) := by decide +kernel

theorem coefficient215 : L24CorrectionsReplay.fullClaim 215 =
    (-23 / 1080 : ℚ) := by decide +kernel

theorem coefficient216 : L24CorrectionsReplay.fullClaim 216 =
    (899 / 1080 : ℚ) := by decide +kernel

theorem coefficient217 : L24CorrectionsReplay.fullClaim 217 =
    (701 / 1326 : ℚ) := by decide +kernel

theorem coefficient218 : L24CorrectionsReplay.fullClaim 218 =
    (791 / 390 : ℚ) := by decide +kernel

theorem coefficient219 : L24CorrectionsReplay.fullClaim 219 =
    (-2797 / 3978 : ℚ) := by decide +kernel

theorem coefficient220 : L24CorrectionsReplay.fullClaim 220 =
    (-1 / 15 : ℚ) := by decide +kernel

theorem coefficient221 : L24CorrectionsReplay.fullClaim 221 =
    (-1 / 15 : ℚ) := by decide +kernel

theorem coefficient222 : L24CorrectionsReplay.fullClaim 222 =
    (-1 / 15 : ℚ) := by decide +kernel

theorem coefficient223 : L24CorrectionsReplay.fullClaim 223 =
    (1285 / 468 : ℚ) := by decide +kernel

theorem coefficient224 : L24CorrectionsReplay.fullClaim 224 =
    (161 / 60 : ℚ) := by decide +kernel

theorem coefficient225 : L24CorrectionsReplay.fullClaim 225 =
    (-745 / 117 : ℚ) := by decide +kernel

theorem coefficient242 : L24CorrectionsReplay.fullClaim 242 =
    (13913 / 21060 : ℚ) := by decide +kernel

theorem coefficient243 : L24CorrectionsReplay.fullClaim 243 =
    (-4229 / 71604 : ℚ) := by decide +kernel

theorem coefficient244 : L24CorrectionsReplay.fullClaim 244 =
    (13913 / 21060 : ℚ) := by decide +kernel

theorem coefficient245 : L24CorrectionsReplay.fullClaim 245 =
    (-4229 / 71604 : ℚ) := by decide +kernel

theorem coefficient246 : L24CorrectionsReplay.fullClaim 246 =
    (20933 / 21060 : ℚ) := by decide +kernel

theorem coefficient247 : L24CorrectionsReplay.fullClaim 247 =
    (-4229 / 71604 : ℚ) := by decide +kernel

theorem coefficient248 : L24CorrectionsReplay.fullClaim 248 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient249 : L24CorrectionsReplay.fullClaim 249 =
    (-1 / 1 : ℚ) := by decide +kernel

theorem coefficient250 : L24CorrectionsReplay.fullClaim 250 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient251 : L24CorrectionsReplay.fullClaim 251 =
    (1481 / 1053 : ℚ) := by decide +kernel

theorem coefficient252 : L24CorrectionsReplay.fullClaim 252 =
    (161 / 135 : ℚ) := by decide +kernel

theorem coefficient253 : L24CorrectionsReplay.fullClaim 253 =
    (-3050 / 1053 : ℚ) := by decide +kernel

theorem coefficient260 : L24CorrectionsReplay.fullClaim 260 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient261 : L24CorrectionsReplay.fullClaim 261 =
    (-1 / 1 : ℚ) := by decide +kernel

theorem coefficient262 : L24CorrectionsReplay.fullClaim 262 =
    (-1 / 5 : ℚ) := by decide +kernel

theorem coefficient263 : L24CorrectionsReplay.fullClaim 263 =
    (1481 / 1053 : ℚ) := by decide +kernel

theorem coefficient264 : L24CorrectionsReplay.fullClaim 264 =
    (161 / 135 : ℚ) := by decide +kernel

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels193_212 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation14 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar193_eq212 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 193).expression.scalarPointContraction X v
      (L24Gluing.term 193).decoration (L24Gluing.term 193).labels beta n insertions =
    (L24Gluing.term 212).expression.scalarPointContraction X v
      (L24Gluing.term 212).decoration (L24Gluing.term 212).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core193 L24Gluing.term193.decoration L24Gluing.term193.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation14 beta n insertions labels193_212

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded193_eq212 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 193) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 212) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 193) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 212) (by decide +kernel)]
  exact scalar193_eq212 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted212_eq193 : originalWeighted 212 =
    (1 / 1 : ℚ) * originalWeighted 193 := by
  rw [originalWeighted, originalWeighted, ← guarded193_eq212,
    coefficient212, coefficient193]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels193_242 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation15 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar193_eq242 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 193).expression.scalarPointContraction X v
      (L24Gluing.term 193).decoration (L24Gluing.term 193).labels beta n insertions =
    (L24Gluing.term 242).expression.scalarPointContraction X v
      (L24Gluing.term 242).decoration (L24Gluing.term 242).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core193 L24Gluing.term193.decoration L24Gluing.term193.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation15 beta n insertions labels193_242

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded193_eq242 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 193) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 242) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 193) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 242) (by decide +kernel)]
  exact scalar193_eq242 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted242_eq193 : originalWeighted 242 =
    (27826 / 54423 : ℚ) * originalWeighted 193 := by
  rw [originalWeighted, originalWeighted, ← guarded193_eq242,
    coefficient242, coefficient193]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels194_213 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation14 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar194_eq213 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 194).expression.scalarPointContraction X v
      (L24Gluing.term 194).decoration (L24Gluing.term 194).labels beta n insertions =
    (L24Gluing.term 213).expression.scalarPointContraction X v
      (L24Gluing.term 213).decoration (L24Gluing.term 213).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core194 L24Gluing.term194.decoration L24Gluing.term194.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation14 beta n insertions labels194_213

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded194_eq213 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 194) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 213) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 194) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 213) (by decide +kernel)]
  exact scalar194_eq213 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted213_eq194 : originalWeighted 213 =
    (1 / 1 : ℚ) * originalWeighted 194 := by
  rw [originalWeighted, originalWeighted, ← guarded194_eq213,
    coefficient213, coefficient194]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels195_214 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation14 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar195_eq214 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 195).expression.scalarPointContraction X v
      (L24Gluing.term 195).decoration (L24Gluing.term 195).labels beta n insertions =
    (L24Gluing.term 214).expression.scalarPointContraction X v
      (L24Gluing.term 214).decoration (L24Gluing.term 214).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core195 L24Gluing.term195.decoration L24Gluing.term195.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation14 beta n insertions labels195_214

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded195_eq214 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 195) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 214) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 195) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 214) (by decide +kernel)]
  exact scalar195_eq214 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted214_eq195 : originalWeighted 214 =
    (1 / 1 : ℚ) * originalWeighted 195 := by
  rw [originalWeighted, originalWeighted, ← guarded195_eq214,
    coefficient214, coefficient195]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels195_243 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation15 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar195_eq243 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 195).expression.scalarPointContraction X v
      (L24Gluing.term 195).decoration (L24Gluing.term 195).labels beta n insertions =
    (L24Gluing.term 243).expression.scalarPointContraction X v
      (L24Gluing.term 243).decoration (L24Gluing.term 243).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core195 L24Gluing.term195.decoration L24Gluing.term195.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation15 beta n insertions labels195_243

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded195_eq243 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 195) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 243) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 195) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 243) (by decide +kernel)]
  exact scalar195_eq243 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted243_eq195 : originalWeighted 243 =
    (4229 / 151980 : ℚ) * originalWeighted 195 := by
  rw [originalWeighted, originalWeighted, ← guarded195_eq243,
    coefficient243, coefficient195]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels196_215 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation6 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar196_eq215 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 196).expression.scalarPointContraction X v
      (L24Gluing.term 196).decoration (L24Gluing.term 196).labels beta n insertions =
    (L24Gluing.term 215).expression.scalarPointContraction X v
      (L24Gluing.term 215).decoration (L24Gluing.term 215).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core196 L24Gluing.term196.decoration L24Gluing.term196.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 beta n insertions labels196_215

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded196_eq215 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 196) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 215) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 196) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 215) (by decide +kernel)]
  exact scalar196_eq215 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted215_eq196 : originalWeighted 215 =
    (1 / 1 : ℚ) * originalWeighted 196 := by
  rw [originalWeighted, originalWeighted, ← guarded196_eq215,
    coefficient215, coefficient196]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels196_244 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar196_eq244 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 196).expression.scalarPointContraction X v
      (L24Gluing.term 196).decoration (L24Gluing.term 196).labels beta n insertions =
    (L24Gluing.term 244).expression.scalarPointContraction X v
      (L24Gluing.term 244).decoration (L24Gluing.term 244).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core196 L24Gluing.term196.decoration L24Gluing.term196.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 beta n insertions labels196_244

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded196_eq244 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 196) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 244) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 196) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 244) (by decide +kernel)]
  exact scalar196_eq244 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted244_eq196 : originalWeighted 244 =
    (-27826 / 897 : ℚ) * originalWeighted 196 := by
  rw [originalWeighted, originalWeighted, ← guarded196_eq244,
    coefficient244, coefficient196]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels197_216 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation6 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar197_eq216 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 197).expression.scalarPointContraction X v
      (L24Gluing.term 197).decoration (L24Gluing.term 197).labels beta n insertions =
    (L24Gluing.term 216).expression.scalarPointContraction X v
      (L24Gluing.term 216).decoration (L24Gluing.term 216).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core197 L24Gluing.term197.decoration L24Gluing.term197.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 beta n insertions labels197_216

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded197_eq216 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 197) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 216) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 197) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 216) (by decide +kernel)]
  exact scalar197_eq216 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted216_eq197 : originalWeighted 216 =
    (1 / 1 : ℚ) * originalWeighted 197 := by
  rw [originalWeighted, originalWeighted, ← guarded197_eq216,
    coefficient216, coefficient197]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels198_217 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation6 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar198_eq217 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 198).expression.scalarPointContraction X v
      (L24Gluing.term 198).decoration (L24Gluing.term 198).labels beta n insertions =
    (L24Gluing.term 217).expression.scalarPointContraction X v
      (L24Gluing.term 217).decoration (L24Gluing.term 217).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core198 L24Gluing.term198.decoration L24Gluing.term198.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 beta n insertions labels198_217

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded198_eq217 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 198) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 217) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 198) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 217) (by decide +kernel)]
  exact scalar198_eq217 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted217_eq198 : originalWeighted 217 =
    (1 / 1 : ℚ) * originalWeighted 198 := by
  rw [originalWeighted, originalWeighted, ← guarded198_eq217,
    coefficient217, coefficient198]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels198_245 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar198_eq245 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 198).expression.scalarPointContraction X v
      (L24Gluing.term 198).decoration (L24Gluing.term 198).labels beta n insertions =
    (L24Gluing.term 245).expression.scalarPointContraction X v
      (L24Gluing.term 245).decoration (L24Gluing.term 245).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core198 L24Gluing.term198.decoration L24Gluing.term198.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 beta n insertions labels198_245

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded198_eq245 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 198) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 245) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 198) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 245) (by decide +kernel)]
  exact scalar198_eq245 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted245_eq198 : originalWeighted 245 =
    (-4229 / 37854 : ℚ) * originalWeighted 198 := by
  rw [originalWeighted, originalWeighted, ← guarded198_eq245,
    coefficient245, coefficient198]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels199_218 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation6 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar199_eq218 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 199).expression.scalarPointContraction X v
      (L24Gluing.term 199).decoration (L24Gluing.term 199).labels beta n insertions =
    (L24Gluing.term 218).expression.scalarPointContraction X v
      (L24Gluing.term 218).decoration (L24Gluing.term 218).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core199 L24Gluing.term199.decoration L24Gluing.term199.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 beta n insertions labels199_218

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded199_eq218 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 199) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 218) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 199) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 218) (by decide +kernel)]
  exact scalar199_eq218 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted218_eq199 : originalWeighted 218 =
    (1 / 1 : ℚ) * originalWeighted 199 := by
  rw [originalWeighted, originalWeighted, ← guarded199_eq218,
    coefficient218, coefficient199]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels199_246 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar199_eq246 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 199).expression.scalarPointContraction X v
      (L24Gluing.term 199).decoration (L24Gluing.term 199).labels beta n insertions =
    (L24Gluing.term 246).expression.scalarPointContraction X v
      (L24Gluing.term 246).decoration (L24Gluing.term 246).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core199 L24Gluing.term199.decoration L24Gluing.term199.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 beta n insertions labels199_246

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded199_eq246 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 199) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 246) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 199) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 246) (by decide +kernel)]
  exact scalar199_eq246 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted246_eq199 : originalWeighted 246 =
    (20933 / 42714 : ℚ) * originalWeighted 199 := by
  rw [originalWeighted, originalWeighted, ← guarded199_eq246,
    coefficient246, coefficient199]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels200_219 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation6 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar200_eq219 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 200).expression.scalarPointContraction X v
      (L24Gluing.term 200).decoration (L24Gluing.term 200).labels beta n insertions =
    (L24Gluing.term 219).expression.scalarPointContraction X v
      (L24Gluing.term 219).decoration (L24Gluing.term 219).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core200 L24Gluing.term200.decoration L24Gluing.term200.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 beta n insertions labels200_219

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded200_eq219 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 200) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 219) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 200) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 219) (by decide +kernel)]
  exact scalar200_eq219 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted219_eq200 : originalWeighted 219 =
    (1 / 1 : ℚ) * originalWeighted 200 := by
  rw [originalWeighted, originalWeighted, ← guarded200_eq219,
    coefficient219, coefficient200]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels200_247 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar200_eq247 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 200).expression.scalarPointContraction X v
      (L24Gluing.term 200).decoration (L24Gluing.term 200).labels beta n insertions =
    (L24Gluing.term 247).expression.scalarPointContraction X v
      (L24Gluing.term 247).decoration (L24Gluing.term 247).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core200 L24Gluing.term200.decoration L24Gluing.term200.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 beta n insertions labels200_247

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded200_eq247 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 200) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 247) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 200) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 247) (by decide +kernel)]
  exact scalar200_eq247 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted247_eq200 : originalWeighted 247 =
    (4229 / 50346 : ℚ) * originalWeighted 200 := by
  rw [originalWeighted, originalWeighted, ← guarded200_eq247,
    coefficient247, coefficient200]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels220_248 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar220_eq248 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 220).expression.scalarPointContraction X v
      (L24Gluing.term 220).decoration (L24Gluing.term 220).labels beta n insertions =
    (L24Gluing.term 248).expression.scalarPointContraction X v
      (L24Gluing.term 248).decoration (L24Gluing.term 248).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core220 L24Gluing.term220.decoration L24Gluing.term220.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels220_248

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded220_eq248 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 220) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 248) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 220) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 248) (by decide +kernel)]
  exact scalar220_eq248 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted248_eq220 : originalWeighted 248 =
    (3 / 1 : ℚ) * originalWeighted 220 := by
  rw [originalWeighted, originalWeighted, ← guarded220_eq248,
    coefficient248, coefficient220]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels220_260 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar220_eq260 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 220).expression.scalarPointContraction X v
      (L24Gluing.term 220).decoration (L24Gluing.term 220).labels beta n insertions =
    (L24Gluing.term 260).expression.scalarPointContraction X v
      (L24Gluing.term 260).decoration (L24Gluing.term 260).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core220 L24Gluing.term220.decoration L24Gluing.term220.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels220_260

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded220_eq260 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 220) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 260) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 220) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 260) (by decide +kernel)]
  exact scalar220_eq260 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted260_eq220 : originalWeighted 260 =
    (3 / 1 : ℚ) * originalWeighted 220 := by
  rw [originalWeighted, originalWeighted, ← guarded220_eq260,
    coefficient260, coefficient220]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels221_249 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar221_eq249 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 221).expression.scalarPointContraction X v
      (L24Gluing.term 221).decoration (L24Gluing.term 221).labels beta n insertions =
    (L24Gluing.term 249).expression.scalarPointContraction X v
      (L24Gluing.term 249).decoration (L24Gluing.term 249).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core221 L24Gluing.term221.decoration L24Gluing.term221.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels221_249

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded221_eq249 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 221) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 249) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 221) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 249) (by decide +kernel)]
  exact scalar221_eq249 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted249_eq221 : originalWeighted 249 =
    (15 / 1 : ℚ) * originalWeighted 221 := by
  rw [originalWeighted, originalWeighted, ← guarded221_eq249,
    coefficient249, coefficient221]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels221_261 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar221_eq261 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 221).expression.scalarPointContraction X v
      (L24Gluing.term 221).decoration (L24Gluing.term 221).labels beta n insertions =
    (L24Gluing.term 261).expression.scalarPointContraction X v
      (L24Gluing.term 261).decoration (L24Gluing.term 261).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core221 L24Gluing.term221.decoration L24Gluing.term221.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels221_261

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded221_eq261 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 221) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 261) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 221) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 261) (by decide +kernel)]
  exact scalar221_eq261 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted261_eq221 : originalWeighted 261 =
    (15 / 1 : ℚ) * originalWeighted 221 := by
  rw [originalWeighted, originalWeighted, ← guarded221_eq261,
    coefficient261, coefficient221]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels222_250 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar222_eq250 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 222).expression.scalarPointContraction X v
      (L24Gluing.term 222).decoration (L24Gluing.term 222).labels beta n insertions =
    (L24Gluing.term 250).expression.scalarPointContraction X v
      (L24Gluing.term 250).decoration (L24Gluing.term 250).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core222 L24Gluing.term222.decoration L24Gluing.term222.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels222_250

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded222_eq250 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 222) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 250) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 222) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 250) (by decide +kernel)]
  exact scalar222_eq250 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted250_eq222 : originalWeighted 250 =
    (3 / 1 : ℚ) * originalWeighted 222 := by
  rw [originalWeighted, originalWeighted, ← guarded222_eq250,
    coefficient250, coefficient222]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels222_262 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar222_eq262 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 222).expression.scalarPointContraction X v
      (L24Gluing.term 222).decoration (L24Gluing.term 222).labels beta n insertions =
    (L24Gluing.term 262).expression.scalarPointContraction X v
      (L24Gluing.term 262).decoration (L24Gluing.term 262).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core222 L24Gluing.term222.decoration L24Gluing.term222.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels222_262

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded222_eq262 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 222) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 262) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 222) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 262) (by decide +kernel)]
  exact scalar222_eq262 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted262_eq222 : originalWeighted 262 =
    (3 / 1 : ℚ) * originalWeighted 222 := by
  rw [originalWeighted, originalWeighted, ← guarded222_eq262,
    coefficient262, coefficient222]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels223_251 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar223_eq251 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 223).expression.scalarPointContraction X v
      (L24Gluing.term 223).decoration (L24Gluing.term 223).labels beta n insertions =
    (L24Gluing.term 251).expression.scalarPointContraction X v
      (L24Gluing.term 251).decoration (L24Gluing.term 251).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core223 L24Gluing.term223.decoration L24Gluing.term223.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels223_251

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded223_eq251 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 223) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 251) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 223) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 251) (by decide +kernel)]
  exact scalar223_eq251 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted251_eq223 : originalWeighted 251 =
    (5924 / 11565 : ℚ) * originalWeighted 223 := by
  rw [originalWeighted, originalWeighted, ← guarded223_eq251,
    coefficient251, coefficient223]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels223_263 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar223_eq263 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 223).expression.scalarPointContraction X v
      (L24Gluing.term 223).decoration (L24Gluing.term 223).labels beta n insertions =
    (L24Gluing.term 263).expression.scalarPointContraction X v
      (L24Gluing.term 263).decoration (L24Gluing.term 263).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core223 L24Gluing.term223.decoration L24Gluing.term223.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels223_263

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded223_eq263 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 223) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 263) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 223) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 263) (by decide +kernel)]
  exact scalar223_eq263 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted263_eq223 : originalWeighted 263 =
    (5924 / 11565 : ℚ) * originalWeighted 223 := by
  rw [originalWeighted, originalWeighted, ← guarded223_eq263,
    coefficient263, coefficient223]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels224_252 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar224_eq252 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 224).expression.scalarPointContraction X v
      (L24Gluing.term 224).decoration (L24Gluing.term 224).labels beta n insertions =
    (L24Gluing.term 252).expression.scalarPointContraction X v
      (L24Gluing.term 252).decoration (L24Gluing.term 252).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core224 L24Gluing.term224.decoration L24Gluing.term224.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels224_252

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded224_eq252 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 224) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 252) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 224) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 252) (by decide +kernel)]
  exact scalar224_eq252 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted252_eq224 : originalWeighted 252 =
    (4 / 9 : ℚ) * originalWeighted 224 := by
  rw [originalWeighted, originalWeighted, ← guarded224_eq252,
    coefficient252, coefficient224]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels224_264 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar224_eq264 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 224).expression.scalarPointContraction X v
      (L24Gluing.term 224).decoration (L24Gluing.term 224).labels beta n insertions =
    (L24Gluing.term 264).expression.scalarPointContraction X v
      (L24Gluing.term 264).decoration (L24Gluing.term 264).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core224 L24Gluing.term224.decoration L24Gluing.term224.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels224_264

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded224_eq264 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 224) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 264) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 224) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 264) (by decide +kernel)]
  exact scalar224_eq264 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted264_eq224 : originalWeighted 264 =
    (4 / 9 : ℚ) * originalWeighted 224 := by
  rw [originalWeighted, originalWeighted, ← guarded224_eq264,
    coefficient264, coefficient224]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels225_253 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar225_eq253 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 225).expression.scalarPointContraction X v
      (L24Gluing.term 225).decoration (L24Gluing.term 225).labels beta n insertions =
    (L24Gluing.term 253).expression.scalarPointContraction X v
      (L24Gluing.term 253).decoration (L24Gluing.term 253).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core225 L24Gluing.term225.decoration L24Gluing.term225.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels225_253

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded225_eq253 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 225) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 253) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 225) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 253) (by decide +kernel)]
  exact scalar225_eq253 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted253_eq225 : originalWeighted 253 =
    (610 / 1341 : ℚ) * originalWeighted 225 := by
  rw [originalWeighted, originalWeighted, ← guarded225_eq253,
    coefficient253, coefficient225]
  ring

end AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02

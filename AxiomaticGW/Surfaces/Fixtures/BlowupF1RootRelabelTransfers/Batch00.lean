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

namespace AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00

open BlowupF1RootAssembly SurfaceGenusTwo GetzlerGraphs L24Gluing

private def core121 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])))

private def core122 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])))

private def core124 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])))

private def core126 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core127 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core128 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core129 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core130 : GluingExpression 2 (Fin 4) :=
  join (m := 1) (n := 3) 1 3
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

private def core131 : GluingExpression 2 (Fin 4) :=
  join (m := 1) (n := 3) 1 3
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

private def core132 : GluingExpression 2 (Fin 4) :=
  join (m := 1) (n := 3) 1 3
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

private def core134 : GluingExpression 2 (Fin 4) :=
  join (m := 1) (n := 3) 1 3
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

private def core135 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core137 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

theorem coefficient121 : L24CorrectionsReplay.fullClaim 121 =
    (1 / 15 : ℚ) := by decide +kernel

theorem coefficient122 : L24CorrectionsReplay.fullClaim 122 =
    (4259 / 3510 : ℚ) := by decide +kernel

theorem coefficient124 : L24CorrectionsReplay.fullClaim 124 =
    (-745 / 351 : ℚ) := by decide +kernel

theorem coefficient126 : L24CorrectionsReplay.fullClaim 126 =
    (12553 / 23868 : ℚ) := by decide +kernel

theorem coefficient127 : L24CorrectionsReplay.fullClaim 127 =
    (-193 / 1080 : ℚ) := by decide +kernel

theorem coefficient128 : L24CorrectionsReplay.fullClaim 128 =
    (27371 / 14040 : ℚ) := by decide +kernel

theorem coefficient129 : L24CorrectionsReplay.fullClaim 129 =
    (-991 / 1404 : ℚ) := by decide +kernel

theorem coefficient130 : L24CorrectionsReplay.fullClaim 130 =
    (791 / 390 : ℚ) := by decide +kernel

theorem coefficient131 : L24CorrectionsReplay.fullClaim 131 =
    (-2797 / 3978 : ℚ) := by decide +kernel

theorem coefficient132 : L24CorrectionsReplay.fullClaim 132 =
    (-23 / 1080 : ℚ) := by decide +kernel

theorem coefficient134 : L24CorrectionsReplay.fullClaim 134 =
    (701 / 1326 : ℚ) := by decide +kernel

theorem coefficient135 : L24CorrectionsReplay.fullClaim 135 =
    (6047 / 4680 : ℚ) := by decide +kernel

theorem coefficient137 : L24CorrectionsReplay.fullClaim 137 =
    (-745 / 351 : ℚ) := by decide +kernel

theorem coefficient140 : L24CorrectionsReplay.fullClaim 140 =
    (3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient141 : L24CorrectionsReplay.fullClaim 141 =
    (3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient142 : L24CorrectionsReplay.fullClaim 142 =
    (-1490 / 1053 : ℚ) := by decide +kernel

theorem coefficient143 : L24CorrectionsReplay.fullClaim 143 =
    (7706 / 5967 : ℚ) := by decide +kernel

theorem coefficient144 : L24CorrectionsReplay.fullClaim 144 =
    (3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient145 : L24CorrectionsReplay.fullClaim 145 =
    (3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient146 : L24CorrectionsReplay.fullClaim 146 =
    (-1490 / 1053 : ℚ) := by decide +kernel

theorem coefficient147 : L24CorrectionsReplay.fullClaim 147 =
    (20933 / 21060 : ℚ) := by decide +kernel

theorem coefficient148 : L24CorrectionsReplay.fullClaim 148 =
    (-4229 / 71604 : ℚ) := by decide +kernel

theorem coefficient149 : L24CorrectionsReplay.fullClaim 149 =
    (13913 / 21060 : ℚ) := by decide +kernel

theorem coefficient150 : L24CorrectionsReplay.fullClaim 150 =
    (-4229 / 71604 : ℚ) := by decide +kernel

theorem coefficient151 : L24CorrectionsReplay.fullClaim 151 =
    (13913 / 21060 : ℚ) := by decide +kernel

theorem coefficient152 : L24CorrectionsReplay.fullClaim 152 =
    (-4229 / 71604 : ℚ) := by decide +kernel

theorem coefficient155 : L24CorrectionsReplay.fullClaim 155 =
    (3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient156 : L24CorrectionsReplay.fullClaim 156 =
    (3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient157 : L24CorrectionsReplay.fullClaim 157 =
    (-1490 / 1053 : ℚ) := by decide +kernel

theorem coefficient158 : L24CorrectionsReplay.fullClaim 158 =
    (7706 / 5967 : ℚ) := by decide +kernel

theorem coefficient159 : L24CorrectionsReplay.fullClaim 159 =
    (3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient160 : L24CorrectionsReplay.fullClaim 160 =
    (3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient161 : L24CorrectionsReplay.fullClaim 161 =
    (-1490 / 1053 : ℚ) := by decide +kernel

theorem coefficient162 : L24CorrectionsReplay.fullClaim 162 =
    (20933 / 21060 : ℚ) := by decide +kernel

theorem coefficient163 : L24CorrectionsReplay.fullClaim 163 =
    (-4229 / 71604 : ℚ) := by decide +kernel

theorem coefficient164 : L24CorrectionsReplay.fullClaim 164 =
    (13913 / 21060 : ℚ) := by decide +kernel

theorem coefficient165 : L24CorrectionsReplay.fullClaim 165 =
    (-4229 / 71604 : ℚ) := by decide +kernel

theorem coefficient166 : L24CorrectionsReplay.fullClaim 166 =
    (13913 / 21060 : ℚ) := by decide +kernel

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels121_140 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar121_eq140 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 121).expression.scalarPointContraction X v
      (L24Gluing.term 121).decoration (L24Gluing.term 121).labels beta n insertions =
    (L24Gluing.term 140).expression.scalarPointContraction X v
      (L24Gluing.term 140).decoration (L24Gluing.term 140).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core121 L24Gluing.term121.decoration L24Gluing.term121.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels121_140

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded121_eq140 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 121) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 140) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 121) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 140) (by decide +kernel)]
  exact scalar121_eq140 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted140_eq121 : originalWeighted 140 =
    (3527 / 351 : ℚ) * originalWeighted 121 := by
  rw [originalWeighted, originalWeighted, ← guarded121_eq140,
    coefficient140, coefficient121]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels121_155 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar121_eq155 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 121).expression.scalarPointContraction X v
      (L24Gluing.term 121).decoration (L24Gluing.term 121).labels beta n insertions =
    (L24Gluing.term 155).expression.scalarPointContraction X v
      (L24Gluing.term 155).decoration (L24Gluing.term 155).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core121 L24Gluing.term121.decoration L24Gluing.term121.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels121_155

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded121_eq155 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 121) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 155) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 121) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 155) (by decide +kernel)]
  exact scalar121_eq155 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted155_eq121 : originalWeighted 155 =
    (3527 / 351 : ℚ) * originalWeighted 121 := by
  rw [originalWeighted, originalWeighted, ← guarded121_eq155,
    coefficient155, coefficient121]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels122_141 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar122_eq141 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 122).expression.scalarPointContraction X v
      (L24Gluing.term 122).decoration (L24Gluing.term 122).labels beta n insertions =
    (L24Gluing.term 141).expression.scalarPointContraction X v
      (L24Gluing.term 141).decoration (L24Gluing.term 141).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core122 L24Gluing.term122.decoration L24Gluing.term122.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels122_141

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded122_eq141 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 122) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 141) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 122) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 141) (by decide +kernel)]
  exact scalar122_eq141 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted141_eq122 : originalWeighted 141 =
    (7054 / 12777 : ℚ) * originalWeighted 122 := by
  rw [originalWeighted, originalWeighted, ← guarded122_eq141,
    coefficient141, coefficient122]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels122_156 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar122_eq156 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 122).expression.scalarPointContraction X v
      (L24Gluing.term 122).decoration (L24Gluing.term 122).labels beta n insertions =
    (L24Gluing.term 156).expression.scalarPointContraction X v
      (L24Gluing.term 156).decoration (L24Gluing.term 156).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core122 L24Gluing.term122.decoration L24Gluing.term122.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels122_156

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded122_eq156 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 122) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 156) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 122) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 156) (by decide +kernel)]
  exact scalar122_eq156 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted156_eq122 : originalWeighted 156 =
    (7054 / 12777 : ℚ) * originalWeighted 122 := by
  rw [originalWeighted, originalWeighted, ← guarded122_eq156,
    coefficient156, coefficient122]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels124_142 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar124_eq142 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 124).expression.scalarPointContraction X v
      (L24Gluing.term 124).decoration (L24Gluing.term 124).labels beta n insertions =
    (L24Gluing.term 142).expression.scalarPointContraction X v
      (L24Gluing.term 142).decoration (L24Gluing.term 142).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core124 L24Gluing.term124.decoration L24Gluing.term124.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels124_142

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded124_eq142 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 124) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 142) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 124) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 142) (by decide +kernel)]
  exact scalar124_eq142 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted142_eq124 : originalWeighted 142 =
    (2 / 3 : ℚ) * originalWeighted 124 := by
  rw [originalWeighted, originalWeighted, ← guarded124_eq142,
    coefficient142, coefficient124]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels124_157 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar124_eq157 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 124).expression.scalarPointContraction X v
      (L24Gluing.term 124).decoration (L24Gluing.term 124).labels beta n insertions =
    (L24Gluing.term 157).expression.scalarPointContraction X v
      (L24Gluing.term 157).decoration (L24Gluing.term 157).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core124 L24Gluing.term124.decoration L24Gluing.term124.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels124_157

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded124_eq157 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 124) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 157) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 124) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 157) (by decide +kernel)]
  exact scalar124_eq157 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted157_eq124 : originalWeighted 157 =
    (2 / 3 : ℚ) * originalWeighted 124 := by
  rw [originalWeighted, originalWeighted, ← guarded124_eq157,
    coefficient157, coefficient124]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels126_143 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar126_eq143 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 126).expression.scalarPointContraction X v
      (L24Gluing.term 126).decoration (L24Gluing.term 126).labels beta n insertions =
    (L24Gluing.term 143).expression.scalarPointContraction X v
      (L24Gluing.term 143).decoration (L24Gluing.term 143).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core126 L24Gluing.term126.decoration L24Gluing.term126.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels126_143

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded126_eq143 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 126) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 143) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 126) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 143) (by decide +kernel)]
  exact scalar126_eq143 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted143_eq126 : originalWeighted 143 =
    (30824 / 12553 : ℚ) * originalWeighted 126 := by
  rw [originalWeighted, originalWeighted, ← guarded126_eq143,
    coefficient143, coefficient126]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels126_158 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar126_eq158 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 126).expression.scalarPointContraction X v
      (L24Gluing.term 126).decoration (L24Gluing.term 126).labels beta n insertions =
    (L24Gluing.term 158).expression.scalarPointContraction X v
      (L24Gluing.term 158).decoration (L24Gluing.term 158).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core126 L24Gluing.term126.decoration L24Gluing.term126.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels126_158

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded126_eq158 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 126) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 158) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 126) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 158) (by decide +kernel)]
  exact scalar126_eq158 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted158_eq126 : originalWeighted 158 =
    (30824 / 12553 : ℚ) * originalWeighted 126 := by
  rw [originalWeighted, originalWeighted, ← guarded126_eq158,
    coefficient158, coefficient126]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels127_144 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar127_eq144 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 127).expression.scalarPointContraction X v
      (L24Gluing.term 127).decoration (L24Gluing.term 127).labels beta n insertions =
    (L24Gluing.term 144).expression.scalarPointContraction X v
      (L24Gluing.term 144).decoration (L24Gluing.term 144).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core127 L24Gluing.term127.decoration L24Gluing.term127.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels127_144

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded127_eq144 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 127) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 144) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 127) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 144) (by decide +kernel)]
  exact scalar127_eq144 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted144_eq127 : originalWeighted 144 =
    (-28216 / 7527 : ℚ) * originalWeighted 127 := by
  rw [originalWeighted, originalWeighted, ← guarded127_eq144,
    coefficient144, coefficient127]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels127_159 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar127_eq159 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 127).expression.scalarPointContraction X v
      (L24Gluing.term 127).decoration (L24Gluing.term 127).labels beta n insertions =
    (L24Gluing.term 159).expression.scalarPointContraction X v
      (L24Gluing.term 159).decoration (L24Gluing.term 159).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core127 L24Gluing.term127.decoration L24Gluing.term127.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels127_159

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded127_eq159 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 127) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 159) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 127) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 159) (by decide +kernel)]
  exact scalar127_eq159 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted159_eq127 : originalWeighted 159 =
    (-28216 / 7527 : ℚ) * originalWeighted 127 := by
  rw [originalWeighted, originalWeighted, ← guarded127_eq159,
    coefficient159, coefficient127]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels128_145 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar128_eq145 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 128).expression.scalarPointContraction X v
      (L24Gluing.term 128).decoration (L24Gluing.term 128).labels beta n insertions =
    (L24Gluing.term 145).expression.scalarPointContraction X v
      (L24Gluing.term 145).decoration (L24Gluing.term 145).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core128 L24Gluing.term128.decoration L24Gluing.term128.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels128_145

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded128_eq145 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 128) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 145) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 128) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 145) (by decide +kernel)]
  exact scalar128_eq145 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted145_eq128 : originalWeighted 145 =
    (28216 / 82113 : ℚ) * originalWeighted 128 := by
  rw [originalWeighted, originalWeighted, ← guarded128_eq145,
    coefficient145, coefficient128]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels128_160 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar128_eq160 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 128).expression.scalarPointContraction X v
      (L24Gluing.term 128).decoration (L24Gluing.term 128).labels beta n insertions =
    (L24Gluing.term 160).expression.scalarPointContraction X v
      (L24Gluing.term 160).decoration (L24Gluing.term 160).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core128 L24Gluing.term128.decoration L24Gluing.term128.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels128_160

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded128_eq160 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 128) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 160) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 128) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 160) (by decide +kernel)]
  exact scalar128_eq160 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted160_eq128 : originalWeighted 160 =
    (28216 / 82113 : ℚ) * originalWeighted 128 := by
  rw [originalWeighted, originalWeighted, ← guarded128_eq160,
    coefficient160, coefficient128]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels129_146 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar129_eq146 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 129).expression.scalarPointContraction X v
      (L24Gluing.term 129).decoration (L24Gluing.term 129).labels beta n insertions =
    (L24Gluing.term 146).expression.scalarPointContraction X v
      (L24Gluing.term 146).decoration (L24Gluing.term 146).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core129 L24Gluing.term129.decoration L24Gluing.term129.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels129_146

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded129_eq146 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 129) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 146) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 129) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 146) (by decide +kernel)]
  exact scalar129_eq146 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted146_eq129 : originalWeighted 146 =
    (5960 / 2973 : ℚ) * originalWeighted 129 := by
  rw [originalWeighted, originalWeighted, ← guarded129_eq146,
    coefficient146, coefficient129]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels129_161 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar129_eq161 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 129).expression.scalarPointContraction X v
      (L24Gluing.term 129).decoration (L24Gluing.term 129).labels beta n insertions =
    (L24Gluing.term 161).expression.scalarPointContraction X v
      (L24Gluing.term 161).decoration (L24Gluing.term 161).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core129 L24Gluing.term129.decoration L24Gluing.term129.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels129_161

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded129_eq161 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 129) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 161) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 129) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 161) (by decide +kernel)]
  exact scalar129_eq161 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted161_eq129 : originalWeighted 161 =
    (5960 / 2973 : ℚ) * originalWeighted 129 := by
  rw [originalWeighted, originalWeighted, ← guarded129_eq161,
    coefficient161, coefficient129]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels130_147 :
    insertions ∘ L24Gluing.flagPermutation3 =
      insertions ∘ L24Gluing.flagPermutation11 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar130_eq147 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 130).expression.scalarPointContraction X v
      (L24Gluing.term 130).decoration (L24Gluing.term 130).labels beta n insertions =
    (L24Gluing.term 147).expression.scalarPointContraction X v
      (L24Gluing.term 147).decoration (L24Gluing.term 147).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core130 L24Gluing.term130.decoration L24Gluing.term130.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation11 beta n insertions labels130_147

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded130_eq147 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 130) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 147) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 130) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 147) (by decide +kernel)]
  exact scalar130_eq147 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted147_eq130 : originalWeighted 147 =
    (20933 / 42714 : ℚ) * originalWeighted 130 := by
  rw [originalWeighted, originalWeighted, ← guarded130_eq147,
    coefficient147, coefficient130]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels130_162 :
    insertions ∘ L24Gluing.flagPermutation3 =
      insertions ∘ L24Gluing.flagPermutation12 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar130_eq162 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 130).expression.scalarPointContraction X v
      (L24Gluing.term 130).decoration (L24Gluing.term 130).labels beta n insertions =
    (L24Gluing.term 162).expression.scalarPointContraction X v
      (L24Gluing.term 162).decoration (L24Gluing.term 162).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core130 L24Gluing.term130.decoration L24Gluing.term130.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation12 beta n insertions labels130_162

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded130_eq162 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 130) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 162) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 130) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 162) (by decide +kernel)]
  exact scalar130_eq162 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted162_eq130 : originalWeighted 162 =
    (20933 / 42714 : ℚ) * originalWeighted 130 := by
  rw [originalWeighted, originalWeighted, ← guarded130_eq162,
    coefficient162, coefficient130]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels131_148 :
    insertions ∘ L24Gluing.flagPermutation3 =
      insertions ∘ L24Gluing.flagPermutation11 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar131_eq148 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 131).expression.scalarPointContraction X v
      (L24Gluing.term 131).decoration (L24Gluing.term 131).labels beta n insertions =
    (L24Gluing.term 148).expression.scalarPointContraction X v
      (L24Gluing.term 148).decoration (L24Gluing.term 148).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core131 L24Gluing.term131.decoration L24Gluing.term131.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation11 beta n insertions labels131_148

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded131_eq148 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 131) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 148) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 131) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 148) (by decide +kernel)]
  exact scalar131_eq148 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted148_eq131 : originalWeighted 148 =
    (4229 / 50346 : ℚ) * originalWeighted 131 := by
  rw [originalWeighted, originalWeighted, ← guarded131_eq148,
    coefficient148, coefficient131]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels131_163 :
    insertions ∘ L24Gluing.flagPermutation3 =
      insertions ∘ L24Gluing.flagPermutation12 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar131_eq163 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 131).expression.scalarPointContraction X v
      (L24Gluing.term 131).decoration (L24Gluing.term 131).labels beta n insertions =
    (L24Gluing.term 163).expression.scalarPointContraction X v
      (L24Gluing.term 163).decoration (L24Gluing.term 163).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core131 L24Gluing.term131.decoration L24Gluing.term131.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation12 beta n insertions labels131_163

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded131_eq163 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 131) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 163) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 131) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 163) (by decide +kernel)]
  exact scalar131_eq163 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted163_eq131 : originalWeighted 163 =
    (4229 / 50346 : ℚ) * originalWeighted 131 := by
  rw [originalWeighted, originalWeighted, ← guarded131_eq163,
    coefficient163, coefficient131]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels132_149 :
    insertions ∘ L24Gluing.flagPermutation3 =
      insertions ∘ L24Gluing.flagPermutation11 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar132_eq149 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 132).expression.scalarPointContraction X v
      (L24Gluing.term 132).decoration (L24Gluing.term 132).labels beta n insertions =
    (L24Gluing.term 149).expression.scalarPointContraction X v
      (L24Gluing.term 149).decoration (L24Gluing.term 149).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core132 L24Gluing.term132.decoration L24Gluing.term132.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation11 beta n insertions labels132_149

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded132_eq149 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 132) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 149) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 132) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 149) (by decide +kernel)]
  exact scalar132_eq149 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted149_eq132 : originalWeighted 149 =
    (-27826 / 897 : ℚ) * originalWeighted 132 := by
  rw [originalWeighted, originalWeighted, ← guarded132_eq149,
    coefficient149, coefficient132]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels132_164 :
    insertions ∘ L24Gluing.flagPermutation3 =
      insertions ∘ L24Gluing.flagPermutation12 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar132_eq164 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 132).expression.scalarPointContraction X v
      (L24Gluing.term 132).decoration (L24Gluing.term 132).labels beta n insertions =
    (L24Gluing.term 164).expression.scalarPointContraction X v
      (L24Gluing.term 164).decoration (L24Gluing.term 164).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core132 L24Gluing.term132.decoration L24Gluing.term132.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation12 beta n insertions labels132_164

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded132_eq164 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 132) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 164) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 132) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 164) (by decide +kernel)]
  exact scalar132_eq164 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted164_eq132 : originalWeighted 164 =
    (-27826 / 897 : ℚ) * originalWeighted 132 := by
  rw [originalWeighted, originalWeighted, ← guarded132_eq164,
    coefficient164, coefficient132]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels134_150 :
    insertions ∘ L24Gluing.flagPermutation3 =
      insertions ∘ L24Gluing.flagPermutation11 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar134_eq150 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 134).expression.scalarPointContraction X v
      (L24Gluing.term 134).decoration (L24Gluing.term 134).labels beta n insertions =
    (L24Gluing.term 150).expression.scalarPointContraction X v
      (L24Gluing.term 150).decoration (L24Gluing.term 150).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core134 L24Gluing.term134.decoration L24Gluing.term134.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation11 beta n insertions labels134_150

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded134_eq150 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 134) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 150) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 134) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 150) (by decide +kernel)]
  exact scalar134_eq150 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted150_eq134 : originalWeighted 150 =
    (-4229 / 37854 : ℚ) * originalWeighted 134 := by
  rw [originalWeighted, originalWeighted, ← guarded134_eq150,
    coefficient150, coefficient134]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels134_165 :
    insertions ∘ L24Gluing.flagPermutation3 =
      insertions ∘ L24Gluing.flagPermutation12 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar134_eq165 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 134).expression.scalarPointContraction X v
      (L24Gluing.term 134).decoration (L24Gluing.term 134).labels beta n insertions =
    (L24Gluing.term 165).expression.scalarPointContraction X v
      (L24Gluing.term 165).decoration (L24Gluing.term 165).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core134 L24Gluing.term134.decoration L24Gluing.term134.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation12 beta n insertions labels134_165

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded134_eq165 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 134) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 165) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 134) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 165) (by decide +kernel)]
  exact scalar134_eq165 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted165_eq134 : originalWeighted 165 =
    (-4229 / 37854 : ℚ) * originalWeighted 134 := by
  rw [originalWeighted, originalWeighted, ← guarded134_eq165,
    coefficient165, coefficient134]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels135_151 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation9 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar135_eq151 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 135).expression.scalarPointContraction X v
      (L24Gluing.term 135).decoration (L24Gluing.term 135).labels beta n insertions =
    (L24Gluing.term 151).expression.scalarPointContraction X v
      (L24Gluing.term 151).decoration (L24Gluing.term 151).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core135 L24Gluing.term135.decoration L24Gluing.term135.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 beta n insertions labels135_151

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded135_eq151 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 135) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 151) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 135) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 151) (by decide +kernel)]
  exact scalar135_eq151 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted151_eq135 : originalWeighted 151 =
    (27826 / 54423 : ℚ) * originalWeighted 135 := by
  rw [originalWeighted, originalWeighted, ← guarded135_eq151,
    coefficient151, coefficient135]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels135_166 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation3 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar135_eq166 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 135).expression.scalarPointContraction X v
      (L24Gluing.term 135).decoration (L24Gluing.term 135).labels beta n insertions =
    (L24Gluing.term 166).expression.scalarPointContraction X v
      (L24Gluing.term 166).decoration (L24Gluing.term 166).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core135 L24Gluing.term135.decoration L24Gluing.term135.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 beta n insertions labels135_166

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded135_eq166 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 135) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 166) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 135) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 166) (by decide +kernel)]
  exact scalar135_eq166 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted166_eq135 : originalWeighted 166 =
    (27826 / 54423 : ℚ) * originalWeighted 135 := by
  rw [originalWeighted, originalWeighted, ← guarded135_eq166,
    coefficient166, coefficient135]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels137_152 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation9 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar137_eq152 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 137).expression.scalarPointContraction X v
      (L24Gluing.term 137).decoration (L24Gluing.term 137).labels beta n insertions =
    (L24Gluing.term 152).expression.scalarPointContraction X v
      (L24Gluing.term 152).decoration (L24Gluing.term 152).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core137 L24Gluing.term137.decoration L24Gluing.term137.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 beta n insertions labels137_152

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded137_eq152 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 137) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 152) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 137) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 152) (by decide +kernel)]
  exact scalar137_eq152 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted152_eq137 : originalWeighted 152 =
    (4229 / 151980 : ℚ) * originalWeighted 137 := by
  rw [originalWeighted, originalWeighted, ← guarded137_eq152,
    coefficient152, coefficient137]
  ring

end AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00

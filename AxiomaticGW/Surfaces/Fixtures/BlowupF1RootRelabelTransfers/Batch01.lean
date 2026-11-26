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

namespace AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01

open BlowupF1RootAssembly SurfaceGenusTwo GetzlerGraphs L24Gluing

private def core137 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core138 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core139 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core182 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])))

private def core183 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])))

private def core184 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])))

private def core185 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])))

private def core186 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core187 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core188 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core189 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core190 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core191 : GluingExpression 2 (Fin 4) :=
  join (m := 1) (n := 3) 1 3
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))

private def core192 : GluingExpression 2 (Fin 4) :=
  join (m := 1) (n := 3) 1 3
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))

theorem coefficient137 : L24CorrectionsReplay.fullClaim 137 =
    (-745 / 351 : ℚ) := by decide +kernel

theorem coefficient138 : L24CorrectionsReplay.fullClaim 138 =
    (1 / 15 : ℚ) := by decide +kernel

theorem coefficient139 : L24CorrectionsReplay.fullClaim 139 =
    (3853 / 1989 : ℚ) := by decide +kernel

theorem coefficient153 : L24CorrectionsReplay.fullClaim 153 =
    (20933 / 21060 : ℚ) := by decide +kernel

theorem coefficient154 : L24CorrectionsReplay.fullClaim 154 =
    (-4229 / 71604 : ℚ) := by decide +kernel

theorem coefficient167 : L24CorrectionsReplay.fullClaim 167 =
    (-4229 / 71604 : ℚ) := by decide +kernel

theorem coefficient168 : L24CorrectionsReplay.fullClaim 168 =
    (20933 / 21060 : ℚ) := by decide +kernel

theorem coefficient169 : L24CorrectionsReplay.fullClaim 169 =
    (-4229 / 71604 : ℚ) := by decide +kernel

theorem coefficient182 : L24CorrectionsReplay.fullClaim 182 =
    (4259 / 3510 : ℚ) := by decide +kernel

theorem coefficient183 : L24CorrectionsReplay.fullClaim 183 =
    (1 / 15 : ℚ) := by decide +kernel

theorem coefficient184 : L24CorrectionsReplay.fullClaim 184 =
    (161 / 270 : ℚ) := by decide +kernel

theorem coefficient185 : L24CorrectionsReplay.fullClaim 185 =
    (-745 / 351 : ℚ) := by decide +kernel

theorem coefficient186 : L24CorrectionsReplay.fullClaim 186 =
    (407 / 540 : ℚ) := by decide +kernel

theorem coefficient187 : L24CorrectionsReplay.fullClaim 187 =
    (12553 / 23868 : ℚ) := by decide +kernel

theorem coefficient188 : L24CorrectionsReplay.fullClaim 188 =
    (27371 / 14040 : ℚ) := by decide +kernel

theorem coefficient189 : L24CorrectionsReplay.fullClaim 189 =
    (-193 / 1080 : ℚ) := by decide +kernel

theorem coefficient190 : L24CorrectionsReplay.fullClaim 190 =
    (-991 / 1404 : ℚ) := by decide +kernel

theorem coefficient191 : L24CorrectionsReplay.fullClaim 191 =
    (1 / 15 : ℚ) := by decide +kernel

theorem coefficient192 : L24CorrectionsReplay.fullClaim 192 =
    (3853 / 1989 : ℚ) := by decide +kernel

theorem coefficient201 : L24CorrectionsReplay.fullClaim 201 =
    (4259 / 3510 : ℚ) := by decide +kernel

theorem coefficient202 : L24CorrectionsReplay.fullClaim 202 =
    (1 / 15 : ℚ) := by decide +kernel

theorem coefficient203 : L24CorrectionsReplay.fullClaim 203 =
    (161 / 270 : ℚ) := by decide +kernel

theorem coefficient204 : L24CorrectionsReplay.fullClaim 204 =
    (-745 / 351 : ℚ) := by decide +kernel

theorem coefficient205 : L24CorrectionsReplay.fullClaim 205 =
    (407 / 540 : ℚ) := by decide +kernel

theorem coefficient206 : L24CorrectionsReplay.fullClaim 206 =
    (12553 / 23868 : ℚ) := by decide +kernel

theorem coefficient207 : L24CorrectionsReplay.fullClaim 207 =
    (27371 / 14040 : ℚ) := by decide +kernel

theorem coefficient208 : L24CorrectionsReplay.fullClaim 208 =
    (-193 / 1080 : ℚ) := by decide +kernel

theorem coefficient209 : L24CorrectionsReplay.fullClaim 209 =
    (-991 / 1404 : ℚ) := by decide +kernel

theorem coefficient210 : L24CorrectionsReplay.fullClaim 210 =
    (1 / 15 : ℚ) := by decide +kernel

theorem coefficient211 : L24CorrectionsReplay.fullClaim 211 =
    (3853 / 1989 : ℚ) := by decide +kernel

theorem coefficient233 : L24CorrectionsReplay.fullClaim 233 =
    (3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient234 : L24CorrectionsReplay.fullClaim 234 =
    (3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient235 : L24CorrectionsReplay.fullClaim 235 =
    (-1490 / 1053 : ℚ) := by decide +kernel

theorem coefficient236 : L24CorrectionsReplay.fullClaim 236 =
    (7706 / 5967 : ℚ) := by decide +kernel

theorem coefficient237 : L24CorrectionsReplay.fullClaim 237 =
    (3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient238 : L24CorrectionsReplay.fullClaim 238 =
    (3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient239 : L24CorrectionsReplay.fullClaim 239 =
    (-1490 / 1053 : ℚ) := by decide +kernel

theorem coefficient240 : L24CorrectionsReplay.fullClaim 240 =
    (20933 / 21060 : ℚ) := by decide +kernel

theorem coefficient241 : L24CorrectionsReplay.fullClaim 241 =
    (-4229 / 71604 : ℚ) := by decide +kernel

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels137_167 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation3 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar137_eq167 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 137).expression.scalarPointContraction X v
      (L24Gluing.term 137).decoration (L24Gluing.term 137).labels beta n insertions =
    (L24Gluing.term 167).expression.scalarPointContraction X v
      (L24Gluing.term 167).decoration (L24Gluing.term 167).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core137 L24Gluing.term137.decoration L24Gluing.term137.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 beta n insertions labels137_167

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded137_eq167 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 137) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 167) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 137) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 167) (by decide +kernel)]
  exact scalar137_eq167 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted167_eq137 : originalWeighted 167 =
    (4229 / 151980 : ℚ) * originalWeighted 137 := by
  rw [originalWeighted, originalWeighted, ← guarded137_eq167,
    coefficient167, coefficient137]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels138_153 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation9 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar138_eq153 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 138).expression.scalarPointContraction X v
      (L24Gluing.term 138).decoration (L24Gluing.term 138).labels beta n insertions =
    (L24Gluing.term 153).expression.scalarPointContraction X v
      (L24Gluing.term 153).decoration (L24Gluing.term 153).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core138 L24Gluing.term138.decoration L24Gluing.term138.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 beta n insertions labels138_153

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded138_eq153 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 138) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 153) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 138) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 153) (by decide +kernel)]
  exact scalar138_eq153 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted153_eq138 : originalWeighted 153 =
    (20933 / 1404 : ℚ) * originalWeighted 138 := by
  rw [originalWeighted, originalWeighted, ← guarded138_eq153,
    coefficient153, coefficient138]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels138_168 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation3 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar138_eq168 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 138).expression.scalarPointContraction X v
      (L24Gluing.term 138).decoration (L24Gluing.term 138).labels beta n insertions =
    (L24Gluing.term 168).expression.scalarPointContraction X v
      (L24Gluing.term 168).decoration (L24Gluing.term 168).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core138 L24Gluing.term138.decoration L24Gluing.term138.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 beta n insertions labels138_168

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded138_eq168 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 138) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 168) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 138) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 168) (by decide +kernel)]
  exact scalar138_eq168 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted168_eq138 : originalWeighted 168 =
    (20933 / 1404 : ℚ) * originalWeighted 138 := by
  rw [originalWeighted, originalWeighted, ← guarded138_eq168,
    coefficient168, coefficient138]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels139_154 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation9 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar139_eq154 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 139).expression.scalarPointContraction X v
      (L24Gluing.term 139).decoration (L24Gluing.term 139).labels beta n insertions =
    (L24Gluing.term 154).expression.scalarPointContraction X v
      (L24Gluing.term 154).decoration (L24Gluing.term 154).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core139 L24Gluing.term139.decoration L24Gluing.term139.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 beta n insertions labels139_154

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded139_eq154 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 139) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 154) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 139) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 154) (by decide +kernel)]
  exact scalar139_eq154 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted154_eq139 : originalWeighted 154 =
    (-4229 / 138708 : ℚ) * originalWeighted 139 := by
  rw [originalWeighted, originalWeighted, ← guarded139_eq154,
    coefficient154, coefficient139]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels139_169 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation3 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar139_eq169 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 139).expression.scalarPointContraction X v
      (L24Gluing.term 139).decoration (L24Gluing.term 139).labels beta n insertions =
    (L24Gluing.term 169).expression.scalarPointContraction X v
      (L24Gluing.term 169).decoration (L24Gluing.term 169).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core139 L24Gluing.term139.decoration L24Gluing.term139.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 beta n insertions labels139_169

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded139_eq169 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 139) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 169) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 139) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 169) (by decide +kernel)]
  exact scalar139_eq169 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted169_eq139 : originalWeighted 169 =
    (-4229 / 138708 : ℚ) * originalWeighted 139 := by
  rw [originalWeighted, originalWeighted, ← guarded139_eq169,
    coefficient169, coefficient139]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels182_201 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar182_eq201 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 182).expression.scalarPointContraction X v
      (L24Gluing.term 182).decoration (L24Gluing.term 182).labels beta n insertions =
    (L24Gluing.term 201).expression.scalarPointContraction X v
      (L24Gluing.term 201).decoration (L24Gluing.term 201).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core182 L24Gluing.term182.decoration L24Gluing.term182.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels182_201

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded182_eq201 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 182) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 201) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 182) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 201) (by decide +kernel)]
  exact scalar182_eq201 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted201_eq182 : originalWeighted 201 =
    (1 / 1 : ℚ) * originalWeighted 182 := by
  rw [originalWeighted, originalWeighted, ← guarded182_eq201,
    coefficient201, coefficient182]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels182_233 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar182_eq233 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 182).expression.scalarPointContraction X v
      (L24Gluing.term 182).decoration (L24Gluing.term 182).labels beta n insertions =
    (L24Gluing.term 233).expression.scalarPointContraction X v
      (L24Gluing.term 233).decoration (L24Gluing.term 233).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core182 L24Gluing.term182.decoration L24Gluing.term182.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels182_233

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded182_eq233 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 182) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 233) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 182) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 233) (by decide +kernel)]
  exact scalar182_eq233 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted233_eq182 : originalWeighted 233 =
    (7054 / 12777 : ℚ) * originalWeighted 182 := by
  rw [originalWeighted, originalWeighted, ← guarded182_eq233,
    coefficient233, coefficient182]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels183_202 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar183_eq202 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 183).expression.scalarPointContraction X v
      (L24Gluing.term 183).decoration (L24Gluing.term 183).labels beta n insertions =
    (L24Gluing.term 202).expression.scalarPointContraction X v
      (L24Gluing.term 202).decoration (L24Gluing.term 202).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core183 L24Gluing.term183.decoration L24Gluing.term183.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels183_202

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded183_eq202 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 183) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 202) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 183) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 202) (by decide +kernel)]
  exact scalar183_eq202 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted202_eq183 : originalWeighted 202 =
    (1 / 1 : ℚ) * originalWeighted 183 := by
  rw [originalWeighted, originalWeighted, ← guarded183_eq202,
    coefficient202, coefficient183]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels183_234 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar183_eq234 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 183).expression.scalarPointContraction X v
      (L24Gluing.term 183).decoration (L24Gluing.term 183).labels beta n insertions =
    (L24Gluing.term 234).expression.scalarPointContraction X v
      (L24Gluing.term 234).decoration (L24Gluing.term 234).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core183 L24Gluing.term183.decoration L24Gluing.term183.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels183_234

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded183_eq234 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 183) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 234) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 183) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 234) (by decide +kernel)]
  exact scalar183_eq234 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted234_eq183 : originalWeighted 234 =
    (3527 / 351 : ℚ) * originalWeighted 183 := by
  rw [originalWeighted, originalWeighted, ← guarded183_eq234,
    coefficient234, coefficient183]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels184_203 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar184_eq203 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 184).expression.scalarPointContraction X v
      (L24Gluing.term 184).decoration (L24Gluing.term 184).labels beta n insertions =
    (L24Gluing.term 203).expression.scalarPointContraction X v
      (L24Gluing.term 203).decoration (L24Gluing.term 203).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core184 L24Gluing.term184.decoration L24Gluing.term184.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels184_203

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded184_eq203 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 184) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 203) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 184) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 203) (by decide +kernel)]
  exact scalar184_eq203 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted203_eq184 : originalWeighted 203 =
    (1 / 1 : ℚ) * originalWeighted 184 := by
  rw [originalWeighted, originalWeighted, ← guarded184_eq203,
    coefficient203, coefficient184]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels185_204 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar185_eq204 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 185).expression.scalarPointContraction X v
      (L24Gluing.term 185).decoration (L24Gluing.term 185).labels beta n insertions =
    (L24Gluing.term 204).expression.scalarPointContraction X v
      (L24Gluing.term 204).decoration (L24Gluing.term 204).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core185 L24Gluing.term185.decoration L24Gluing.term185.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels185_204

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded185_eq204 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 185) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 204) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 185) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 204) (by decide +kernel)]
  exact scalar185_eq204 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted204_eq185 : originalWeighted 204 =
    (1 / 1 : ℚ) * originalWeighted 185 := by
  rw [originalWeighted, originalWeighted, ← guarded185_eq204,
    coefficient204, coefficient185]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels185_235 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar185_eq235 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 185).expression.scalarPointContraction X v
      (L24Gluing.term 185).decoration (L24Gluing.term 185).labels beta n insertions =
    (L24Gluing.term 235).expression.scalarPointContraction X v
      (L24Gluing.term 235).decoration (L24Gluing.term 235).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core185 L24Gluing.term185.decoration L24Gluing.term185.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels185_235

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded185_eq235 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 185) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 235) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 185) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 235) (by decide +kernel)]
  exact scalar185_eq235 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted235_eq185 : originalWeighted 235 =
    (2 / 3 : ℚ) * originalWeighted 185 := by
  rw [originalWeighted, originalWeighted, ← guarded185_eq235,
    coefficient235, coefficient185]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels186_205 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar186_eq205 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 186).expression.scalarPointContraction X v
      (L24Gluing.term 186).decoration (L24Gluing.term 186).labels beta n insertions =
    (L24Gluing.term 205).expression.scalarPointContraction X v
      (L24Gluing.term 205).decoration (L24Gluing.term 205).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core186 L24Gluing.term186.decoration L24Gluing.term186.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels186_205

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded186_eq205 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 186) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 205) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 186) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 205) (by decide +kernel)]
  exact scalar186_eq205 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted205_eq186 : originalWeighted 205 =
    (1 / 1 : ℚ) * originalWeighted 186 := by
  rw [originalWeighted, originalWeighted, ← guarded186_eq205,
    coefficient205, coefficient186]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels187_206 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar187_eq206 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 187).expression.scalarPointContraction X v
      (L24Gluing.term 187).decoration (L24Gluing.term 187).labels beta n insertions =
    (L24Gluing.term 206).expression.scalarPointContraction X v
      (L24Gluing.term 206).decoration (L24Gluing.term 206).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core187 L24Gluing.term187.decoration L24Gluing.term187.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels187_206

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded187_eq206 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 187) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 206) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 187) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 206) (by decide +kernel)]
  exact scalar187_eq206 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted206_eq187 : originalWeighted 206 =
    (1 / 1 : ℚ) * originalWeighted 187 := by
  rw [originalWeighted, originalWeighted, ← guarded187_eq206,
    coefficient206, coefficient187]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels187_236 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar187_eq236 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 187).expression.scalarPointContraction X v
      (L24Gluing.term 187).decoration (L24Gluing.term 187).labels beta n insertions =
    (L24Gluing.term 236).expression.scalarPointContraction X v
      (L24Gluing.term 236).decoration (L24Gluing.term 236).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core187 L24Gluing.term187.decoration L24Gluing.term187.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels187_236

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded187_eq236 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 187) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 236) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 187) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 236) (by decide +kernel)]
  exact scalar187_eq236 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted236_eq187 : originalWeighted 236 =
    (30824 / 12553 : ℚ) * originalWeighted 187 := by
  rw [originalWeighted, originalWeighted, ← guarded187_eq236,
    coefficient236, coefficient187]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels188_207 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar188_eq207 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 188).expression.scalarPointContraction X v
      (L24Gluing.term 188).decoration (L24Gluing.term 188).labels beta n insertions =
    (L24Gluing.term 207).expression.scalarPointContraction X v
      (L24Gluing.term 207).decoration (L24Gluing.term 207).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core188 L24Gluing.term188.decoration L24Gluing.term188.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels188_207

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded188_eq207 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 188) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 207) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 188) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 207) (by decide +kernel)]
  exact scalar188_eq207 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted207_eq188 : originalWeighted 207 =
    (1 / 1 : ℚ) * originalWeighted 188 := by
  rw [originalWeighted, originalWeighted, ← guarded188_eq207,
    coefficient207, coefficient188]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels188_237 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar188_eq237 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 188).expression.scalarPointContraction X v
      (L24Gluing.term 188).decoration (L24Gluing.term 188).labels beta n insertions =
    (L24Gluing.term 237).expression.scalarPointContraction X v
      (L24Gluing.term 237).decoration (L24Gluing.term 237).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core188 L24Gluing.term188.decoration L24Gluing.term188.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels188_237

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded188_eq237 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 188) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 237) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 188) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 237) (by decide +kernel)]
  exact scalar188_eq237 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted237_eq188 : originalWeighted 237 =
    (28216 / 82113 : ℚ) * originalWeighted 188 := by
  rw [originalWeighted, originalWeighted, ← guarded188_eq237,
    coefficient237, coefficient188]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels189_208 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar189_eq208 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 189).expression.scalarPointContraction X v
      (L24Gluing.term 189).decoration (L24Gluing.term 189).labels beta n insertions =
    (L24Gluing.term 208).expression.scalarPointContraction X v
      (L24Gluing.term 208).decoration (L24Gluing.term 208).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core189 L24Gluing.term189.decoration L24Gluing.term189.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels189_208

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded189_eq208 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 189) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 208) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 189) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 208) (by decide +kernel)]
  exact scalar189_eq208 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted208_eq189 : originalWeighted 208 =
    (1 / 1 : ℚ) * originalWeighted 189 := by
  rw [originalWeighted, originalWeighted, ← guarded189_eq208,
    coefficient208, coefficient189]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels189_238 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar189_eq238 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 189).expression.scalarPointContraction X v
      (L24Gluing.term 189).decoration (L24Gluing.term 189).labels beta n insertions =
    (L24Gluing.term 238).expression.scalarPointContraction X v
      (L24Gluing.term 238).decoration (L24Gluing.term 238).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core189 L24Gluing.term189.decoration L24Gluing.term189.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels189_238

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded189_eq238 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 189) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 238) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 189) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 238) (by decide +kernel)]
  exact scalar189_eq238 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted238_eq189 : originalWeighted 238 =
    (-28216 / 7527 : ℚ) * originalWeighted 189 := by
  rw [originalWeighted, originalWeighted, ← guarded189_eq238,
    coefficient238, coefficient189]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels190_209 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar190_eq209 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 190).expression.scalarPointContraction X v
      (L24Gluing.term 190).decoration (L24Gluing.term 190).labels beta n insertions =
    (L24Gluing.term 209).expression.scalarPointContraction X v
      (L24Gluing.term 209).decoration (L24Gluing.term 209).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core190 L24Gluing.term190.decoration L24Gluing.term190.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels190_209

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded190_eq209 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 190) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 209) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 190) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 209) (by decide +kernel)]
  exact scalar190_eq209 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted209_eq190 : originalWeighted 209 =
    (1 / 1 : ℚ) * originalWeighted 190 := by
  rw [originalWeighted, originalWeighted, ← guarded190_eq209,
    coefficient209, coefficient190]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels190_239 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar190_eq239 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 190).expression.scalarPointContraction X v
      (L24Gluing.term 190).decoration (L24Gluing.term 190).labels beta n insertions =
    (L24Gluing.term 239).expression.scalarPointContraction X v
      (L24Gluing.term 239).decoration (L24Gluing.term 239).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core190 L24Gluing.term190.decoration L24Gluing.term190.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels190_239

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded190_eq239 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 190) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 239) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 190) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 239) (by decide +kernel)]
  exact scalar190_eq239 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted239_eq190 : originalWeighted 239 =
    (5960 / 2973 : ℚ) * originalWeighted 190 := by
  rw [originalWeighted, originalWeighted, ← guarded190_eq239,
    coefficient239, coefficient190]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels191_210 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation14 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar191_eq210 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 191).expression.scalarPointContraction X v
      (L24Gluing.term 191).decoration (L24Gluing.term 191).labels beta n insertions =
    (L24Gluing.term 210).expression.scalarPointContraction X v
      (L24Gluing.term 210).decoration (L24Gluing.term 210).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core191 L24Gluing.term191.decoration L24Gluing.term191.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation14 beta n insertions labels191_210

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded191_eq210 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 191) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 210) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 191) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 210) (by decide +kernel)]
  exact scalar191_eq210 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted210_eq191 : originalWeighted 210 =
    (1 / 1 : ℚ) * originalWeighted 191 := by
  rw [originalWeighted, originalWeighted, ← guarded191_eq210,
    coefficient210, coefficient191]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels191_240 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation15 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar191_eq240 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 191).expression.scalarPointContraction X v
      (L24Gluing.term 191).decoration (L24Gluing.term 191).labels beta n insertions =
    (L24Gluing.term 240).expression.scalarPointContraction X v
      (L24Gluing.term 240).decoration (L24Gluing.term 240).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core191 L24Gluing.term191.decoration L24Gluing.term191.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation15 beta n insertions labels191_240

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded191_eq240 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 191) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 240) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 191) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 240) (by decide +kernel)]
  exact scalar191_eq240 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted240_eq191 : originalWeighted 240 =
    (20933 / 1404 : ℚ) * originalWeighted 191 := by
  rw [originalWeighted, originalWeighted, ← guarded191_eq240,
    coefficient240, coefficient191]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels192_211 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation14 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar192_eq211 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 192).expression.scalarPointContraction X v
      (L24Gluing.term 192).decoration (L24Gluing.term 192).labels beta n insertions =
    (L24Gluing.term 211).expression.scalarPointContraction X v
      (L24Gluing.term 211).decoration (L24Gluing.term 211).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core192 L24Gluing.term192.decoration L24Gluing.term192.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation14 beta n insertions labels192_211

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded192_eq211 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 192) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 211) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 192) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 211) (by decide +kernel)]
  exact scalar192_eq211 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted211_eq192 : originalWeighted 211 =
    (1 / 1 : ℚ) * originalWeighted 192 := by
  rw [originalWeighted, originalWeighted, ← guarded192_eq211,
    coefficient211, coefficient192]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels192_241 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation15 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar192_eq241 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 192).expression.scalarPointContraction X v
      (L24Gluing.term 192).decoration (L24Gluing.term 192).labels beta n insertions =
    (L24Gluing.term 241).expression.scalarPointContraction X v
      (L24Gluing.term 241).decoration (L24Gluing.term 241).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core192 L24Gluing.term192.decoration L24Gluing.term192.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation15 beta n insertions labels192_241

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded192_eq241 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 192) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 241) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 192) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 241) (by decide +kernel)]
  exact scalar192_eq241 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted241_eq192 : originalWeighted 241 =
    (-4229 / 138708 : ℚ) * originalWeighted 192 := by
  rw [originalWeighted, originalWeighted, ← guarded192_eq241,
    coefficient241, coefficient192]
  ring

end AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01

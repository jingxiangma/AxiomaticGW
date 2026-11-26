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

namespace AxiomaticGW.BlowupF1RootRelabelTransfers.Pilot

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

private def core744 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 6) (n := 0) 6 0
    (join (m := 2) (n := 5) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

theorem coefficient121 : L24CorrectionsReplay.fullClaim 121 =
    (1 / 15 : ℚ) := by decide +kernel

theorem coefficient122 : L24CorrectionsReplay.fullClaim 122 =
    (4259 / 3510 : ℚ) := by decide +kernel

theorem coefficient140 : L24CorrectionsReplay.fullClaim 140 =
    (3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient141 : L24CorrectionsReplay.fullClaim 141 =
    (3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient155 : L24CorrectionsReplay.fullClaim 155 =
    (3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient156 : L24CorrectionsReplay.fullClaim 156 =
    (3527 / 5265 : ℚ) := by decide +kernel

theorem coefficient744 : L24CorrectionsReplay.fullClaim 744 =
    (-227 / 9360 : ℚ) := by decide +kernel

theorem coefficient762 : L24CorrectionsReplay.fullClaim 762 =
    (-227 / 9360 : ℚ) := by decide +kernel

theorem coefficient788 : L24CorrectionsReplay.fullClaim 788 =
    (-227 / 14040 : ℚ) := by decide +kernel

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
theorem labels744_762 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar744_eq762 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 744).expression.scalarPointContraction X v
      (L24Gluing.term 744).decoration (L24Gluing.term 744).labels beta n insertions =
    (L24Gluing.term 762).expression.scalarPointContraction X v
      (L24Gluing.term 762).decoration (L24Gluing.term 762).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core744 L24Gluing.term744.decoration L24Gluing.term744.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels744_762

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded744_eq762 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 744) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 762) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 744) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 762) (by decide +kernel)]
  exact scalar744_eq762 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted762_eq744 : originalWeighted 762 =
    (1 / 1 : ℚ) * originalWeighted 744 := by
  rw [originalWeighted, originalWeighted, ← guarded744_eq762,
    coefficient762, coefficient744]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels744_788 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar744_eq788 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 744).expression.scalarPointContraction X v
      (L24Gluing.term 744).decoration (L24Gluing.term 744).labels beta n insertions =
    (L24Gluing.term 788).expression.scalarPointContraction X v
      (L24Gluing.term 788).decoration (L24Gluing.term 788).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core744 L24Gluing.term744.decoration L24Gluing.term744.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels744_788

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded744_eq788 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 744) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 788) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 744) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 788) (by decide +kernel)]
  exact scalar744_eq788 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted788_eq744 : originalWeighted 788 =
    (2 / 3 : ℚ) * originalWeighted 744 := by
  rw [originalWeighted, originalWeighted, ← guarded744_eq788,
    coefficient788, coefficient744]
  ring

end AxiomaticGW.BlowupF1RootRelabelTransfers.Pilot

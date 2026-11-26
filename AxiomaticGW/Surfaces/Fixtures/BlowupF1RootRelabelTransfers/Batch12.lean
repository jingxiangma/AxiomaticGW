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

namespace AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12

open BlowupF1RootAssembly SurfaceGenusTwo GetzlerGraphs L24Gluing

private def core635 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)

private def core636 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)

private def core637 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)

private def core642 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 5) (n := 1) 5 1
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)

private def core643 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 5) (n := 1) 5 1
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)

private def core644 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 5) (n := 1) 5 1
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)

private def core645 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 5) (n := 1) 5 1
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)

private def core662 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 3
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core663 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 3
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core664 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)

private def core665 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 4) (n := 2) 4 2
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core666 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 0 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation24)

private def core667 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 1 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)

theorem coefficient635 : L24CorrectionsReplay.fullClaim 635 =
    (-1 / 240 : ℚ) := by decide +kernel

theorem coefficient636 : L24CorrectionsReplay.fullClaim 636 =
    (1 / 80 : ℚ) := by decide +kernel

theorem coefficient637 : L24CorrectionsReplay.fullClaim 637 =
    (1 / 80 : ℚ) := by decide +kernel

theorem coefficient640 : L24CorrectionsReplay.fullClaim 640 =
    (1 / 80 : ℚ) := by decide +kernel

theorem coefficient641 : L24CorrectionsReplay.fullClaim 641 =
    (1 / 80 : ℚ) := by decide +kernel

theorem coefficient642 : L24CorrectionsReplay.fullClaim 642 =
    (-1 / 240 : ℚ) := by decide +kernel

theorem coefficient643 : L24CorrectionsReplay.fullClaim 643 =
    (-1 / 240 : ℚ) := by decide +kernel

theorem coefficient644 : L24CorrectionsReplay.fullClaim 644 =
    (-1 / 240 : ℚ) := by decide +kernel

theorem coefficient645 : L24CorrectionsReplay.fullClaim 645 =
    (-3 / 80 : ℚ) := by decide +kernel

theorem coefficient647 : L24CorrectionsReplay.fullClaim 647 =
    (-1 / 80 : ℚ) := by decide +kernel

theorem coefficient648 : L24CorrectionsReplay.fullClaim 648 =
    (1 / 240 : ℚ) := by decide +kernel

theorem coefficient649 : L24CorrectionsReplay.fullClaim 649 =
    (1 / 240 : ℚ) := by decide +kernel

theorem coefficient650 : L24CorrectionsReplay.fullClaim 650 =
    (1 / 720 : ℚ) := by decide +kernel

theorem coefficient651 : L24CorrectionsReplay.fullClaim 651 =
    (-1 / 48 : ℚ) := by decide +kernel

theorem coefficient652 : L24CorrectionsReplay.fullClaim 652 =
    (1 / 720 : ℚ) := by decide +kernel

theorem coefficient653 : L24CorrectionsReplay.fullClaim 653 =
    (-7 / 720 : ℚ) := by decide +kernel

theorem coefficient654 : L24CorrectionsReplay.fullClaim 654 =
    (1 / 720 : ℚ) := by decide +kernel

theorem coefficient655 : L24CorrectionsReplay.fullClaim 655 =
    (-1 / 48 : ℚ) := by decide +kernel

theorem coefficient656 : L24CorrectionsReplay.fullClaim 656 =
    (1 / 720 : ℚ) := by decide +kernel

theorem coefficient657 : L24CorrectionsReplay.fullClaim 657 =
    (-7 / 720 : ℚ) := by decide +kernel

theorem coefficient662 : L24CorrectionsReplay.fullClaim 662 =
    (-491 / 5616 : ℚ) := by decide +kernel

theorem coefficient663 : L24CorrectionsReplay.fullClaim 663 =
    (-79 / 2160 : ℚ) := by decide +kernel

theorem coefficient664 : L24CorrectionsReplay.fullClaim 664 =
    (-5299 / 42120 : ℚ) := by decide +kernel

theorem coefficient665 : L24CorrectionsReplay.fullClaim 665 =
    (-491 / 5616 : ℚ) := by decide +kernel

theorem coefficient666 : L24CorrectionsReplay.fullClaim 666 =
    (641 / 28080 : ℚ) := by decide +kernel

theorem coefficient667 : L24CorrectionsReplay.fullClaim 667 =
    (-629 / 28080 : ℚ) := by decide +kernel

theorem coefficient681 : L24CorrectionsReplay.fullClaim 681 =
    (-2923 / 84240 : ℚ) := by decide +kernel

theorem coefficient682 : L24CorrectionsReplay.fullClaim 682 =
    (-2923 / 84240 : ℚ) := by decide +kernel

theorem coefficient683 : L24CorrectionsReplay.fullClaim 683 =
    (-5299 / 42120 : ℚ) := by decide +kernel

theorem coefficient684 : L24CorrectionsReplay.fullClaim 684 =
    (-491 / 8424 : ℚ) := by decide +kernel

theorem coefficient685 : L24CorrectionsReplay.fullClaim 685 =
    (539 / 8424 : ℚ) := by decide +kernel

theorem coefficient686 : L24CorrectionsReplay.fullClaim 686 =
    (1 / 7020 : ℚ) := by decide +kernel

theorem coefficient700 : L24CorrectionsReplay.fullClaim 700 =
    (-2923 / 84240 : ℚ) := by decide +kernel

theorem coefficient701 : L24CorrectionsReplay.fullClaim 701 =
    (-2923 / 84240 : ℚ) := by decide +kernel

theorem coefficient702 : L24CorrectionsReplay.fullClaim 702 =
    (-5299 / 42120 : ℚ) := by decide +kernel

theorem coefficient703 : L24CorrectionsReplay.fullClaim 703 =
    (-491 / 8424 : ℚ) := by decide +kernel

theorem coefficient704 : L24CorrectionsReplay.fullClaim 704 =
    (539 / 8424 : ℚ) := by decide +kernel

theorem coefficient705 : L24CorrectionsReplay.fullClaim 705 =
    (1 / 7020 : ℚ) := by decide +kernel

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels635_647 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar635_eq647 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 635).expression.scalarPointContraction X v
      (L24Gluing.term 635).decoration (L24Gluing.term 635).labels beta n insertions =
    (L24Gluing.term 647).expression.scalarPointContraction X v
      (L24Gluing.term 647).decoration (L24Gluing.term 647).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core635 L24Gluing.term635.decoration L24Gluing.term635.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels635_647

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded635_eq647 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 635) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 647) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 635) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 647) (by decide +kernel)]
  exact scalar635_eq647 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted647_eq635 : originalWeighted 647 =
    (3 / 1 : ℚ) * originalWeighted 635 := by
  rw [originalWeighted, originalWeighted, ← guarded635_eq647,
    coefficient647, coefficient635]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels636_640 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar636_eq640 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 636).expression.scalarPointContraction X v
      (L24Gluing.term 636).decoration (L24Gluing.term 636).labels beta n insertions =
    (L24Gluing.term 640).expression.scalarPointContraction X v
      (L24Gluing.term 640).decoration (L24Gluing.term 640).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core636 L24Gluing.term636.decoration L24Gluing.term636.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels636_640

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded636_eq640 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 636) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 640) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 636) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 640) (by decide +kernel)]
  exact scalar636_eq640 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted640_eq636 : originalWeighted 640 =
    (1 / 1 : ℚ) * originalWeighted 636 := by
  rw [originalWeighted, originalWeighted, ← guarded636_eq640,
    coefficient640, coefficient636]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels636_648 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar636_eq648 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 636).expression.scalarPointContraction X v
      (L24Gluing.term 636).decoration (L24Gluing.term 636).labels beta n insertions =
    (L24Gluing.term 648).expression.scalarPointContraction X v
      (L24Gluing.term 648).decoration (L24Gluing.term 648).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core636 L24Gluing.term636.decoration L24Gluing.term636.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels636_648

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded636_eq648 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 636) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 648) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 636) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 648) (by decide +kernel)]
  exact scalar636_eq648 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted648_eq636 : originalWeighted 648 =
    (1 / 3 : ℚ) * originalWeighted 636 := by
  rw [originalWeighted, originalWeighted, ← guarded636_eq648,
    coefficient648, coefficient636]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels637_641 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar637_eq641 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 637).expression.scalarPointContraction X v
      (L24Gluing.term 637).decoration (L24Gluing.term 637).labels beta n insertions =
    (L24Gluing.term 641).expression.scalarPointContraction X v
      (L24Gluing.term 641).decoration (L24Gluing.term 641).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core637 L24Gluing.term637.decoration L24Gluing.term637.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels637_641

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded637_eq641 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 637) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 641) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 637) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 641) (by decide +kernel)]
  exact scalar637_eq641 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted641_eq637 : originalWeighted 641 =
    (1 / 1 : ℚ) * originalWeighted 637 := by
  rw [originalWeighted, originalWeighted, ← guarded637_eq641,
    coefficient641, coefficient637]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels637_649 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar637_eq649 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 637).expression.scalarPointContraction X v
      (L24Gluing.term 637).decoration (L24Gluing.term 637).labels beta n insertions =
    (L24Gluing.term 649).expression.scalarPointContraction X v
      (L24Gluing.term 649).decoration (L24Gluing.term 649).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core637 L24Gluing.term637.decoration L24Gluing.term637.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels637_649

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded637_eq649 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 637) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 649) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 637) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 649) (by decide +kernel)]
  exact scalar637_eq649 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted649_eq637 : originalWeighted 649 =
    (1 / 3 : ℚ) * originalWeighted 637 := by
  rw [originalWeighted, originalWeighted, ← guarded637_eq649,
    coefficient649, coefficient637]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels642_650 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar642_eq650 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 642).expression.scalarPointContraction X v
      (L24Gluing.term 642).decoration (L24Gluing.term 642).labels beta n insertions =
    (L24Gluing.term 650).expression.scalarPointContraction X v
      (L24Gluing.term 650).decoration (L24Gluing.term 650).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core642 L24Gluing.term642.decoration L24Gluing.term642.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels642_650

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded642_eq650 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 642) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 650) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 642) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 650) (by decide +kernel)]
  exact scalar642_eq650 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted650_eq642 : originalWeighted 650 =
    (-1 / 3 : ℚ) * originalWeighted 642 := by
  rw [originalWeighted, originalWeighted, ← guarded642_eq650,
    coefficient650, coefficient642]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels642_654 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar642_eq654 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 642).expression.scalarPointContraction X v
      (L24Gluing.term 642).decoration (L24Gluing.term 642).labels beta n insertions =
    (L24Gluing.term 654).expression.scalarPointContraction X v
      (L24Gluing.term 654).decoration (L24Gluing.term 654).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core642 L24Gluing.term642.decoration L24Gluing.term642.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels642_654

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded642_eq654 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 642) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 654) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 642) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 654) (by decide +kernel)]
  exact scalar642_eq654 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted654_eq642 : originalWeighted 654 =
    (-1 / 3 : ℚ) * originalWeighted 642 := by
  rw [originalWeighted, originalWeighted, ← guarded642_eq654,
    coefficient654, coefficient642]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels643_651 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar643_eq651 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 643).expression.scalarPointContraction X v
      (L24Gluing.term 643).decoration (L24Gluing.term 643).labels beta n insertions =
    (L24Gluing.term 651).expression.scalarPointContraction X v
      (L24Gluing.term 651).decoration (L24Gluing.term 651).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core643 L24Gluing.term643.decoration L24Gluing.term643.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels643_651

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded643_eq651 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 643) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 651) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 643) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 651) (by decide +kernel)]
  exact scalar643_eq651 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted651_eq643 : originalWeighted 651 =
    (5 / 1 : ℚ) * originalWeighted 643 := by
  rw [originalWeighted, originalWeighted, ← guarded643_eq651,
    coefficient651, coefficient643]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels643_655 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar643_eq655 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 643).expression.scalarPointContraction X v
      (L24Gluing.term 643).decoration (L24Gluing.term 643).labels beta n insertions =
    (L24Gluing.term 655).expression.scalarPointContraction X v
      (L24Gluing.term 655).decoration (L24Gluing.term 655).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core643 L24Gluing.term643.decoration L24Gluing.term643.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels643_655

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded643_eq655 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 643) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 655) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 643) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 655) (by decide +kernel)]
  exact scalar643_eq655 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted655_eq643 : originalWeighted 655 =
    (5 / 1 : ℚ) * originalWeighted 643 := by
  rw [originalWeighted, originalWeighted, ← guarded643_eq655,
    coefficient655, coefficient643]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels644_652 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar644_eq652 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 644).expression.scalarPointContraction X v
      (L24Gluing.term 644).decoration (L24Gluing.term 644).labels beta n insertions =
    (L24Gluing.term 652).expression.scalarPointContraction X v
      (L24Gluing.term 652).decoration (L24Gluing.term 652).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core644 L24Gluing.term644.decoration L24Gluing.term644.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels644_652

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded644_eq652 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 644) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 652) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 644) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 652) (by decide +kernel)]
  exact scalar644_eq652 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted652_eq644 : originalWeighted 652 =
    (-1 / 3 : ℚ) * originalWeighted 644 := by
  rw [originalWeighted, originalWeighted, ← guarded644_eq652,
    coefficient652, coefficient644]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels644_656 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar644_eq656 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 644).expression.scalarPointContraction X v
      (L24Gluing.term 644).decoration (L24Gluing.term 644).labels beta n insertions =
    (L24Gluing.term 656).expression.scalarPointContraction X v
      (L24Gluing.term 656).decoration (L24Gluing.term 656).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core644 L24Gluing.term644.decoration L24Gluing.term644.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels644_656

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded644_eq656 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 644) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 656) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 644) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 656) (by decide +kernel)]
  exact scalar644_eq656 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted656_eq644 : originalWeighted 656 =
    (-1 / 3 : ℚ) * originalWeighted 644 := by
  rw [originalWeighted, originalWeighted, ← guarded644_eq656,
    coefficient656, coefficient644]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels645_653 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar645_eq653 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 645).expression.scalarPointContraction X v
      (L24Gluing.term 645).decoration (L24Gluing.term 645).labels beta n insertions =
    (L24Gluing.term 653).expression.scalarPointContraction X v
      (L24Gluing.term 653).decoration (L24Gluing.term 653).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core645 L24Gluing.term645.decoration L24Gluing.term645.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels645_653

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded645_eq653 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 645) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 653) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 645) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 653) (by decide +kernel)]
  exact scalar645_eq653 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted653_eq645 : originalWeighted 653 =
    (7 / 27 : ℚ) * originalWeighted 645 := by
  rw [originalWeighted, originalWeighted, ← guarded645_eq653,
    coefficient653, coefficient645]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels645_657 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar645_eq657 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 645).expression.scalarPointContraction X v
      (L24Gluing.term 645).decoration (L24Gluing.term 645).labels beta n insertions =
    (L24Gluing.term 657).expression.scalarPointContraction X v
      (L24Gluing.term 657).decoration (L24Gluing.term 657).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core645 L24Gluing.term645.decoration L24Gluing.term645.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels645_657

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded645_eq657 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 645) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 657) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 645) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 657) (by decide +kernel)]
  exact scalar645_eq657 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted657_eq645 : originalWeighted 657 =
    (7 / 27 : ℚ) * originalWeighted 645 := by
  rw [originalWeighted, originalWeighted, ← guarded645_eq657,
    coefficient657, coefficient645]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels662_681 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation9 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar662_eq681 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 662).expression.scalarPointContraction X v
      (L24Gluing.term 662).decoration (L24Gluing.term 662).labels beta n insertions =
    (L24Gluing.term 681).expression.scalarPointContraction X v
      (L24Gluing.term 681).decoration (L24Gluing.term 681).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core662 L24Gluing.term662.decoration L24Gluing.term662.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 beta n insertions labels662_681

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded662_eq681 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 662) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 681) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 662) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 681) (by decide +kernel)]
  exact scalar662_eq681 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted681_eq662 : originalWeighted 681 =
    (2923 / 7365 : ℚ) * originalWeighted 662 := by
  rw [originalWeighted, originalWeighted, ← guarded662_eq681,
    coefficient681, coefficient662]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels662_700 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation3 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar662_eq700 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 662).expression.scalarPointContraction X v
      (L24Gluing.term 662).decoration (L24Gluing.term 662).labels beta n insertions =
    (L24Gluing.term 700).expression.scalarPointContraction X v
      (L24Gluing.term 700).decoration (L24Gluing.term 700).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core662 L24Gluing.term662.decoration L24Gluing.term662.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 beta n insertions labels662_700

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded662_eq700 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 662) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 700) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 662) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 700) (by decide +kernel)]
  exact scalar662_eq700 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted700_eq662 : originalWeighted 700 =
    (2923 / 7365 : ℚ) * originalWeighted 662 := by
  rw [originalWeighted, originalWeighted, ← guarded662_eq700,
    coefficient700, coefficient662]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels663_682 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar663_eq682 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 663).expression.scalarPointContraction X v
      (L24Gluing.term 663).decoration (L24Gluing.term 663).labels beta n insertions =
    (L24Gluing.term 682).expression.scalarPointContraction X v
      (L24Gluing.term 682).decoration (L24Gluing.term 682).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core663 L24Gluing.term663.decoration L24Gluing.term663.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels663_682

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded663_eq682 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 663) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 682) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 663) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 682) (by decide +kernel)]
  exact scalar663_eq682 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted682_eq663 : originalWeighted 682 =
    (37 / 39 : ℚ) * originalWeighted 663 := by
  rw [originalWeighted, originalWeighted, ← guarded663_eq682,
    coefficient682, coefficient663]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels663_701 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar663_eq701 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 663).expression.scalarPointContraction X v
      (L24Gluing.term 663).decoration (L24Gluing.term 663).labels beta n insertions =
    (L24Gluing.term 701).expression.scalarPointContraction X v
      (L24Gluing.term 701).decoration (L24Gluing.term 701).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core663 L24Gluing.term663.decoration L24Gluing.term663.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels663_701

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded663_eq701 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 663) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 701) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 663) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 701) (by decide +kernel)]
  exact scalar663_eq701 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted701_eq663 : originalWeighted 701 =
    (37 / 39 : ℚ) * originalWeighted 663 := by
  rw [originalWeighted, originalWeighted, ← guarded663_eq701,
    coefficient701, coefficient663]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels664_683 :
    insertions ∘ (Equiv.refl (Fin 4)) =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar664_eq683 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 664).expression.scalarPointContraction X v
      (L24Gluing.term 664).decoration (L24Gluing.term 664).labels beta n insertions =
    (L24Gluing.term 683).expression.scalarPointContraction X v
      (L24Gluing.term 683).decoration (L24Gluing.term 683).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core664 L24Gluing.term664.decoration L24Gluing.term664.labels
    (Equiv.refl (Fin 4)) L24Gluing.flagPermutation5 beta n insertions labels664_683

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded664_eq683 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 664) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 683) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 664) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 683) (by decide +kernel)]
  exact scalar664_eq683 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted683_eq664 : originalWeighted 683 =
    (1 / 1 : ℚ) * originalWeighted 664 := by
  rw [originalWeighted, originalWeighted, ← guarded664_eq683,
    coefficient683, coefficient664]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels664_702 :
    insertions ∘ (Equiv.refl (Fin 4)) =
      insertions ∘ L24Gluing.flagPermutation4 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar664_eq702 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 664).expression.scalarPointContraction X v
      (L24Gluing.term 664).decoration (L24Gluing.term 664).labels beta n insertions =
    (L24Gluing.term 702).expression.scalarPointContraction X v
      (L24Gluing.term 702).decoration (L24Gluing.term 702).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core664 L24Gluing.term664.decoration L24Gluing.term664.labels
    (Equiv.refl (Fin 4)) L24Gluing.flagPermutation4 beta n insertions labels664_702

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded664_eq702 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 664) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 702) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 664) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 702) (by decide +kernel)]
  exact scalar664_eq702 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted702_eq664 : originalWeighted 702 =
    (1 / 1 : ℚ) * originalWeighted 664 := by
  rw [originalWeighted, originalWeighted, ← guarded664_eq702,
    coefficient702, coefficient664]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels665_684 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar665_eq684 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 665).expression.scalarPointContraction X v
      (L24Gluing.term 665).decoration (L24Gluing.term 665).labels beta n insertions =
    (L24Gluing.term 684).expression.scalarPointContraction X v
      (L24Gluing.term 684).decoration (L24Gluing.term 684).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core665 L24Gluing.term665.decoration L24Gluing.term665.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels665_684

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded665_eq684 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 665) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 684) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 665) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 684) (by decide +kernel)]
  exact scalar665_eq684 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted684_eq665 : originalWeighted 684 =
    (2 / 3 : ℚ) * originalWeighted 665 := by
  rw [originalWeighted, originalWeighted, ← guarded665_eq684,
    coefficient684, coefficient665]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels665_703 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar665_eq703 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 665).expression.scalarPointContraction X v
      (L24Gluing.term 665).decoration (L24Gluing.term 665).labels beta n insertions =
    (L24Gluing.term 703).expression.scalarPointContraction X v
      (L24Gluing.term 703).decoration (L24Gluing.term 703).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core665 L24Gluing.term665.decoration L24Gluing.term665.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels665_703

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded665_eq703 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 665) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 703) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 665) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 703) (by decide +kernel)]
  exact scalar665_eq703 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted703_eq665 : originalWeighted 703 =
    (2 / 3 : ℚ) * originalWeighted 665 := by
  rw [originalWeighted, originalWeighted, ← guarded665_eq703,
    coefficient703, coefficient665]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels666_685 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar666_eq685 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 666).expression.scalarPointContraction X v
      (L24Gluing.term 666).decoration (L24Gluing.term 666).labels beta n insertions =
    (L24Gluing.term 685).expression.scalarPointContraction X v
      (L24Gluing.term 685).decoration (L24Gluing.term 685).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core666 L24Gluing.term666.decoration L24Gluing.term666.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels666_685

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded666_eq685 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 666) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 685) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 666) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 685) (by decide +kernel)]
  exact scalar666_eq685 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted685_eq666 : originalWeighted 685 =
    (5390 / 1923 : ℚ) * originalWeighted 666 := by
  rw [originalWeighted, originalWeighted, ← guarded666_eq685,
    coefficient685, coefficient666]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels666_704 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar666_eq704 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 666).expression.scalarPointContraction X v
      (L24Gluing.term 666).decoration (L24Gluing.term 666).labels beta n insertions =
    (L24Gluing.term 704).expression.scalarPointContraction X v
      (L24Gluing.term 704).decoration (L24Gluing.term 704).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core666 L24Gluing.term666.decoration L24Gluing.term666.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels666_704

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded666_eq704 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 666) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 704) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 666) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 704) (by decide +kernel)]
  exact scalar666_eq704 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted704_eq666 : originalWeighted 704 =
    (5390 / 1923 : ℚ) * originalWeighted 666 := by
  rw [originalWeighted, originalWeighted, ← guarded666_eq704,
    coefficient704, coefficient666]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels667_686 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation9 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar667_eq686 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 667).expression.scalarPointContraction X v
      (L24Gluing.term 667).decoration (L24Gluing.term 667).labels beta n insertions =
    (L24Gluing.term 686).expression.scalarPointContraction X v
      (L24Gluing.term 686).decoration (L24Gluing.term 686).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core667 L24Gluing.term667.decoration L24Gluing.term667.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 beta n insertions labels667_686

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded667_eq686 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 667) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 686) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 667) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 686) (by decide +kernel)]
  exact scalar667_eq686 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted686_eq667 : originalWeighted 686 =
    (-4 / 629 : ℚ) * originalWeighted 667 := by
  rw [originalWeighted, originalWeighted, ← guarded667_eq686,
    coefficient686, coefficient667]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels667_705 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation3 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar667_eq705 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 667).expression.scalarPointContraction X v
      (L24Gluing.term 667).decoration (L24Gluing.term 667).labels beta n insertions =
    (L24Gluing.term 705).expression.scalarPointContraction X v
      (L24Gluing.term 705).decoration (L24Gluing.term 705).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core667 L24Gluing.term667.decoration L24Gluing.term667.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 beta n insertions labels667_705

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded667_eq705 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 667) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 705) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 667) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 705) (by decide +kernel)]
  exact scalar667_eq705 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted705_eq667 : originalWeighted 705 =
    (-4 / 629 : ℚ) * originalWeighted 667 := by
  rw [originalWeighted, originalWeighted, ← guarded667_eq705,
    coefficient705, coefficient667]
  ring

end AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12

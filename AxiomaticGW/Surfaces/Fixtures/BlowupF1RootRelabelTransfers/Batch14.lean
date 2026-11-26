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

namespace AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14

open BlowupF1RootAssembly SurfaceGenusTwo GetzlerGraphs L24Gluing

private def core680 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 6) (n := 0) 6 0
    (join (m := 2) (n := 5) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core727 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 3
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core729 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 4) (n := 2) 4 2
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core730 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 0 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation24)

private def core731 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 1 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)

private def core732 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 1 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)

private def core735 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)

private def core736 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)

private def core737 : GluingExpression 2 (Fin 4) :=
  close (join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )))

theorem coefficient680 : L24CorrectionsReplay.fullClaim 680 =
    (-227 / 9360 : ℚ) := by decide +kernel

theorem coefficient718 : L24CorrectionsReplay.fullClaim 718 =
    (-227 / 14040 : ℚ) := by decide +kernel

theorem coefficient727 : L24CorrectionsReplay.fullClaim 727 =
    (-79 / 2160 : ℚ) := by decide +kernel

theorem coefficient728 : L24CorrectionsReplay.fullClaim 728 =
    (-491 / 5616 : ℚ) := by decide +kernel

theorem coefficient729 : L24CorrectionsReplay.fullClaim 729 =
    (-491 / 5616 : ℚ) := by decide +kernel

theorem coefficient730 : L24CorrectionsReplay.fullClaim 730 =
    (641 / 28080 : ℚ) := by decide +kernel

theorem coefficient731 : L24CorrectionsReplay.fullClaim 731 =
    (539 / 5616 : ℚ) := by decide +kernel

theorem coefficient732 : L24CorrectionsReplay.fullClaim 732 =
    (1421 / 28080 : ℚ) := by decide +kernel

theorem coefficient733 : L24CorrectionsReplay.fullClaim 733 =
    (-629 / 28080 : ℚ) := by decide +kernel

theorem coefficient734 : L24CorrectionsReplay.fullClaim 734 =
    (-5023 / 28080 : ℚ) := by decide +kernel

theorem coefficient735 : L24CorrectionsReplay.fullClaim 735 =
    (-1409 / 28080 : ℚ) := by decide +kernel

theorem coefficient736 : L24CorrectionsReplay.fullClaim 736 =
    (-5023 / 28080 : ℚ) := by decide +kernel

theorem coefficient737 : L24CorrectionsReplay.fullClaim 737 =
    (4637 / 238680 : ℚ) := by decide +kernel

theorem coefficient745 : L24CorrectionsReplay.fullClaim 745 =
    (-79 / 2160 : ℚ) := by decide +kernel

theorem coefficient746 : L24CorrectionsReplay.fullClaim 746 =
    (-491 / 5616 : ℚ) := by decide +kernel

theorem coefficient747 : L24CorrectionsReplay.fullClaim 747 =
    (-491 / 5616 : ℚ) := by decide +kernel

theorem coefficient748 : L24CorrectionsReplay.fullClaim 748 =
    (641 / 28080 : ℚ) := by decide +kernel

theorem coefficient749 : L24CorrectionsReplay.fullClaim 749 =
    (539 / 5616 : ℚ) := by decide +kernel

theorem coefficient750 : L24CorrectionsReplay.fullClaim 750 =
    (1421 / 28080 : ℚ) := by decide +kernel

theorem coefficient751 : L24CorrectionsReplay.fullClaim 751 =
    (-629 / 28080 : ℚ) := by decide +kernel

theorem coefficient752 : L24CorrectionsReplay.fullClaim 752 =
    (-5023 / 28080 : ℚ) := by decide +kernel

theorem coefficient753 : L24CorrectionsReplay.fullClaim 753 =
    (-1409 / 28080 : ℚ) := by decide +kernel

theorem coefficient754 : L24CorrectionsReplay.fullClaim 754 =
    (-5023 / 28080 : ℚ) := by decide +kernel

theorem coefficient755 : L24CorrectionsReplay.fullClaim 755 =
    (4637 / 238680 : ℚ) := by decide +kernel

theorem coefficient771 : L24CorrectionsReplay.fullClaim 771 =
    (-2923 / 84240 : ℚ) := by decide +kernel

theorem coefficient772 : L24CorrectionsReplay.fullClaim 772 =
    (-2923 / 84240 : ℚ) := by decide +kernel

theorem coefficient773 : L24CorrectionsReplay.fullClaim 773 =
    (-491 / 8424 : ℚ) := by decide +kernel

theorem coefficient774 : L24CorrectionsReplay.fullClaim 774 =
    (539 / 8424 : ℚ) := by decide +kernel

theorem coefficient775 : L24CorrectionsReplay.fullClaim 775 =
    (1 / 7020 : ℚ) := by decide +kernel

theorem coefficient776 : L24CorrectionsReplay.fullClaim 776 =
    (1 / 7020 : ℚ) := by decide +kernel

theorem coefficient777 : L24CorrectionsReplay.fullClaim 777 =
    (1 / 7020 : ℚ) := by decide +kernel

theorem coefficient778 : L24CorrectionsReplay.fullClaim 778 =
    (1 / 7020 : ℚ) := by decide +kernel

theorem coefficient779 : L24CorrectionsReplay.fullClaim 779 =
    (-5023 / 42120 : ℚ) := by decide +kernel

theorem coefficient780 : L24CorrectionsReplay.fullClaim 780 =
    (-5023 / 42120 : ℚ) := by decide +kernel

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels680_718 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar680_eq718 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 680).expression.scalarPointContraction X v
      (L24Gluing.term 680).decoration (L24Gluing.term 680).labels beta n insertions =
    (L24Gluing.term 718).expression.scalarPointContraction X v
      (L24Gluing.term 718).decoration (L24Gluing.term 718).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core680 L24Gluing.term680.decoration L24Gluing.term680.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels680_718

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded680_eq718 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 680) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 718) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 680) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 718) (by decide +kernel)]
  exact scalar680_eq718 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted718_eq680 : originalWeighted 718 =
    (2 / 3 : ℚ) * originalWeighted 680 := by
  rw [originalWeighted, originalWeighted, ← guarded680_eq718,
    coefficient718, coefficient680]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels727_728 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation4 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar727_eq728 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 727).expression.scalarPointContraction X v
      (L24Gluing.term 727).decoration (L24Gluing.term 727).labels beta n insertions =
    (L24Gluing.term 728).expression.scalarPointContraction X v
      (L24Gluing.term 728).decoration (L24Gluing.term 728).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core727 L24Gluing.term727.decoration L24Gluing.term727.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation4 beta n insertions labels727_728

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded727_eq728 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 727) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 728) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 727) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 728) (by decide +kernel)]
  exact scalar727_eq728 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted728_eq727 : originalWeighted 728 =
    (2455 / 1027 : ℚ) * originalWeighted 727 := by
  rw [originalWeighted, originalWeighted, ← guarded727_eq728,
    coefficient728, coefficient727]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels727_745 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation6 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar727_eq745 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 727).expression.scalarPointContraction X v
      (L24Gluing.term 727).decoration (L24Gluing.term 727).labels beta n insertions =
    (L24Gluing.term 745).expression.scalarPointContraction X v
      (L24Gluing.term 745).decoration (L24Gluing.term 745).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core727 L24Gluing.term727.decoration L24Gluing.term727.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 beta n insertions labels727_745

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded727_eq745 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 727) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 745) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 727) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 745) (by decide +kernel)]
  exact scalar727_eq745 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted745_eq727 : originalWeighted 745 =
    (1 / 1 : ℚ) * originalWeighted 727 := by
  rw [originalWeighted, originalWeighted, ← guarded727_eq745,
    coefficient745, coefficient727]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels727_746 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar727_eq746 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 727).expression.scalarPointContraction X v
      (L24Gluing.term 727).decoration (L24Gluing.term 727).labels beta n insertions =
    (L24Gluing.term 746).expression.scalarPointContraction X v
      (L24Gluing.term 746).decoration (L24Gluing.term 746).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core727 L24Gluing.term727.decoration L24Gluing.term727.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation5 beta n insertions labels727_746

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded727_eq746 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 727) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 746) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 727) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 746) (by decide +kernel)]
  exact scalar727_eq746 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted746_eq727 : originalWeighted 746 =
    (2455 / 1027 : ℚ) * originalWeighted 727 := by
  rw [originalWeighted, originalWeighted, ← guarded727_eq746,
    coefficient746, coefficient727]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels727_771 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar727_eq771 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 727).expression.scalarPointContraction X v
      (L24Gluing.term 727).decoration (L24Gluing.term 727).labels beta n insertions =
    (L24Gluing.term 771).expression.scalarPointContraction X v
      (L24Gluing.term 771).decoration (L24Gluing.term 771).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core727 L24Gluing.term727.decoration L24Gluing.term727.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 beta n insertions labels727_771

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded727_eq771 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 727) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 771) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 727) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 771) (by decide +kernel)]
  exact scalar727_eq771 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted771_eq727 : originalWeighted 771 =
    (37 / 39 : ℚ) * originalWeighted 727 := by
  rw [originalWeighted, originalWeighted, ← guarded727_eq771,
    coefficient771, coefficient727]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels727_772 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar727_eq772 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 727).expression.scalarPointContraction X v
      (L24Gluing.term 727).decoration (L24Gluing.term 727).labels beta n insertions =
    (L24Gluing.term 772).expression.scalarPointContraction X v
      (L24Gluing.term 772).decoration (L24Gluing.term 772).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core727 L24Gluing.term727.decoration L24Gluing.term727.labels
    L24Gluing.flagPermutation10 (Equiv.refl (Fin 4)) beta n insertions labels727_772

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded727_eq772 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 727) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 772) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 727) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 772) (by decide +kernel)]
  exact scalar727_eq772 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted772_eq727 : originalWeighted 772 =
    (37 / 39 : ℚ) * originalWeighted 727 := by
  rw [originalWeighted, originalWeighted, ← guarded727_eq772,
    coefficient772, coefficient727]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels729_747 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar729_eq747 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 729).expression.scalarPointContraction X v
      (L24Gluing.term 729).decoration (L24Gluing.term 729).labels beta n insertions =
    (L24Gluing.term 747).expression.scalarPointContraction X v
      (L24Gluing.term 747).decoration (L24Gluing.term 747).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core729 L24Gluing.term729.decoration L24Gluing.term729.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels729_747

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded729_eq747 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 729) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 747) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 729) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 747) (by decide +kernel)]
  exact scalar729_eq747 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted747_eq729 : originalWeighted 747 =
    (1 / 1 : ℚ) * originalWeighted 729 := by
  rw [originalWeighted, originalWeighted, ← guarded729_eq747,
    coefficient747, coefficient729]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels729_773 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar729_eq773 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 729).expression.scalarPointContraction X v
      (L24Gluing.term 729).decoration (L24Gluing.term 729).labels beta n insertions =
    (L24Gluing.term 773).expression.scalarPointContraction X v
      (L24Gluing.term 773).decoration (L24Gluing.term 773).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core729 L24Gluing.term729.decoration L24Gluing.term729.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels729_773

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded729_eq773 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 729) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 773) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 729) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 773) (by decide +kernel)]
  exact scalar729_eq773 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted773_eq729 : originalWeighted 773 =
    (2 / 3 : ℚ) * originalWeighted 729 := by
  rw [originalWeighted, originalWeighted, ← guarded729_eq773,
    coefficient773, coefficient729]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels730_748 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar730_eq748 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 730).expression.scalarPointContraction X v
      (L24Gluing.term 730).decoration (L24Gluing.term 730).labels beta n insertions =
    (L24Gluing.term 748).expression.scalarPointContraction X v
      (L24Gluing.term 748).decoration (L24Gluing.term 748).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core730 L24Gluing.term730.decoration L24Gluing.term730.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels730_748

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded730_eq748 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 730) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 748) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 730) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 748) (by decide +kernel)]
  exact scalar730_eq748 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted748_eq730 : originalWeighted 748 =
    (1 / 1 : ℚ) * originalWeighted 730 := by
  rw [originalWeighted, originalWeighted, ← guarded730_eq748,
    coefficient748, coefficient730]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels730_774 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar730_eq774 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 730).expression.scalarPointContraction X v
      (L24Gluing.term 730).decoration (L24Gluing.term 730).labels beta n insertions =
    (L24Gluing.term 774).expression.scalarPointContraction X v
      (L24Gluing.term 774).decoration (L24Gluing.term 774).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core730 L24Gluing.term730.decoration L24Gluing.term730.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels730_774

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded730_eq774 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 730) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 774) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 730) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 774) (by decide +kernel)]
  exact scalar730_eq774 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted774_eq730 : originalWeighted 774 =
    (5390 / 1923 : ℚ) * originalWeighted 730 := by
  rw [originalWeighted, originalWeighted, ← guarded730_eq774,
    coefficient774, coefficient730]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels731_733 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation4 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar731_eq733 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 731).expression.scalarPointContraction X v
      (L24Gluing.term 731).decoration (L24Gluing.term 731).labels beta n insertions =
    (L24Gluing.term 733).expression.scalarPointContraction X v
      (L24Gluing.term 733).decoration (L24Gluing.term 733).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core731 L24Gluing.term731.decoration L24Gluing.term731.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation4 beta n insertions labels731_733

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded731_eq733 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 731) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 733) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 731) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 733) (by decide +kernel)]
  exact scalar731_eq733 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted733_eq731 : originalWeighted 733 =
    (-629 / 2695 : ℚ) * originalWeighted 731 := by
  rw [originalWeighted, originalWeighted, ← guarded731_eq733,
    coefficient733, coefficient731]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels731_749 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation6 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar731_eq749 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 731).expression.scalarPointContraction X v
      (L24Gluing.term 731).decoration (L24Gluing.term 731).labels beta n insertions =
    (L24Gluing.term 749).expression.scalarPointContraction X v
      (L24Gluing.term 749).decoration (L24Gluing.term 749).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core731 L24Gluing.term731.decoration L24Gluing.term731.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 beta n insertions labels731_749

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded731_eq749 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 731) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 749) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 731) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 749) (by decide +kernel)]
  exact scalar731_eq749 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted749_eq731 : originalWeighted 749 =
    (1 / 1 : ℚ) * originalWeighted 731 := by
  rw [originalWeighted, originalWeighted, ← guarded731_eq749,
    coefficient749, coefficient731]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels731_751 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar731_eq751 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 731).expression.scalarPointContraction X v
      (L24Gluing.term 731).decoration (L24Gluing.term 731).labels beta n insertions =
    (L24Gluing.term 751).expression.scalarPointContraction X v
      (L24Gluing.term 751).decoration (L24Gluing.term 751).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core731 L24Gluing.term731.decoration L24Gluing.term731.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation5 beta n insertions labels731_751

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded731_eq751 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 731) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 751) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 731) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 751) (by decide +kernel)]
  exact scalar731_eq751 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted751_eq731 : originalWeighted 751 =
    (-629 / 2695 : ℚ) * originalWeighted 731 := by
  rw [originalWeighted, originalWeighted, ← guarded731_eq751,
    coefficient751, coefficient731]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels731_775 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar731_eq775 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 731).expression.scalarPointContraction X v
      (L24Gluing.term 731).decoration (L24Gluing.term 731).labels beta n insertions =
    (L24Gluing.term 775).expression.scalarPointContraction X v
      (L24Gluing.term 775).decoration (L24Gluing.term 775).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core731 L24Gluing.term731.decoration L24Gluing.term731.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 beta n insertions labels731_775

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded731_eq775 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 731) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 775) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 731) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 775) (by decide +kernel)]
  exact scalar731_eq775 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted775_eq731 : originalWeighted 775 =
    (4 / 2695 : ℚ) * originalWeighted 731 := by
  rw [originalWeighted, originalWeighted, ← guarded731_eq775,
    coefficient775, coefficient731]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels731_777 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar731_eq777 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 731).expression.scalarPointContraction X v
      (L24Gluing.term 731).decoration (L24Gluing.term 731).labels beta n insertions =
    (L24Gluing.term 777).expression.scalarPointContraction X v
      (L24Gluing.term 777).decoration (L24Gluing.term 777).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core731 L24Gluing.term731.decoration L24Gluing.term731.labels
    L24Gluing.flagPermutation10 (Equiv.refl (Fin 4)) beta n insertions labels731_777

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded731_eq777 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 731) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 777) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 731) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 777) (by decide +kernel)]
  exact scalar731_eq777 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted777_eq731 : originalWeighted 777 =
    (4 / 2695 : ℚ) * originalWeighted 731 := by
  rw [originalWeighted, originalWeighted, ← guarded731_eq777,
    coefficient777, coefficient731]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels732_734 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation4 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar732_eq734 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 732).expression.scalarPointContraction X v
      (L24Gluing.term 732).decoration (L24Gluing.term 732).labels beta n insertions =
    (L24Gluing.term 734).expression.scalarPointContraction X v
      (L24Gluing.term 734).decoration (L24Gluing.term 734).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core732 L24Gluing.term732.decoration L24Gluing.term732.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation4 beta n insertions labels732_734

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded732_eq734 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 732) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 734) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 732) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 734) (by decide +kernel)]
  exact scalar732_eq734 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted734_eq732 : originalWeighted 734 =
    (-5023 / 1421 : ℚ) * originalWeighted 732 := by
  rw [originalWeighted, originalWeighted, ← guarded732_eq734,
    coefficient734, coefficient732]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels732_750 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation6 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar732_eq750 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 732).expression.scalarPointContraction X v
      (L24Gluing.term 732).decoration (L24Gluing.term 732).labels beta n insertions =
    (L24Gluing.term 750).expression.scalarPointContraction X v
      (L24Gluing.term 750).decoration (L24Gluing.term 750).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core732 L24Gluing.term732.decoration L24Gluing.term732.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 beta n insertions labels732_750

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded732_eq750 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 732) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 750) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 732) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 750) (by decide +kernel)]
  exact scalar732_eq750 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted750_eq732 : originalWeighted 750 =
    (1 / 1 : ℚ) * originalWeighted 732 := by
  rw [originalWeighted, originalWeighted, ← guarded732_eq750,
    coefficient750, coefficient732]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels732_752 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar732_eq752 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 732).expression.scalarPointContraction X v
      (L24Gluing.term 732).decoration (L24Gluing.term 732).labels beta n insertions =
    (L24Gluing.term 752).expression.scalarPointContraction X v
      (L24Gluing.term 752).decoration (L24Gluing.term 752).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core732 L24Gluing.term732.decoration L24Gluing.term732.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation5 beta n insertions labels732_752

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded732_eq752 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 732) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 752) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 732) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 752) (by decide +kernel)]
  exact scalar732_eq752 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted752_eq732 : originalWeighted 752 =
    (-5023 / 1421 : ℚ) * originalWeighted 732 := by
  rw [originalWeighted, originalWeighted, ← guarded732_eq752,
    coefficient752, coefficient732]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels732_776 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar732_eq776 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 732).expression.scalarPointContraction X v
      (L24Gluing.term 732).decoration (L24Gluing.term 732).labels beta n insertions =
    (L24Gluing.term 776).expression.scalarPointContraction X v
      (L24Gluing.term 776).decoration (L24Gluing.term 776).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core732 L24Gluing.term732.decoration L24Gluing.term732.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 beta n insertions labels732_776

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded732_eq776 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 732) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 776) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 732) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 776) (by decide +kernel)]
  exact scalar732_eq776 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted776_eq732 : originalWeighted 776 =
    (4 / 1421 : ℚ) * originalWeighted 732 := by
  rw [originalWeighted, originalWeighted, ← guarded732_eq776,
    coefficient776, coefficient732]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels732_778 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar732_eq778 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 732).expression.scalarPointContraction X v
      (L24Gluing.term 732).decoration (L24Gluing.term 732).labels beta n insertions =
    (L24Gluing.term 778).expression.scalarPointContraction X v
      (L24Gluing.term 778).decoration (L24Gluing.term 778).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core732 L24Gluing.term732.decoration L24Gluing.term732.labels
    L24Gluing.flagPermutation10 (Equiv.refl (Fin 4)) beta n insertions labels732_778

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded732_eq778 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 732) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 778) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 732) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 778) (by decide +kernel)]
  exact scalar732_eq778 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted778_eq732 : originalWeighted 778 =
    (4 / 1421 : ℚ) * originalWeighted 732 := by
  rw [originalWeighted, originalWeighted, ← guarded732_eq778,
    coefficient778, coefficient732]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels735_753 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar735_eq753 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 735).expression.scalarPointContraction X v
      (L24Gluing.term 735).decoration (L24Gluing.term 735).labels beta n insertions =
    (L24Gluing.term 753).expression.scalarPointContraction X v
      (L24Gluing.term 753).decoration (L24Gluing.term 753).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core735 L24Gluing.term735.decoration L24Gluing.term735.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels735_753

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded735_eq753 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 735) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 753) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 735) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 753) (by decide +kernel)]
  exact scalar735_eq753 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted753_eq735 : originalWeighted 753 =
    (1 / 1 : ℚ) * originalWeighted 735 := by
  rw [originalWeighted, originalWeighted, ← guarded735_eq753,
    coefficient753, coefficient735]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels735_779 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar735_eq779 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 735).expression.scalarPointContraction X v
      (L24Gluing.term 735).decoration (L24Gluing.term 735).labels beta n insertions =
    (L24Gluing.term 779).expression.scalarPointContraction X v
      (L24Gluing.term 779).decoration (L24Gluing.term 779).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core735 L24Gluing.term735.decoration L24Gluing.term735.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels735_779

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded735_eq779 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 735) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 779) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 735) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 779) (by decide +kernel)]
  exact scalar735_eq779 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted779_eq735 : originalWeighted 779 =
    (10046 / 4227 : ℚ) * originalWeighted 735 := by
  rw [originalWeighted, originalWeighted, ← guarded735_eq779,
    coefficient779, coefficient735]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels736_754 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar736_eq754 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 736).expression.scalarPointContraction X v
      (L24Gluing.term 736).decoration (L24Gluing.term 736).labels beta n insertions =
    (L24Gluing.term 754).expression.scalarPointContraction X v
      (L24Gluing.term 754).decoration (L24Gluing.term 754).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core736 L24Gluing.term736.decoration L24Gluing.term736.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels736_754

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded736_eq754 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 736) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 754) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 736) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 754) (by decide +kernel)]
  exact scalar736_eq754 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted754_eq736 : originalWeighted 754 =
    (1 / 1 : ℚ) * originalWeighted 736 := by
  rw [originalWeighted, originalWeighted, ← guarded736_eq754,
    coefficient754, coefficient736]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels736_780 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar736_eq780 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 736).expression.scalarPointContraction X v
      (L24Gluing.term 736).decoration (L24Gluing.term 736).labels beta n insertions =
    (L24Gluing.term 780).expression.scalarPointContraction X v
      (L24Gluing.term 780).decoration (L24Gluing.term 780).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core736 L24Gluing.term736.decoration L24Gluing.term736.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels736_780

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded736_eq780 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 736) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 780) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 736) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 780) (by decide +kernel)]
  exact scalar736_eq780 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted780_eq736 : originalWeighted 780 =
    (2 / 3 : ℚ) * originalWeighted 736 := by
  rw [originalWeighted, originalWeighted, ← guarded736_eq780,
    coefficient780, coefficient736]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels737_755 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar737_eq755 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 737).expression.scalarPointContraction X v
      (L24Gluing.term 737).decoration (L24Gluing.term 737).labels beta n insertions =
    (L24Gluing.term 755).expression.scalarPointContraction X v
      (L24Gluing.term 755).decoration (L24Gluing.term 755).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core737 L24Gluing.term737.decoration L24Gluing.term737.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels737_755

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded737_eq755 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 737) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 755) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 737) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 755) (by decide +kernel)]
  exact scalar737_eq755 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted755_eq737 : originalWeighted 755 =
    (1 / 1 : ℚ) * originalWeighted 737 := by
  rw [originalWeighted, originalWeighted, ← guarded737_eq755,
    coefficient755, coefficient737]
  ring

end AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14

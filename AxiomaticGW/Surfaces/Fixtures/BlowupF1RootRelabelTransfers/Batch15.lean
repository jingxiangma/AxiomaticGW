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

namespace AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15

open BlowupF1RootAssembly SurfaceGenusTwo GetzlerGraphs L24Gluing

private def core737 : GluingExpression 2 (Fin 4) :=
  close (join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )))

private def core738 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 4) (n := 2) 4 2
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)

private def core739 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation26)

private def core740 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 5) (n := 1) 5 1
    (join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)

private def core743 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation27)

private def core744 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 6) (n := 0) 6 0
    (join (m := 2) (n := 5) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core763 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 4) (n := 2) 4 2
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core764 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 0 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)

private def core765 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 1 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)

private def core766 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 3) (n := 1) 1 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)

theorem coefficient737 : L24CorrectionsReplay.fullClaim 737 =
    (4637 / 238680 : ℚ) := by decide +kernel

theorem coefficient738 : L24CorrectionsReplay.fullClaim 738 =
    (83 / 17680 : ℚ) := by decide +kernel

theorem coefficient739 : L24CorrectionsReplay.fullClaim 739 =
    (4637 / 238680 : ℚ) := by decide +kernel

theorem coefficient740 : L24CorrectionsReplay.fullClaim 740 =
    (2371 / 477360 : ℚ) := by decide +kernel

theorem coefficient741 : L24CorrectionsReplay.fullClaim 741 =
    (-2077 / 238680 : ℚ) := by decide +kernel

theorem coefficient742 : L24CorrectionsReplay.fullClaim 742 =
    (-227 / 9360 : ℚ) := by decide +kernel

theorem coefficient743 : L24CorrectionsReplay.fullClaim 743 =
    (-7 / 780 : ℚ) := by decide +kernel

theorem coefficient744 : L24CorrectionsReplay.fullClaim 744 =
    (-227 / 9360 : ℚ) := by decide +kernel

theorem coefficient756 : L24CorrectionsReplay.fullClaim 756 =
    (83 / 17680 : ℚ) := by decide +kernel

theorem coefficient757 : L24CorrectionsReplay.fullClaim 757 =
    (4637 / 238680 : ℚ) := by decide +kernel

theorem coefficient758 : L24CorrectionsReplay.fullClaim 758 =
    (2371 / 477360 : ℚ) := by decide +kernel

theorem coefficient759 : L24CorrectionsReplay.fullClaim 759 =
    (-2077 / 238680 : ℚ) := by decide +kernel

theorem coefficient760 : L24CorrectionsReplay.fullClaim 760 =
    (-227 / 9360 : ℚ) := by decide +kernel

theorem coefficient761 : L24CorrectionsReplay.fullClaim 761 =
    (-7 / 780 : ℚ) := by decide +kernel

theorem coefficient762 : L24CorrectionsReplay.fullClaim 762 =
    (-227 / 9360 : ℚ) := by decide +kernel

theorem coefficient763 : L24CorrectionsReplay.fullClaim 763 =
    (-491 / 1872 : ℚ) := by decide +kernel

theorem coefficient764 : L24CorrectionsReplay.fullClaim 764 =
    (-193 / 4680 : ℚ) := by decide +kernel

theorem coefficient765 : L24CorrectionsReplay.fullClaim 765 =
    (199 / 4680 : ℚ) := by decide +kernel

theorem coefficient766 : L24CorrectionsReplay.fullClaim 766 =
    (-5023 / 9360 : ℚ) := by decide +kernel

theorem coefficient781 : L24CorrectionsReplay.fullClaim 781 =
    (4637 / 358020 : ℚ) := by decide +kernel

theorem coefficient782 : L24CorrectionsReplay.fullClaim 782 =
    (4637 / 358020 : ℚ) := by decide +kernel

theorem coefficient783 : L24CorrectionsReplay.fullClaim 783 =
    (-1913 / 1432080 : ℚ) := by decide +kernel

theorem coefficient784 : L24CorrectionsReplay.fullClaim 784 =
    (-1913 / 1432080 : ℚ) := by decide +kernel

theorem coefficient785 : L24CorrectionsReplay.fullClaim 785 =
    (-1913 / 1432080 : ℚ) := by decide +kernel

theorem coefficient786 : L24CorrectionsReplay.fullClaim 786 =
    (-1913 / 1432080 : ℚ) := by decide +kernel

theorem coefficient787 : L24CorrectionsReplay.fullClaim 787 =
    (-227 / 14040 : ℚ) := by decide +kernel

theorem coefficient788 : L24CorrectionsReplay.fullClaim 788 =
    (-227 / 14040 : ℚ) := by decide +kernel

theorem coefficient789 : L24CorrectionsReplay.fullClaim 789 =
    (-115 / 1053 : ℚ) := by decide +kernel

theorem coefficient790 : L24CorrectionsReplay.fullClaim 790 =
    (-737 / 42120 : ℚ) := by decide +kernel

theorem coefficient791 : L24CorrectionsReplay.fullClaim 791 =
    (47 / 42120 : ℚ) := by decide +kernel

theorem coefficient792 : L24CorrectionsReplay.fullClaim 792 =
    (-2159 / 8424 : ℚ) := by decide +kernel

theorem coefficient797 : L24CorrectionsReplay.fullClaim 797 =
    (-115 / 1053 : ℚ) := by decide +kernel

theorem coefficient798 : L24CorrectionsReplay.fullClaim 798 =
    (-737 / 42120 : ℚ) := by decide +kernel

theorem coefficient799 : L24CorrectionsReplay.fullClaim 799 =
    (47 / 42120 : ℚ) := by decide +kernel

theorem coefficient800 : L24CorrectionsReplay.fullClaim 800 =
    (-2159 / 8424 : ℚ) := by decide +kernel

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels737_781 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar737_eq781 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 737).expression.scalarPointContraction X v
      (L24Gluing.term 737).decoration (L24Gluing.term 737).labels beta n insertions =
    (L24Gluing.term 781).expression.scalarPointContraction X v
      (L24Gluing.term 781).decoration (L24Gluing.term 781).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core737 L24Gluing.term737.decoration L24Gluing.term737.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels737_781

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded737_eq781 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 737) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 781) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 737) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 781) (by decide +kernel)]
  exact scalar737_eq781 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted781_eq737 : originalWeighted 781 =
    (2 / 3 : ℚ) * originalWeighted 737 := by
  rw [originalWeighted, originalWeighted, ← guarded737_eq781,
    coefficient781, coefficient737]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels738_756 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar738_eq756 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 738).expression.scalarPointContraction X v
      (L24Gluing.term 738).decoration (L24Gluing.term 738).labels beta n insertions =
    (L24Gluing.term 756).expression.scalarPointContraction X v
      (L24Gluing.term 756).decoration (L24Gluing.term 756).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core738 L24Gluing.term738.decoration L24Gluing.term738.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels738_756

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded738_eq756 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 738) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 756) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 738) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 756) (by decide +kernel)]
  exact scalar738_eq756 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted756_eq738 : originalWeighted 756 =
    (1 / 1 : ℚ) * originalWeighted 738 := by
  rw [originalWeighted, originalWeighted, ← guarded738_eq756,
    coefficient756, coefficient738]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels738_782 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar738_eq782 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 738).expression.scalarPointContraction X v
      (L24Gluing.term 738).decoration (L24Gluing.term 738).labels beta n insertions =
    (L24Gluing.term 782).expression.scalarPointContraction X v
      (L24Gluing.term 782).decoration (L24Gluing.term 782).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core738 L24Gluing.term738.decoration L24Gluing.term738.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels738_782

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded738_eq782 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 738) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 782) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 738) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 782) (by decide +kernel)]
  exact scalar738_eq782 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted782_eq738 : originalWeighted 782 =
    (18548 / 6723 : ℚ) * originalWeighted 738 := by
  rw [originalWeighted, originalWeighted, ← guarded738_eq782,
    coefficient782, coefficient738]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels739_741 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation21 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar739_eq741 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 739).expression.scalarPointContraction X v
      (L24Gluing.term 739).decoration (L24Gluing.term 739).labels beta n insertions =
    (L24Gluing.term 741).expression.scalarPointContraction X v
      (L24Gluing.term 741).decoration (L24Gluing.term 741).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core739 L24Gluing.term739.decoration L24Gluing.term739.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation21 beta n insertions labels739_741

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded739_eq741 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 739) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 741) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 739) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 741) (by decide +kernel)]
  exact scalar739_eq741 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted741_eq739 : originalWeighted 741 =
    (-2077 / 4637 : ℚ) * originalWeighted 739 := by
  rw [originalWeighted, originalWeighted, ← guarded739_eq741,
    coefficient741, coefficient739]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels739_757 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation14 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar739_eq757 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 739).expression.scalarPointContraction X v
      (L24Gluing.term 739).decoration (L24Gluing.term 739).labels beta n insertions =
    (L24Gluing.term 757).expression.scalarPointContraction X v
      (L24Gluing.term 757).decoration (L24Gluing.term 757).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core739 L24Gluing.term739.decoration L24Gluing.term739.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation14 beta n insertions labels739_757

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded739_eq757 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 739) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 757) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 739) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 757) (by decide +kernel)]
  exact scalar739_eq757 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted757_eq739 : originalWeighted 757 =
    (1 / 1 : ℚ) * originalWeighted 739 := by
  rw [originalWeighted, originalWeighted, ← guarded739_eq757,
    coefficient757, coefficient739]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels739_759 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation17 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar739_eq759 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 739).expression.scalarPointContraction X v
      (L24Gluing.term 739).decoration (L24Gluing.term 739).labels beta n insertions =
    (L24Gluing.term 759).expression.scalarPointContraction X v
      (L24Gluing.term 759).decoration (L24Gluing.term 759).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core739 L24Gluing.term739.decoration L24Gluing.term739.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation17 beta n insertions labels739_759

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded739_eq759 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 739) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 759) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 739) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 759) (by decide +kernel)]
  exact scalar739_eq759 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted759_eq739 : originalWeighted 759 =
    (-2077 / 4637 : ℚ) * originalWeighted 739 := by
  rw [originalWeighted, originalWeighted, ← guarded739_eq759,
    coefficient759, coefficient739]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels739_783 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation15 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar739_eq783 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 739).expression.scalarPointContraction X v
      (L24Gluing.term 739).decoration (L24Gluing.term 739).labels beta n insertions =
    (L24Gluing.term 783).expression.scalarPointContraction X v
      (L24Gluing.term 783).decoration (L24Gluing.term 783).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core739 L24Gluing.term739.decoration L24Gluing.term739.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation15 beta n insertions labels739_783

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded739_eq783 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 739) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 783) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 739) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 783) (by decide +kernel)]
  exact scalar739_eq783 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted783_eq739 : originalWeighted 783 =
    (-1913 / 27822 : ℚ) * originalWeighted 739 := by
  rw [originalWeighted, originalWeighted, ← guarded739_eq783,
    coefficient783, coefficient739]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels739_785 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation16 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar739_eq785 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 739).expression.scalarPointContraction X v
      (L24Gluing.term 739).decoration (L24Gluing.term 739).labels beta n insertions =
    (L24Gluing.term 785).expression.scalarPointContraction X v
      (L24Gluing.term 785).decoration (L24Gluing.term 785).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core739 L24Gluing.term739.decoration L24Gluing.term739.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation16 beta n insertions labels739_785

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded739_eq785 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 739) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 785) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 739) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 785) (by decide +kernel)]
  exact scalar739_eq785 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted785_eq739 : originalWeighted 785 =
    (-1913 / 27822 : ℚ) * originalWeighted 739 := by
  rw [originalWeighted, originalWeighted, ← guarded739_eq785,
    coefficient785, coefficient739]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels740_742 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation4 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar740_eq742 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 740).expression.scalarPointContraction X v
      (L24Gluing.term 740).decoration (L24Gluing.term 740).labels beta n insertions =
    (L24Gluing.term 742).expression.scalarPointContraction X v
      (L24Gluing.term 742).decoration (L24Gluing.term 742).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core740 L24Gluing.term740.decoration L24Gluing.term740.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation4 beta n insertions labels740_742

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded740_eq742 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 740) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 742) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 740) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 742) (by decide +kernel)]
  exact scalar740_eq742 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted742_eq740 : originalWeighted 742 =
    (-11577 / 2371 : ℚ) * originalWeighted 740 := by
  rw [originalWeighted, originalWeighted, ← guarded740_eq742,
    coefficient742, coefficient740]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels740_758 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation6 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar740_eq758 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 740).expression.scalarPointContraction X v
      (L24Gluing.term 740).decoration (L24Gluing.term 740).labels beta n insertions =
    (L24Gluing.term 758).expression.scalarPointContraction X v
      (L24Gluing.term 758).decoration (L24Gluing.term 758).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core740 L24Gluing.term740.decoration L24Gluing.term740.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 beta n insertions labels740_758

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded740_eq758 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 740) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 758) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 740) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 758) (by decide +kernel)]
  exact scalar740_eq758 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted758_eq740 : originalWeighted 758 =
    (1 / 1 : ℚ) * originalWeighted 740 := by
  rw [originalWeighted, originalWeighted, ← guarded740_eq758,
    coefficient758, coefficient740]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels740_760 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar740_eq760 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 740).expression.scalarPointContraction X v
      (L24Gluing.term 740).decoration (L24Gluing.term 740).labels beta n insertions =
    (L24Gluing.term 760).expression.scalarPointContraction X v
      (L24Gluing.term 760).decoration (L24Gluing.term 760).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core740 L24Gluing.term740.decoration L24Gluing.term740.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation5 beta n insertions labels740_760

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded740_eq760 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 740) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 760) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 740) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 760) (by decide +kernel)]
  exact scalar740_eq760 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted760_eq740 : originalWeighted 760 =
    (-11577 / 2371 : ℚ) * originalWeighted 740 := by
  rw [originalWeighted, originalWeighted, ← guarded740_eq760,
    coefficient760, coefficient740]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels740_784 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar740_eq784 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 740).expression.scalarPointContraction X v
      (L24Gluing.term 740).decoration (L24Gluing.term 740).labels beta n insertions =
    (L24Gluing.term 784).expression.scalarPointContraction X v
      (L24Gluing.term 784).decoration (L24Gluing.term 784).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core740 L24Gluing.term740.decoration L24Gluing.term740.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 beta n insertions labels740_784

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded740_eq784 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 740) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 784) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 740) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 784) (by decide +kernel)]
  exact scalar740_eq784 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted784_eq740 : originalWeighted 784 =
    (-1913 / 7113 : ℚ) * originalWeighted 740 := by
  rw [originalWeighted, originalWeighted, ← guarded740_eq784,
    coefficient784, coefficient740]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels740_786 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar740_eq786 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 740).expression.scalarPointContraction X v
      (L24Gluing.term 740).decoration (L24Gluing.term 740).labels beta n insertions =
    (L24Gluing.term 786).expression.scalarPointContraction X v
      (L24Gluing.term 786).decoration (L24Gluing.term 786).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core740 L24Gluing.term740.decoration L24Gluing.term740.labels
    L24Gluing.flagPermutation10 (Equiv.refl (Fin 4)) beta n insertions labels740_786

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded740_eq786 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 740) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 786) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 740) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 786) (by decide +kernel)]
  exact scalar740_eq786 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted786_eq740 : originalWeighted 786 =
    (-1913 / 7113 : ℚ) * originalWeighted 740 := by
  rw [originalWeighted, originalWeighted, ← guarded740_eq786,
    coefficient786, coefficient740]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels743_761 :
    insertions ∘ L24Gluing.flagPermutation2 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar743_eq761 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 743).expression.scalarPointContraction X v
      (L24Gluing.term 743).decoration (L24Gluing.term 743).labels beta n insertions =
    (L24Gluing.term 761).expression.scalarPointContraction X v
      (L24Gluing.term 761).decoration (L24Gluing.term 761).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core743 L24Gluing.term743.decoration L24Gluing.term743.labels
    L24Gluing.flagPermutation2 L24Gluing.flagPermutation1 beta n insertions labels743_761

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded743_eq761 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 743) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 761) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 743) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 761) (by decide +kernel)]
  exact scalar743_eq761 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted761_eq743 : originalWeighted 761 =
    (1 / 1 : ℚ) * originalWeighted 743 := by
  rw [originalWeighted, originalWeighted, ← guarded743_eq761,
    coefficient761, coefficient743]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels743_787 :
    insertions ∘ L24Gluing.flagPermutation2 =
      insertions ∘ L24Gluing.flagPermutation0 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar743_eq787 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 743).expression.scalarPointContraction X v
      (L24Gluing.term 743).decoration (L24Gluing.term 743).labels beta n insertions =
    (L24Gluing.term 787).expression.scalarPointContraction X v
      (L24Gluing.term 787).decoration (L24Gluing.term 787).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core743 L24Gluing.term743.decoration L24Gluing.term743.labels
    L24Gluing.flagPermutation2 L24Gluing.flagPermutation0 beta n insertions labels743_787

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded743_eq787 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 743) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 787) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 743) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 787) (by decide +kernel)]
  exact scalar743_eq787 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted787_eq743 : originalWeighted 787 =
    (227 / 126 : ℚ) * originalWeighted 743 := by
  rw [originalWeighted, originalWeighted, ← guarded743_eq787,
    coefficient787, coefficient743]
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

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels763_789 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar763_eq789 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 763).expression.scalarPointContraction X v
      (L24Gluing.term 763).decoration (L24Gluing.term 763).labels beta n insertions =
    (L24Gluing.term 789).expression.scalarPointContraction X v
      (L24Gluing.term 789).decoration (L24Gluing.term 789).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core763 L24Gluing.term763.decoration L24Gluing.term763.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels763_789

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded763_eq789 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 763) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 789) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 763) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 789) (by decide +kernel)]
  exact scalar763_eq789 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted789_eq763 : originalWeighted 789 =
    (1840 / 4419 : ℚ) * originalWeighted 763 := by
  rw [originalWeighted, originalWeighted, ← guarded763_eq789,
    coefficient789, coefficient763]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels763_797 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar763_eq797 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 763).expression.scalarPointContraction X v
      (L24Gluing.term 763).decoration (L24Gluing.term 763).labels beta n insertions =
    (L24Gluing.term 797).expression.scalarPointContraction X v
      (L24Gluing.term 797).decoration (L24Gluing.term 797).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core763 L24Gluing.term763.decoration L24Gluing.term763.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels763_797

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded763_eq797 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 763) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 797) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 763) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 797) (by decide +kernel)]
  exact scalar763_eq797 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted797_eq763 : originalWeighted 797 =
    (1840 / 4419 : ℚ) * originalWeighted 763 := by
  rw [originalWeighted, originalWeighted, ← guarded763_eq797,
    coefficient797, coefficient763]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels764_790 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar764_eq790 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 764).expression.scalarPointContraction X v
      (L24Gluing.term 764).decoration (L24Gluing.term 764).labels beta n insertions =
    (L24Gluing.term 790).expression.scalarPointContraction X v
      (L24Gluing.term 790).decoration (L24Gluing.term 790).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core764 L24Gluing.term764.decoration L24Gluing.term764.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels764_790

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded764_eq790 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 764) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 790) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 764) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 790) (by decide +kernel)]
  exact scalar764_eq790 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted790_eq764 : originalWeighted 790 =
    (737 / 1737 : ℚ) * originalWeighted 764 := by
  rw [originalWeighted, originalWeighted, ← guarded764_eq790,
    coefficient790, coefficient764]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels764_798 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar764_eq798 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 764).expression.scalarPointContraction X v
      (L24Gluing.term 764).decoration (L24Gluing.term 764).labels beta n insertions =
    (L24Gluing.term 798).expression.scalarPointContraction X v
      (L24Gluing.term 798).decoration (L24Gluing.term 798).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core764 L24Gluing.term764.decoration L24Gluing.term764.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels764_798

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded764_eq798 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 764) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 798) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 764) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 798) (by decide +kernel)]
  exact scalar764_eq798 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted798_eq764 : originalWeighted 798 =
    (737 / 1737 : ℚ) * originalWeighted 764 := by
  rw [originalWeighted, originalWeighted, ← guarded764_eq798,
    coefficient798, coefficient764]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels765_791 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar765_eq791 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 765).expression.scalarPointContraction X v
      (L24Gluing.term 765).decoration (L24Gluing.term 765).labels beta n insertions =
    (L24Gluing.term 791).expression.scalarPointContraction X v
      (L24Gluing.term 791).decoration (L24Gluing.term 791).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core765 L24Gluing.term765.decoration L24Gluing.term765.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels765_791

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded765_eq791 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 765) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 791) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 765) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 791) (by decide +kernel)]
  exact scalar765_eq791 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted791_eq765 : originalWeighted 791 =
    (47 / 1791 : ℚ) * originalWeighted 765 := by
  rw [originalWeighted, originalWeighted, ← guarded765_eq791,
    coefficient791, coefficient765]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels765_799 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar765_eq799 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 765).expression.scalarPointContraction X v
      (L24Gluing.term 765).decoration (L24Gluing.term 765).labels beta n insertions =
    (L24Gluing.term 799).expression.scalarPointContraction X v
      (L24Gluing.term 799).decoration (L24Gluing.term 799).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core765 L24Gluing.term765.decoration L24Gluing.term765.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels765_799

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded765_eq799 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 765) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 799) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 765) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 799) (by decide +kernel)]
  exact scalar765_eq799 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted799_eq765 : originalWeighted 799 =
    (47 / 1791 : ℚ) * originalWeighted 765 := by
  rw [originalWeighted, originalWeighted, ← guarded765_eq799,
    coefficient799, coefficient765]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels766_792 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar766_eq792 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 766).expression.scalarPointContraction X v
      (L24Gluing.term 766).decoration (L24Gluing.term 766).labels beta n insertions =
    (L24Gluing.term 792).expression.scalarPointContraction X v
      (L24Gluing.term 792).decoration (L24Gluing.term 792).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core766 L24Gluing.term766.decoration L24Gluing.term766.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels766_792

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded766_eq792 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 766) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 792) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 766) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 792) (by decide +kernel)]
  exact scalar766_eq792 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted792_eq766 : originalWeighted 792 =
    (21590 / 45207 : ℚ) * originalWeighted 766 := by
  rw [originalWeighted, originalWeighted, ← guarded766_eq792,
    coefficient792, coefficient766]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels766_800 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar766_eq800 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 766).expression.scalarPointContraction X v
      (L24Gluing.term 766).decoration (L24Gluing.term 766).labels beta n insertions =
    (L24Gluing.term 800).expression.scalarPointContraction X v
      (L24Gluing.term 800).decoration (L24Gluing.term 800).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core766 L24Gluing.term766.decoration L24Gluing.term766.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels766_800

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded766_eq800 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 766) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 800) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 766) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 800) (by decide +kernel)]
  exact scalar766_eq800 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted800_eq766 : originalWeighted 800 =
    (21590 / 45207 : ℚ) * originalWeighted 766 := by
  rw [originalWeighted, originalWeighted, ← guarded766_eq800,
    coefficient800, coefficient766]
  ring

end AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15

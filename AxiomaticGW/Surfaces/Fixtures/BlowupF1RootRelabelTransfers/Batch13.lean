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

namespace AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13

open BlowupF1RootAssembly SurfaceGenusTwo GetzlerGraphs L24Gluing

private def core668 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 1 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)

private def core669 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 1 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)

private def core670 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 1 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation25)

private def core671 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)

private def core672 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 4) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation22)

private def core673 : GluingExpression 2 (Fin 4) :=
  close (join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )))

private def core674 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 4) (n := 2) 4 2
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)

private def core675 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation26)

private def core676 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 5) (n := 1) 5 1
    (join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)

private def core677 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))).relabel
      flagPermutation26)

private def core678 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 5) (n := 1) 5 1
    (join (m := 2) (n := 4) 2 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)

private def core679 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation27)

private def core680 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 6) (n := 0) 6 0
    (join (m := 2) (n := 5) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

theorem coefficient668 : L24CorrectionsReplay.fullClaim 668 =
    (-5023 / 28080 : ℚ) := by decide +kernel

theorem coefficient669 : L24CorrectionsReplay.fullClaim 669 =
    (539 / 5616 : ℚ) := by decide +kernel

theorem coefficient670 : L24CorrectionsReplay.fullClaim 670 =
    (1421 / 28080 : ℚ) := by decide +kernel

theorem coefficient671 : L24CorrectionsReplay.fullClaim 671 =
    (-1409 / 28080 : ℚ) := by decide +kernel

theorem coefficient672 : L24CorrectionsReplay.fullClaim 672 =
    (-5023 / 28080 : ℚ) := by decide +kernel

theorem coefficient673 : L24CorrectionsReplay.fullClaim 673 =
    (4637 / 238680 : ℚ) := by decide +kernel

theorem coefficient674 : L24CorrectionsReplay.fullClaim 674 =
    (83 / 17680 : ℚ) := by decide +kernel

theorem coefficient675 : L24CorrectionsReplay.fullClaim 675 =
    (-2077 / 238680 : ℚ) := by decide +kernel

theorem coefficient676 : L24CorrectionsReplay.fullClaim 676 =
    (-227 / 9360 : ℚ) := by decide +kernel

theorem coefficient677 : L24CorrectionsReplay.fullClaim 677 =
    (4637 / 238680 : ℚ) := by decide +kernel

theorem coefficient678 : L24CorrectionsReplay.fullClaim 678 =
    (2371 / 477360 : ℚ) := by decide +kernel

theorem coefficient679 : L24CorrectionsReplay.fullClaim 679 =
    (-7 / 780 : ℚ) := by decide +kernel

theorem coefficient680 : L24CorrectionsReplay.fullClaim 680 =
    (-227 / 9360 : ℚ) := by decide +kernel

theorem coefficient687 : L24CorrectionsReplay.fullClaim 687 =
    (1 / 7020 : ℚ) := by decide +kernel

theorem coefficient688 : L24CorrectionsReplay.fullClaim 688 =
    (1 / 7020 : ℚ) := by decide +kernel

theorem coefficient689 : L24CorrectionsReplay.fullClaim 689 =
    (1 / 7020 : ℚ) := by decide +kernel

theorem coefficient690 : L24CorrectionsReplay.fullClaim 690 =
    (-5023 / 42120 : ℚ) := by decide +kernel

theorem coefficient691 : L24CorrectionsReplay.fullClaim 691 =
    (-5023 / 42120 : ℚ) := by decide +kernel

theorem coefficient692 : L24CorrectionsReplay.fullClaim 692 =
    (4637 / 358020 : ℚ) := by decide +kernel

theorem coefficient693 : L24CorrectionsReplay.fullClaim 693 =
    (4637 / 358020 : ℚ) := by decide +kernel

theorem coefficient694 : L24CorrectionsReplay.fullClaim 694 =
    (-1913 / 1432080 : ℚ) := by decide +kernel

theorem coefficient695 : L24CorrectionsReplay.fullClaim 695 =
    (-1913 / 1432080 : ℚ) := by decide +kernel

theorem coefficient696 : L24CorrectionsReplay.fullClaim 696 =
    (-1913 / 1432080 : ℚ) := by decide +kernel

theorem coefficient697 : L24CorrectionsReplay.fullClaim 697 =
    (-1913 / 1432080 : ℚ) := by decide +kernel

theorem coefficient698 : L24CorrectionsReplay.fullClaim 698 =
    (-227 / 14040 : ℚ) := by decide +kernel

theorem coefficient699 : L24CorrectionsReplay.fullClaim 699 =
    (-227 / 14040 : ℚ) := by decide +kernel

theorem coefficient706 : L24CorrectionsReplay.fullClaim 706 =
    (1 / 7020 : ℚ) := by decide +kernel

theorem coefficient707 : L24CorrectionsReplay.fullClaim 707 =
    (1 / 7020 : ℚ) := by decide +kernel

theorem coefficient708 : L24CorrectionsReplay.fullClaim 708 =
    (1 / 7020 : ℚ) := by decide +kernel

theorem coefficient709 : L24CorrectionsReplay.fullClaim 709 =
    (-5023 / 42120 : ℚ) := by decide +kernel

theorem coefficient710 : L24CorrectionsReplay.fullClaim 710 =
    (-5023 / 42120 : ℚ) := by decide +kernel

theorem coefficient711 : L24CorrectionsReplay.fullClaim 711 =
    (4637 / 358020 : ℚ) := by decide +kernel

theorem coefficient712 : L24CorrectionsReplay.fullClaim 712 =
    (4637 / 358020 : ℚ) := by decide +kernel

theorem coefficient713 : L24CorrectionsReplay.fullClaim 713 =
    (-1913 / 1432080 : ℚ) := by decide +kernel

theorem coefficient714 : L24CorrectionsReplay.fullClaim 714 =
    (-1913 / 1432080 : ℚ) := by decide +kernel

theorem coefficient715 : L24CorrectionsReplay.fullClaim 715 =
    (-1913 / 1432080 : ℚ) := by decide +kernel

theorem coefficient716 : L24CorrectionsReplay.fullClaim 716 =
    (-1913 / 1432080 : ℚ) := by decide +kernel

theorem coefficient717 : L24CorrectionsReplay.fullClaim 717 =
    (-227 / 14040 : ℚ) := by decide +kernel

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels668_687 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation9 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar668_eq687 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 668).expression.scalarPointContraction X v
      (L24Gluing.term 668).decoration (L24Gluing.term 668).labels beta n insertions =
    (L24Gluing.term 687).expression.scalarPointContraction X v
      (L24Gluing.term 687).decoration (L24Gluing.term 687).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core668 L24Gluing.term668.decoration L24Gluing.term668.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 beta n insertions labels668_687

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded668_eq687 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 668) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 687) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 668) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 687) (by decide +kernel)]
  exact scalar668_eq687 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted687_eq668 : originalWeighted 687 =
    (-4 / 5023 : ℚ) * originalWeighted 668 := by
  rw [originalWeighted, originalWeighted, ← guarded668_eq687,
    coefficient687, coefficient668]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels668_706 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation3 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar668_eq706 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 668).expression.scalarPointContraction X v
      (L24Gluing.term 668).decoration (L24Gluing.term 668).labels beta n insertions =
    (L24Gluing.term 706).expression.scalarPointContraction X v
      (L24Gluing.term 706).decoration (L24Gluing.term 706).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core668 L24Gluing.term668.decoration L24Gluing.term668.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 beta n insertions labels668_706

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded668_eq706 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 668) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 706) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 668) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 706) (by decide +kernel)]
  exact scalar668_eq706 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted706_eq668 : originalWeighted 706 =
    (-4 / 5023 : ℚ) * originalWeighted 668 := by
  rw [originalWeighted, originalWeighted, ← guarded668_eq706,
    coefficient706, coefficient668]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels669_688 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar669_eq688 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 669).expression.scalarPointContraction X v
      (L24Gluing.term 669).decoration (L24Gluing.term 669).labels beta n insertions =
    (L24Gluing.term 688).expression.scalarPointContraction X v
      (L24Gluing.term 688).decoration (L24Gluing.term 688).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core669 L24Gluing.term669.decoration L24Gluing.term669.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels669_688

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded669_eq688 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 669) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 688) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 669) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 688) (by decide +kernel)]
  exact scalar669_eq688 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted688_eq669 : originalWeighted 688 =
    (4 / 2695 : ℚ) * originalWeighted 669 := by
  rw [originalWeighted, originalWeighted, ← guarded669_eq688,
    coefficient688, coefficient669]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels669_707 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar669_eq707 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 669).expression.scalarPointContraction X v
      (L24Gluing.term 669).decoration (L24Gluing.term 669).labels beta n insertions =
    (L24Gluing.term 707).expression.scalarPointContraction X v
      (L24Gluing.term 707).decoration (L24Gluing.term 707).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core669 L24Gluing.term669.decoration L24Gluing.term669.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels669_707

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded669_eq707 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 669) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 707) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 669) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 707) (by decide +kernel)]
  exact scalar669_eq707 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted707_eq669 : originalWeighted 707 =
    (4 / 2695 : ℚ) * originalWeighted 669 := by
  rw [originalWeighted, originalWeighted, ← guarded669_eq707,
    coefficient707, coefficient669]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels670_689 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar670_eq689 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 670).expression.scalarPointContraction X v
      (L24Gluing.term 670).decoration (L24Gluing.term 670).labels beta n insertions =
    (L24Gluing.term 689).expression.scalarPointContraction X v
      (L24Gluing.term 689).decoration (L24Gluing.term 689).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core670 L24Gluing.term670.decoration L24Gluing.term670.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels670_689

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded670_eq689 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 670) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 689) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 670) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 689) (by decide +kernel)]
  exact scalar670_eq689 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted689_eq670 : originalWeighted 689 =
    (4 / 1421 : ℚ) * originalWeighted 670 := by
  rw [originalWeighted, originalWeighted, ← guarded670_eq689,
    coefficient689, coefficient670]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels670_708 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar670_eq708 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 670).expression.scalarPointContraction X v
      (L24Gluing.term 670).decoration (L24Gluing.term 670).labels beta n insertions =
    (L24Gluing.term 708).expression.scalarPointContraction X v
      (L24Gluing.term 708).decoration (L24Gluing.term 708).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core670 L24Gluing.term670.decoration L24Gluing.term670.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels670_708

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded670_eq708 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 670) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 708) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 670) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 708) (by decide +kernel)]
  exact scalar670_eq708 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted708_eq670 : originalWeighted 708 =
    (4 / 1421 : ℚ) * originalWeighted 670 := by
  rw [originalWeighted, originalWeighted, ← guarded670_eq708,
    coefficient708, coefficient670]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels671_690 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar671_eq690 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 671).expression.scalarPointContraction X v
      (L24Gluing.term 671).decoration (L24Gluing.term 671).labels beta n insertions =
    (L24Gluing.term 690).expression.scalarPointContraction X v
      (L24Gluing.term 690).decoration (L24Gluing.term 690).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core671 L24Gluing.term671.decoration L24Gluing.term671.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels671_690

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded671_eq690 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 671) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 690) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 671) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 690) (by decide +kernel)]
  exact scalar671_eq690 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted690_eq671 : originalWeighted 690 =
    (10046 / 4227 : ℚ) * originalWeighted 671 := by
  rw [originalWeighted, originalWeighted, ← guarded671_eq690,
    coefficient690, coefficient671]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels671_709 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar671_eq709 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 671).expression.scalarPointContraction X v
      (L24Gluing.term 671).decoration (L24Gluing.term 671).labels beta n insertions =
    (L24Gluing.term 709).expression.scalarPointContraction X v
      (L24Gluing.term 709).decoration (L24Gluing.term 709).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core671 L24Gluing.term671.decoration L24Gluing.term671.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels671_709

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded671_eq709 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 671) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 709) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 671) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 709) (by decide +kernel)]
  exact scalar671_eq709 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted709_eq671 : originalWeighted 709 =
    (10046 / 4227 : ℚ) * originalWeighted 671 := by
  rw [originalWeighted, originalWeighted, ← guarded671_eq709,
    coefficient709, coefficient671]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels672_691 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar672_eq691 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 672).expression.scalarPointContraction X v
      (L24Gluing.term 672).decoration (L24Gluing.term 672).labels beta n insertions =
    (L24Gluing.term 691).expression.scalarPointContraction X v
      (L24Gluing.term 691).decoration (L24Gluing.term 691).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core672 L24Gluing.term672.decoration L24Gluing.term672.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels672_691

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded672_eq691 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 672) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 691) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 672) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 691) (by decide +kernel)]
  exact scalar672_eq691 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted691_eq672 : originalWeighted 691 =
    (2 / 3 : ℚ) * originalWeighted 672 := by
  rw [originalWeighted, originalWeighted, ← guarded672_eq691,
    coefficient691, coefficient672]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels672_710 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar672_eq710 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 672).expression.scalarPointContraction X v
      (L24Gluing.term 672).decoration (L24Gluing.term 672).labels beta n insertions =
    (L24Gluing.term 710).expression.scalarPointContraction X v
      (L24Gluing.term 710).decoration (L24Gluing.term 710).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core672 L24Gluing.term672.decoration L24Gluing.term672.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels672_710

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded672_eq710 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 672) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 710) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 672) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 710) (by decide +kernel)]
  exact scalar672_eq710 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted710_eq672 : originalWeighted 710 =
    (2 / 3 : ℚ) * originalWeighted 672 := by
  rw [originalWeighted, originalWeighted, ← guarded672_eq710,
    coefficient710, coefficient672]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels673_692 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar673_eq692 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 673).expression.scalarPointContraction X v
      (L24Gluing.term 673).decoration (L24Gluing.term 673).labels beta n insertions =
    (L24Gluing.term 692).expression.scalarPointContraction X v
      (L24Gluing.term 692).decoration (L24Gluing.term 692).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core673 L24Gluing.term673.decoration L24Gluing.term673.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels673_692

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded673_eq692 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 673) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 692) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 673) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 692) (by decide +kernel)]
  exact scalar673_eq692 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted692_eq673 : originalWeighted 692 =
    (2 / 3 : ℚ) * originalWeighted 673 := by
  rw [originalWeighted, originalWeighted, ← guarded673_eq692,
    coefficient692, coefficient673]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels673_711 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar673_eq711 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 673).expression.scalarPointContraction X v
      (L24Gluing.term 673).decoration (L24Gluing.term 673).labels beta n insertions =
    (L24Gluing.term 711).expression.scalarPointContraction X v
      (L24Gluing.term 711).decoration (L24Gluing.term 711).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core673 L24Gluing.term673.decoration L24Gluing.term673.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels673_711

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded673_eq711 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 673) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 711) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 673) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 711) (by decide +kernel)]
  exact scalar673_eq711 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted711_eq673 : originalWeighted 711 =
    (2 / 3 : ℚ) * originalWeighted 673 := by
  rw [originalWeighted, originalWeighted, ← guarded673_eq711,
    coefficient711, coefficient673]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels674_693 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar674_eq693 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 674).expression.scalarPointContraction X v
      (L24Gluing.term 674).decoration (L24Gluing.term 674).labels beta n insertions =
    (L24Gluing.term 693).expression.scalarPointContraction X v
      (L24Gluing.term 693).decoration (L24Gluing.term 693).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core674 L24Gluing.term674.decoration L24Gluing.term674.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels674_693

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded674_eq693 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 674) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 693) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 674) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 693) (by decide +kernel)]
  exact scalar674_eq693 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted693_eq674 : originalWeighted 693 =
    (18548 / 6723 : ℚ) * originalWeighted 674 := by
  rw [originalWeighted, originalWeighted, ← guarded674_eq693,
    coefficient693, coefficient674]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels674_712 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar674_eq712 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 674).expression.scalarPointContraction X v
      (L24Gluing.term 674).decoration (L24Gluing.term 674).labels beta n insertions =
    (L24Gluing.term 712).expression.scalarPointContraction X v
      (L24Gluing.term 712).decoration (L24Gluing.term 712).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core674 L24Gluing.term674.decoration L24Gluing.term674.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels674_712

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded674_eq712 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 674) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 712) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 674) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 712) (by decide +kernel)]
  exact scalar674_eq712 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted712_eq674 : originalWeighted 712 =
    (18548 / 6723 : ℚ) * originalWeighted 674 := by
  rw [originalWeighted, originalWeighted, ← guarded674_eq712,
    coefficient712, coefficient674]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels675_694 :
    insertions ∘ L24Gluing.flagPermutation3 =
      insertions ∘ L24Gluing.flagPermutation11 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar675_eq694 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 675).expression.scalarPointContraction X v
      (L24Gluing.term 675).decoration (L24Gluing.term 675).labels beta n insertions =
    (L24Gluing.term 694).expression.scalarPointContraction X v
      (L24Gluing.term 694).decoration (L24Gluing.term 694).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core675 L24Gluing.term675.decoration L24Gluing.term675.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation11 beta n insertions labels675_694

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded675_eq694 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 675) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 694) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 675) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 694) (by decide +kernel)]
  exact scalar675_eq694 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted694_eq675 : originalWeighted 694 =
    (1913 / 12462 : ℚ) * originalWeighted 675 := by
  rw [originalWeighted, originalWeighted, ← guarded675_eq694,
    coefficient694, coefficient675]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels675_713 :
    insertions ∘ L24Gluing.flagPermutation3 =
      insertions ∘ L24Gluing.flagPermutation12 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar675_eq713 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 675).expression.scalarPointContraction X v
      (L24Gluing.term 675).decoration (L24Gluing.term 675).labels beta n insertions =
    (L24Gluing.term 713).expression.scalarPointContraction X v
      (L24Gluing.term 713).decoration (L24Gluing.term 713).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core675 L24Gluing.term675.decoration L24Gluing.term675.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation12 beta n insertions labels675_713

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded675_eq713 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 675) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 713) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 675) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 713) (by decide +kernel)]
  exact scalar675_eq713 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted713_eq675 : originalWeighted 713 =
    (1913 / 12462 : ℚ) * originalWeighted 675 := by
  rw [originalWeighted, originalWeighted, ← guarded675_eq713,
    coefficient713, coefficient675]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels676_695 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation9 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar676_eq695 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 676).expression.scalarPointContraction X v
      (L24Gluing.term 676).decoration (L24Gluing.term 676).labels beta n insertions =
    (L24Gluing.term 695).expression.scalarPointContraction X v
      (L24Gluing.term 695).decoration (L24Gluing.term 695).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core676 L24Gluing.term676.decoration L24Gluing.term676.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 beta n insertions labels676_695

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded676_eq695 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 676) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 695) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 676) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 695) (by decide +kernel)]
  exact scalar676_eq695 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted695_eq676 : originalWeighted 695 =
    (1913 / 34731 : ℚ) * originalWeighted 676 := by
  rw [originalWeighted, originalWeighted, ← guarded676_eq695,
    coefficient695, coefficient676]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels676_714 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation3 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar676_eq714 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 676).expression.scalarPointContraction X v
      (L24Gluing.term 676).decoration (L24Gluing.term 676).labels beta n insertions =
    (L24Gluing.term 714).expression.scalarPointContraction X v
      (L24Gluing.term 714).decoration (L24Gluing.term 714).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core676 L24Gluing.term676.decoration L24Gluing.term676.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 beta n insertions labels676_714

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded676_eq714 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 676) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 714) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 676) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 714) (by decide +kernel)]
  exact scalar676_eq714 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted714_eq676 : originalWeighted 714 =
    (1913 / 34731 : ℚ) * originalWeighted 676 := by
  rw [originalWeighted, originalWeighted, ← guarded676_eq714,
    coefficient714, coefficient676]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels677_696 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar677_eq696 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 677).expression.scalarPointContraction X v
      (L24Gluing.term 677).decoration (L24Gluing.term 677).labels beta n insertions =
    (L24Gluing.term 696).expression.scalarPointContraction X v
      (L24Gluing.term 696).decoration (L24Gluing.term 696).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core677 L24Gluing.term677.decoration L24Gluing.term677.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels677_696

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded677_eq696 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 677) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 696) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 677) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 696) (by decide +kernel)]
  exact scalar677_eq696 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted696_eq677 : originalWeighted 696 =
    (-1913 / 27822 : ℚ) * originalWeighted 677 := by
  rw [originalWeighted, originalWeighted, ← guarded677_eq696,
    coefficient696, coefficient677]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels677_715 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar677_eq715 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 677).expression.scalarPointContraction X v
      (L24Gluing.term 677).decoration (L24Gluing.term 677).labels beta n insertions =
    (L24Gluing.term 715).expression.scalarPointContraction X v
      (L24Gluing.term 715).decoration (L24Gluing.term 715).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core677 L24Gluing.term677.decoration L24Gluing.term677.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels677_715

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded677_eq715 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 677) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 715) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 677) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 715) (by decide +kernel)]
  exact scalar677_eq715 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted715_eq677 : originalWeighted 715 =
    (-1913 / 27822 : ℚ) * originalWeighted 677 := by
  rw [originalWeighted, originalWeighted, ← guarded677_eq715,
    coefficient715, coefficient677]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels678_697 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar678_eq697 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 678).expression.scalarPointContraction X v
      (L24Gluing.term 678).decoration (L24Gluing.term 678).labels beta n insertions =
    (L24Gluing.term 697).expression.scalarPointContraction X v
      (L24Gluing.term 697).decoration (L24Gluing.term 697).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core678 L24Gluing.term678.decoration L24Gluing.term678.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels678_697

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded678_eq697 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 678) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 697) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 678) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 697) (by decide +kernel)]
  exact scalar678_eq697 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted697_eq678 : originalWeighted 697 =
    (-1913 / 7113 : ℚ) * originalWeighted 678 := by
  rw [originalWeighted, originalWeighted, ← guarded678_eq697,
    coefficient697, coefficient678]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels678_716 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar678_eq716 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 678).expression.scalarPointContraction X v
      (L24Gluing.term 678).decoration (L24Gluing.term 678).labels beta n insertions =
    (L24Gluing.term 716).expression.scalarPointContraction X v
      (L24Gluing.term 716).decoration (L24Gluing.term 716).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core678 L24Gluing.term678.decoration L24Gluing.term678.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels678_716

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded678_eq716 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 678) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 716) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 678) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 716) (by decide +kernel)]
  exact scalar678_eq716 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted716_eq678 : originalWeighted 716 =
    (-1913 / 7113 : ℚ) * originalWeighted 678 := by
  rw [originalWeighted, originalWeighted, ← guarded678_eq716,
    coefficient716, coefficient678]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels679_698 :
    insertions ∘ (Equiv.refl (Fin 4)) =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar679_eq698 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 679).expression.scalarPointContraction X v
      (L24Gluing.term 679).decoration (L24Gluing.term 679).labels beta n insertions =
    (L24Gluing.term 698).expression.scalarPointContraction X v
      (L24Gluing.term 698).decoration (L24Gluing.term 698).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core679 L24Gluing.term679.decoration L24Gluing.term679.labels
    (Equiv.refl (Fin 4)) L24Gluing.flagPermutation5 beta n insertions labels679_698

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded679_eq698 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 679) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 698) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 679) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 698) (by decide +kernel)]
  exact scalar679_eq698 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted698_eq679 : originalWeighted 698 =
    (227 / 126 : ℚ) * originalWeighted 679 := by
  rw [originalWeighted, originalWeighted, ← guarded679_eq698,
    coefficient698, coefficient679]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels679_717 :
    insertions ∘ (Equiv.refl (Fin 4)) =
      insertions ∘ L24Gluing.flagPermutation4 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar679_eq717 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 679).expression.scalarPointContraction X v
      (L24Gluing.term 679).decoration (L24Gluing.term 679).labels beta n insertions =
    (L24Gluing.term 717).expression.scalarPointContraction X v
      (L24Gluing.term 717).decoration (L24Gluing.term 717).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core679 L24Gluing.term679.decoration L24Gluing.term679.labels
    (Equiv.refl (Fin 4)) L24Gluing.flagPermutation4 beta n insertions labels679_717

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded679_eq717 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 679) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 717) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 679) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 717) (by decide +kernel)]
  exact scalar679_eq717 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted717_eq679 : originalWeighted 717 =
    (227 / 126 : ℚ) * originalWeighted 679 := by
  rw [originalWeighted, originalWeighted, ← guarded679_eq717,
    coefficient717, coefficient679]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels680_699 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar680_eq699 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 680).expression.scalarPointContraction X v
      (L24Gluing.term 680).decoration (L24Gluing.term 680).labels beta n insertions =
    (L24Gluing.term 699).expression.scalarPointContraction X v
      (L24Gluing.term 699).decoration (L24Gluing.term 699).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core680 L24Gluing.term680.decoration L24Gluing.term680.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels680_699

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded680_eq699 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 680) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 699) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 680) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 699) (by decide +kernel)]
  exact scalar680_eq699 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted699_eq680 : originalWeighted 699 =
    (2 / 3 : ℚ) * originalWeighted 680 := by
  rw [originalWeighted, originalWeighted, ← guarded680_eq699,
    coefficient699, coefficient680]
  ring

end AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13

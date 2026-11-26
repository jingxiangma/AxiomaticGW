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

namespace AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11

open BlowupF1RootAssembly SurfaceGenusTwo GetzlerGraphs L24Gluing

private def core579 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 4) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation25)

private def core580 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 4) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation25)

private def core581 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 4) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation25)

private def core602 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation26)

private def core603 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation26)

private def core604 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation26)

private def core605 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation26)

private def core610 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)

private def core611 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)

private def core612 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)

private def core613 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)

private def core634 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)

private def core635 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 4) (n := 2) 4 2
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation27)

theorem coefficient579 : L24CorrectionsReplay.fullClaim 579 =
    (-1 / 60 : ℚ) := by decide +kernel

theorem coefficient580 : L24CorrectionsReplay.fullClaim 580 =
    (-1 / 60 : ℚ) := by decide +kernel

theorem coefficient581 : L24CorrectionsReplay.fullClaim 581 =
    (-3 / 20 : ℚ) := by decide +kernel

theorem coefficient587 : L24CorrectionsReplay.fullClaim 587 =
    (-1 / 20 : ℚ) := by decide +kernel

theorem coefficient588 : L24CorrectionsReplay.fullClaim 588 =
    (1 / 60 : ℚ) := by decide +kernel

theorem coefficient589 : L24CorrectionsReplay.fullClaim 589 =
    (-1 / 20 : ℚ) := by decide +kernel

theorem coefficient591 : L24CorrectionsReplay.fullClaim 591 =
    (-1 / 20 : ℚ) := by decide +kernel

theorem coefficient592 : L24CorrectionsReplay.fullClaim 592 =
    (1 / 60 : ℚ) := by decide +kernel

theorem coefficient593 : L24CorrectionsReplay.fullClaim 593 =
    (-1 / 20 : ℚ) := by decide +kernel

theorem coefficient602 : L24CorrectionsReplay.fullClaim 602 =
    (7 / 720 : ℚ) := by decide +kernel

theorem coefficient603 : L24CorrectionsReplay.fullClaim 603 =
    (-1 / 720 : ℚ) := by decide +kernel

theorem coefficient604 : L24CorrectionsReplay.fullClaim 604 =
    (1 / 48 : ℚ) := by decide +kernel

theorem coefficient605 : L24CorrectionsReplay.fullClaim 605 =
    (-1 / 720 : ℚ) := by decide +kernel

theorem coefficient606 : L24CorrectionsReplay.fullClaim 606 =
    (7 / 720 : ℚ) := by decide +kernel

theorem coefficient607 : L24CorrectionsReplay.fullClaim 607 =
    (-1 / 720 : ℚ) := by decide +kernel

theorem coefficient608 : L24CorrectionsReplay.fullClaim 608 =
    (1 / 48 : ℚ) := by decide +kernel

theorem coefficient609 : L24CorrectionsReplay.fullClaim 609 =
    (-1 / 720 : ℚ) := by decide +kernel

theorem coefficient610 : L24CorrectionsReplay.fullClaim 610 =
    (-1 / 240 : ℚ) := by decide +kernel

theorem coefficient611 : L24CorrectionsReplay.fullClaim 611 =
    (-1 / 240 : ℚ) := by decide +kernel

theorem coefficient612 : L24CorrectionsReplay.fullClaim 612 =
    (1 / 80 : ℚ) := by decide +kernel

theorem coefficient613 : L24CorrectionsReplay.fullClaim 613 =
    (1 / 80 : ℚ) := by decide +kernel

theorem coefficient614 : L24CorrectionsReplay.fullClaim 614 =
    (3 / 80 : ℚ) := by decide +kernel

theorem coefficient615 : L24CorrectionsReplay.fullClaim 615 =
    (1 / 240 : ℚ) := by decide +kernel

theorem coefficient616 : L24CorrectionsReplay.fullClaim 616 =
    (1 / 240 : ℚ) := by decide +kernel

theorem coefficient617 : L24CorrectionsReplay.fullClaim 617 =
    (1 / 240 : ℚ) := by decide +kernel

theorem coefficient618 : L24CorrectionsReplay.fullClaim 618 =
    (-1 / 80 : ℚ) := by decide +kernel

theorem coefficient619 : L24CorrectionsReplay.fullClaim 619 =
    (-1 / 80 : ℚ) := by decide +kernel

theorem coefficient620 : L24CorrectionsReplay.fullClaim 620 =
    (1 / 240 : ℚ) := by decide +kernel

theorem coefficient621 : L24CorrectionsReplay.fullClaim 621 =
    (1 / 240 : ℚ) := by decide +kernel

theorem coefficient622 : L24CorrectionsReplay.fullClaim 622 =
    (-1 / 80 : ℚ) := by decide +kernel

theorem coefficient623 : L24CorrectionsReplay.fullClaim 623 =
    (-1 / 80 : ℚ) := by decide +kernel

theorem coefficient624 : L24CorrectionsReplay.fullClaim 624 =
    (1 / 240 : ℚ) := by decide +kernel

theorem coefficient625 : L24CorrectionsReplay.fullClaim 625 =
    (1 / 240 : ℚ) := by decide +kernel

theorem coefficient634 : L24CorrectionsReplay.fullClaim 634 =
    (-1 / 240 : ℚ) := by decide +kernel

theorem coefficient635 : L24CorrectionsReplay.fullClaim 635 =
    (-1 / 240 : ℚ) := by decide +kernel

theorem coefficient638 : L24CorrectionsReplay.fullClaim 638 =
    (-1 / 240 : ℚ) := by decide +kernel

theorem coefficient639 : L24CorrectionsReplay.fullClaim 639 =
    (-1 / 240 : ℚ) := by decide +kernel

theorem coefficient646 : L24CorrectionsReplay.fullClaim 646 =
    (-1 / 80 : ℚ) := by decide +kernel

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels579_587 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar579_eq587 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 579).expression.scalarPointContraction X v
      (L24Gluing.term 579).decoration (L24Gluing.term 579).labels beta n insertions =
    (L24Gluing.term 587).expression.scalarPointContraction X v
      (L24Gluing.term 587).decoration (L24Gluing.term 587).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core579 L24Gluing.term579.decoration L24Gluing.term579.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels579_587

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded579_eq587 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 579) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 587) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 579) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 587) (by decide +kernel)]
  exact scalar579_eq587 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted587_eq579 : originalWeighted 587 =
    (3 / 1 : ℚ) * originalWeighted 579 := by
  rw [originalWeighted, originalWeighted, ← guarded579_eq587,
    coefficient587, coefficient579]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels579_591 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar579_eq591 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 579).expression.scalarPointContraction X v
      (L24Gluing.term 579).decoration (L24Gluing.term 579).labels beta n insertions =
    (L24Gluing.term 591).expression.scalarPointContraction X v
      (L24Gluing.term 591).decoration (L24Gluing.term 591).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core579 L24Gluing.term579.decoration L24Gluing.term579.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels579_591

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded579_eq591 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 579) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 591) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 579) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 591) (by decide +kernel)]
  exact scalar579_eq591 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted591_eq579 : originalWeighted 591 =
    (3 / 1 : ℚ) * originalWeighted 579 := by
  rw [originalWeighted, originalWeighted, ← guarded579_eq591,
    coefficient591, coefficient579]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels580_588 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar580_eq588 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 580).expression.scalarPointContraction X v
      (L24Gluing.term 580).decoration (L24Gluing.term 580).labels beta n insertions =
    (L24Gluing.term 588).expression.scalarPointContraction X v
      (L24Gluing.term 588).decoration (L24Gluing.term 588).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core580 L24Gluing.term580.decoration L24Gluing.term580.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels580_588

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded580_eq588 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 580) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 588) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 580) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 588) (by decide +kernel)]
  exact scalar580_eq588 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted588_eq580 : originalWeighted 588 =
    (-1 / 1 : ℚ) * originalWeighted 580 := by
  rw [originalWeighted, originalWeighted, ← guarded580_eq588,
    coefficient588, coefficient580]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels580_592 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar580_eq592 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 580).expression.scalarPointContraction X v
      (L24Gluing.term 580).decoration (L24Gluing.term 580).labels beta n insertions =
    (L24Gluing.term 592).expression.scalarPointContraction X v
      (L24Gluing.term 592).decoration (L24Gluing.term 592).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core580 L24Gluing.term580.decoration L24Gluing.term580.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels580_592

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded580_eq592 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 580) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 592) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 580) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 592) (by decide +kernel)]
  exact scalar580_eq592 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted592_eq580 : originalWeighted 592 =
    (-1 / 1 : ℚ) * originalWeighted 580 := by
  rw [originalWeighted, originalWeighted, ← guarded580_eq592,
    coefficient592, coefficient580]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels581_589 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar581_eq589 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 581).expression.scalarPointContraction X v
      (L24Gluing.term 581).decoration (L24Gluing.term 581).labels beta n insertions =
    (L24Gluing.term 589).expression.scalarPointContraction X v
      (L24Gluing.term 589).decoration (L24Gluing.term 589).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core581 L24Gluing.term581.decoration L24Gluing.term581.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels581_589

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded581_eq589 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 581) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 589) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 581) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 589) (by decide +kernel)]
  exact scalar581_eq589 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted589_eq581 : originalWeighted 589 =
    (1 / 3 : ℚ) * originalWeighted 581 := by
  rw [originalWeighted, originalWeighted, ← guarded581_eq589,
    coefficient589, coefficient581]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels581_593 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar581_eq593 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 581).expression.scalarPointContraction X v
      (L24Gluing.term 581).decoration (L24Gluing.term 581).labels beta n insertions =
    (L24Gluing.term 593).expression.scalarPointContraction X v
      (L24Gluing.term 593).decoration (L24Gluing.term 593).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core581 L24Gluing.term581.decoration L24Gluing.term581.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels581_593

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded581_eq593 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 581) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 593) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 581) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 593) (by decide +kernel)]
  exact scalar581_eq593 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted593_eq581 : originalWeighted 593 =
    (1 / 3 : ℚ) * originalWeighted 581 := by
  rw [originalWeighted, originalWeighted, ← guarded581_eq593,
    coefficient593, coefficient581]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels602_606 :
    insertions ∘ L24Gluing.flagPermutation15 =
      insertions ∘ L24Gluing.flagPermutation16 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar602_eq606 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 602).expression.scalarPointContraction X v
      (L24Gluing.term 602).decoration (L24Gluing.term 602).labels beta n insertions =
    (L24Gluing.term 606).expression.scalarPointContraction X v
      (L24Gluing.term 606).decoration (L24Gluing.term 606).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core602 L24Gluing.term602.decoration L24Gluing.term602.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation16 beta n insertions labels602_606

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded602_eq606 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 602) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 606) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 602) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 606) (by decide +kernel)]
  exact scalar602_eq606 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted606_eq602 : originalWeighted 606 =
    (1 / 1 : ℚ) * originalWeighted 602 := by
  rw [originalWeighted, originalWeighted, ← guarded602_eq606,
    coefficient606, coefficient602]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels602_614 :
    insertions ∘ L24Gluing.flagPermutation15 =
      insertions ∘ L24Gluing.flagPermutation17 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar602_eq614 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 602).expression.scalarPointContraction X v
      (L24Gluing.term 602).decoration (L24Gluing.term 602).labels beta n insertions =
    (L24Gluing.term 614).expression.scalarPointContraction X v
      (L24Gluing.term 614).decoration (L24Gluing.term 614).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core602 L24Gluing.term602.decoration L24Gluing.term602.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation17 beta n insertions labels602_614

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded602_eq614 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 602) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 614) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 602) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 614) (by decide +kernel)]
  exact scalar602_eq614 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted614_eq602 : originalWeighted 614 =
    (27 / 7 : ℚ) * originalWeighted 602 := by
  rw [originalWeighted, originalWeighted, ← guarded602_eq614,
    coefficient614, coefficient602]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels603_607 :
    insertions ∘ L24Gluing.flagPermutation15 =
      insertions ∘ L24Gluing.flagPermutation16 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar603_eq607 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 603).expression.scalarPointContraction X v
      (L24Gluing.term 603).decoration (L24Gluing.term 603).labels beta n insertions =
    (L24Gluing.term 607).expression.scalarPointContraction X v
      (L24Gluing.term 607).decoration (L24Gluing.term 607).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core603 L24Gluing.term603.decoration L24Gluing.term603.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation16 beta n insertions labels603_607

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded603_eq607 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 603) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 607) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 603) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 607) (by decide +kernel)]
  exact scalar603_eq607 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted607_eq603 : originalWeighted 607 =
    (1 / 1 : ℚ) * originalWeighted 603 := by
  rw [originalWeighted, originalWeighted, ← guarded603_eq607,
    coefficient607, coefficient603]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels603_615 :
    insertions ∘ L24Gluing.flagPermutation15 =
      insertions ∘ L24Gluing.flagPermutation17 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar603_eq615 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 603).expression.scalarPointContraction X v
      (L24Gluing.term 603).decoration (L24Gluing.term 603).labels beta n insertions =
    (L24Gluing.term 615).expression.scalarPointContraction X v
      (L24Gluing.term 615).decoration (L24Gluing.term 615).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core603 L24Gluing.term603.decoration L24Gluing.term603.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation17 beta n insertions labels603_615

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded603_eq615 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 603) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 615) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 603) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 615) (by decide +kernel)]
  exact scalar603_eq615 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted615_eq603 : originalWeighted 615 =
    (-3 / 1 : ℚ) * originalWeighted 603 := by
  rw [originalWeighted, originalWeighted, ← guarded603_eq615,
    coefficient615, coefficient603]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels604_608 :
    insertions ∘ L24Gluing.flagPermutation15 =
      insertions ∘ L24Gluing.flagPermutation16 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar604_eq608 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 604).expression.scalarPointContraction X v
      (L24Gluing.term 604).decoration (L24Gluing.term 604).labels beta n insertions =
    (L24Gluing.term 608).expression.scalarPointContraction X v
      (L24Gluing.term 608).decoration (L24Gluing.term 608).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core604 L24Gluing.term604.decoration L24Gluing.term604.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation16 beta n insertions labels604_608

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded604_eq608 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 604) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 608) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 604) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 608) (by decide +kernel)]
  exact scalar604_eq608 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted608_eq604 : originalWeighted 608 =
    (1 / 1 : ℚ) * originalWeighted 604 := by
  rw [originalWeighted, originalWeighted, ← guarded604_eq608,
    coefficient608, coefficient604]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels604_616 :
    insertions ∘ L24Gluing.flagPermutation15 =
      insertions ∘ L24Gluing.flagPermutation17 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar604_eq616 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 604).expression.scalarPointContraction X v
      (L24Gluing.term 604).decoration (L24Gluing.term 604).labels beta n insertions =
    (L24Gluing.term 616).expression.scalarPointContraction X v
      (L24Gluing.term 616).decoration (L24Gluing.term 616).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core604 L24Gluing.term604.decoration L24Gluing.term604.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation17 beta n insertions labels604_616

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded604_eq616 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 604) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 616) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 604) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 616) (by decide +kernel)]
  exact scalar604_eq616 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted616_eq604 : originalWeighted 616 =
    (1 / 5 : ℚ) * originalWeighted 604 := by
  rw [originalWeighted, originalWeighted, ← guarded604_eq616,
    coefficient616, coefficient604]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels605_609 :
    insertions ∘ L24Gluing.flagPermutation15 =
      insertions ∘ L24Gluing.flagPermutation16 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar605_eq609 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 605).expression.scalarPointContraction X v
      (L24Gluing.term 605).decoration (L24Gluing.term 605).labels beta n insertions =
    (L24Gluing.term 609).expression.scalarPointContraction X v
      (L24Gluing.term 609).decoration (L24Gluing.term 609).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core605 L24Gluing.term605.decoration L24Gluing.term605.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation16 beta n insertions labels605_609

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded605_eq609 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 605) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 609) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 605) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 609) (by decide +kernel)]
  exact scalar605_eq609 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted609_eq605 : originalWeighted 609 =
    (1 / 1 : ℚ) * originalWeighted 605 := by
  rw [originalWeighted, originalWeighted, ← guarded605_eq609,
    coefficient609, coefficient605]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels605_617 :
    insertions ∘ L24Gluing.flagPermutation15 =
      insertions ∘ L24Gluing.flagPermutation17 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar605_eq617 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 605).expression.scalarPointContraction X v
      (L24Gluing.term 605).decoration (L24Gluing.term 605).labels beta n insertions =
    (L24Gluing.term 617).expression.scalarPointContraction X v
      (L24Gluing.term 617).decoration (L24Gluing.term 617).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core605 L24Gluing.term605.decoration L24Gluing.term605.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation17 beta n insertions labels605_617

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded605_eq617 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 605) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 617) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 605) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 617) (by decide +kernel)]
  exact scalar605_eq617 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted617_eq605 : originalWeighted 617 =
    (-3 / 1 : ℚ) * originalWeighted 605 := by
  rw [originalWeighted, originalWeighted, ← guarded605_eq617,
    coefficient617, coefficient605]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels610_618 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar610_eq618 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 610).expression.scalarPointContraction X v
      (L24Gluing.term 610).decoration (L24Gluing.term 610).labels beta n insertions =
    (L24Gluing.term 618).expression.scalarPointContraction X v
      (L24Gluing.term 618).decoration (L24Gluing.term 618).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core610 L24Gluing.term610.decoration L24Gluing.term610.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels610_618

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded610_eq618 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 610) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 618) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 610) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 618) (by decide +kernel)]
  exact scalar610_eq618 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted618_eq610 : originalWeighted 618 =
    (3 / 1 : ℚ) * originalWeighted 610 := by
  rw [originalWeighted, originalWeighted, ← guarded610_eq618,
    coefficient618, coefficient610]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels610_622 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar610_eq622 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 610).expression.scalarPointContraction X v
      (L24Gluing.term 610).decoration (L24Gluing.term 610).labels beta n insertions =
    (L24Gluing.term 622).expression.scalarPointContraction X v
      (L24Gluing.term 622).decoration (L24Gluing.term 622).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core610 L24Gluing.term610.decoration L24Gluing.term610.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels610_622

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded610_eq622 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 610) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 622) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 610) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 622) (by decide +kernel)]
  exact scalar610_eq622 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted622_eq610 : originalWeighted 622 =
    (3 / 1 : ℚ) * originalWeighted 610 := by
  rw [originalWeighted, originalWeighted, ← guarded610_eq622,
    coefficient622, coefficient610]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels611_619 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar611_eq619 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 611).expression.scalarPointContraction X v
      (L24Gluing.term 611).decoration (L24Gluing.term 611).labels beta n insertions =
    (L24Gluing.term 619).expression.scalarPointContraction X v
      (L24Gluing.term 619).decoration (L24Gluing.term 619).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core611 L24Gluing.term611.decoration L24Gluing.term611.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels611_619

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded611_eq619 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 611) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 619) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 611) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 619) (by decide +kernel)]
  exact scalar611_eq619 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted619_eq611 : originalWeighted 619 =
    (3 / 1 : ℚ) * originalWeighted 611 := by
  rw [originalWeighted, originalWeighted, ← guarded611_eq619,
    coefficient619, coefficient611]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels611_623 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar611_eq623 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 611).expression.scalarPointContraction X v
      (L24Gluing.term 611).decoration (L24Gluing.term 611).labels beta n insertions =
    (L24Gluing.term 623).expression.scalarPointContraction X v
      (L24Gluing.term 623).decoration (L24Gluing.term 623).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core611 L24Gluing.term611.decoration L24Gluing.term611.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels611_623

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded611_eq623 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 611) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 623) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 611) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 623) (by decide +kernel)]
  exact scalar611_eq623 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted623_eq611 : originalWeighted 623 =
    (3 / 1 : ℚ) * originalWeighted 611 := by
  rw [originalWeighted, originalWeighted, ← guarded611_eq623,
    coefficient623, coefficient611]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels612_620 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar612_eq620 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 612).expression.scalarPointContraction X v
      (L24Gluing.term 612).decoration (L24Gluing.term 612).labels beta n insertions =
    (L24Gluing.term 620).expression.scalarPointContraction X v
      (L24Gluing.term 620).decoration (L24Gluing.term 620).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core612 L24Gluing.term612.decoration L24Gluing.term612.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels612_620

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded612_eq620 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 612) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 620) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 612) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 620) (by decide +kernel)]
  exact scalar612_eq620 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted620_eq612 : originalWeighted 620 =
    (1 / 3 : ℚ) * originalWeighted 612 := by
  rw [originalWeighted, originalWeighted, ← guarded612_eq620,
    coefficient620, coefficient612]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels612_624 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar612_eq624 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 612).expression.scalarPointContraction X v
      (L24Gluing.term 612).decoration (L24Gluing.term 612).labels beta n insertions =
    (L24Gluing.term 624).expression.scalarPointContraction X v
      (L24Gluing.term 624).decoration (L24Gluing.term 624).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core612 L24Gluing.term612.decoration L24Gluing.term612.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels612_624

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded612_eq624 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 612) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 624) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 612) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 624) (by decide +kernel)]
  exact scalar612_eq624 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted624_eq612 : originalWeighted 624 =
    (1 / 3 : ℚ) * originalWeighted 612 := by
  rw [originalWeighted, originalWeighted, ← guarded612_eq624,
    coefficient624, coefficient612]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels613_621 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar613_eq621 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 613).expression.scalarPointContraction X v
      (L24Gluing.term 613).decoration (L24Gluing.term 613).labels beta n insertions =
    (L24Gluing.term 621).expression.scalarPointContraction X v
      (L24Gluing.term 621).decoration (L24Gluing.term 621).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core613 L24Gluing.term613.decoration L24Gluing.term613.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels613_621

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded613_eq621 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 613) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 621) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 613) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 621) (by decide +kernel)]
  exact scalar613_eq621 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted621_eq613 : originalWeighted 621 =
    (1 / 3 : ℚ) * originalWeighted 613 := by
  rw [originalWeighted, originalWeighted, ← guarded613_eq621,
    coefficient621, coefficient613]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels613_625 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar613_eq625 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 613).expression.scalarPointContraction X v
      (L24Gluing.term 613).decoration (L24Gluing.term 613).labels beta n insertions =
    (L24Gluing.term 625).expression.scalarPointContraction X v
      (L24Gluing.term 625).decoration (L24Gluing.term 625).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core613 L24Gluing.term613.decoration L24Gluing.term613.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels613_625

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded613_eq625 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 613) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 625) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 613) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 625) (by decide +kernel)]
  exact scalar613_eq625 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted625_eq613 : originalWeighted 625 =
    (1 / 3 : ℚ) * originalWeighted 613 := by
  rw [originalWeighted, originalWeighted, ← guarded613_eq625,
    coefficient625, coefficient613]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels634_638 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar634_eq638 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 634).expression.scalarPointContraction X v
      (L24Gluing.term 634).decoration (L24Gluing.term 634).labels beta n insertions =
    (L24Gluing.term 638).expression.scalarPointContraction X v
      (L24Gluing.term 638).decoration (L24Gluing.term 638).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core634 L24Gluing.term634.decoration L24Gluing.term634.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels634_638

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded634_eq638 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 634) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 638) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 634) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 638) (by decide +kernel)]
  exact scalar634_eq638 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted638_eq634 : originalWeighted 638 =
    (1 / 1 : ℚ) * originalWeighted 634 := by
  rw [originalWeighted, originalWeighted, ← guarded634_eq638,
    coefficient638, coefficient634]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels634_646 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar634_eq646 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 634).expression.scalarPointContraction X v
      (L24Gluing.term 634).decoration (L24Gluing.term 634).labels beta n insertions =
    (L24Gluing.term 646).expression.scalarPointContraction X v
      (L24Gluing.term 646).decoration (L24Gluing.term 646).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core634 L24Gluing.term634.decoration L24Gluing.term634.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels634_646

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded634_eq646 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 634) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 646) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 634) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 646) (by decide +kernel)]
  exact scalar634_eq646 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted646_eq634 : originalWeighted 646 =
    (3 / 1 : ℚ) * originalWeighted 634 := by
  rw [originalWeighted, originalWeighted, ← guarded634_eq646,
    coefficient646, coefficient634]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels635_639 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar635_eq639 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 635).expression.scalarPointContraction X v
      (L24Gluing.term 635).decoration (L24Gluing.term 635).labels beta n insertions =
    (L24Gluing.term 639).expression.scalarPointContraction X v
      (L24Gluing.term 639).decoration (L24Gluing.term 639).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core635 L24Gluing.term635.decoration L24Gluing.term635.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels635_639

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded635_eq639 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 635) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 639) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 635) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 639) (by decide +kernel)]
  exact scalar635_eq639 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted639_eq635 : originalWeighted 639 =
    (1 / 1 : ℚ) * originalWeighted 635 := by
  rw [originalWeighted, originalWeighted, ← guarded635_eq639,
    coefficient639, coefficient635]
  ring

end AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11

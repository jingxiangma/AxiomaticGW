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

namespace AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10

open BlowupF1RootAssembly SurfaceGenusTwo GetzlerGraphs L24Gluing

private def core526 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core527 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core528 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core548 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 1 3
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 5) (by norm_num [StableArity]) )).relabel
      flagPermutation23)

private def core550 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation24)

private def core551 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation24)

private def core552 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation24)

private def core553 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation24)

private def core570 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation24)

private def core571 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation24)

private def core572 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation24)

private def core573 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation24)

private def core578 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 4) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )).relabel
      flagPermutation25)

theorem coefficient526 : L24CorrectionsReplay.fullClaim 526 =
    (-1 / 360 : ℚ) := by decide +kernel

theorem coefficient527 : L24CorrectionsReplay.fullClaim 527 =
    (553 / 3744 : ℚ) := by decide +kernel

theorem coefficient528 : L24CorrectionsReplay.fullClaim 528 =
    (67 / 480 : ℚ) := by decide +kernel

theorem coefficient536 : L24CorrectionsReplay.fullClaim 536 =
    (76 / 1053 : ℚ) := by decide +kernel

theorem coefficient537 : L24CorrectionsReplay.fullClaim 537 =
    (67 / 1080 : ℚ) := by decide +kernel

theorem coefficient541 : L24CorrectionsReplay.fullClaim 541 =
    (-1 / 120 : ℚ) := by decide +kernel

theorem coefficient542 : L24CorrectionsReplay.fullClaim 542 =
    (76 / 1053 : ℚ) := by decide +kernel

theorem coefficient543 : L24CorrectionsReplay.fullClaim 543 =
    (67 / 1080 : ℚ) := by decide +kernel

theorem coefficient548 : L24CorrectionsReplay.fullClaim 548 =
    (1 / 30 : ℚ) := by decide +kernel

theorem coefficient549 : L24CorrectionsReplay.fullClaim 549 =
    (1 / 30 : ℚ) := by decide +kernel

theorem coefficient550 : L24CorrectionsReplay.fullClaim 550 =
    (-1 / 60 : ℚ) := by decide +kernel

theorem coefficient551 : L24CorrectionsReplay.fullClaim 551 =
    (-1 / 60 : ℚ) := by decide +kernel

theorem coefficient552 : L24CorrectionsReplay.fullClaim 552 =
    (1 / 36 : ℚ) := by decide +kernel

theorem coefficient553 : L24CorrectionsReplay.fullClaim 553 =
    (-1 / 60 : ℚ) := by decide +kernel

theorem coefficient555 : L24CorrectionsReplay.fullClaim 555 =
    (1 / 180 : ℚ) := by decide +kernel

theorem coefficient557 : L24CorrectionsReplay.fullClaim 557 =
    (-1 / 12 : ℚ) := by decide +kernel

theorem coefficient558 : L24CorrectionsReplay.fullClaim 558 =
    (-7 / 180 : ℚ) := by decide +kernel

theorem coefficient559 : L24CorrectionsReplay.fullClaim 559 =
    (1 / 180 : ℚ) := by decide +kernel

theorem coefficient560 : L24CorrectionsReplay.fullClaim 560 =
    (1 / 180 : ℚ) := by decide +kernel

theorem coefficient561 : L24CorrectionsReplay.fullClaim 561 =
    (-1 / 12 : ℚ) := by decide +kernel

theorem coefficient562 : L24CorrectionsReplay.fullClaim 562 =
    (-7 / 180 : ℚ) := by decide +kernel

theorem coefficient563 : L24CorrectionsReplay.fullClaim 563 =
    (1 / 180 : ℚ) := by decide +kernel

theorem coefficient564 : L24CorrectionsReplay.fullClaim 564 =
    (1 / 180 : ℚ) := by decide +kernel

theorem coefficient570 : L24CorrectionsReplay.fullClaim 570 =
    (-1 / 60 : ℚ) := by decide +kernel

theorem coefficient571 : L24CorrectionsReplay.fullClaim 571 =
    (-1 / 60 : ℚ) := by decide +kernel

theorem coefficient572 : L24CorrectionsReplay.fullClaim 572 =
    (-1 / 60 : ℚ) := by decide +kernel

theorem coefficient573 : L24CorrectionsReplay.fullClaim 573 =
    (1 / 36 : ℚ) := by decide +kernel

theorem coefficient574 : L24CorrectionsReplay.fullClaim 574 =
    (-1 / 60 : ℚ) := by decide +kernel

theorem coefficient575 : L24CorrectionsReplay.fullClaim 575 =
    (-1 / 60 : ℚ) := by decide +kernel

theorem coefficient576 : L24CorrectionsReplay.fullClaim 576 =
    (-1 / 60 : ℚ) := by decide +kernel

theorem coefficient577 : L24CorrectionsReplay.fullClaim 577 =
    (1 / 36 : ℚ) := by decide +kernel

theorem coefficient578 : L24CorrectionsReplay.fullClaim 578 =
    (-1 / 60 : ℚ) := by decide +kernel

theorem coefficient582 : L24CorrectionsReplay.fullClaim 582 =
    (-7 / 180 : ℚ) := by decide +kernel

theorem coefficient583 : L24CorrectionsReplay.fullClaim 583 =
    (-1 / 12 : ℚ) := by decide +kernel

theorem coefficient584 : L24CorrectionsReplay.fullClaim 584 =
    (1 / 180 : ℚ) := by decide +kernel

theorem coefficient585 : L24CorrectionsReplay.fullClaim 585 =
    (1 / 180 : ℚ) := by decide +kernel

theorem coefficient586 : L24CorrectionsReplay.fullClaim 586 =
    (1 / 60 : ℚ) := by decide +kernel

theorem coefficient590 : L24CorrectionsReplay.fullClaim 590 =
    (1 / 60 : ℚ) := by decide +kernel

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels526_541 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar526_eq541 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 526).expression.scalarPointContraction X v
      (L24Gluing.term 526).decoration (L24Gluing.term 526).labels beta n insertions =
    (L24Gluing.term 541).expression.scalarPointContraction X v
      (L24Gluing.term 541).decoration (L24Gluing.term 541).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core526 L24Gluing.term526.decoration L24Gluing.term526.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels526_541

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded526_eq541 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 526) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 541) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 526) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 541) (by decide +kernel)]
  exact scalar526_eq541 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted541_eq526 : originalWeighted 541 =
    (3 / 1 : ℚ) * originalWeighted 526 := by
  rw [originalWeighted, originalWeighted, ← guarded526_eq541,
    coefficient541, coefficient526]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels527_536 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar527_eq536 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 527).expression.scalarPointContraction X v
      (L24Gluing.term 527).decoration (L24Gluing.term 527).labels beta n insertions =
    (L24Gluing.term 536).expression.scalarPointContraction X v
      (L24Gluing.term 536).decoration (L24Gluing.term 536).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core527 L24Gluing.term527.decoration L24Gluing.term527.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels527_536

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded527_eq536 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 527) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 536) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 527) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 536) (by decide +kernel)]
  exact scalar527_eq536 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted536_eq527 : originalWeighted 536 =
    (2432 / 4977 : ℚ) * originalWeighted 527 := by
  rw [originalWeighted, originalWeighted, ← guarded527_eq536,
    coefficient536, coefficient527]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels527_542 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar527_eq542 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 527).expression.scalarPointContraction X v
      (L24Gluing.term 527).decoration (L24Gluing.term 527).labels beta n insertions =
    (L24Gluing.term 542).expression.scalarPointContraction X v
      (L24Gluing.term 542).decoration (L24Gluing.term 542).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core527 L24Gluing.term527.decoration L24Gluing.term527.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels527_542

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded527_eq542 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 527) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 542) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 527) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 542) (by decide +kernel)]
  exact scalar527_eq542 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted542_eq527 : originalWeighted 542 =
    (2432 / 4977 : ℚ) * originalWeighted 527 := by
  rw [originalWeighted, originalWeighted, ← guarded527_eq542,
    coefficient542, coefficient527]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels528_537 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar528_eq537 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 528).expression.scalarPointContraction X v
      (L24Gluing.term 528).decoration (L24Gluing.term 528).labels beta n insertions =
    (L24Gluing.term 537).expression.scalarPointContraction X v
      (L24Gluing.term 537).decoration (L24Gluing.term 537).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core528 L24Gluing.term528.decoration L24Gluing.term528.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels528_537

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded528_eq537 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 528) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 537) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 528) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 537) (by decide +kernel)]
  exact scalar528_eq537 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted537_eq528 : originalWeighted 537 =
    (4 / 9 : ℚ) * originalWeighted 528 := by
  rw [originalWeighted, originalWeighted, ← guarded528_eq537,
    coefficient537, coefficient528]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels528_543 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar528_eq543 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 528).expression.scalarPointContraction X v
      (L24Gluing.term 528).decoration (L24Gluing.term 528).labels beta n insertions =
    (L24Gluing.term 543).expression.scalarPointContraction X v
      (L24Gluing.term 543).decoration (L24Gluing.term 543).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core528 L24Gluing.term528.decoration L24Gluing.term528.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels528_543

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded528_eq543 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 528) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 543) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 528) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 543) (by decide +kernel)]
  exact scalar528_eq543 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted543_eq528 : originalWeighted 543 =
    (4 / 9 : ℚ) * originalWeighted 528 := by
  rw [originalWeighted, originalWeighted, ← guarded528_eq543,
    coefficient543, coefficient528]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels548_549 :
    insertions ∘ L24Gluing.flagPermutation15 =
      insertions ∘ L24Gluing.flagPermutation16 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar548_eq549 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 548).expression.scalarPointContraction X v
      (L24Gluing.term 548).decoration (L24Gluing.term 548).labels beta n insertions =
    (L24Gluing.term 549).expression.scalarPointContraction X v
      (L24Gluing.term 549).decoration (L24Gluing.term 549).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core548 L24Gluing.term548.decoration L24Gluing.term548.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation16 beta n insertions labels548_549

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded548_eq549 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 548) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 549) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 548) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 549) (by decide +kernel)]
  exact scalar548_eq549 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted549_eq548 : originalWeighted 549 =
    (1 / 1 : ℚ) * originalWeighted 548 := by
  rw [originalWeighted, originalWeighted, ← guarded548_eq549,
    coefficient549, coefficient548]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels548_555 :
    insertions ∘ L24Gluing.flagPermutation15 =
      insertions ∘ L24Gluing.flagPermutation17 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar548_eq555 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 548).expression.scalarPointContraction X v
      (L24Gluing.term 548).decoration (L24Gluing.term 548).labels beta n insertions =
    (L24Gluing.term 555).expression.scalarPointContraction X v
      (L24Gluing.term 555).decoration (L24Gluing.term 555).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core548 L24Gluing.term548.decoration L24Gluing.term548.labels
    L24Gluing.flagPermutation15 L24Gluing.flagPermutation17 beta n insertions labels548_555

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded548_eq555 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 548) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 555) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 548) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 555) (by decide +kernel)]
  exact scalar548_eq555 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted555_eq548 : originalWeighted 555 =
    (1 / 6 : ℚ) * originalWeighted 548 := by
  rw [originalWeighted, originalWeighted, ← guarded548_eq555,
    coefficient555, coefficient548]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels550_557 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar550_eq557 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 550).expression.scalarPointContraction X v
      (L24Gluing.term 550).decoration (L24Gluing.term 550).labels beta n insertions =
    (L24Gluing.term 557).expression.scalarPointContraction X v
      (L24Gluing.term 557).decoration (L24Gluing.term 557).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core550 L24Gluing.term550.decoration L24Gluing.term550.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels550_557

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded550_eq557 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 550) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 557) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 550) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 557) (by decide +kernel)]
  exact scalar550_eq557 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted557_eq550 : originalWeighted 557 =
    (5 / 1 : ℚ) * originalWeighted 550 := by
  rw [originalWeighted, originalWeighted, ← guarded550_eq557,
    coefficient557, coefficient550]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels550_561 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar550_eq561 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 550).expression.scalarPointContraction X v
      (L24Gluing.term 550).decoration (L24Gluing.term 550).labels beta n insertions =
    (L24Gluing.term 561).expression.scalarPointContraction X v
      (L24Gluing.term 561).decoration (L24Gluing.term 561).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core550 L24Gluing.term550.decoration L24Gluing.term550.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels550_561

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded550_eq561 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 550) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 561) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 550) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 561) (by decide +kernel)]
  exact scalar550_eq561 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted561_eq550 : originalWeighted 561 =
    (5 / 1 : ℚ) * originalWeighted 550 := by
  rw [originalWeighted, originalWeighted, ← guarded550_eq561,
    coefficient561, coefficient550]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels551_558 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar551_eq558 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 551).expression.scalarPointContraction X v
      (L24Gluing.term 551).decoration (L24Gluing.term 551).labels beta n insertions =
    (L24Gluing.term 558).expression.scalarPointContraction X v
      (L24Gluing.term 558).decoration (L24Gluing.term 558).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core551 L24Gluing.term551.decoration L24Gluing.term551.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels551_558

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded551_eq558 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 551) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 558) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 551) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 558) (by decide +kernel)]
  exact scalar551_eq558 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted558_eq551 : originalWeighted 558 =
    (7 / 3 : ℚ) * originalWeighted 551 := by
  rw [originalWeighted, originalWeighted, ← guarded551_eq558,
    coefficient558, coefficient551]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels551_562 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar551_eq562 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 551).expression.scalarPointContraction X v
      (L24Gluing.term 551).decoration (L24Gluing.term 551).labels beta n insertions =
    (L24Gluing.term 562).expression.scalarPointContraction X v
      (L24Gluing.term 562).decoration (L24Gluing.term 562).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core551 L24Gluing.term551.decoration L24Gluing.term551.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels551_562

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded551_eq562 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 551) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 562) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 551) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 562) (by decide +kernel)]
  exact scalar551_eq562 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted562_eq551 : originalWeighted 562 =
    (7 / 3 : ℚ) * originalWeighted 551 := by
  rw [originalWeighted, originalWeighted, ← guarded551_eq562,
    coefficient562, coefficient551]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels552_559 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar552_eq559 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 552).expression.scalarPointContraction X v
      (L24Gluing.term 552).decoration (L24Gluing.term 552).labels beta n insertions =
    (L24Gluing.term 559).expression.scalarPointContraction X v
      (L24Gluing.term 559).decoration (L24Gluing.term 559).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core552 L24Gluing.term552.decoration L24Gluing.term552.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels552_559

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded552_eq559 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 552) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 559) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 552) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 559) (by decide +kernel)]
  exact scalar552_eq559 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted559_eq552 : originalWeighted 559 =
    (1 / 5 : ℚ) * originalWeighted 552 := by
  rw [originalWeighted, originalWeighted, ← guarded552_eq559,
    coefficient559, coefficient552]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels552_563 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar552_eq563 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 552).expression.scalarPointContraction X v
      (L24Gluing.term 552).decoration (L24Gluing.term 552).labels beta n insertions =
    (L24Gluing.term 563).expression.scalarPointContraction X v
      (L24Gluing.term 563).decoration (L24Gluing.term 563).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core552 L24Gluing.term552.decoration L24Gluing.term552.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels552_563

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded552_eq563 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 552) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 563) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 552) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 563) (by decide +kernel)]
  exact scalar552_eq563 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted563_eq552 : originalWeighted 563 =
    (1 / 5 : ℚ) * originalWeighted 552 := by
  rw [originalWeighted, originalWeighted, ← guarded552_eq563,
    coefficient563, coefficient552]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels553_560 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar553_eq560 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 553).expression.scalarPointContraction X v
      (L24Gluing.term 553).decoration (L24Gluing.term 553).labels beta n insertions =
    (L24Gluing.term 560).expression.scalarPointContraction X v
      (L24Gluing.term 560).decoration (L24Gluing.term 560).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core553 L24Gluing.term553.decoration L24Gluing.term553.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels553_560

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded553_eq560 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 553) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 560) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 553) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 560) (by decide +kernel)]
  exact scalar553_eq560 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted560_eq553 : originalWeighted 560 =
    (-1 / 3 : ℚ) * originalWeighted 553 := by
  rw [originalWeighted, originalWeighted, ← guarded553_eq560,
    coefficient560, coefficient553]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels553_564 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar553_eq564 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 553).expression.scalarPointContraction X v
      (L24Gluing.term 553).decoration (L24Gluing.term 553).labels beta n insertions =
    (L24Gluing.term 564).expression.scalarPointContraction X v
      (L24Gluing.term 564).decoration (L24Gluing.term 564).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core553 L24Gluing.term553.decoration L24Gluing.term553.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels553_564

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded553_eq564 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 553) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 564) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 553) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 564) (by decide +kernel)]
  exact scalar553_eq564 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted564_eq553 : originalWeighted 564 =
    (-1 / 3 : ℚ) * originalWeighted 553 := by
  rw [originalWeighted, originalWeighted, ← guarded553_eq564,
    coefficient564, coefficient553]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels570_574 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar570_eq574 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 570).expression.scalarPointContraction X v
      (L24Gluing.term 570).decoration (L24Gluing.term 570).labels beta n insertions =
    (L24Gluing.term 574).expression.scalarPointContraction X v
      (L24Gluing.term 574).decoration (L24Gluing.term 574).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core570 L24Gluing.term570.decoration L24Gluing.term570.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels570_574

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded570_eq574 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 570) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 574) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 570) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 574) (by decide +kernel)]
  exact scalar570_eq574 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted574_eq570 : originalWeighted 574 =
    (1 / 1 : ℚ) * originalWeighted 570 := by
  rw [originalWeighted, originalWeighted, ← guarded570_eq574,
    coefficient574, coefficient570]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels570_582 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar570_eq582 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 570).expression.scalarPointContraction X v
      (L24Gluing.term 570).decoration (L24Gluing.term 570).labels beta n insertions =
    (L24Gluing.term 582).expression.scalarPointContraction X v
      (L24Gluing.term 582).decoration (L24Gluing.term 582).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core570 L24Gluing.term570.decoration L24Gluing.term570.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels570_582

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded570_eq582 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 570) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 582) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 570) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 582) (by decide +kernel)]
  exact scalar570_eq582 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted582_eq570 : originalWeighted 582 =
    (7 / 3 : ℚ) * originalWeighted 570 := by
  rw [originalWeighted, originalWeighted, ← guarded570_eq582,
    coefficient582, coefficient570]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels571_575 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar571_eq575 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 571).expression.scalarPointContraction X v
      (L24Gluing.term 571).decoration (L24Gluing.term 571).labels beta n insertions =
    (L24Gluing.term 575).expression.scalarPointContraction X v
      (L24Gluing.term 575).decoration (L24Gluing.term 575).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core571 L24Gluing.term571.decoration L24Gluing.term571.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels571_575

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded571_eq575 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 571) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 575) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 571) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 575) (by decide +kernel)]
  exact scalar571_eq575 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted575_eq571 : originalWeighted 575 =
    (1 / 1 : ℚ) * originalWeighted 571 := by
  rw [originalWeighted, originalWeighted, ← guarded571_eq575,
    coefficient575, coefficient571]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels571_583 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar571_eq583 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 571).expression.scalarPointContraction X v
      (L24Gluing.term 571).decoration (L24Gluing.term 571).labels beta n insertions =
    (L24Gluing.term 583).expression.scalarPointContraction X v
      (L24Gluing.term 583).decoration (L24Gluing.term 583).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core571 L24Gluing.term571.decoration L24Gluing.term571.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels571_583

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded571_eq583 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 571) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 583) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 571) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 583) (by decide +kernel)]
  exact scalar571_eq583 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted583_eq571 : originalWeighted 583 =
    (5 / 1 : ℚ) * originalWeighted 571 := by
  rw [originalWeighted, originalWeighted, ← guarded571_eq583,
    coefficient583, coefficient571]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels572_576 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar572_eq576 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 572).expression.scalarPointContraction X v
      (L24Gluing.term 572).decoration (L24Gluing.term 572).labels beta n insertions =
    (L24Gluing.term 576).expression.scalarPointContraction X v
      (L24Gluing.term 576).decoration (L24Gluing.term 576).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core572 L24Gluing.term572.decoration L24Gluing.term572.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels572_576

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded572_eq576 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 572) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 576) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 572) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 576) (by decide +kernel)]
  exact scalar572_eq576 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted576_eq572 : originalWeighted 576 =
    (1 / 1 : ℚ) * originalWeighted 572 := by
  rw [originalWeighted, originalWeighted, ← guarded572_eq576,
    coefficient576, coefficient572]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels572_584 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar572_eq584 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 572).expression.scalarPointContraction X v
      (L24Gluing.term 572).decoration (L24Gluing.term 572).labels beta n insertions =
    (L24Gluing.term 584).expression.scalarPointContraction X v
      (L24Gluing.term 584).decoration (L24Gluing.term 584).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core572 L24Gluing.term572.decoration L24Gluing.term572.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels572_584

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded572_eq584 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 572) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 584) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 572) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 584) (by decide +kernel)]
  exact scalar572_eq584 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted584_eq572 : originalWeighted 584 =
    (-1 / 3 : ℚ) * originalWeighted 572 := by
  rw [originalWeighted, originalWeighted, ← guarded572_eq584,
    coefficient584, coefficient572]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels573_577 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar573_eq577 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 573).expression.scalarPointContraction X v
      (L24Gluing.term 573).decoration (L24Gluing.term 573).labels beta n insertions =
    (L24Gluing.term 577).expression.scalarPointContraction X v
      (L24Gluing.term 577).decoration (L24Gluing.term 577).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core573 L24Gluing.term573.decoration L24Gluing.term573.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels573_577

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded573_eq577 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 573) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 577) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 573) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 577) (by decide +kernel)]
  exact scalar573_eq577 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted577_eq573 : originalWeighted 577 =
    (1 / 1 : ℚ) * originalWeighted 573 := by
  rw [originalWeighted, originalWeighted, ← guarded573_eq577,
    coefficient577, coefficient573]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels573_585 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar573_eq585 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 573).expression.scalarPointContraction X v
      (L24Gluing.term 573).decoration (L24Gluing.term 573).labels beta n insertions =
    (L24Gluing.term 585).expression.scalarPointContraction X v
      (L24Gluing.term 585).decoration (L24Gluing.term 585).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core573 L24Gluing.term573.decoration L24Gluing.term573.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels573_585

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded573_eq585 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 573) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 585) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 573) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 585) (by decide +kernel)]
  exact scalar573_eq585 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted585_eq573 : originalWeighted 585 =
    (1 / 5 : ℚ) * originalWeighted 573 := by
  rw [originalWeighted, originalWeighted, ← guarded573_eq585,
    coefficient585, coefficient573]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels578_586 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar578_eq586 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 578).expression.scalarPointContraction X v
      (L24Gluing.term 578).decoration (L24Gluing.term 578).labels beta n insertions =
    (L24Gluing.term 586).expression.scalarPointContraction X v
      (L24Gluing.term 586).decoration (L24Gluing.term 586).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core578 L24Gluing.term578.decoration L24Gluing.term578.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels578_586

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded578_eq586 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 578) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 586) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 578) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 586) (by decide +kernel)]
  exact scalar578_eq586 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted586_eq578 : originalWeighted 586 =
    (-1 / 1 : ℚ) * originalWeighted 578 := by
  rw [originalWeighted, originalWeighted, ← guarded578_eq586,
    coefficient586, coefficient578]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels578_590 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar578_eq590 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 578).expression.scalarPointContraction X v
      (L24Gluing.term 578).decoration (L24Gluing.term 578).labels beta n insertions =
    (L24Gluing.term 590).expression.scalarPointContraction X v
      (L24Gluing.term 590).decoration (L24Gluing.term 590).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core578 L24Gluing.term578.decoration L24Gluing.term578.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels578_590

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded578_eq590 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 578) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 590) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 578) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 590) (by decide +kernel)]
  exact scalar578_eq590 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted590_eq578 : originalWeighted 590 =
    (-1 / 1 : ℚ) * originalWeighted 578 := by
  rw [originalWeighted, originalWeighted, ← guarded578_eq590,
    coefficient590, coefficient578]
  ring

end AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10

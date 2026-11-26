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

namespace AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09

open BlowupF1RootAssembly SurfaceGenusTwo GetzlerGraphs L24Gluing

private def core489 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])))

private def core493 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])))

private def core495 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

private def core499 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 5) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core500 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 5) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core501 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 5) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core515 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 5) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core516 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 5) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core517 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 5) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core518 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 5) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core523 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core524 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core525 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core526 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

theorem coefficient489 : L24CorrectionsReplay.fullClaim 489 =
    (3853 / 1989 : ℚ) := by decide +kernel

theorem coefficient491 : L24CorrectionsReplay.fullClaim 491 =
    (7706 / 5967 : ℚ) := by decide +kernel

theorem coefficient493 : L24CorrectionsReplay.fullClaim 493 =
    (3853 / 1989 : ℚ) := by decide +kernel

theorem coefficient494 : L24CorrectionsReplay.fullClaim 494 =
    (3853 / 1989 : ℚ) := by decide +kernel

theorem coefficient495 : L24CorrectionsReplay.fullClaim 495 =
    (3853 / 663 : ℚ) := by decide +kernel

theorem coefficient496 : L24CorrectionsReplay.fullClaim 496 =
    (7706 / 5967 : ℚ) := by decide +kernel

theorem coefficient497 : L24CorrectionsReplay.fullClaim 497 =
    (15740 / 5967 : ℚ) := by decide +kernel

theorem coefficient498 : L24CorrectionsReplay.fullClaim 498 =
    (15740 / 5967 : ℚ) := by decide +kernel

theorem coefficient499 : L24CorrectionsReplay.fullClaim 499 =
    (-539 / 5616 : ℚ) := by decide +kernel

theorem coefficient500 : L24CorrectionsReplay.fullClaim 500 =
    (1 / 360 : ℚ) := by decide +kernel

theorem coefficient501 : L24CorrectionsReplay.fullClaim 501 =
    (101 / 1560 : ℚ) := by decide +kernel

theorem coefficient503 : L24CorrectionsReplay.fullClaim 503 =
    (-539 / 8424 : ℚ) := by decide +kernel

theorem coefficient504 : L24CorrectionsReplay.fullClaim 504 =
    (2923 / 84240 : ℚ) := by decide +kernel

theorem coefficient505 : L24CorrectionsReplay.fullClaim 505 =
    (2923 / 84240 : ℚ) := by decide +kernel

theorem coefficient506 : L24CorrectionsReplay.fullClaim 506 =
    (-539 / 8424 : ℚ) := by decide +kernel

theorem coefficient507 : L24CorrectionsReplay.fullClaim 507 =
    (2923 / 84240 : ℚ) := by decide +kernel

theorem coefficient508 : L24CorrectionsReplay.fullClaim 508 =
    (2923 / 84240 : ℚ) := by decide +kernel

theorem coefficient515 : L24CorrectionsReplay.fullClaim 515 =
    (-539 / 5616 : ℚ) := by decide +kernel

theorem coefficient516 : L24CorrectionsReplay.fullClaim 516 =
    (101 / 1560 : ℚ) := by decide +kernel

theorem coefficient517 : L24CorrectionsReplay.fullClaim 517 =
    (1 / 360 : ℚ) := by decide +kernel

theorem coefficient518 : L24CorrectionsReplay.fullClaim 518 =
    (67 / 2160 : ℚ) := by decide +kernel

theorem coefficient519 : L24CorrectionsReplay.fullClaim 519 =
    (-539 / 5616 : ℚ) := by decide +kernel

theorem coefficient520 : L24CorrectionsReplay.fullClaim 520 =
    (101 / 1560 : ℚ) := by decide +kernel

theorem coefficient521 : L24CorrectionsReplay.fullClaim 521 =
    (1 / 360 : ℚ) := by decide +kernel

theorem coefficient522 : L24CorrectionsReplay.fullClaim 522 =
    (67 / 2160 : ℚ) := by decide +kernel

theorem coefficient523 : L24CorrectionsReplay.fullClaim 523 =
    (-539 / 1872 : ℚ) := by decide +kernel

theorem coefficient524 : L24CorrectionsReplay.fullClaim 524 =
    (-1 / 360 : ℚ) := by decide +kernel

theorem coefficient525 : L24CorrectionsReplay.fullClaim 525 =
    (-1 / 360 : ℚ) := by decide +kernel

theorem coefficient526 : L24CorrectionsReplay.fullClaim 526 =
    (-1 / 360 : ℚ) := by decide +kernel

theorem coefficient529 : L24CorrectionsReplay.fullClaim 529 =
    (-539 / 8424 : ℚ) := by decide +kernel

theorem coefficient530 : L24CorrectionsReplay.fullClaim 530 =
    (2923 / 84240 : ℚ) := by decide +kernel

theorem coefficient531 : L24CorrectionsReplay.fullClaim 531 =
    (2923 / 84240 : ℚ) := by decide +kernel

theorem coefficient532 : L24CorrectionsReplay.fullClaim 532 =
    (-1085 / 8424 : ℚ) := by decide +kernel

theorem coefficient533 : L24CorrectionsReplay.fullClaim 533 =
    (-1 / 120 : ℚ) := by decide +kernel

theorem coefficient534 : L24CorrectionsReplay.fullClaim 534 =
    (-1 / 24 : ℚ) := by decide +kernel

theorem coefficient535 : L24CorrectionsReplay.fullClaim 535 =
    (-1 / 120 : ℚ) := by decide +kernel

theorem coefficient538 : L24CorrectionsReplay.fullClaim 538 =
    (-1085 / 8424 : ℚ) := by decide +kernel

theorem coefficient539 : L24CorrectionsReplay.fullClaim 539 =
    (-1 / 120 : ℚ) := by decide +kernel

theorem coefficient540 : L24CorrectionsReplay.fullClaim 540 =
    (-1 / 24 : ℚ) := by decide +kernel

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels489_491 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar489_eq491 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 489).expression.scalarPointContraction X v
      (L24Gluing.term 489).decoration (L24Gluing.term 489).labels beta n insertions =
    (L24Gluing.term 491).expression.scalarPointContraction X v
      (L24Gluing.term 491).decoration (L24Gluing.term 491).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core489 L24Gluing.term489.decoration L24Gluing.term489.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels489_491

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded489_eq491 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 489) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 491) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 489) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 491) (by decide +kernel)]
  exact scalar489_eq491 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted491_eq489 : originalWeighted 491 =
    (2 / 3 : ℚ) * originalWeighted 489 := by
  rw [originalWeighted, originalWeighted, ← guarded489_eq491,
    coefficient491, coefficient489]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels493_494 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar493_eq494 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 493).expression.scalarPointContraction X v
      (L24Gluing.term 493).decoration (L24Gluing.term 493).labels beta n insertions =
    (L24Gluing.term 494).expression.scalarPointContraction X v
      (L24Gluing.term 494).decoration (L24Gluing.term 494).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core493 L24Gluing.term493.decoration L24Gluing.term493.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels493_494

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded493_eq494 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 493) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 494) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 493) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 494) (by decide +kernel)]
  exact scalar493_eq494 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted494_eq493 : originalWeighted 494 =
    (1 / 1 : ℚ) * originalWeighted 493 := by
  rw [originalWeighted, originalWeighted, ← guarded493_eq494,
    coefficient494, coefficient493]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels493_496 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar493_eq496 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 493).expression.scalarPointContraction X v
      (L24Gluing.term 493).decoration (L24Gluing.term 493).labels beta n insertions =
    (L24Gluing.term 496).expression.scalarPointContraction X v
      (L24Gluing.term 496).decoration (L24Gluing.term 496).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core493 L24Gluing.term493.decoration L24Gluing.term493.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels493_496

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded493_eq496 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 493) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 496) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 493) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 496) (by decide +kernel)]
  exact scalar493_eq496 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted496_eq493 : originalWeighted 496 =
    (2 / 3 : ℚ) * originalWeighted 493 := by
  rw [originalWeighted, originalWeighted, ← guarded493_eq496,
    coefficient496, coefficient493]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels495_497 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar495_eq497 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 495).expression.scalarPointContraction X v
      (L24Gluing.term 495).decoration (L24Gluing.term 495).labels beta n insertions =
    (L24Gluing.term 497).expression.scalarPointContraction X v
      (L24Gluing.term 497).decoration (L24Gluing.term 497).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core495 L24Gluing.term495.decoration L24Gluing.term495.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels495_497

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded495_eq497 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 495) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 497) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 495) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 497) (by decide +kernel)]
  exact scalar495_eq497 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted497_eq495 : originalWeighted 497 =
    (15740 / 34677 : ℚ) * originalWeighted 495 := by
  rw [originalWeighted, originalWeighted, ← guarded495_eq497,
    coefficient497, coefficient495]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels495_498 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar495_eq498 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 495).expression.scalarPointContraction X v
      (L24Gluing.term 495).decoration (L24Gluing.term 495).labels beta n insertions =
    (L24Gluing.term 498).expression.scalarPointContraction X v
      (L24Gluing.term 498).decoration (L24Gluing.term 498).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core495 L24Gluing.term495.decoration L24Gluing.term495.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels495_498

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded495_eq498 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 495) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 498) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 495) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 498) (by decide +kernel)]
  exact scalar495_eq498 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted498_eq495 : originalWeighted 498 =
    (15740 / 34677 : ℚ) * originalWeighted 495 := by
  rw [originalWeighted, originalWeighted, ← guarded495_eq498,
    coefficient498, coefficient495]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels499_503 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar499_eq503 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 499).expression.scalarPointContraction X v
      (L24Gluing.term 499).decoration (L24Gluing.term 499).labels beta n insertions =
    (L24Gluing.term 503).expression.scalarPointContraction X v
      (L24Gluing.term 503).decoration (L24Gluing.term 503).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core499 L24Gluing.term499.decoration L24Gluing.term499.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels499_503

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded499_eq503 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 499) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 503) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 499) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 503) (by decide +kernel)]
  exact scalar499_eq503 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted503_eq499 : originalWeighted 503 =
    (2 / 3 : ℚ) * originalWeighted 499 := by
  rw [originalWeighted, originalWeighted, ← guarded499_eq503,
    coefficient503, coefficient499]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels499_506 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar499_eq506 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 499).expression.scalarPointContraction X v
      (L24Gluing.term 499).decoration (L24Gluing.term 499).labels beta n insertions =
    (L24Gluing.term 506).expression.scalarPointContraction X v
      (L24Gluing.term 506).decoration (L24Gluing.term 506).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core499 L24Gluing.term499.decoration L24Gluing.term499.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels499_506

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded499_eq506 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 499) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 506) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 499) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 506) (by decide +kernel)]
  exact scalar499_eq506 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted506_eq499 : originalWeighted 506 =
    (2 / 3 : ℚ) * originalWeighted 499 := by
  rw [originalWeighted, originalWeighted, ← guarded499_eq506,
    coefficient506, coefficient499]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels500_504 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar500_eq504 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 500).expression.scalarPointContraction X v
      (L24Gluing.term 500).decoration (L24Gluing.term 500).labels beta n insertions =
    (L24Gluing.term 504).expression.scalarPointContraction X v
      (L24Gluing.term 504).decoration (L24Gluing.term 504).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core500 L24Gluing.term500.decoration L24Gluing.term500.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels500_504

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded500_eq504 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 500) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 504) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 500) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 504) (by decide +kernel)]
  exact scalar500_eq504 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted504_eq500 : originalWeighted 504 =
    (2923 / 234 : ℚ) * originalWeighted 500 := by
  rw [originalWeighted, originalWeighted, ← guarded500_eq504,
    coefficient504, coefficient500]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels500_507 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar500_eq507 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 500).expression.scalarPointContraction X v
      (L24Gluing.term 500).decoration (L24Gluing.term 500).labels beta n insertions =
    (L24Gluing.term 507).expression.scalarPointContraction X v
      (L24Gluing.term 507).decoration (L24Gluing.term 507).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core500 L24Gluing.term500.decoration L24Gluing.term500.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels500_507

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded500_eq507 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 500) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 507) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 500) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 507) (by decide +kernel)]
  exact scalar500_eq507 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted507_eq500 : originalWeighted 507 =
    (2923 / 234 : ℚ) * originalWeighted 500 := by
  rw [originalWeighted, originalWeighted, ← guarded500_eq507,
    coefficient507, coefficient500]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels501_505 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar501_eq505 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 501).expression.scalarPointContraction X v
      (L24Gluing.term 501).decoration (L24Gluing.term 501).labels beta n insertions =
    (L24Gluing.term 505).expression.scalarPointContraction X v
      (L24Gluing.term 505).decoration (L24Gluing.term 505).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core501 L24Gluing.term501.decoration L24Gluing.term501.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels501_505

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded501_eq505 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 501) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 505) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 501) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 505) (by decide +kernel)]
  exact scalar501_eq505 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted505_eq501 : originalWeighted 505 =
    (2923 / 5454 : ℚ) * originalWeighted 501 := by
  rw [originalWeighted, originalWeighted, ← guarded501_eq505,
    coefficient505, coefficient501]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels501_508 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar501_eq508 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 501).expression.scalarPointContraction X v
      (L24Gluing.term 501).decoration (L24Gluing.term 501).labels beta n insertions =
    (L24Gluing.term 508).expression.scalarPointContraction X v
      (L24Gluing.term 508).decoration (L24Gluing.term 508).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core501 L24Gluing.term501.decoration L24Gluing.term501.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels501_508

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded501_eq508 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 501) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 508) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 501) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 508) (by decide +kernel)]
  exact scalar501_eq508 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted508_eq501 : originalWeighted 508 =
    (2923 / 5454 : ℚ) * originalWeighted 501 := by
  rw [originalWeighted, originalWeighted, ← guarded501_eq508,
    coefficient508, coefficient501]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels515_519 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar515_eq519 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 515).expression.scalarPointContraction X v
      (L24Gluing.term 515).decoration (L24Gluing.term 515).labels beta n insertions =
    (L24Gluing.term 519).expression.scalarPointContraction X v
      (L24Gluing.term 519).decoration (L24Gluing.term 519).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core515 L24Gluing.term515.decoration L24Gluing.term515.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels515_519

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded515_eq519 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 515) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 519) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 515) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 519) (by decide +kernel)]
  exact scalar515_eq519 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted519_eq515 : originalWeighted 519 =
    (1 / 1 : ℚ) * originalWeighted 515 := by
  rw [originalWeighted, originalWeighted, ← guarded515_eq519,
    coefficient519, coefficient515]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels515_529 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar515_eq529 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 515).expression.scalarPointContraction X v
      (L24Gluing.term 515).decoration (L24Gluing.term 515).labels beta n insertions =
    (L24Gluing.term 529).expression.scalarPointContraction X v
      (L24Gluing.term 529).decoration (L24Gluing.term 529).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core515 L24Gluing.term515.decoration L24Gluing.term515.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels515_529

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded515_eq529 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 515) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 529) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 515) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 529) (by decide +kernel)]
  exact scalar515_eq529 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted529_eq515 : originalWeighted 529 =
    (2 / 3 : ℚ) * originalWeighted 515 := by
  rw [originalWeighted, originalWeighted, ← guarded515_eq529,
    coefficient529, coefficient515]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels516_520 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar516_eq520 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 516).expression.scalarPointContraction X v
      (L24Gluing.term 516).decoration (L24Gluing.term 516).labels beta n insertions =
    (L24Gluing.term 520).expression.scalarPointContraction X v
      (L24Gluing.term 520).decoration (L24Gluing.term 520).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core516 L24Gluing.term516.decoration L24Gluing.term516.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels516_520

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded516_eq520 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 516) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 520) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 516) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 520) (by decide +kernel)]
  exact scalar516_eq520 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted520_eq516 : originalWeighted 520 =
    (1 / 1 : ℚ) * originalWeighted 516 := by
  rw [originalWeighted, originalWeighted, ← guarded516_eq520,
    coefficient520, coefficient516]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels516_530 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar516_eq530 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 516).expression.scalarPointContraction X v
      (L24Gluing.term 516).decoration (L24Gluing.term 516).labels beta n insertions =
    (L24Gluing.term 530).expression.scalarPointContraction X v
      (L24Gluing.term 530).decoration (L24Gluing.term 530).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core516 L24Gluing.term516.decoration L24Gluing.term516.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels516_530

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded516_eq530 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 516) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 530) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 516) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 530) (by decide +kernel)]
  exact scalar516_eq530 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted530_eq516 : originalWeighted 530 =
    (2923 / 5454 : ℚ) * originalWeighted 516 := by
  rw [originalWeighted, originalWeighted, ← guarded516_eq530,
    coefficient530, coefficient516]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels517_521 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar517_eq521 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 517).expression.scalarPointContraction X v
      (L24Gluing.term 517).decoration (L24Gluing.term 517).labels beta n insertions =
    (L24Gluing.term 521).expression.scalarPointContraction X v
      (L24Gluing.term 521).decoration (L24Gluing.term 521).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core517 L24Gluing.term517.decoration L24Gluing.term517.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels517_521

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded517_eq521 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 517) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 521) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 517) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 521) (by decide +kernel)]
  exact scalar517_eq521 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted521_eq517 : originalWeighted 521 =
    (1 / 1 : ℚ) * originalWeighted 517 := by
  rw [originalWeighted, originalWeighted, ← guarded517_eq521,
    coefficient521, coefficient517]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels517_531 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar517_eq531 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 517).expression.scalarPointContraction X v
      (L24Gluing.term 517).decoration (L24Gluing.term 517).labels beta n insertions =
    (L24Gluing.term 531).expression.scalarPointContraction X v
      (L24Gluing.term 531).decoration (L24Gluing.term 531).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core517 L24Gluing.term517.decoration L24Gluing.term517.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels517_531

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded517_eq531 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 517) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 531) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 517) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 531) (by decide +kernel)]
  exact scalar517_eq531 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted531_eq517 : originalWeighted 531 =
    (2923 / 234 : ℚ) * originalWeighted 517 := by
  rw [originalWeighted, originalWeighted, ← guarded517_eq531,
    coefficient531, coefficient517]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels518_522 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar518_eq522 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 518).expression.scalarPointContraction X v
      (L24Gluing.term 518).decoration (L24Gluing.term 518).labels beta n insertions =
    (L24Gluing.term 522).expression.scalarPointContraction X v
      (L24Gluing.term 522).decoration (L24Gluing.term 522).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core518 L24Gluing.term518.decoration L24Gluing.term518.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels518_522

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded518_eq522 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 518) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 522) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 518) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 522) (by decide +kernel)]
  exact scalar518_eq522 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted522_eq518 : originalWeighted 522 =
    (1 / 1 : ℚ) * originalWeighted 518 := by
  rw [originalWeighted, originalWeighted, ← guarded518_eq522,
    coefficient522, coefficient518]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels523_532 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar523_eq532 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 523).expression.scalarPointContraction X v
      (L24Gluing.term 523).decoration (L24Gluing.term 523).labels beta n insertions =
    (L24Gluing.term 532).expression.scalarPointContraction X v
      (L24Gluing.term 532).decoration (L24Gluing.term 532).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core523 L24Gluing.term523.decoration L24Gluing.term523.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels523_532

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded523_eq532 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 523) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 532) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 523) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 532) (by decide +kernel)]
  exact scalar523_eq532 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted532_eq523 : originalWeighted 532 =
    (310 / 693 : ℚ) * originalWeighted 523 := by
  rw [originalWeighted, originalWeighted, ← guarded523_eq532,
    coefficient532, coefficient523]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels523_538 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar523_eq538 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 523).expression.scalarPointContraction X v
      (L24Gluing.term 523).decoration (L24Gluing.term 523).labels beta n insertions =
    (L24Gluing.term 538).expression.scalarPointContraction X v
      (L24Gluing.term 538).decoration (L24Gluing.term 538).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core523 L24Gluing.term523.decoration L24Gluing.term523.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels523_538

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded523_eq538 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 523) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 538) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 523) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 538) (by decide +kernel)]
  exact scalar523_eq538 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted538_eq523 : originalWeighted 538 =
    (310 / 693 : ℚ) * originalWeighted 523 := by
  rw [originalWeighted, originalWeighted, ← guarded523_eq538,
    coefficient538, coefficient523]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels524_533 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar524_eq533 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 524).expression.scalarPointContraction X v
      (L24Gluing.term 524).decoration (L24Gluing.term 524).labels beta n insertions =
    (L24Gluing.term 533).expression.scalarPointContraction X v
      (L24Gluing.term 533).decoration (L24Gluing.term 533).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core524 L24Gluing.term524.decoration L24Gluing.term524.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels524_533

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded524_eq533 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 524) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 533) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 524) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 533) (by decide +kernel)]
  exact scalar524_eq533 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted533_eq524 : originalWeighted 533 =
    (3 / 1 : ℚ) * originalWeighted 524 := by
  rw [originalWeighted, originalWeighted, ← guarded524_eq533,
    coefficient533, coefficient524]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels524_539 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar524_eq539 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 524).expression.scalarPointContraction X v
      (L24Gluing.term 524).decoration (L24Gluing.term 524).labels beta n insertions =
    (L24Gluing.term 539).expression.scalarPointContraction X v
      (L24Gluing.term 539).decoration (L24Gluing.term 539).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core524 L24Gluing.term524.decoration L24Gluing.term524.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels524_539

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded524_eq539 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 524) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 539) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 524) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 539) (by decide +kernel)]
  exact scalar524_eq539 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted539_eq524 : originalWeighted 539 =
    (3 / 1 : ℚ) * originalWeighted 524 := by
  rw [originalWeighted, originalWeighted, ← guarded524_eq539,
    coefficient539, coefficient524]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels525_534 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar525_eq534 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 525).expression.scalarPointContraction X v
      (L24Gluing.term 525).decoration (L24Gluing.term 525).labels beta n insertions =
    (L24Gluing.term 534).expression.scalarPointContraction X v
      (L24Gluing.term 534).decoration (L24Gluing.term 534).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core525 L24Gluing.term525.decoration L24Gluing.term525.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels525_534

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded525_eq534 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 525) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 534) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 525) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 534) (by decide +kernel)]
  exact scalar525_eq534 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted534_eq525 : originalWeighted 534 =
    (15 / 1 : ℚ) * originalWeighted 525 := by
  rw [originalWeighted, originalWeighted, ← guarded525_eq534,
    coefficient534, coefficient525]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels525_540 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar525_eq540 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 525).expression.scalarPointContraction X v
      (L24Gluing.term 525).decoration (L24Gluing.term 525).labels beta n insertions =
    (L24Gluing.term 540).expression.scalarPointContraction X v
      (L24Gluing.term 540).decoration (L24Gluing.term 540).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core525 L24Gluing.term525.decoration L24Gluing.term525.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels525_540

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded525_eq540 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 525) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 540) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 525) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 540) (by decide +kernel)]
  exact scalar525_eq540 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted540_eq525 : originalWeighted 540 =
    (15 / 1 : ℚ) * originalWeighted 525 := by
  rw [originalWeighted, originalWeighted, ← guarded525_eq540,
    coefficient540, coefficient525]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels526_535 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar526_eq535 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 526).expression.scalarPointContraction X v
      (L24Gluing.term 526).decoration (L24Gluing.term 526).labels beta n insertions =
    (L24Gluing.term 535).expression.scalarPointContraction X v
      (L24Gluing.term 535).decoration (L24Gluing.term 535).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core526 L24Gluing.term526.decoration L24Gluing.term526.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels526_535

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded526_eq535 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 526) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 535) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 526) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 535) (by decide +kernel)]
  exact scalar526_eq535 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted535_eq526 : originalWeighted 535 =
    (3 / 1 : ℚ) * originalWeighted 526 := by
  rw [originalWeighted, originalWeighted, ← guarded526_eq535,
    coefficient535, coefficient526]
  ring

end AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09

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

namespace AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08

open BlowupF1RootAssembly SurfaceGenusTwo GetzlerGraphs L24Gluing

private def core451 : GluingExpression 2 (Fin 4) :=
  join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))

private def core452 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core455 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))

private def core456 : GluingExpression 2 (Fin 4) :=
  join (m := 4) (n := 0) 4 0
    (join (m := 0) (n := 5) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 4) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))

private def core457 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core459 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core470 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core471 : GluingExpression 2 (Fin 4) :=
  join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 3) (n := 1) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))

private def core472 : GluingExpression 2 (Fin 4) :=
  join (m := 4) (n := 0) 4 0
    (join (m := 0) (n := 5) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 3) (n := 3) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))

private def core489 : GluingExpression 2 (Fin 4) :=
  join (m := 0) (n := 4) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 4) (by norm_num [StableArity])))

theorem coefficient451 : L24CorrectionsReplay.fullClaim 451 =
    (1106 / 5967 : ℚ) := by decide +kernel

theorem coefficient452 : L24CorrectionsReplay.fullClaim 452 =
    (-809 / 59670 : ℚ) := by decide +kernel

theorem coefficient454 : L24CorrectionsReplay.fullClaim 454 =
    (-73 / 195 : ℚ) := by decide +kernel

theorem coefficient455 : L24CorrectionsReplay.fullClaim 455 =
    (-547 / 3510 : ℚ) := by decide +kernel

theorem coefficient456 : L24CorrectionsReplay.fullClaim 456 =
    (-73 / 390 : ℚ) := by decide +kernel

theorem coefficient457 : L24CorrectionsReplay.fullClaim 457 =
    (4229 / 23868 : ℚ) := by decide +kernel

theorem coefficient458 : L24CorrectionsReplay.fullClaim 458 =
    (-343 / 2340 : ℚ) := by decide +kernel

theorem coefficient459 : L24CorrectionsReplay.fullClaim 459 =
    (-2723 / 119340 : ℚ) := by decide +kernel

theorem coefficient462 : L24CorrectionsReplay.fullClaim 462 =
    (-809 / 59670 : ℚ) := by decide +kernel

theorem coefficient464 : L24CorrectionsReplay.fullClaim 464 =
    (-73 / 195 : ℚ) := by decide +kernel

theorem coefficient465 : L24CorrectionsReplay.fullClaim 465 =
    (-547 / 3510 : ℚ) := by decide +kernel

theorem coefficient466 : L24CorrectionsReplay.fullClaim 466 =
    (-73 / 390 : ℚ) := by decide +kernel

theorem coefficient467 : L24CorrectionsReplay.fullClaim 467 =
    (4229 / 23868 : ℚ) := by decide +kernel

theorem coefficient468 : L24CorrectionsReplay.fullClaim 468 =
    (-343 / 2340 : ℚ) := by decide +kernel

theorem coefficient469 : L24CorrectionsReplay.fullClaim 469 =
    (-2723 / 119340 : ℚ) := by decide +kernel

theorem coefficient470 : L24CorrectionsReplay.fullClaim 470 =
    (-14657 / 39780 : ℚ) := by decide +kernel

theorem coefficient471 : L24CorrectionsReplay.fullClaim 471 =
    (-109 / 780 : ℚ) := by decide +kernel

theorem coefficient472 : L24CorrectionsReplay.fullClaim 472 =
    (-73 / 130 : ℚ) := by decide +kernel

theorem coefficient474 : L24CorrectionsReplay.fullClaim 474 =
    (-5054 / 89505 : ℚ) := by decide +kernel

theorem coefficient475 : L24CorrectionsReplay.fullClaim 475 =
    (-5054 / 89505 : ℚ) := by decide +kernel

theorem coefficient476 : L24CorrectionsReplay.fullClaim 476 =
    (-5054 / 89505 : ℚ) := by decide +kernel

theorem coefficient477 : L24CorrectionsReplay.fullClaim 477 =
    (-5054 / 89505 : ℚ) := by decide +kernel

theorem coefficient478 : L24CorrectionsReplay.fullClaim 478 =
    (-146 / 585 : ℚ) := by decide +kernel

theorem coefficient479 : L24CorrectionsReplay.fullClaim 479 =
    (-73 / 585 : ℚ) := by decide +kernel

theorem coefficient480 : L24CorrectionsReplay.fullClaim 480 =
    (-5054 / 89505 : ℚ) := by decide +kernel

theorem coefficient481 : L24CorrectionsReplay.fullClaim 481 =
    (-5054 / 89505 : ℚ) := by decide +kernel

theorem coefficient482 : L24CorrectionsReplay.fullClaim 482 =
    (4229 / 35802 : ℚ) := by decide +kernel

theorem coefficient483 : L24CorrectionsReplay.fullClaim 483 =
    (-13627 / 89505 : ℚ) := by decide +kernel

theorem coefficient484 : L24CorrectionsReplay.fullClaim 484 =
    (-178 / 1755 : ℚ) := by decide +kernel

theorem coefficient485 : L24CorrectionsReplay.fullClaim 485 =
    (-7 / 26 : ℚ) := by decide +kernel

theorem coefficient486 : L24CorrectionsReplay.fullClaim 486 =
    (-13627 / 89505 : ℚ) := by decide +kernel

theorem coefficient487 : L24CorrectionsReplay.fullClaim 487 =
    (-178 / 1755 : ℚ) := by decide +kernel

theorem coefficient488 : L24CorrectionsReplay.fullClaim 488 =
    (-7 / 26 : ℚ) := by decide +kernel

theorem coefficient489 : L24CorrectionsReplay.fullClaim 489 =
    (3853 / 1989 : ℚ) := by decide +kernel

theorem coefficient490 : L24CorrectionsReplay.fullClaim 490 =
    (7706 / 5967 : ℚ) := by decide +kernel

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels451_474 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation15 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar451_eq474 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 451).expression.scalarPointContraction X v
      (L24Gluing.term 451).decoration (L24Gluing.term 451).labels beta n insertions =
    (L24Gluing.term 474).expression.scalarPointContraction X v
      (L24Gluing.term 474).decoration (L24Gluing.term 474).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core451 L24Gluing.term451.decoration L24Gluing.term451.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation15 beta n insertions labels451_474

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded451_eq474 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 451) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 474) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 451) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 474) (by decide +kernel)]
  exact scalar451_eq474 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted474_eq451 : originalWeighted 474 =
    (-361 / 1185 : ℚ) * originalWeighted 451 := by
  rw [originalWeighted, originalWeighted, ← guarded451_eq474,
    coefficient474, coefficient451]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels451_476 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation16 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar451_eq476 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 451).expression.scalarPointContraction X v
      (L24Gluing.term 451).decoration (L24Gluing.term 451).labels beta n insertions =
    (L24Gluing.term 476).expression.scalarPointContraction X v
      (L24Gluing.term 476).decoration (L24Gluing.term 476).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core451 L24Gluing.term451.decoration L24Gluing.term451.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation16 beta n insertions labels451_476

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded451_eq476 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 451) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 476) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 451) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 476) (by decide +kernel)]
  exact scalar451_eq476 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted476_eq451 : originalWeighted 476 =
    (-361 / 1185 : ℚ) * originalWeighted 451 := by
  rw [originalWeighted, originalWeighted, ← guarded451_eq476,
    coefficient476, coefficient451]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels452_454 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation4 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar452_eq454 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 452).expression.scalarPointContraction X v
      (L24Gluing.term 452).decoration (L24Gluing.term 452).labels beta n insertions =
    (L24Gluing.term 454).expression.scalarPointContraction X v
      (L24Gluing.term 454).decoration (L24Gluing.term 454).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core452 L24Gluing.term452.decoration L24Gluing.term452.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation4 beta n insertions labels452_454

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded452_eq454 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 452) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 454) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 452) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 454) (by decide +kernel)]
  exact scalar452_eq454 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted454_eq452 : originalWeighted 454 =
    (22338 / 809 : ℚ) * originalWeighted 452 := by
  rw [originalWeighted, originalWeighted, ← guarded452_eq454,
    coefficient454, coefficient452]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels452_462 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation6 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar452_eq462 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 452).expression.scalarPointContraction X v
      (L24Gluing.term 452).decoration (L24Gluing.term 452).labels beta n insertions =
    (L24Gluing.term 462).expression.scalarPointContraction X v
      (L24Gluing.term 462).decoration (L24Gluing.term 462).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core452 L24Gluing.term452.decoration L24Gluing.term452.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 beta n insertions labels452_462

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded452_eq462 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 452) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 462) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 452) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 462) (by decide +kernel)]
  exact scalar452_eq462 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted462_eq452 : originalWeighted 462 =
    (1 / 1 : ℚ) * originalWeighted 452 := by
  rw [originalWeighted, originalWeighted, ← guarded452_eq462,
    coefficient462, coefficient452]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels452_464 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar452_eq464 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 452).expression.scalarPointContraction X v
      (L24Gluing.term 452).decoration (L24Gluing.term 452).labels beta n insertions =
    (L24Gluing.term 464).expression.scalarPointContraction X v
      (L24Gluing.term 464).decoration (L24Gluing.term 464).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core452 L24Gluing.term452.decoration L24Gluing.term452.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation5 beta n insertions labels452_464

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded452_eq464 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 452) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 464) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 452) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 464) (by decide +kernel)]
  exact scalar452_eq464 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted464_eq452 : originalWeighted 464 =
    (22338 / 809 : ℚ) * originalWeighted 452 := by
  rw [originalWeighted, originalWeighted, ← guarded452_eq464,
    coefficient464, coefficient452]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels452_475 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar452_eq475 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 452).expression.scalarPointContraction X v
      (L24Gluing.term 452).decoration (L24Gluing.term 452).labels beta n insertions =
    (L24Gluing.term 475).expression.scalarPointContraction X v
      (L24Gluing.term 475).decoration (L24Gluing.term 475).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core452 L24Gluing.term452.decoration L24Gluing.term452.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 beta n insertions labels452_475

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded452_eq475 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 452) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 475) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 452) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 475) (by decide +kernel)]
  exact scalar452_eq475 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted475_eq452 : originalWeighted 475 =
    (10108 / 2427 : ℚ) * originalWeighted 452 := by
  rw [originalWeighted, originalWeighted, ← guarded452_eq475,
    coefficient475, coefficient452]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels452_477 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar452_eq477 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 452).expression.scalarPointContraction X v
      (L24Gluing.term 452).decoration (L24Gluing.term 452).labels beta n insertions =
    (L24Gluing.term 477).expression.scalarPointContraction X v
      (L24Gluing.term 477).decoration (L24Gluing.term 477).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core452 L24Gluing.term452.decoration L24Gluing.term452.labels
    L24Gluing.flagPermutation10 (Equiv.refl (Fin 4)) beta n insertions labels452_477

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded452_eq477 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 452) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 477) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 452) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 477) (by decide +kernel)]
  exact scalar452_eq477 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted477_eq452 : originalWeighted 477 =
    (10108 / 2427 : ℚ) * originalWeighted 452 := by
  rw [originalWeighted, originalWeighted, ← guarded452_eq477,
    coefficient477, coefficient452]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels455_465 :
    insertions ∘ L24Gluing.flagPermutation2 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar455_eq465 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 455).expression.scalarPointContraction X v
      (L24Gluing.term 455).decoration (L24Gluing.term 455).labels beta n insertions =
    (L24Gluing.term 465).expression.scalarPointContraction X v
      (L24Gluing.term 465).decoration (L24Gluing.term 465).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core455 L24Gluing.term455.decoration L24Gluing.term455.labels
    L24Gluing.flagPermutation2 L24Gluing.flagPermutation1 beta n insertions labels455_465

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded455_eq465 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 455) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 465) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 455) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 465) (by decide +kernel)]
  exact scalar455_eq465 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted465_eq455 : originalWeighted 465 =
    (1 / 1 : ℚ) * originalWeighted 455 := by
  rw [originalWeighted, originalWeighted, ← guarded455_eq465,
    coefficient465, coefficient455]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels455_478 :
    insertions ∘ L24Gluing.flagPermutation2 =
      insertions ∘ L24Gluing.flagPermutation0 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar455_eq478 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 455).expression.scalarPointContraction X v
      (L24Gluing.term 455).decoration (L24Gluing.term 455).labels beta n insertions =
    (L24Gluing.term 478).expression.scalarPointContraction X v
      (L24Gluing.term 478).decoration (L24Gluing.term 478).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core455 L24Gluing.term455.decoration L24Gluing.term455.labels
    L24Gluing.flagPermutation2 L24Gluing.flagPermutation0 beta n insertions labels455_478

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded455_eq478 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 455) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 478) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 455) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 478) (by decide +kernel)]
  exact scalar455_eq478 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted478_eq455 : originalWeighted 478 =
    (876 / 547 : ℚ) * originalWeighted 455 := by
  rw [originalWeighted, originalWeighted, ← guarded455_eq478,
    coefficient478, coefficient455]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels456_466 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar456_eq466 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 456).expression.scalarPointContraction X v
      (L24Gluing.term 456).decoration (L24Gluing.term 456).labels beta n insertions =
    (L24Gluing.term 466).expression.scalarPointContraction X v
      (L24Gluing.term 466).decoration (L24Gluing.term 466).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core456 L24Gluing.term456.decoration L24Gluing.term456.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels456_466

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded456_eq466 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 456) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 466) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 456) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 466) (by decide +kernel)]
  exact scalar456_eq466 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted466_eq456 : originalWeighted 466 =
    (1 / 1 : ℚ) * originalWeighted 456 := by
  rw [originalWeighted, originalWeighted, ← guarded456_eq466,
    coefficient466, coefficient456]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels456_479 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar456_eq479 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 456).expression.scalarPointContraction X v
      (L24Gluing.term 456).decoration (L24Gluing.term 456).labels beta n insertions =
    (L24Gluing.term 479).expression.scalarPointContraction X v
      (L24Gluing.term 479).decoration (L24Gluing.term 479).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core456 L24Gluing.term456.decoration L24Gluing.term456.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels456_479

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded456_eq479 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 456) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 479) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 456) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 479) (by decide +kernel)]
  exact scalar456_eq479 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted479_eq456 : originalWeighted 479 =
    (2 / 3 : ℚ) * originalWeighted 456 := by
  rw [originalWeighted, originalWeighted, ← guarded456_eq479,
    coefficient479, coefficient456]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels457_458 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation4 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar457_eq458 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 457).expression.scalarPointContraction X v
      (L24Gluing.term 457).decoration (L24Gluing.term 457).labels beta n insertions =
    (L24Gluing.term 458).expression.scalarPointContraction X v
      (L24Gluing.term 458).decoration (L24Gluing.term 458).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core457 L24Gluing.term457.decoration L24Gluing.term457.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation4 beta n insertions labels457_458

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded457_eq458 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 457) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 458) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 457) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 458) (by decide +kernel)]
  exact scalar457_eq458 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted458_eq457 : originalWeighted 458 =
    (-17493 / 21145 : ℚ) * originalWeighted 457 := by
  rw [originalWeighted, originalWeighted, ← guarded457_eq458,
    coefficient458, coefficient457]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels457_467 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation6 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar457_eq467 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 457).expression.scalarPointContraction X v
      (L24Gluing.term 457).decoration (L24Gluing.term 457).labels beta n insertions =
    (L24Gluing.term 467).expression.scalarPointContraction X v
      (L24Gluing.term 467).decoration (L24Gluing.term 467).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core457 L24Gluing.term457.decoration L24Gluing.term457.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation6 beta n insertions labels457_467

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded457_eq467 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 457) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 467) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 457) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 467) (by decide +kernel)]
  exact scalar457_eq467 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted467_eq457 : originalWeighted 467 =
    (1 / 1 : ℚ) * originalWeighted 457 := by
  rw [originalWeighted, originalWeighted, ← guarded457_eq467,
    coefficient467, coefficient457]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels457_468 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar457_eq468 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 457).expression.scalarPointContraction X v
      (L24Gluing.term 457).decoration (L24Gluing.term 457).labels beta n insertions =
    (L24Gluing.term 468).expression.scalarPointContraction X v
      (L24Gluing.term 468).decoration (L24Gluing.term 468).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core457 L24Gluing.term457.decoration L24Gluing.term457.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation5 beta n insertions labels457_468

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded457_eq468 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 457) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 468) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 457) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 468) (by decide +kernel)]
  exact scalar457_eq468 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted468_eq457 : originalWeighted 468 =
    (-17493 / 21145 : ℚ) * originalWeighted 457 := by
  rw [originalWeighted, originalWeighted, ← guarded457_eq468,
    coefficient468, coefficient457]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels457_480 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar457_eq480 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 457).expression.scalarPointContraction X v
      (L24Gluing.term 457).decoration (L24Gluing.term 457).labels beta n insertions =
    (L24Gluing.term 480).expression.scalarPointContraction X v
      (L24Gluing.term 480).decoration (L24Gluing.term 480).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core457 L24Gluing.term457.decoration L24Gluing.term457.labels
    L24Gluing.flagPermutation10 L24Gluing.flagPermutation7 beta n insertions labels457_480

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded457_eq480 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 457) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 480) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 457) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 480) (by decide +kernel)]
  exact scalar457_eq480 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted480_eq457 : originalWeighted 480 =
    (-20216 / 63435 : ℚ) * originalWeighted 457 := by
  rw [originalWeighted, originalWeighted, ← guarded457_eq480,
    coefficient480, coefficient457]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels457_481 :
    insertions ∘ L24Gluing.flagPermutation10 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar457_eq481 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 457).expression.scalarPointContraction X v
      (L24Gluing.term 457).decoration (L24Gluing.term 457).labels beta n insertions =
    (L24Gluing.term 481).expression.scalarPointContraction X v
      (L24Gluing.term 481).decoration (L24Gluing.term 481).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core457 L24Gluing.term457.decoration L24Gluing.term457.labels
    L24Gluing.flagPermutation10 (Equiv.refl (Fin 4)) beta n insertions labels457_481

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded457_eq481 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 457) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 481) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 457) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 481) (by decide +kernel)]
  exact scalar457_eq481 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted481_eq457 : originalWeighted 481 =
    (-20216 / 63435 : ℚ) * originalWeighted 457 := by
  rw [originalWeighted, originalWeighted, ← guarded457_eq481,
    coefficient481, coefficient457]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels459_469 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation14 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar459_eq469 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 459).expression.scalarPointContraction X v
      (L24Gluing.term 459).decoration (L24Gluing.term 459).labels beta n insertions =
    (L24Gluing.term 469).expression.scalarPointContraction X v
      (L24Gluing.term 469).decoration (L24Gluing.term 469).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core459 L24Gluing.term459.decoration L24Gluing.term459.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation14 beta n insertions labels459_469

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded459_eq469 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 459) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 469) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 459) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 469) (by decide +kernel)]
  exact scalar459_eq469 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted469_eq459 : originalWeighted 469 =
    (1 / 1 : ℚ) * originalWeighted 459 := by
  rw [originalWeighted, originalWeighted, ← guarded459_eq469,
    coefficient469, coefficient459]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels459_482 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation15 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar459_eq482 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 459).expression.scalarPointContraction X v
      (L24Gluing.term 459).decoration (L24Gluing.term 459).labels beta n insertions =
    (L24Gluing.term 482).expression.scalarPointContraction X v
      (L24Gluing.term 482).decoration (L24Gluing.term 482).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core459 L24Gluing.term459.decoration L24Gluing.term459.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation15 beta n insertions labels459_482

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded459_eq482 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 459) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 482) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 459) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 482) (by decide +kernel)]
  exact scalar459_eq482 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted482_eq459 : originalWeighted 482 =
    (-42290 / 8169 : ℚ) * originalWeighted 459 := by
  rw [originalWeighted, originalWeighted, ← guarded459_eq482,
    coefficient482, coefficient459]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels470_483 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar470_eq483 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 470).expression.scalarPointContraction X v
      (L24Gluing.term 470).decoration (L24Gluing.term 470).labels beta n insertions =
    (L24Gluing.term 483).expression.scalarPointContraction X v
      (L24Gluing.term 483).decoration (L24Gluing.term 483).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core470 L24Gluing.term470.decoration L24Gluing.term470.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels470_483

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded470_eq483 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 470) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 483) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 470) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 483) (by decide +kernel)]
  exact scalar470_eq483 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted483_eq470 : originalWeighted 483 =
    (54508 / 131913 : ℚ) * originalWeighted 470 := by
  rw [originalWeighted, originalWeighted, ← guarded470_eq483,
    coefficient483, coefficient470]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels470_486 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar470_eq486 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 470).expression.scalarPointContraction X v
      (L24Gluing.term 470).decoration (L24Gluing.term 470).labels beta n insertions =
    (L24Gluing.term 486).expression.scalarPointContraction X v
      (L24Gluing.term 486).decoration (L24Gluing.term 486).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core470 L24Gluing.term470.decoration L24Gluing.term470.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels470_486

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded470_eq486 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 470) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 486) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 470) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 486) (by decide +kernel)]
  exact scalar470_eq486 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted486_eq470 : originalWeighted 486 =
    (54508 / 131913 : ℚ) * originalWeighted 470 := by
  rw [originalWeighted, originalWeighted, ← guarded470_eq486,
    coefficient486, coefficient470]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels471_484 :
    insertions ∘ L24Gluing.flagPermutation17 =
      insertions ∘ L24Gluing.flagPermutation16 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar471_eq484 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 471).expression.scalarPointContraction X v
      (L24Gluing.term 471).decoration (L24Gluing.term 471).labels beta n insertions =
    (L24Gluing.term 484).expression.scalarPointContraction X v
      (L24Gluing.term 484).decoration (L24Gluing.term 484).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core471 L24Gluing.term471.decoration L24Gluing.term471.labels
    L24Gluing.flagPermutation17 L24Gluing.flagPermutation16 beta n insertions labels471_484

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded471_eq484 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 471) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 484) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 471) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 484) (by decide +kernel)]
  exact scalar471_eq484 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted484_eq471 : originalWeighted 484 =
    (712 / 981 : ℚ) * originalWeighted 471 := by
  rw [originalWeighted, originalWeighted, ← guarded471_eq484,
    coefficient484, coefficient471]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels471_487 :
    insertions ∘ L24Gluing.flagPermutation17 =
      insertions ∘ L24Gluing.flagPermutation15 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar471_eq487 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 471).expression.scalarPointContraction X v
      (L24Gluing.term 471).decoration (L24Gluing.term 471).labels beta n insertions =
    (L24Gluing.term 487).expression.scalarPointContraction X v
      (L24Gluing.term 487).decoration (L24Gluing.term 487).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core471 L24Gluing.term471.decoration L24Gluing.term471.labels
    L24Gluing.flagPermutation17 L24Gluing.flagPermutation15 beta n insertions labels471_487

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded471_eq487 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 471) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 487) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 471) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 487) (by decide +kernel)]
  exact scalar471_eq487 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted487_eq471 : originalWeighted 487 =
    (712 / 981 : ℚ) * originalWeighted 471 := by
  rw [originalWeighted, originalWeighted, ← guarded471_eq487,
    coefficient487, coefficient471]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels472_485 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar472_eq485 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 472).expression.scalarPointContraction X v
      (L24Gluing.term 472).decoration (L24Gluing.term 472).labels beta n insertions =
    (L24Gluing.term 485).expression.scalarPointContraction X v
      (L24Gluing.term 485).decoration (L24Gluing.term 485).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core472 L24Gluing.term472.decoration L24Gluing.term472.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels472_485

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded472_eq485 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 472) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 485) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 472) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 485) (by decide +kernel)]
  exact scalar472_eq485 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted485_eq472 : originalWeighted 485 =
    (35 / 73 : ℚ) * originalWeighted 472 := by
  rw [originalWeighted, originalWeighted, ← guarded472_eq485,
    coefficient485, coefficient472]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels472_488 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar472_eq488 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 472).expression.scalarPointContraction X v
      (L24Gluing.term 472).decoration (L24Gluing.term 472).labels beta n insertions =
    (L24Gluing.term 488).expression.scalarPointContraction X v
      (L24Gluing.term 488).decoration (L24Gluing.term 488).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core472 L24Gluing.term472.decoration L24Gluing.term472.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels472_488

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded472_eq488 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 472) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 488) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 472) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 488) (by decide +kernel)]
  exact scalar472_eq488 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted488_eq472 : originalWeighted 488 =
    (35 / 73 : ℚ) * originalWeighted 472 := by
  rw [originalWeighted, originalWeighted, ← guarded472_eq488,
    coefficient488, coefficient472]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels489_490 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar489_eq490 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 489).expression.scalarPointContraction X v
      (L24Gluing.term 489).decoration (L24Gluing.term 489).labels beta n insertions =
    (L24Gluing.term 490).expression.scalarPointContraction X v
      (L24Gluing.term 490).decoration (L24Gluing.term 490).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core489 L24Gluing.term489.decoration L24Gluing.term489.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels489_490

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded489_eq490 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 489) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 490) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 489) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 490) (by decide +kernel)]
  exact scalar489_eq490 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted490_eq489 : originalWeighted 490 =
    (2 / 3 : ℚ) * originalWeighted 489 := by
  rw [originalWeighted, originalWeighted, ← guarded489_eq490,
    coefficient490, coefficient489]
  ring

end AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08

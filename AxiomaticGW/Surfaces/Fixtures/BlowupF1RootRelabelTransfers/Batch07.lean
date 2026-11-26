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

namespace AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07

open BlowupF1RootAssembly SurfaceGenusTwo GetzlerGraphs L24Gluing

private def core417 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core418 : GluingExpression 2 (Fin 4) :=
  join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

private def core419 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core420 : GluingExpression 2 (Fin 4) :=
  join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity])))

private def core421 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 0) (n := 4) 0 3
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 3) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core422 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))

private def core423 : GluingExpression 2 (Fin 4) :=
  join (m := 4) (n := 0) 4 0
    (join (m := 0) (n := 5) 0 4
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 4) 2 2
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))

private def core424 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core425 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 2) (n := 2) 2 1
    (join (m := 2) (n := 1) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity])))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core426 : GluingExpression 2 (Fin 4) :=
  join (m := 3) (n := 1) 3 1
    (join (m := 1) (n := 3) 1 2
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]))

private def core450 : GluingExpression 2 (Fin 4) :=
  join (m := 2) (n := 2) 2 2
    (join (m := 0) (n := 3) 0 2
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (join (m := 2) (n := 2) 2 0
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]))

private def core451 : GluingExpression 2 (Fin 4) :=
  join (m := 1) (n := 3) 1 3
    (join (m := 0) (n := 2) 0 1
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (join (m := 2) (n := 2) 2 1
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) ))

theorem coefficient417 : L24CorrectionsReplay.fullClaim 417 =
    (-1199 / 59670 : ℚ) := by decide +kernel

theorem coefficient418 : L24CorrectionsReplay.fullClaim 418 =
    (-8909 / 59670 : ℚ) := by decide +kernel

theorem coefficient419 : L24CorrectionsReplay.fullClaim 419 =
    (-73 / 195 : ℚ) := by decide +kernel

theorem coefficient420 : L24CorrectionsReplay.fullClaim 420 =
    (1106 / 5967 : ℚ) := by decide +kernel

theorem coefficient421 : L24CorrectionsReplay.fullClaim 421 =
    (-809 / 59670 : ℚ) := by decide +kernel

theorem coefficient422 : L24CorrectionsReplay.fullClaim 422 =
    (-547 / 3510 : ℚ) := by decide +kernel

theorem coefficient423 : L24CorrectionsReplay.fullClaim 423 =
    (-73 / 390 : ℚ) := by decide +kernel

theorem coefficient424 : L24CorrectionsReplay.fullClaim 424 =
    (-343 / 2340 : ℚ) := by decide +kernel

theorem coefficient425 : L24CorrectionsReplay.fullClaim 425 =
    (4229 / 23868 : ℚ) := by decide +kernel

theorem coefficient426 : L24CorrectionsReplay.fullClaim 426 =
    (-2723 / 119340 : ℚ) := by decide +kernel

theorem coefficient427 : L24CorrectionsReplay.fullClaim 427 =
    (2212 / 17901 : ℚ) := by decide +kernel

theorem coefficient428 : L24CorrectionsReplay.fullClaim 428 =
    (-5054 / 89505 : ℚ) := by decide +kernel

theorem coefficient429 : L24CorrectionsReplay.fullClaim 429 =
    (-5054 / 89505 : ℚ) := by decide +kernel

theorem coefficient430 : L24CorrectionsReplay.fullClaim 430 =
    (-5054 / 89505 : ℚ) := by decide +kernel

theorem coefficient431 : L24CorrectionsReplay.fullClaim 431 =
    (-5054 / 89505 : ℚ) := by decide +kernel

theorem coefficient432 : L24CorrectionsReplay.fullClaim 432 =
    (-146 / 585 : ℚ) := by decide +kernel

theorem coefficient433 : L24CorrectionsReplay.fullClaim 433 =
    (-73 / 585 : ℚ) := by decide +kernel

theorem coefficient434 : L24CorrectionsReplay.fullClaim 434 =
    (-5054 / 89505 : ℚ) := by decide +kernel

theorem coefficient435 : L24CorrectionsReplay.fullClaim 435 =
    (-5054 / 89505 : ℚ) := by decide +kernel

theorem coefficient436 : L24CorrectionsReplay.fullClaim 436 =
    (4229 / 35802 : ℚ) := by decide +kernel

theorem coefficient437 : L24CorrectionsReplay.fullClaim 437 =
    (2212 / 17901 : ℚ) := by decide +kernel

theorem coefficient438 : L24CorrectionsReplay.fullClaim 438 =
    (-5054 / 89505 : ℚ) := by decide +kernel

theorem coefficient439 : L24CorrectionsReplay.fullClaim 439 =
    (-5054 / 89505 : ℚ) := by decide +kernel

theorem coefficient440 : L24CorrectionsReplay.fullClaim 440 =
    (-5054 / 89505 : ℚ) := by decide +kernel

theorem coefficient441 : L24CorrectionsReplay.fullClaim 441 =
    (-5054 / 89505 : ℚ) := by decide +kernel

theorem coefficient442 : L24CorrectionsReplay.fullClaim 442 =
    (-146 / 585 : ℚ) := by decide +kernel

theorem coefficient443 : L24CorrectionsReplay.fullClaim 443 =
    (-73 / 585 : ℚ) := by decide +kernel

theorem coefficient444 : L24CorrectionsReplay.fullClaim 444 =
    (-5054 / 89505 : ℚ) := by decide +kernel

theorem coefficient445 : L24CorrectionsReplay.fullClaim 445 =
    (-5054 / 89505 : ℚ) := by decide +kernel

theorem coefficient446 : L24CorrectionsReplay.fullClaim 446 =
    (4229 / 35802 : ℚ) := by decide +kernel

theorem coefficient450 : L24CorrectionsReplay.fullClaim 450 =
    (-1199 / 59670 : ℚ) := by decide +kernel

theorem coefficient451 : L24CorrectionsReplay.fullClaim 451 =
    (1106 / 5967 : ℚ) := by decide +kernel

theorem coefficient453 : L24CorrectionsReplay.fullClaim 453 =
    (-8909 / 59670 : ℚ) := by decide +kernel

theorem coefficient460 : L24CorrectionsReplay.fullClaim 460 =
    (-1199 / 59670 : ℚ) := by decide +kernel

theorem coefficient461 : L24CorrectionsReplay.fullClaim 461 =
    (1106 / 5967 : ℚ) := by decide +kernel

theorem coefficient463 : L24CorrectionsReplay.fullClaim 463 =
    (-8909 / 59670 : ℚ) := by decide +kernel

theorem coefficient473 : L24CorrectionsReplay.fullClaim 473 =
    (2212 / 17901 : ℚ) := by decide +kernel

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels417_427 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar417_eq427 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 417).expression.scalarPointContraction X v
      (L24Gluing.term 417).decoration (L24Gluing.term 417).labels beta n insertions =
    (L24Gluing.term 427).expression.scalarPointContraction X v
      (L24Gluing.term 427).decoration (L24Gluing.term 427).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core417 L24Gluing.term417.decoration L24Gluing.term417.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels417_427

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded417_eq427 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 417) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 427) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 417) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 427) (by decide +kernel)]
  exact scalar417_eq427 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted427_eq417 : originalWeighted 427 =
    (-22120 / 3597 : ℚ) * originalWeighted 417 := by
  rw [originalWeighted, originalWeighted, ← guarded417_eq427,
    coefficient427, coefficient417]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels417_437 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar417_eq437 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 417).expression.scalarPointContraction X v
      (L24Gluing.term 417).decoration (L24Gluing.term 417).labels beta n insertions =
    (L24Gluing.term 437).expression.scalarPointContraction X v
      (L24Gluing.term 437).decoration (L24Gluing.term 437).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core417 L24Gluing.term417.decoration L24Gluing.term417.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels417_437

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded417_eq437 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 417) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 437) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 417) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 437) (by decide +kernel)]
  exact scalar417_eq437 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted437_eq417 : originalWeighted 437 =
    (-22120 / 3597 : ℚ) * originalWeighted 417 := by
  rw [originalWeighted, originalWeighted, ← guarded417_eq437,
    coefficient437, coefficient417]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels418_428 :
    insertions ∘ L24Gluing.flagPermutation3 =
      insertions ∘ L24Gluing.flagPermutation11 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar418_eq428 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 418).expression.scalarPointContraction X v
      (L24Gluing.term 418).decoration (L24Gluing.term 418).labels beta n insertions =
    (L24Gluing.term 428).expression.scalarPointContraction X v
      (L24Gluing.term 428).decoration (L24Gluing.term 428).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core418 L24Gluing.term418.decoration L24Gluing.term418.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation11 beta n insertions labels418_428

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded418_eq428 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 418) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 428) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 418) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 428) (by decide +kernel)]
  exact scalar418_eq428 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted428_eq418 : originalWeighted 428 =
    (10108 / 26727 : ℚ) * originalWeighted 418 := by
  rw [originalWeighted, originalWeighted, ← guarded418_eq428,
    coefficient428, coefficient418]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels418_438 :
    insertions ∘ L24Gluing.flagPermutation3 =
      insertions ∘ L24Gluing.flagPermutation12 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar418_eq438 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 418).expression.scalarPointContraction X v
      (L24Gluing.term 418).decoration (L24Gluing.term 418).labels beta n insertions =
    (L24Gluing.term 438).expression.scalarPointContraction X v
      (L24Gluing.term 438).decoration (L24Gluing.term 438).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core418 L24Gluing.term418.decoration L24Gluing.term418.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation12 beta n insertions labels418_438

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded418_eq438 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 418) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 438) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 418) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 438) (by decide +kernel)]
  exact scalar418_eq438 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted438_eq418 : originalWeighted 438 =
    (10108 / 26727 : ℚ) * originalWeighted 418 := by
  rw [originalWeighted, originalWeighted, ← guarded418_eq438,
    coefficient438, coefficient418]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels419_429 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation9 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar419_eq429 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 419).expression.scalarPointContraction X v
      (L24Gluing.term 419).decoration (L24Gluing.term 419).labels beta n insertions =
    (L24Gluing.term 429).expression.scalarPointContraction X v
      (L24Gluing.term 429).decoration (L24Gluing.term 429).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core419 L24Gluing.term419.decoration L24Gluing.term419.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 beta n insertions labels419_429

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded419_eq429 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 419) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 429) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 419) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 429) (by decide +kernel)]
  exact scalar419_eq429 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted429_eq419 : originalWeighted 429 =
    (5054 / 33507 : ℚ) * originalWeighted 419 := by
  rw [originalWeighted, originalWeighted, ← guarded419_eq429,
    coefficient429, coefficient419]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels419_439 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation3 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar419_eq439 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 419).expression.scalarPointContraction X v
      (L24Gluing.term 419).decoration (L24Gluing.term 419).labels beta n insertions =
    (L24Gluing.term 439).expression.scalarPointContraction X v
      (L24Gluing.term 439).decoration (L24Gluing.term 439).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core419 L24Gluing.term419.decoration L24Gluing.term419.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 beta n insertions labels419_439

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded419_eq439 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 419) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 439) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 419) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 439) (by decide +kernel)]
  exact scalar419_eq439 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted439_eq419 : originalWeighted 439 =
    (5054 / 33507 : ℚ) * originalWeighted 419 := by
  rw [originalWeighted, originalWeighted, ← guarded419_eq439,
    coefficient439, coefficient419]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels420_430 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar420_eq430 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 420).expression.scalarPointContraction X v
      (L24Gluing.term 420).decoration (L24Gluing.term 420).labels beta n insertions =
    (L24Gluing.term 430).expression.scalarPointContraction X v
      (L24Gluing.term 430).decoration (L24Gluing.term 430).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core420 L24Gluing.term420.decoration L24Gluing.term420.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels420_430

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded420_eq430 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 420) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 430) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 420) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 430) (by decide +kernel)]
  exact scalar420_eq430 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted430_eq420 : originalWeighted 430 =
    (-361 / 1185 : ℚ) * originalWeighted 420 := by
  rw [originalWeighted, originalWeighted, ← guarded420_eq430,
    coefficient430, coefficient420]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels420_440 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar420_eq440 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 420).expression.scalarPointContraction X v
      (L24Gluing.term 420).decoration (L24Gluing.term 420).labels beta n insertions =
    (L24Gluing.term 440).expression.scalarPointContraction X v
      (L24Gluing.term 440).decoration (L24Gluing.term 440).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core420 L24Gluing.term420.decoration L24Gluing.term420.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels420_440

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded420_eq440 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 420) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 440) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 420) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 440) (by decide +kernel)]
  exact scalar420_eq440 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted440_eq420 : originalWeighted 440 =
    (-361 / 1185 : ℚ) * originalWeighted 420 := by
  rw [originalWeighted, originalWeighted, ← guarded420_eq440,
    coefficient440, coefficient420]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels421_431 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar421_eq431 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 421).expression.scalarPointContraction X v
      (L24Gluing.term 421).decoration (L24Gluing.term 421).labels beta n insertions =
    (L24Gluing.term 431).expression.scalarPointContraction X v
      (L24Gluing.term 431).decoration (L24Gluing.term 431).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core421 L24Gluing.term421.decoration L24Gluing.term421.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels421_431

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded421_eq431 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 421) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 431) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 421) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 431) (by decide +kernel)]
  exact scalar421_eq431 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted431_eq421 : originalWeighted 431 =
    (10108 / 2427 : ℚ) * originalWeighted 421 := by
  rw [originalWeighted, originalWeighted, ← guarded421_eq431,
    coefficient431, coefficient421]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels421_441 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar421_eq441 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 421).expression.scalarPointContraction X v
      (L24Gluing.term 421).decoration (L24Gluing.term 421).labels beta n insertions =
    (L24Gluing.term 441).expression.scalarPointContraction X v
      (L24Gluing.term 441).decoration (L24Gluing.term 441).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core421 L24Gluing.term421.decoration L24Gluing.term421.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels421_441

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded421_eq441 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 421) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 441) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 421) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 441) (by decide +kernel)]
  exact scalar421_eq441 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted441_eq421 : originalWeighted 441 =
    (10108 / 2427 : ℚ) * originalWeighted 421 := by
  rw [originalWeighted, originalWeighted, ← guarded421_eq441,
    coefficient441, coefficient421]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels422_432 :
    insertions ∘ (Equiv.refl (Fin 4)) =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar422_eq432 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 422).expression.scalarPointContraction X v
      (L24Gluing.term 422).decoration (L24Gluing.term 422).labels beta n insertions =
    (L24Gluing.term 432).expression.scalarPointContraction X v
      (L24Gluing.term 432).decoration (L24Gluing.term 432).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core422 L24Gluing.term422.decoration L24Gluing.term422.labels
    (Equiv.refl (Fin 4)) L24Gluing.flagPermutation5 beta n insertions labels422_432

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded422_eq432 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 422) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 432) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 422) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 432) (by decide +kernel)]
  exact scalar422_eq432 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted432_eq422 : originalWeighted 432 =
    (876 / 547 : ℚ) * originalWeighted 422 := by
  rw [originalWeighted, originalWeighted, ← guarded422_eq432,
    coefficient432, coefficient422]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels422_442 :
    insertions ∘ (Equiv.refl (Fin 4)) =
      insertions ∘ L24Gluing.flagPermutation4 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar422_eq442 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 422).expression.scalarPointContraction X v
      (L24Gluing.term 422).decoration (L24Gluing.term 422).labels beta n insertions =
    (L24Gluing.term 442).expression.scalarPointContraction X v
      (L24Gluing.term 442).decoration (L24Gluing.term 442).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core422 L24Gluing.term422.decoration L24Gluing.term422.labels
    (Equiv.refl (Fin 4)) L24Gluing.flagPermutation4 beta n insertions labels422_442

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded422_eq442 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 422) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 442) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 422) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 442) (by decide +kernel)]
  exact scalar422_eq442 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted442_eq422 : originalWeighted 442 =
    (876 / 547 : ℚ) * originalWeighted 422 := by
  rw [originalWeighted, originalWeighted, ← guarded422_eq442,
    coefficient442, coefficient422]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels423_433 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar423_eq433 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 423).expression.scalarPointContraction X v
      (L24Gluing.term 423).decoration (L24Gluing.term 423).labels beta n insertions =
    (L24Gluing.term 433).expression.scalarPointContraction X v
      (L24Gluing.term 433).decoration (L24Gluing.term 433).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core423 L24Gluing.term423.decoration L24Gluing.term423.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels423_433

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded423_eq433 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 423) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 433) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 423) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 433) (by decide +kernel)]
  exact scalar423_eq433 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted433_eq423 : originalWeighted 433 =
    (2 / 3 : ℚ) * originalWeighted 423 := by
  rw [originalWeighted, originalWeighted, ← guarded423_eq433,
    coefficient433, coefficient423]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels423_443 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar423_eq443 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 423).expression.scalarPointContraction X v
      (L24Gluing.term 423).decoration (L24Gluing.term 423).labels beta n insertions =
    (L24Gluing.term 443).expression.scalarPointContraction X v
      (L24Gluing.term 443).decoration (L24Gluing.term 443).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core423 L24Gluing.term423.decoration L24Gluing.term423.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels423_443

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded423_eq443 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 423) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 443) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 423) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 443) (by decide +kernel)]
  exact scalar423_eq443 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted443_eq423 : originalWeighted 443 =
    (2 / 3 : ℚ) * originalWeighted 423 := by
  rw [originalWeighted, originalWeighted, ← guarded423_eq443,
    coefficient443, coefficient423]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels424_434 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation9 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar424_eq434 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 424).expression.scalarPointContraction X v
      (L24Gluing.term 424).decoration (L24Gluing.term 424).labels beta n insertions =
    (L24Gluing.term 434).expression.scalarPointContraction X v
      (L24Gluing.term 434).decoration (L24Gluing.term 434).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core424 L24Gluing.term424.decoration L24Gluing.term424.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation9 beta n insertions labels424_434

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded424_eq434 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 424) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 434) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 424) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 434) (by decide +kernel)]
  exact scalar424_eq434 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted434_eq424 : originalWeighted 434 =
    (2888 / 7497 : ℚ) * originalWeighted 424 := by
  rw [originalWeighted, originalWeighted, ← guarded424_eq434,
    coefficient434, coefficient424]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels424_444 :
    insertions ∘ L24Gluing.flagPermutation8 =
      insertions ∘ L24Gluing.flagPermutation3 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar424_eq444 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 424).expression.scalarPointContraction X v
      (L24Gluing.term 424).decoration (L24Gluing.term 424).labels beta n insertions =
    (L24Gluing.term 444).expression.scalarPointContraction X v
      (L24Gluing.term 444).decoration (L24Gluing.term 444).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core424 L24Gluing.term424.decoration L24Gluing.term424.labels
    L24Gluing.flagPermutation8 L24Gluing.flagPermutation3 beta n insertions labels424_444

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded424_eq444 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 424) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 444) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 424) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 444) (by decide +kernel)]
  exact scalar424_eq444 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted444_eq424 : originalWeighted 444 =
    (2888 / 7497 : ℚ) * originalWeighted 424 := by
  rw [originalWeighted, originalWeighted, ← guarded424_eq444,
    coefficient444, coefficient424]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels425_435 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar425_eq435 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 425).expression.scalarPointContraction X v
      (L24Gluing.term 425).decoration (L24Gluing.term 425).labels beta n insertions =
    (L24Gluing.term 435).expression.scalarPointContraction X v
      (L24Gluing.term 435).decoration (L24Gluing.term 435).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core425 L24Gluing.term425.decoration L24Gluing.term425.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels425_435

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded425_eq435 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 425) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 435) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 425) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 435) (by decide +kernel)]
  exact scalar425_eq435 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted435_eq425 : originalWeighted 435 =
    (-20216 / 63435 : ℚ) * originalWeighted 425 := by
  rw [originalWeighted, originalWeighted, ← guarded425_eq435,
    coefficient435, coefficient425]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels425_445 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar425_eq445 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 425).expression.scalarPointContraction X v
      (L24Gluing.term 425).decoration (L24Gluing.term 425).labels beta n insertions =
    (L24Gluing.term 445).expression.scalarPointContraction X v
      (L24Gluing.term 445).decoration (L24Gluing.term 445).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core425 L24Gluing.term425.decoration L24Gluing.term425.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels425_445

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded425_eq445 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 425) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 445) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 425) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 445) (by decide +kernel)]
  exact scalar425_eq445 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted445_eq425 : originalWeighted 445 =
    (-20216 / 63435 : ℚ) * originalWeighted 425 := by
  rw [originalWeighted, originalWeighted, ← guarded425_eq445,
    coefficient445, coefficient425]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels426_436 :
    insertions ∘ L24Gluing.flagPermutation3 =
      insertions ∘ L24Gluing.flagPermutation11 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar426_eq436 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 426).expression.scalarPointContraction X v
      (L24Gluing.term 426).decoration (L24Gluing.term 426).labels beta n insertions =
    (L24Gluing.term 436).expression.scalarPointContraction X v
      (L24Gluing.term 436).decoration (L24Gluing.term 436).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core426 L24Gluing.term426.decoration L24Gluing.term426.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation11 beta n insertions labels426_436

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded426_eq436 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 426) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 436) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 426) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 436) (by decide +kernel)]
  exact scalar426_eq436 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted436_eq426 : originalWeighted 436 =
    (-42290 / 8169 : ℚ) * originalWeighted 426 := by
  rw [originalWeighted, originalWeighted, ← guarded426_eq436,
    coefficient436, coefficient426]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels426_446 :
    insertions ∘ L24Gluing.flagPermutation3 =
      insertions ∘ L24Gluing.flagPermutation12 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar426_eq446 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 426).expression.scalarPointContraction X v
      (L24Gluing.term 426).decoration (L24Gluing.term 426).labels beta n insertions =
    (L24Gluing.term 446).expression.scalarPointContraction X v
      (L24Gluing.term 446).decoration (L24Gluing.term 446).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core426 L24Gluing.term426.decoration L24Gluing.term426.labels
    L24Gluing.flagPermutation3 L24Gluing.flagPermutation12 beta n insertions labels426_446

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded426_eq446 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 426) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 446) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 426) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 446) (by decide +kernel)]
  exact scalar426_eq446 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted446_eq426 : originalWeighted 446 =
    (-42290 / 8169 : ℚ) * originalWeighted 426 := by
  rw [originalWeighted, originalWeighted, ← guarded426_eq446,
    coefficient446, coefficient426]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels450_460 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar450_eq460 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 450).expression.scalarPointContraction X v
      (L24Gluing.term 450).decoration (L24Gluing.term 450).labels beta n insertions =
    (L24Gluing.term 460).expression.scalarPointContraction X v
      (L24Gluing.term 460).decoration (L24Gluing.term 460).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core450 L24Gluing.term450.decoration L24Gluing.term450.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels450_460

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded450_eq460 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 450) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 460) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 450) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 460) (by decide +kernel)]
  exact scalar450_eq460 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted460_eq450 : originalWeighted 460 =
    (1 / 1 : ℚ) * originalWeighted 450 := by
  rw [originalWeighted, originalWeighted, ← guarded450_eq460,
    coefficient460, coefficient450]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels450_473 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar450_eq473 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 450).expression.scalarPointContraction X v
      (L24Gluing.term 450).decoration (L24Gluing.term 450).labels beta n insertions =
    (L24Gluing.term 473).expression.scalarPointContraction X v
      (L24Gluing.term 473).decoration (L24Gluing.term 473).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core450 L24Gluing.term450.decoration L24Gluing.term450.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels450_473

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded450_eq473 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 450) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 473) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 450) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 473) (by decide +kernel)]
  exact scalar450_eq473 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted473_eq450 : originalWeighted 473 =
    (-22120 / 3597 : ℚ) * originalWeighted 450 := by
  rw [originalWeighted, originalWeighted, ← guarded450_eq473,
    coefficient473, coefficient450]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels451_453 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation21 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar451_eq453 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 451).expression.scalarPointContraction X v
      (L24Gluing.term 451).decoration (L24Gluing.term 451).labels beta n insertions =
    (L24Gluing.term 453).expression.scalarPointContraction X v
      (L24Gluing.term 453).decoration (L24Gluing.term 453).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core451 L24Gluing.term451.decoration L24Gluing.term451.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation21 beta n insertions labels451_453

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded451_eq453 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 451) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 453) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 451) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 453) (by decide +kernel)]
  exact scalar451_eq453 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted453_eq451 : originalWeighted 453 =
    (-8909 / 11060 : ℚ) * originalWeighted 451 := by
  rw [originalWeighted, originalWeighted, ← guarded451_eq453,
    coefficient453, coefficient451]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels451_461 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation14 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar451_eq461 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 451).expression.scalarPointContraction X v
      (L24Gluing.term 451).decoration (L24Gluing.term 451).labels beta n insertions =
    (L24Gluing.term 461).expression.scalarPointContraction X v
      (L24Gluing.term 461).decoration (L24Gluing.term 461).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core451 L24Gluing.term451.decoration L24Gluing.term451.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation14 beta n insertions labels451_461

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded451_eq461 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 451) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 461) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 451) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 461) (by decide +kernel)]
  exact scalar451_eq461 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted461_eq451 : originalWeighted 461 =
    (1 / 1 : ℚ) * originalWeighted 451 := by
  rw [originalWeighted, originalWeighted, ← guarded451_eq461,
    coefficient461, coefficient451]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels451_463 :
    insertions ∘ L24Gluing.flagPermutation13 =
      insertions ∘ L24Gluing.flagPermutation17 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar451_eq463 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 451).expression.scalarPointContraction X v
      (L24Gluing.term 451).decoration (L24Gluing.term 451).labels beta n insertions =
    (L24Gluing.term 463).expression.scalarPointContraction X v
      (L24Gluing.term 463).decoration (L24Gluing.term 463).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core451 L24Gluing.term451.decoration L24Gluing.term451.labels
    L24Gluing.flagPermutation13 L24Gluing.flagPermutation17 beta n insertions labels451_463

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded451_eq463 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 451) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 463) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 451) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 463) (by decide +kernel)]
  exact scalar451_eq463 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted463_eq451 : originalWeighted 463 =
    (-8909 / 11060 : ℚ) * originalWeighted 451 := by
  rw [originalWeighted, originalWeighted, ← guarded451_eq463,
    coefficient463, coefficient451]
  ring

end AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07

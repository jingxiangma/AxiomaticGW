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

namespace AxiomaticGW.BlowupF1RootRelabelTransfers.Batch16

open BlowupF1RootAssembly SurfaceGenusTwo GetzlerGraphs L24Gluing

private def core767 : GluingExpression 2 (Fin 4) :=
  close (join (m := 2) (n := 4) 2 4
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (join (m := 3) (n := 2) 3 1
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 3) (by norm_num [StableArity]) )))

private def core768 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 5) (n := 1) 5 1
    (join (m := 3) (n := 3) 3 2
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) )).relabel
      flagPermutation28)

private def core769 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 3) (n := 3) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (join (m := 3) (n := 1) 3 0
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 1 (Fin 2) (by norm_num [StableArity]) ))).relabel
      flagPermutation26)

private def core770 : GluingExpression 2 (Fin 4) :=
  close ((join (m := 6) (n := 0) 6 0
    (join (m := 3) (n := 4) 3 3
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 5) (by norm_num [StableArity])))
    (GluingExpression.fundamental 1 (Fin 1) (by norm_num [StableArity]) )).relabel
      flagPermutation22)

private def core805 : GluingExpression 2 (Fin 4) :=
  close ((close ((join (m := 2) (n := 6) 2 6
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 7) (by norm_num [StableArity]) )).relabel
      flagPermutation29)).relabel flagPermutation22)

private def core809 : GluingExpression 2 (Fin 4) :=
  close ((close ((join (m := 2) (n := 6) 2 6
    (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 7) (by norm_num [StableArity]) )).relabel
      flagPermutation29)).relabel flagPermutation22)

private def core811 : GluingExpression 2 (Fin 4) :=
  close ((close ((join (m := 3) (n := 5) 3 5
    (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (GluingExpression.fundamental 0 (Fin 6) (by norm_num [StableArity]) )).relabel
      flagPermutation29)).relabel flagPermutation22)

theorem coefficient767 : L24CorrectionsReplay.fullClaim 767 =
    (4637 / 79560 : ℚ) := by decide +kernel

theorem coefficient768 : L24CorrectionsReplay.fullClaim 768 =
    (-2551 / 318240 : ℚ) := by decide +kernel

theorem coefficient769 : L24CorrectionsReplay.fullClaim 769 =
    (-5 / 1248 : ℚ) := by decide +kernel

theorem coefficient770 : L24CorrectionsReplay.fullClaim 770 =
    (-227 / 3120 : ℚ) := by decide +kernel

theorem coefficient793 : L24CorrectionsReplay.fullClaim 793 =
    (7399 / 286416 : ℚ) := by decide +kernel

theorem coefficient794 : L24CorrectionsReplay.fullClaim 794 =
    (-5203 / 1432080 : ℚ) := by decide +kernel

theorem coefficient795 : L24CorrectionsReplay.fullClaim 795 =
    (-77 / 28080 : ℚ) := by decide +kernel

theorem coefficient796 : L24CorrectionsReplay.fullClaim 796 =
    (-187 / 5616 : ℚ) := by decide +kernel

theorem coefficient801 : L24CorrectionsReplay.fullClaim 801 =
    (7399 / 286416 : ℚ) := by decide +kernel

theorem coefficient802 : L24CorrectionsReplay.fullClaim 802 =
    (-5203 / 1432080 : ℚ) := by decide +kernel

theorem coefficient803 : L24CorrectionsReplay.fullClaim 803 =
    (-77 / 28080 : ℚ) := by decide +kernel

theorem coefficient804 : L24CorrectionsReplay.fullClaim 804 =
    (-187 / 5616 : ℚ) := by decide +kernel

theorem coefficient805 : L24CorrectionsReplay.fullClaim 805 =
    (-77 / 112320 : ℚ) := by decide +kernel

theorem coefficient806 : L24CorrectionsReplay.fullClaim 806 =
    (-77 / 168480 : ℚ) := by decide +kernel

theorem coefficient807 : L24CorrectionsReplay.fullClaim 807 =
    (-77 / 168480 : ℚ) := by decide +kernel

theorem coefficient809 : L24CorrectionsReplay.fullClaim 809 =
    (-77 / 112320 : ℚ) := by decide +kernel

theorem coefficient810 : L24CorrectionsReplay.fullClaim 810 =
    (-77 / 112320 : ℚ) := by decide +kernel

theorem coefficient811 : L24CorrectionsReplay.fullClaim 811 =
    (-77 / 37440 : ℚ) := by decide +kernel

theorem coefficient812 : L24CorrectionsReplay.fullClaim 812 =
    (-77 / 168480 : ℚ) := by decide +kernel

theorem coefficient813 : L24CorrectionsReplay.fullClaim 813 =
    (-31 / 33696 : ℚ) := by decide +kernel

theorem coefficient814 : L24CorrectionsReplay.fullClaim 814 =
    (-31 / 33696 : ℚ) := by decide +kernel

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels767_793 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar767_eq793 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 767).expression.scalarPointContraction X v
      (L24Gluing.term 767).decoration (L24Gluing.term 767).labels beta n insertions =
    (L24Gluing.term 793).expression.scalarPointContraction X v
      (L24Gluing.term 793).decoration (L24Gluing.term 793).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core767 L24Gluing.term767.decoration L24Gluing.term767.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels767_793

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded767_eq793 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 767) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 793) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 767) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 793) (by decide +kernel)]
  exact scalar767_eq793 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted793_eq767 : originalWeighted 793 =
    (36995 / 83466 : ℚ) * originalWeighted 767 := by
  rw [originalWeighted, originalWeighted, ← guarded767_eq793,
    coefficient793, coefficient767]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels767_801 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar767_eq801 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 767).expression.scalarPointContraction X v
      (L24Gluing.term 767).decoration (L24Gluing.term 767).labels beta n insertions =
    (L24Gluing.term 801).expression.scalarPointContraction X v
      (L24Gluing.term 801).decoration (L24Gluing.term 801).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core767 L24Gluing.term767.decoration L24Gluing.term767.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels767_801

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded767_eq801 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 767) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 801) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 767) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 801) (by decide +kernel)]
  exact scalar767_eq801 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted801_eq767 : originalWeighted 801 =
    (36995 / 83466 : ℚ) * originalWeighted 767 := by
  rw [originalWeighted, originalWeighted, ← guarded767_eq801,
    coefficient801, coefficient767]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels768_794 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar768_eq794 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 768).expression.scalarPointContraction X v
      (L24Gluing.term 768).decoration (L24Gluing.term 768).labels beta n insertions =
    (L24Gluing.term 794).expression.scalarPointContraction X v
      (L24Gluing.term 794).decoration (L24Gluing.term 794).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core768 L24Gluing.term768.decoration L24Gluing.term768.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels768_794

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded768_eq794 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 768) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 794) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 768) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 794) (by decide +kernel)]
  exact scalar768_eq794 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted794_eq768 : originalWeighted 794 =
    (10406 / 22959 : ℚ) * originalWeighted 768 := by
  rw [originalWeighted, originalWeighted, ← guarded768_eq794,
    coefficient794, coefficient768]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels768_802 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar768_eq802 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 768).expression.scalarPointContraction X v
      (L24Gluing.term 768).decoration (L24Gluing.term 768).labels beta n insertions =
    (L24Gluing.term 802).expression.scalarPointContraction X v
      (L24Gluing.term 802).decoration (L24Gluing.term 802).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core768 L24Gluing.term768.decoration L24Gluing.term768.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels768_802

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded768_eq802 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 768) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 802) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 768) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 802) (by decide +kernel)]
  exact scalar768_eq802 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted802_eq768 : originalWeighted 802 =
    (10406 / 22959 : ℚ) * originalWeighted 768 := by
  rw [originalWeighted, originalWeighted, ← guarded768_eq802,
    coefficient802, coefficient768]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels769_795 :
    insertions ∘ L24Gluing.flagPermutation17 =
      insertions ∘ L24Gluing.flagPermutation16 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar769_eq795 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 769).expression.scalarPointContraction X v
      (L24Gluing.term 769).decoration (L24Gluing.term 769).labels beta n insertions =
    (L24Gluing.term 795).expression.scalarPointContraction X v
      (L24Gluing.term 795).decoration (L24Gluing.term 795).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core769 L24Gluing.term769.decoration L24Gluing.term769.labels
    L24Gluing.flagPermutation17 L24Gluing.flagPermutation16 beta n insertions labels769_795

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded769_eq795 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 769) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 795) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 769) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 795) (by decide +kernel)]
  exact scalar769_eq795 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted795_eq769 : originalWeighted 795 =
    (154 / 225 : ℚ) * originalWeighted 769 := by
  rw [originalWeighted, originalWeighted, ← guarded769_eq795,
    coefficient795, coefficient769]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels769_803 :
    insertions ∘ L24Gluing.flagPermutation17 =
      insertions ∘ L24Gluing.flagPermutation15 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar769_eq803 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 769).expression.scalarPointContraction X v
      (L24Gluing.term 769).decoration (L24Gluing.term 769).labels beta n insertions =
    (L24Gluing.term 803).expression.scalarPointContraction X v
      (L24Gluing.term 803).decoration (L24Gluing.term 803).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core769 L24Gluing.term769.decoration L24Gluing.term769.labels
    L24Gluing.flagPermutation17 L24Gluing.flagPermutation15 beta n insertions labels769_803

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded769_eq803 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 769) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 803) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 769) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 803) (by decide +kernel)]
  exact scalar769_eq803 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted803_eq769 : originalWeighted 803 =
    (154 / 225 : ℚ) * originalWeighted 769 := by
  rw [originalWeighted, originalWeighted, ← guarded769_eq803,
    coefficient803, coefficient769]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels770_796 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar770_eq796 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 770).expression.scalarPointContraction X v
      (L24Gluing.term 770).decoration (L24Gluing.term 770).labels beta n insertions =
    (L24Gluing.term 796).expression.scalarPointContraction X v
      (L24Gluing.term 796).decoration (L24Gluing.term 796).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core770 L24Gluing.term770.decoration L24Gluing.term770.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels770_796

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded770_eq796 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 770) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 796) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 770) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 796) (by decide +kernel)]
  exact scalar770_eq796 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted796_eq770 : originalWeighted 796 =
    (935 / 2043 : ℚ) * originalWeighted 770 := by
  rw [originalWeighted, originalWeighted, ← guarded770_eq796,
    coefficient796, coefficient770]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels770_804 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar770_eq804 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 770).expression.scalarPointContraction X v
      (L24Gluing.term 770).decoration (L24Gluing.term 770).labels beta n insertions =
    (L24Gluing.term 804).expression.scalarPointContraction X v
      (L24Gluing.term 804).decoration (L24Gluing.term 804).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core770 L24Gluing.term770.decoration L24Gluing.term770.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels770_804

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded770_eq804 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 770) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 804) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 770) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 804) (by decide +kernel)]
  exact scalar770_eq804 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted804_eq770 : originalWeighted 804 =
    (935 / 2043 : ℚ) * originalWeighted 770 := by
  rw [originalWeighted, originalWeighted, ← guarded770_eq804,
    coefficient804, coefficient770]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels805_806 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar805_eq806 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 805).expression.scalarPointContraction X v
      (L24Gluing.term 805).decoration (L24Gluing.term 805).labels beta n insertions =
    (L24Gluing.term 806).expression.scalarPointContraction X v
      (L24Gluing.term 806).decoration (L24Gluing.term 806).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core805 L24Gluing.term805.decoration L24Gluing.term805.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation1 beta n insertions labels805_806

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded805_eq806 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 805) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 806) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 805) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 806) (by decide +kernel)]
  exact scalar805_eq806 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted806_eq805 : originalWeighted 806 =
    (2 / 3 : ℚ) * originalWeighted 805 := by
  rw [originalWeighted, originalWeighted, ← guarded805_eq806,
    coefficient806, coefficient805]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels805_807 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar805_eq807 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 805).expression.scalarPointContraction X v
      (L24Gluing.term 805).decoration (L24Gluing.term 805).labels beta n insertions =
    (L24Gluing.term 807).expression.scalarPointContraction X v
      (L24Gluing.term 807).decoration (L24Gluing.term 807).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core805 L24Gluing.term805.decoration L24Gluing.term805.labels
    L24Gluing.flagPermutation0 L24Gluing.flagPermutation2 beta n insertions labels805_807

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded805_eq807 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 805) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 807) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 805) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 807) (by decide +kernel)]
  exact scalar805_eq807 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted807_eq805 : originalWeighted 807 =
    (2 / 3 : ℚ) * originalWeighted 805 := by
  rw [originalWeighted, originalWeighted, ← guarded805_eq807,
    coefficient807, coefficient805]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels809_810 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ L24Gluing.flagPermutation5 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar809_eq810 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 809).expression.scalarPointContraction X v
      (L24Gluing.term 809).decoration (L24Gluing.term 809).labels beta n insertions =
    (L24Gluing.term 810).expression.scalarPointContraction X v
      (L24Gluing.term 810).decoration (L24Gluing.term 810).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core809 L24Gluing.term809.decoration L24Gluing.term809.labels
    L24Gluing.flagPermutation4 L24Gluing.flagPermutation5 beta n insertions labels809_810

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded809_eq810 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 809) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 810) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 809) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 810) (by decide +kernel)]
  exact scalar809_eq810 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted810_eq809 : originalWeighted 810 =
    (1 / 1 : ℚ) * originalWeighted 809 := by
  rw [originalWeighted, originalWeighted, ← guarded809_eq810,
    coefficient810, coefficient809]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels809_812 :
    insertions ∘ L24Gluing.flagPermutation4 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar809_eq812 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 809).expression.scalarPointContraction X v
      (L24Gluing.term 809).decoration (L24Gluing.term 809).labels beta n insertions =
    (L24Gluing.term 812).expression.scalarPointContraction X v
      (L24Gluing.term 812).decoration (L24Gluing.term 812).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core809 L24Gluing.term809.decoration L24Gluing.term809.labels
    L24Gluing.flagPermutation4 (Equiv.refl (Fin 4)) beta n insertions labels809_812

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded809_eq812 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 809) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 812) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 809) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 812) (by decide +kernel)]
  exact scalar809_eq812 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted812_eq809 : originalWeighted 812 =
    (2 / 3 : ℚ) * originalWeighted 809 := by
  rw [originalWeighted, originalWeighted, ← guarded809_eq812,
    coefficient812, coefficient809]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels811_813 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ L24Gluing.flagPermutation7 := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar811_eq813 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 811).expression.scalarPointContraction X v
      (L24Gluing.term 811).decoration (L24Gluing.term 811).labels beta n insertions =
    (L24Gluing.term 813).expression.scalarPointContraction X v
      (L24Gluing.term 813).decoration (L24Gluing.term 813).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core811 L24Gluing.term811.decoration L24Gluing.term811.labels
    L24Gluing.flagPermutation6 L24Gluing.flagPermutation7 beta n insertions labels811_813

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded811_eq813 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 811) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 813) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 811) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 813) (by decide +kernel)]
  exact scalar811_eq813 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted813_eq811 : originalWeighted 813 =
    (310 / 693 : ℚ) * originalWeighted 811 := by
  rw [originalWeighted, originalWeighted, ← guarded811_eq813,
    coefficient813, coefficient811]
  ring

/-- Finite equality of actual transported assignments, independent of all values. -/
theorem labels811_814 :
    insertions ∘ L24Gluing.flagPermutation6 =
      insertions ∘ (Equiv.refl (Fin 4)) := by
  funext i
  fin_cases i <;> rfl

/-- Both original source terms have the same decorated core before the outer transport. -/
theorem scalar811_eq814 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 811).expression.scalarPointContraction X v
      (L24Gluing.term 811).decoration (L24Gluing.term 811).labels beta n insertions =
    (L24Gluing.term 814).expression.scalarPointContraction X v
      (L24Gluing.term 814).decoration (L24Gluing.term 814).labels beta n insertions := by
  exact GluingExpression.scalarPointContraction_relabel_eq_of_labels X v
    core811 L24Gluing.term811.decoration L24Gluing.term811.labels
    L24Gluing.flagPermutation6 (Equiv.refl (Fin 4)) beta n insertions labels811_814

/-- The unchanged original guards retain every full curve and marking count. -/
theorem guarded811_eq814 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 811) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 814) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 811) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 814) (by decide +kernel)]
  exact scalar811_eq814 _ beta n

/-- Preserve the original coefficient ratio rather than identifying weighted rows. -/
theorem weighted814_eq811 : originalWeighted 814 =
    (310 / 693 : ℚ) * originalWeighted 811 := by
  rw [originalWeighted, originalWeighted, ← guarded811_eq814,
    coefficient814, coefficient811]
  ring

end AxiomaticGW.BlowupF1RootRelabelTransfers.Batch16

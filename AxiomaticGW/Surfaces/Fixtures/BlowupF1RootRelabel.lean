/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.ScalarPointRelabel
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly

/-!
# Exact outer relabelling reuse for three original F1 rows

The original terms 122, 141 and 156 have the same gluing construction, cotangent
powers and label decisions before their outer flag permutations. The fixed
H,E,E,E insertion assignment pulls back identically along all three permutations.
Consequently their unweighted contractions agree for arbitrary component data.
The original relation coefficients remain outside the contraction and determine
the exact ratio between weighted terms. No numerical component is evaluated.
-/

@[expose] public section

namespace AxiomaticGW.BlowupF1RootRelabel

open BlowupF1RootAssembly SurfaceGenusTwo

/-- Both permutations pull back HEEE to EEHE, at every original marking. -/
theorem insertions_flag01 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation1 := by
  funext i
  fin_cases i <;> rfl

/-- The third permutation has the same actual pulled-back assignment. -/
theorem insertions_flag02 :
    insertions ∘ L24Gluing.flagPermutation0 =
      insertions ∘ L24Gluing.flagPermutation2 := by
  funext i
  fin_cases i <;> rfl

/-- The original full-frame entries agree before multiplying their coefficients. -/
theorem scalar122_eq141 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 122).expression.scalarPointContraction X v
      (L24Gluing.term 122).decoration (L24Gluing.term 122).labels beta n insertions =
    (L24Gluing.term 141).expression.scalarPointContraction X v
      (L24Gluing.term 141).decoration (L24Gluing.term 141).labels beta n insertions := by
  change L24Gluing.term122.expression.scalarPointContraction X v
      L24Gluing.term122.decoration L24Gluing.term122.labels beta n insertions =
    L24Gluing.term141.expression.scalarPointContraction X v
      L24Gluing.term141.decoration L24Gluing.term141.labels beta n insertions
  dsimp only [L24Gluing.term122, L24Gluing.term141,
    L24Gluing.expression51, L24Gluing.expression55]
  apply GluingExpression.scalarPointContraction_relabel_eq_of_labels
  exact insertions_flag01

/-- Row 156 has precisely the same internal expression as rows 122 and 141. -/
theorem scalar122_eq156 (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 122).expression.scalarPointContraction X v
      (L24Gluing.term 122).decoration (L24Gluing.term 122).labels beta n insertions =
    (L24Gluing.term 156).expression.scalarPointContraction X v
      (L24Gluing.term 156).decoration (L24Gluing.term 156).labels beta n insertions := by
  change L24Gluing.term122.expression.scalarPointContraction X v
      L24Gluing.term122.decoration L24Gluing.term122.labels beta n insertions =
    L24Gluing.term156.expression.scalarPointContraction X v
      L24Gluing.term156.decoration L24Gluing.term156.labels beta n insertions
  dsimp only [L24Gluing.term122, L24Gluing.term156,
    L24Gluing.expression51, L24Gluing.expression59]
  apply GluingExpression.scalarPointContraction_relabel_eq_of_labels
  exact insertions_flag02

/-- Their original higher-genus guards also agree, for every class and point count. -/
theorem guarded122_eq141 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 122) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 141) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 122) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 141) (by decide +kernel)]
  exact scalar122_eq141 _ beta n

/-- Guarded equality uses only the checked source syntax and external assignment. -/
theorem guarded122_eq156 (beta : X.Curve) (n : ℕ) :
    guardedConstantPointContraction X (L24Gluing.term 122) beta n insertions =
      guardedConstantPointContraction X (L24Gluing.term 156) beta n insertions := by
  rw [guardedConstantPointContraction_of_lt X (L24Gluing.term 122) (by decide +kernel),
    guardedConstantPointContraction_of_lt X (L24Gluing.term 156) (by decide +kernel)]
  exact scalar122_eq156 _ beta n

/-- These are the actual independent relation coordinates at their original indices. -/
theorem coefficient122 : L24CorrectionsReplay.fullClaim 122 = 4259 / 3510 := rfl

theorem coefficient141 : L24CorrectionsReplay.fullClaim 141 = 3527 / 5265 := rfl

theorem coefficient156 : L24CorrectionsReplay.fullClaim 156 = 3527 / 5265 := rfl

/-- Transfer a weighted value with the exact coefficient ratio; no value is assumed. -/
theorem originalWeighted141_eq_ratio122 :
    originalWeighted 141 = (7054 / 12777 : ℚ) * originalWeighted 122 := by
  rw [originalWeighted, originalWeighted, ← guarded122_eq141,
    coefficient141, coefficient122]
  ring

/-- The second transfer retains the same original coefficient as row 141. -/
theorem originalWeighted156_eq_ratio122 :
    originalWeighted 156 = (7054 / 12777 : ℚ) * originalWeighted 122 := by
  rw [originalWeighted, originalWeighted, ← guarded122_eq156,
    coefficient156, coefficient122]
  ring

/-- Any existing certified cache root sum transfers without inspecting its backend. -/
theorem rootSum141_eq_ratio122 (cache : ResidualCache X) :
    rootSum cache 141 = (7054 / 12777 : ℚ) * rootSum cache 122 := by
  rw [← originalWeighted_eq_rootSum cache 141 (by decide +kernel),
    ← originalWeighted_eq_rootSum cache 122 (by decide +kernel)]
  exact originalWeighted141_eq_ratio122

/-- The complete 37-slot sum is retained for the third original row. -/
theorem rootSum156_eq_ratio122 (cache : ResidualCache X) :
    rootSum cache 156 = (7054 / 12777 : ℚ) * rootSum cache 122 := by
  rw [← originalWeighted_eq_rootSum cache 156 (by decide +kernel),
    ← originalWeighted_eq_rootSum cache 122 (by decide +kernel)]
  exact originalWeighted156_eq_ratio122

end AxiomaticGW.BlowupF1RootRelabel

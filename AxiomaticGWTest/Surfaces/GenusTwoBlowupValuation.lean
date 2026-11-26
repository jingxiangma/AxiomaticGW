/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupValuation
public import AxiomaticGW.Surfaces.GenusTwoBlowupHRow
public import AxiomaticGW.Surfaces.GenusTwoBlowupPRow
public import AxiomaticGW.Surfaces.GenusTwoBlowupKRow

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusTwoBlowupValuation
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder

/-- Equal reconstruction measures do not identify distinct full curve classes. -/
public theorem same_measure_distinct_classes :
    canonicalValuation (fun s : State .blowupTwo ↦ (s.1 0 : ℚ))
      (.inr (Family.hyperplane.query ![1, 0, 1])) = 1 ∧
    canonicalValuation (fun s : State .blowupTwo ↦ (s.1 0 : ℚ))
      (.inr (Family.hyperplane.query ![0, 1, 1])) = 0 := by
  rw [canonicalValuation_query, canonicalValuation_query]
  decide +kernel

/-- Exceptional states of identical class and rank still have different labels. -/
public theorem exceptional_labels_distinct (beta : SurfaceTarget.blowupTwo.Curve) :
    (Family.exceptional 0).query beta ≠ (Family.exceptional 1).query beta := by
  intro h
  have he := state_query_injective (a₁ := (beta, .exceptional 0))
    (a₂ := (beta, .exceptional 1)) h
  have hf := congrArg Prod.snd he
  cases hf

/-- Negative signed multiplicity does not change the full stored class. -/
public theorem negative_multiplicity_table_entry (values : State .hirzebruchOne → ℚ) :
    canonicalValuation values (.inr (Family.primary.query ![3, 1])) =
      values (![3, 1], .primary) := canonicalValuation_query values .primary _

/-- A correct first insertion cannot hide a wrong genus. -/
public theorem rejects_wrong_genus :
    state? (SurfaceFirstDescendant.query (X := .blowupTwo) 1 ![0, 0, 1] .hyperplane 1) =
      none := by decide +kernel

/-- A correct first insertion cannot hide a wrong point count. -/
public theorem rejects_wrong_count :
    state? (SurfaceFirstDescendant.query (X := .hirzebruchOne) 2 ![0, 1] .hyperplane 1) =
      none := by decide +kernel

/-- An extra divisor is not accepted as part of the canonical point tail. -/
public theorem rejects_nonpoint_tail :
    state? (⟨2, ![0, 0, 1], [⟨.exceptional 0, 1⟩, ⟨.hyperplane, 0⟩]⟩ :
      SurfaceQuery .blowupTwo) = none := by decide +kernel

/-- The lookup API deliberately separates nominal table indices from dimension validity. -/
public theorem nominal_point_zero_invalid :
    state? ((Family.point : Family .hirzebruchOne).query 0) = some (0, .point) ∧
      ¬((Family.point : Family .hirzebruchOne).query 0).DimensionCompatible := by
  constructor
  · exact state?_query .point 0
  · decide +kernel

/-- A first insertion of cotangent power two requires the separate ancestor reduction. -/
public theorem rejects_higher_psi :
    state? (⟨2, ![0, 0, 1], [⟨.hyperplane, 2⟩]⟩ : SurfaceQuery .blowupTwo) = none := by
  decide +kernel

-- The imported H step traverses the complete 815-column L24 dispatch.
set_option maxRecDepth 20000 in
/-- Actual H-row support permits replacing arbitrary callbacks by the canonical table. -/
public theorem h_step_uses_table (X : SurfaceTarget) (i : Fin X.blowups) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta) (v : Variable X → ℚ) :
    SurfaceGenusTwoBlowupHRow.step X i v beta =
      SurfaceGenusTwoBlowupHRow.step X i
        (canonicalValuation (fun s ↦ v (.inr (s.2.query s.1)))) beta := by
  apply SurfaceGenusTwoBlowupHRow.step_congr X i v _ beta hbeta
  intro gamma f _
  rw [canonicalValuation_query]

/-- The P row also consumes only the exact canonical table, with constants retained. -/
public theorem p_step_uses_table (X : SurfaceTarget) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta) (v : Variable X → ℚ) :
    SurfaceGenusTwoBlowupPRow.step X v beta =
      SurfaceGenusTwoBlowupPRow.step X
        (canonicalValuation (fun s ↦ v (.inr (s.2.query s.1)))) beta := by
  apply SurfaceGenusTwoBlowupPRow.step_congr X v _ beta hbeta
  intro gamma f _
  rw [canonicalValuation_query]

/-- K uses the same table while preserving the selected exceptional label. -/
public theorem k_step_uses_table (X : SurfaceTarget) (i : Fin X.blowups) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta) (v : Variable X → ℚ) :
    SurfaceGenusTwoBlowupKRow.step X i v beta =
      SurfaceGenusTwoBlowupKRow.step X i
        (canonicalValuation (fun s ↦ v (.inr (s.2.query s.1)))) beta := by
  apply SurfaceGenusTwoBlowupKRow.step_congr X i v _ beta hbeta
  intro gamma f _
  rw [canonicalValuation_query]

end AxiomaticGWTest.Surfaces.GenusTwoBlowupValuation

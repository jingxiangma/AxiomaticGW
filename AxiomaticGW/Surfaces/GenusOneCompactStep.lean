/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusOneRecursion
public import AxiomaticGW.Surfaces.PointExpansion

/-!
# Certified compact evaluation of the elliptic reconstruction step

The leading elliptic singleton is removed by a genus-aware guard. Rational
dependencies at the original energy remain intact, and all residual elliptic
dependencies strictly decrease energy. The uniform coefficient minus nine
turns the solved equation into the remaining evaluation divided by nine.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusOne

open SurfacePolynomialReduction SurfaceLowGenus
open SurfaceGenusZero (variableCurve)

/-- Evaluate the compressed original equation using exactly the permitted dependencies. -/
def compactReconstructionStep (X : SurfaceTarget) (beta : X.Curve)
    (v : Variable X → ℚ) : ℚ :=
  RationalTerms.eval
      (fun u ↦ if variableGenus u = 0 ∨
        X.effective.energy (variableCurve u) < X.effective.energy beta then v u else 0)
      (GetzlerGraphs.compactPrimaryTerms X (X.effective.energy beta - 2) beta
        (GetzlerGraphs.reconstructionLabels X)) / 9

/-- Compression and the genus-aware guard preserve the entire original remainder. -/
theorem compactReconstructionStep_eq (X : SurfaceTarget) (beta : X.Curve)
    (h : ¬IsInitial X beta) (v : Variable X → ℚ) :
    compactReconstructionStep X beta v =
      -RationalTerms.eval v (reconstructionRemainder X beta) /
        reconstructionCoefficient X beta := by
  let w : Variable X → ℚ := fun u ↦ if variableGenus u = 0 ∨
    X.effective.energy (variableCurve u) < X.effective.energy beta then v u else 0
  have hz : w (pointVariable X 1 beta) = 0 := if_neg (by
    change ¬((1 : ℕ) = 0 ∨ X.effective.energy beta < X.effective.energy beta)
    omega)
  have heval : RationalTerms.eval w (reconstructionTerms X beta) =
      RationalTerms.eval v (reconstructionRemainder X beta) := by
    rw [RationalTerms.eval_isolate_singleton w _ (pointVariable X 1 beta), hz,
      mul_zero, zero_add]
    apply RationalTerms.eval_congr
    intro t ht u hu
    obtain ⟨g, gamma, _, rfl, _, hlt⟩ := reconstructionRemainder_dependencies X beta t ht u hu
    exact if_pos hlt
  unfold compactReconstructionStep
  rw [GetzlerGraphs.eval_compactPrimaryTerms]
  change RationalTerms.eval w (reconstructionTerms X beta) / 9 = _
  rw [heval, reconstructionCoefficient_eq X beta h, neg_div_neg_eq]

/-- Rational dependencies also stay inside the same energy bound, even when
their energy is not strictly smaller. This is needed for finite joint replay. -/
theorem reconstructionRemainder_energy_le (X : SurfaceTarget) (beta : X.Curve)
    (t : ℚ × Multiset (Variable X)) (ht : t ∈ reconstructionRemainder X beta)
    (u : Variable X) (hu : u ∈ t.2) :
    X.effective.energy (variableCurve u) ≤ X.effective.energy beta := by
  have ht' : t ∈ reconstructionTerms X beta := (Multiset.mem_filter.mp ht).1
  have hm := pointTerms_getzler X (X.effective.energy beta - 2) beta
    (SurfaceGenusZero.pointLabels (GetzlerGraphs.reconstructionLabels X)
      (X.effective.energy beta - 2)) t ht'
  have hle := SurfaceGenusZero.variable_energy_le_sum t.2 u hu
  rw [hm.2.1] at hle
  exact hle

end AxiomaticGW.SurfaceGenusOne

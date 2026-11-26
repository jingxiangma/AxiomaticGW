/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusOneDimension

/-!
# Grouping identical four-hyperplane Getzler contractions

Every original external label is H, so the marking permutations within each
of the seven orbits give identical scalar contractions. Their original raw
weights, including loop automorphism factors, are added exactly. This avoids
repeating the same contraction for all 33 labelled graphs during kernel replay.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusOne

/-- Seven representative contractions with the summed original labelled weights. -/
def orbitReconstructionStep (X : SurfaceTarget) (beta : X.Curve)
    (v₀ v₁ : X.Curve → ℚ) : ℚ :=
  let f := fun s ↦ dimensionPrunedEval X v₀
    (fun gamma ↦ if X.effective.energy gamma < X.effective.energy beta then v₁ gamma else 0)
    (GetzlerGraphs.representativeExpression s) (by omega) beta (X.effective.energy beta - 2)
    (GetzlerGraphs.reconstructionLabels X)
  (-9 * f .delta22 + 12 * f .delta23 + 3 * f .delta24 - 6 * f .delta34 -
    f .delta03 / 2 - f .delta04 / 8 + 3 * f .deltaBeta / 4) / 9

/-- The finite weight calculation keeps every original multiplicity and sign. -/
private theorem grouped_sum (f : GetzlerStratum → ℚ) :
    (∑ i : Fin 33, GetzlerGraphs.requested i * f (GetzlerGraphs.kind i)) =
      -9 * f .delta22 + 12 * f .delta23 + 3 * f .delta24 - 6 * f .delta34 -
        f .delta03 / 2 - f .delta04 / 8 + 3 * f .deltaBeta / 4 := by
  norm_num [Fin.sum_univ_succ, GetzlerGraphs.requested, GetzlerGraphs.kind,
    GetzlerGraphs.normalization]
  ring

/-- Grouping is valid for this symmetric insertion request and arbitrary candidate tables. -/
theorem orbitReconstructionStep_eq (X : SurfaceTarget) (beta : X.Curve)
    (v₀ v₁ : X.Curve → ℚ) :
    orbitReconstructionStep X beta v₀ v₁ = scalarReconstructionStep X beta v₀ v₁ := by
  have hz (a b : ℚ) : (if a = 0 then 0 else a * b) = a * b := by
    split_ifs with h
    · rw [h, zero_mul]
    · rfl
  unfold orbitReconstructionStep scalarReconstructionStep
  simp only [hz, dimensionPrunedEval_eq]
  change _ = (∑ i : Fin 33, GetzlerGraphs.requested i *
    compactEval X v₀
      (fun gamma ↦ if X.effective.energy gamma < X.effective.energy beta then v₁ gamma else 0)
      (GetzlerGraphs.representativeExpression (GetzlerGraphs.kind i)) (by omega) beta
      (X.effective.energy beta - 2) (GetzlerGraphs.reconstructionLabels X)) / 9
  exact congrArg (fun t : ℚ ↦ t / 9) (grouped_sum (fun s ↦ compactEval X v₀
    (fun gamma ↦ if X.effective.energy gamma < X.effective.energy beta then v₁ gamma else 0)
    (GetzlerGraphs.representativeExpression s) (by omega) beta (X.effective.energy beta - 2)
    (GetzlerGraphs.reconstructionLabels X))).symm

end AxiomaticGW.SurfaceGenusOne

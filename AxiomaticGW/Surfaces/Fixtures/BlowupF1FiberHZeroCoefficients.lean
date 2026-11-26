/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHRequest
public import AxiomaticGW.Surfaces.GenusTwoBlowupHUniform

/-!
# Exact finite coefficient requests for the first F1 fiber equation

Both class-zero first-descendant columns use the full source E+F and exactly
one added primary point. The existing complete genus-two graph frame has 27
terms. Its equality to the full normalized coefficient preserves signed
point-pullback corrections, inverse-metric factors and all rational complements.
No coefficient is assigned a numerical value by this module.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberHZeroCoefficients
open SurfacePolynomialReduction BlowupF1FiberHReduction

-- Match the existing complete L24 coefficient API elaboration depth.
set_option maxRecDepth 20000

/-- A class-zero first descendant, retaining its divisor label. -/
def zeroVariable (b : SurfaceBasisLabel target) : Variable target :=
  .inr (SurfaceFirstDescendant.query 2 0 b 0)

/-- One exact original weighted graph contribution to the zero-class coefficient. -/
def weightedTerm (b : SurfaceBasisLabel target) (j : Fin 815) : ℚ :=
  L24CorrectionsReplay.fullClaim j *
    SurfaceGenusTwo.remainderPointCoefficient target (zeroVariable b)
      (SurfaceGenusTwo.firstCoefficientVertex target 0 b 0) (L24Gluing.term j)
      ![1, 1] 1 ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0]

/-- All 27 nonzero source terms containing genus two remain in the coefficient request. -/
def coefficient (b : SurfaceBasisLabel target) : ℚ :=
  ∑ j ∈ SurfaceGenusTwoBlowupHUniform.genusTwoFrame, weightedTerm b j

/-- The frame is exactly the full compressed coefficient at source E+F, with point budget one. -/
theorem coefficient_eq_full (b : SurfaceBasisLabel target) :
    coefficient b = L24Relation.pointCoefficient target 1 ![1, 1]
      ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] (zeroVariable b) := by
  unfold coefficient weightedTerm L24Relation.pointCoefficient L24Relation.cotangentRelation
  simp only [Multiset.map_map, Function.comp_def, ← Finset.sum_eq_multiset_sum]
  trans ∑ j ∈ SurfaceGenusTwoBlowupHUniform.genusTwoFrame, L24CorrectionsReplay.fullClaim j *
    SurfaceGenusTwo.pointCoefficient target (zeroVariable b) (L24Gluing.term j)
      ![1, 1] 1 ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0]
  · apply Finset.sum_congr rfl
    intro j _
    congr 1
    rw [SurfaceGenusTwo.remainderPointCoefficient_eq target (zeroVariable b)
      (SurfaceGenusTwo.firstCoefficientVertex target 0 b 0)
      (SurfaceGenusTwo.firstCoefficientVertex_eq (X := target) 0 b 0)]
    change SurfaceGenusTwo.pointCoefficient target (zeroVariable b) (L24Gluing.term j)
      (0 + ![1, 1]) 1 _ = _
    rw [zero_add]
  · apply Finset.sum_subset
    · intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
        ((SurfaceGenusTwoBlowupHUniform.genusTwoFrame_checked j).mp hj).1⟩
    · intro j hj hnot
      have hne : (L24Gluing.term j).expression.maxComponentGenus ≠ 2 := by
        intro he
        exact hnot ((SurfaceGenusTwoBlowupHUniform.genusTwoFrame_checked j).mpr
          ⟨(Finset.mem_filter.mp hj).2, he⟩)
      rw [SurfaceGenusTwo.pointCoefficient, if_neg hne, mul_zero]

/-- Binding to the H0 coefficient retains the target fiber and the shifted source separately. -/
theorem hyperplane_eq : coefficient .hyperplane = hZeroCoefficient := by
  rw [coefficient_eq_full]
  have he : target.effective.energy fiber = 2 := by decide +kernel
  have hs : fiber + target.exceptionalCurve 0 = ![1, 1] := by
    funext k
    fin_cases k <;> rfl
  simp only [hZeroCoefficient, SurfaceGenusTwoBlowupScalar.singletonCoefficient,
    he, hs, Nat.reduceSub]
  rfl

/-- Binding to K0 retains the actual exceptional label in the entire first descendant query. -/
theorem exceptional_eq : coefficient (.exceptional 0) = kZeroCoefficient := by
  rw [coefficient_eq_full]
  have he : target.effective.energy fiber = 2 := by decide +kernel
  have hs : fiber + target.exceptionalCurve 0 = ![1, 1] := by
    funext k
    fin_cases k <;> rfl
  simp only [kZeroCoefficient, SurfaceGenusTwoBlowupScalar.singletonCoefficient,
    he, hs, Nat.reduceSub]
  rfl

end AxiomaticGW.BlowupF1FiberHZeroCoefficients

import AxiomaticGW.Surfaces.LowGenusAncestorDimension

open AxiomaticGW

-- These queries have the correct virtual dimension, but their ancestor psi
-- classes exceed the stable-curve dimension. Full curve coordinates are retained.
example (X : SurfaceTarget) : SurfaceGenusZero.ancestorValue X
    ⟨0, 0, ([⟨.hyperplane, 1⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩] : List (SurfaceInsertion X)),
      by change 3 ≤ 3; decide⟩ = 0 := by
  exact SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound _ rfl
    (by change 3 ≤ 3; decide)

example : SurfaceGenusOne.ancestorValue .plane
    ⟨1, ![1], ([⟨.point, 2⟩] : List (SurfaceInsertion .plane)), by decide⟩ = 0 := by
  exact SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound _ rfl (by decide +kernel)

-- The dimension theorem is independent of fuel and of the target class.
example (X : SurfaceTarget) (beta : X.Curve) (fuel : ℕ) :
    SurfaceGenusZero.ancestorValueFuel X fuel
      ⟨0, beta, ([⟨.unit, 100⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩] : List (SurfaceInsertion X)),
        by change 3 ≤ 3; decide⟩ = 0 := by
  exact SurfaceGenusZero.ancestorValueFuel_zero_of_cotangent_bound _ _ rfl
    (by change 3 ≤ 102; decide)

example (X : SurfaceTarget) (beta : X.Curve) (fuel : ℕ) :
    SurfaceGenusOne.ancestorValueFuel X fuel
      ⟨1, beta, ([⟨.unit, 100⟩] : List (SurfaceInsertion X)),
        by change 3 ≤ 3; decide⟩ = 0 := by
  exact SurfaceGenusOne.ancestorValueFuel_zero_of_cotangent_bound _ _ rfl
    (by change 1 < 100; decide)

-- At the dimension boundary, the original nonzero values must survive pruning.
attribute [local cbv_eval] SurfaceGenusZero.ancestorValue_pruned
attribute [local cbv_eval] SurfaceGenusOne.ancestorValue_pruned

example : SurfaceGenusZero.ancestorValue .plane
    ⟨0, 0, ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.unit, 0⟩] :
      List (SurfaceInsertion .plane)), by decide⟩ = 1 := by cbv

example : SurfaceGenusOne.ancestorValue .plane
    ⟨1, 0, ([⟨.unit, 1⟩] : List (SurfaceInsertion .plane)), by decide⟩ = 1 / 8 := by cbv

example : SurfaceGenusOne.ancestorValue .plane
    ⟨1, ![1], ([⟨.point, 2⟩] : List (SurfaceInsertion .plane)), by decide⟩ = 0 := by cbv

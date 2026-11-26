module

import AxiomaticGW.Surfaces.DimensionVanishing

set_option linter.privateModule false

namespace AxiomaticGWTest.SurfaceDimensionVanishing
open AxiomaticGW

-- Five times the plane line class has positive degree and needs insertions to reach dimension 14.
example : let q : SurfaceQuery .plane := ⟨0, ![5], []⟩
    q.GeometricDomain ∧ q.dimensionVanishing? = some 0 := by decide +kernel

-- A point on a plane line has the required dimension at cotangent power one.
example : let q : SurfaceQuery .plane := ⟨0, ![1], [⟨.point, 1⟩]⟩
    q.GeometricDomain ∧ q.dimensionVanishing? = none := by decide +kernel

-- Degree-zero genus-zero two-point conventions lie outside the geometric theorem.
example : ¬(⟨0, ![0], [⟨.unit, 0⟩, ⟨.unit, 0⟩]⟩ : SurfaceQuery .plane).GeometricDomain := by
  decide +kernel

end AxiomaticGWTest.SurfaceDimensionVanishing

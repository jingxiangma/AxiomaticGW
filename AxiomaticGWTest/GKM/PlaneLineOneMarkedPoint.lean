module

import AxiomaticGW.GKM.Fixtures.PlaneLineOneMarkedPointReplay

set_option linter.privateModule false

namespace AxiomaticGWTest.GKM.PlaneLineOneMarkedPoint
open AxiomaticGW.GKM AxiomaticGW.GKM.EquivariantCoefficients
open AxiomaticGW.GKM.PlaneLineOneMarkedPoint

-- The ordinary zero at the second power retains both characters of the torus.
example : equivariant 2 = 2 * y - x ∧ equivariant 2 ≠ 0 ∧ Specializes (equivariant 2) 0 := by
  refine ⟨?_, equivariant_ne_zero (by decide), specializes 2⟩
  rw [equivariant_eq_polynomial]
  simp only [polynomial, pow_one, pow_zero, mul_zero, add_zero, mul_one,
    map_add, map_sub, embed_X_one, embed_X_zero]
  ring

-- The first descendant has ordinary value one in the original geometric query domain.
example : AxiomaticGW.SurfaceGenusZero.queryValue? (requests 1) = some 1 := first_descendant

end AxiomaticGWTest.GKM.PlaneLineOneMarkedPoint

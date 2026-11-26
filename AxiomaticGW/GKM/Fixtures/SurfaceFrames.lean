/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.StateSpaceCertificate
public import AxiomaticGW.Surfaces.TargetData

/-!
# Fixed semantic requests for the three toric surface state spaces

These requests are held independently of the candidate JSON and exporter.
Rows follow the sorted fan cones recorded in GKMExchange.md, with lifts
D2 on the first two targets and D0+D3 on the two-point blowup. Ordinary
tables are computed from the existing rational surface algebra itself.
Identifying these fans with geometric surfaces remains a geometric input.
-/

@[expose] public section

namespace AxiomaticGW.GKM.SurfaceFrames

open EquivariantCoefficients StateSpaceCertificate
open Matrix

noncomputable section

namespace Plane

/-- The fixed rational basis, ordered unit, hyperplane, exceptional classes, point. -/
def states : Fin 3 → SurfaceCohomology 0 :=
  ![((1, 0, 0) : SurfaceCohomology 0), SurfaceCohomology.hyperplane 0, SurfaceCohomology.point 0]

/-- The explicit first basis state is the existing surface algebra unit. -/
theorem states_unit : states 0 = 1 := by
  rw [SurfaceCohomology.one_coordinates]
  rfl

/-- Coordinates in exactly the order used by the GKM exchange. -/
def coordinates (a : SurfaceCohomology 0) : Fin 3 → ℚ :=
  ![a.1, a.2.1.1, a.2.2]

/-- Independently fixed restriction, tangent, and ordinary surface data. -/
def request : Request 3 where
  unitIndex := 0
  restrictions := !![1, 0, 0; 1, -y, y^2-x*y; 1, -x, 0]
  euler := ![x*y, (x-y)*(-y), (-x)*(y-x)]
  tangentSum := ![x+y, x-2*y, y-2*x]
  ordinaryMetric i j := tracePairing (SurfaceCohomology.counit 0) (states i) (states j)
  ordinaryProducts i j k := coordinates (SurfaceCohomology.cupProduct (states i) (states j)) k
  ordinaryC1 := coordinates (SurfaceCohomology.firstChernDivisor 0).val

end Plane

namespace OneBlowup

/-- The fixed rational basis, ordered unit, hyperplane, exceptional classes, point. -/
def states : Fin 4 → SurfaceCohomology 1 :=
  ![((1, 0, 0) : SurfaceCohomology 1), SurfaceCohomology.hyperplane 1,
    SurfaceCohomology.exceptional 1 0, SurfaceCohomology.point 1]

/-- The explicit first basis state is the existing surface algebra unit. -/
theorem states_unit : states 0 = 1 := by
  rw [SurfaceCohomology.one_coordinates]
  rfl

/-- Coordinates in exactly the order used by the GKM exchange. -/
def coordinates (a : SurfaceCohomology 1) : Fin 4 → ℚ :=
  ![a.1, a.2.1.1, a.2.1.2 0, a.2.2]

/-- Independently fixed restriction, tangent, and ordinary surface data. -/
def request : Request 4 where
  unitIndex := 0
  restrictions := !![1, -y, 0, y^2-x*y; 1, 0, y, 0; 1, -x, 0, 0; 1, 0, x, 0]
  euler := ![(x-y)*(-y), (x-y)*y, (-x)*(y-x), x*(y-x)]
  tangentSum := ![x-2*y, x, y-2*x, y]
  ordinaryMetric i j := tracePairing (SurfaceCohomology.counit 1) (states i) (states j)
  ordinaryProducts i j k := coordinates (SurfaceCohomology.cupProduct (states i) (states j)) k
  ordinaryC1 := coordinates (SurfaceCohomology.firstChernDivisor 1).val

end OneBlowup

namespace TwoBlowups

/-- The fixed rational basis, ordered unit, hyperplane, exceptional classes, point. -/
def states : Fin 5 → SurfaceCohomology 2 :=
  ![((1, 0, 0) : SurfaceCohomology 2), SurfaceCohomology.hyperplane 2,
    SurfaceCohomology.exceptional 2 0, SurfaceCohomology.exceptional 2 1, SurfaceCohomology.point 2]

/-- The explicit first basis state is the existing surface algebra unit. -/
theorem states_unit : states 0 = 1 := by
  rw [SurfaceCohomology.one_coordinates]
  rfl

/-- Coordinates in exactly the order used by the GKM exchange. -/
def coordinates (a : SurfaceCohomology 2) : Fin 5 → ℚ :=
  ![a.1, a.2.1.1, a.2.1.2 0, a.2.1.2 1, a.2.2]

/-- Independently fixed restriction, tangent, and ordinary surface data. -/
def request : Request 5 where
  unitIndex := 0
  restrictions := !![1, x-y, 0, 0, y^2-x*y; 1, x, y, 0, 0; 1, x, x, 0, 0;
    1, 0, 0, -x, 0; 1, 0, 0, y-x, 0]
  euler := ![(x-y)*(-y), (x-y)*y, x*(y-x), (-x)*y, (-y)*(y-x)]
  tangentSum := ![x-2*y, x, y, y-x, -x]
  ordinaryMetric i j := tracePairing (SurfaceCohomology.counit 2) (states i) (states j)
  ordinaryProducts i j k := coordinates (SurfaceCohomology.cupProduct (states i) (states j)) k
  ordinaryC1 := coordinates (SurfaceCohomology.firstChernDivisor 2).val

end TwoBlowups

end

end AxiomaticGW.GKM.SurfaceFrames

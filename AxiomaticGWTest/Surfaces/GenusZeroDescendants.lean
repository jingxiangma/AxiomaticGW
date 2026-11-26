/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.GenusZeroFullDescendants

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusZeroDescendants
open AxiomaticGW SurfaceGenusZero

/-- Sorting retains multiplicities and pairs each power with its original state. -/
example : (SurfaceAncestorKey.ofLabels (X := .plane) 2 (Fin 4)
    (by norm_num [StableArity]) 0 ![0,2,1,1]
      ![.point,.unit,.hyperplane,.hyperplane]).orderedInsertions =
    [⟨.hyperplane,1⟩,⟨.hyperplane,1⟩,⟨.unit,2⟩,⟨.point,0⟩] := by decide +kernel

/-- Distinct cotangent monomials on M₀,₅ have different multinomial factors. -/
example : ancestorValue .plane (SurfaceAncestorKey.ofLabels 0 (Fin 5)
      (by norm_num [StableArity]) 0 ![1,1,0,0,0] ![.unit,.unit,.unit,.unit,.point]) = 2 ∧
    ancestorValue .plane (SurfaceAncestorKey.ofLabels 0 (Fin 5)
      (by norm_num [StableArity]) 0 ![2,0,0,0,0] ![.unit,.unit,.unit,.unit,.point]) = 1 := by
  decide +kernel

/-- The three independent psi factors on M₀,₆ contribute 3! = 6. -/
example : ancestorValue .plane (SurfaceAncestorKey.ofLabels 0 (Fin 6)
    (by norm_num [StableArity]) 0 ![1,1,1,0,0,0]
      ![.unit,.unit,.unit,.unit,.unit,.point]) = 6 := by decide +kernel

/-- A stable-map descendant can survive when its corresponding ancestor vanishes. -/
example : ancestorValue .plane (SurfaceAncestorKey.ofLabels 0 (Fin 4)
      (by norm_num [StableArity]) ![1] ![3,0,0,0] ![.point,.unit,.unit,.hyperplane]) = 0 ∧
    stableValue .plane 4 (by omega) ![1] ![3,0,0,0]
      ![.point,.unit,.unit,.hyperplane] = 1 := by decide +kernel

/-- Simultaneous permutation moves the descendant power with the point insertion. -/
example : stableValue .plane 4 (by omega) ![1] ![0,0,0,3]
    ![.hyperplane,.unit,.unit,.point] = 1 := by decide +kernel

/-- The arbitrary-state callback retains scalar factors and exceptional signs. -/
example : stableStateValue .hirzebruchOne (Fin 3) (by norm_num [StableArity]) 0 0
    ![SurfaceCohomology.exceptional 1 0, SurfaceCohomology.exceptional 1 0,
      (2 : ℚ) • (1 : SurfaceCohomology 1) + SurfaceCohomology.hyperplane 1] = -2 := by
  decide +kernel

/-- Empty positive exceptional queries are geometric and reconstructed. -/
example : queryValue? (X := .hirzebruchOne) ⟨0, ![1,0], []⟩ = some 1 := by decide +kernel

/-- Auxiliary degree-zero unstable requests and unsupported genera are rejected. -/
example : queryValue? (X := .plane) ⟨0, 0, []⟩ = none ∧
    queryValue? (X := .plane) ⟨0, 0, [⟨.point,3⟩,⟨.unit,0⟩]⟩ = none ∧
    queryValue? (X := .plane) ⟨1, ![1], [⟨.point,0⟩]⟩ = none := by decide +kernel

end AxiomaticGWTest.Surfaces.GenusZeroDescendants

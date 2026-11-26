/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.PlanePointNormalization

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusTwoZeroRemainder
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwo

-- The classical tail is present with no additional points, and disappears
-- for every positive number, independently of the main component's values.
example : SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane)
    0 0 (Option.elim · .unit (fun t : Bool ↦ if t then .point else .unit)) = 1 := by
  rw [SurfaceGenusZero.primaryScalar_plane_zero_tail]
  rfl

example (n : ℕ) : SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane)
    0 (n + 1) (Option.elim · .unit (fun t : Bool ↦ if t then .point else .unit)) = 0 := by
  rw [SurfaceGenusZero.primaryScalar_plane_zero_tail, if_neg (fun h ↦ Nat.succ_ne_zero n h.1)]

example (f : ℕ → ℚ) (n : ℕ) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (f ij.1 * SurfaceGenusZero.primaryScalar .plane (SurfaceGenusZero.pointValue .plane)
        0 ij.2 (Option.elim · .unit (fun t : Bool ↦ if t then .point else .hyperplane)))) = 0 := by
  rw [SurfaceGenusZero.sum_binomial_primary_plane_zero_tail]
  rfl

private def primary (d : ℕ) : Variable .plane :=
  .inr (SurfaceQuery.points .plane 2 ![d] (3 * d + 1))

private def hyperplane (d : ℕ) : Variable .plane :=
  .inr (SurfaceFirstDescendant.query 2 ![d] .hyperplane (3 * d))

-- The terminal dilaton coefficient is six, but four classical tails subtract
-- four. This checks the complete signed coefficient, not an invariant value.
example : remainderVertex .plane (primary 1) (planeCoefficientVertex (primary 1))
    4 2 (Fin 1) (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0 ![.unit] = 2 := by
  rw [remainderVertex_onePsi_plane_zero_normalized, remainderVertex_plane_primary]
  decide +kernel

-- The same correction is uniform across degree, including the degree-zero key.
example : remainderVertex .plane (primary 3) (planeCoefficientVertex (primary 3))
    10 2 (Fin 1) (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0 ![.unit] = 2 := by
  rw [remainderVertex_onePsi_plane_zero_normalized, remainderVertex_plane_primary]
  decide +kernel

example : remainderVertex .plane (primary 0) (planeCoefficientVertex (primary 0))
    1 2 (Fin 1) (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0 ![.unit] = 2 := by
  rw [remainderVertex_onePsi_plane_zero_normalized, remainderVertex_plane_primary]
  decide +kernel

-- A retained divisor contributes its actual degree after the unit correction.
example : remainderVertex .plane (primary 3) (planeCoefficientVertex (primary 3))
    10 2 (Fin 2) (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0
      ![.unit, .hyperplane] = 9 := by
  rw [remainderVertex_onePsi_plane_zero_normalized, remainderVertex_plane_primary]
  decide +kernel

-- Dimension vanishing is retained at the smallest point-count boundary.
example : remainderVertex .plane (primary 1) (planeCoefficientVertex (primary 1))
    0 2 (Fin 1) (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0 ![.unit] = 0 := by
  rw [remainderVertex_onePsi_plane_zero_normalized]
  decide +kernel

-- Repeated hyperplanes give two distinct divisor-product corrections.
example : remainderVertex .plane (primary 3) (planeCoefficientVertex (primary 3))
    9 2 (Fin 3) (by norm_num [StableArity]) (Pi.single 1 1) inferInstance 0
      ![.hyperplane, .hyperplane, .hyperplane] = 6 := by
  rw [remainderVertex_onePsi_plane_zero_normalized]
  decide +kernel

-- A primary unit with a point descendant invokes string, rather than the
-- different correction for a unit carrying psi.
example : remainderVertex .plane (primary 1) (planeCoefficientVertex (primary 1))
    3 2 (Fin 2) (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0
      ![.point, .unit] = 1 := by
  rw [remainderVertex_onePsi_plane_zero_normalized]
  decide +kernel

-- Moving the psi to a different state changes the coefficient's actual query.
example : remainderVertex .plane (hyperplane 1) (planeCoefficientVertex (hyperplane 1))
    2 2 (Fin 2) (by norm_num [StableArity]) (Pi.single 1 1) inferInstance 0
      ![.point, .hyperplane] = 1 := by
  rw [remainderVertex_onePsi_plane_zero_normalized]
  decide +kernel

example : remainderVertex .plane (hyperplane 1) (planeCoefficientVertex (hyperplane 1))
    2 2 (Fin 2) (by norm_num [StableArity]) (Pi.single 0 1) inferInstance 0
      ![.point, .hyperplane] = 0 := by
  rw [remainderVertex_onePsi_plane_zero_normalized]
  decide +kernel

end AxiomaticGWTest.Surfaces.GenusTwoZeroRemainder

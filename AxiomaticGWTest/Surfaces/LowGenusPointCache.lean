/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.LowGenusPointCache

/-! # Boundary and full-query consumers for primary-backed ancestor recursion -/

@[expose] public section

namespace AxiomaticGWTest.Surfaces.LowGenusPointCache
open AxiomaticGW

/-- Class zero retains the classical triple even with an unrelated point backend. -/
theorem rational_classical :
    SurfaceLowGenusPointCache.rationalPrimary .plane (fun _ ↦ 37) 0
      {.unit, .hyperplane, .hyperplane} = 1 := by decide +kernel

/-- The two elliptic degree-zero divisor constants are independent of the backend. -/
theorem elliptic_classical :
    SurfaceLowGenusPointCache.ellipticPrimary .hirzebruchOne (fun _ ↦ 37) 0
      {.hyperplane} = -1 / 8 ∧
    SurfaceLowGenusPointCache.ellipticPrimary .hirzebruchOne (fun _ ↦ 37) 0
      {.exceptional 0} = -1 / 24 := by decide +kernel

/-- The rational point count is still energy minus one. -/
theorem rational_count_guard :
    SurfaceLowGenusPointCache.rationalPrimary .plane (fun _ ↦ 37) ![1] {.point} = 0 := by
  decide +kernel

/-- The elliptic point count is still the full energy. -/
theorem elliptic_count_guard :
    SurfaceLowGenusPointCache.ellipticPrimary .plane (fun _ ↦ 37) ![1]
      {.point, .point} = 0 := by decide +kernel

/-- An exceptional divisor retains its negative self-intersection factor. -/
theorem signed_exceptional_factor :
    SurfaceLowGenusPointCache.rationalPrimary .hirzebruchOne (fun _ ↦ 7) ![1, 0]
      {.exceptional 0} = -7 := by decide +kernel

/-- Zero-product pruning applies at the correct point count and needs no value assumption. -/
theorem primary_unit_zero :
    SurfaceLowGenusPointCache.rationalPrimary .plane (fun _ ↦ 37) ![1]
      {.unit, .point, .point} = 0 := by decide +kernel

/-- Equal-energy full classes must remain distinguishable to a supplied backend. -/
theorem full_curve_keys :
    SurfaceLowGenusPointCache.rationalPrimary .hirzebruchOne
      (fun beta ↦ if beta 1 = 2 then 7 else 11) ![2, 2]
      (Multiset.replicate 5 .point) = 7 ∧
    SurfaceLowGenusPointCache.rationalPrimary .hirzebruchOne
      (fun beta ↦ if beta 1 = 2 then 7 else 11) ![6, 0]
      (Multiset.replicate 5 .point) = 11 := by decide +kernel

/-- Equality covers insufficient rational fuel as well as the public sufficient bound. -/
theorem arbitrary_rational_fuel (X : SurfaceTarget) (v₀ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (fuel : ℕ) (q : SurfaceAncestorKey X) :
    SurfaceLowGenusPointCache.rationalFuel X v₀ fuel q =
      SurfaceGenusZero.ancestorValueFuel X fuel q :=
  congrFun (SurfaceLowGenusPointCache.rationalFuel_eq X v₀ h₀ fuel) q

/-- The elliptic comparison places no genus, cotangent or dimension restriction on the query. -/
theorem arbitrary_elliptic_fuel (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (h₁ : v₁ = SurfaceGenusOne.pointValue X)
    (fuel : ℕ) (q : SurfaceAncestorKey X) :
    SurfaceLowGenusPointCache.ellipticFuel X v₀ v₁ fuel q =
      SurfaceGenusOne.ancestorValueFuel X fuel q :=
  congrFun (SurfaceLowGenusPointCache.ellipticFuel_eq X v₀ v₁ h₀ h₁ fuel) q

/-- Unsupported genera retain the original zero branch without evaluating point values. -/
theorem unsupported_genus :
    let q : SurfaceAncestorKey .hirzebruchOne :=
      ⟨2, ![1, 1], ([] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩
    SurfaceLowGenusPointCache.rationalFuel .hirzebruchOne (fun _ ↦ 37) 4 q = 0 ∧
    SurfaceLowGenusPointCache.ellipticFuel .hirzebruchOne
      (fun _ ↦ 37) (fun _ ↦ 41) 4 q = 0 := by decide +kernel

end AxiomaticGWTest.Surfaces.LowGenusPointCache

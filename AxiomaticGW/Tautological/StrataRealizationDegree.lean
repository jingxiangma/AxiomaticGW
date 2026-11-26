/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.StrataRealization

/-!
# Homogeneous realization and the connected degree-zero projection

The existing basis-degree condition extends to its rational span. The
connected degree-zero projection therefore annihilates the realization of
every positive-codimension formal expression. These statements require no
product on the strata module and no geometric identification of its classes.
-/

@[expose] public section

namespace AxiomaticGW

universe u

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {g : ℕ} {S : Type} [Fintype S]

attribute [local instance] strataRealizationModule

namespace StrataRealization

/-- The existing basis-degree requirement extends to each full homogeneous submodule. -/
theorem map_mem_degree (A : StrataRealization C g S) {d : ℕ}
    {x : StrataModule g S} (hx : x ∈ StrataModule.degree d) :
    A.map x ∈ (C.H g S).degree d := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    simpa only [hs] using A.map_basis_degree s
  | zero =>
    rw [map_zero]
    exact ((C.H g S).degree d).zero_mem
  | add x y _ _ hx hy =>
    rw [map_add]
    exact ((C.H g S).degree d).add_mem hx hy
  | smul q x _ hx =>
    rw [map_smul]
    change (algebraMap ℚ R q) • A.map x ∈ (C.H g S).degree d
    exact ((C.H g S).degree d).smul_mem _ hx

end StrataRealization

namespace ConnectedDegreeZero

/-- A positive homogeneous class has zero connected degree-zero projection. -/
theorem scalar_eq_zero_of_mem_degree (D : ConnectedDegreeZero C) (h : StableArity g S)
    {d : ℕ} {x : C.H g S} (hd : d ≠ 0) (hx : x ∈ (C.H g S).degree d) :
    D.scalar g S h x = 0 := by
  have hz : EvenGradedAlgebra.projZeroAlgHom (C.H g S) x = 0 := by
    apply Subtype.ext
    change (DirectSum.decompose (C.H g S).degree x 0 : C.H g S) = 0
    exact DirectSum.decompose_of_mem_ne _ hx hd
  change (D.degreeZeroEquiv g S h).toAlgHom
    (EvenGradedAlgebra.projZeroAlgHom (C.H g S) x) = 0
  rw [hz, map_zero]

/-- Positive-degree formal strata expressions vanish after realization and scalar projection. -/
theorem scalar_map_eq_zero_of_mem_degree (D : ConnectedDegreeZero C)
    (A : StrataRealization C g S) (h : StableArity g S)
    {d : ℕ} {x : StrataModule g S} (hd : d ≠ 0) (hx : x ∈ StrataModule.degree d) :
    D.scalar g S h (A.map x) = 0 :=
  D.scalar_eq_zero_of_mem_degree h hd (A.map_mem_degree hx)

end ConnectedDegreeZero
end AxiomaticGW

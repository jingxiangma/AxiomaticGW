/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupQueryCertificate

/-!
# The four one-marking genus-two descendant requests in the exceptional class of F1

In effective coordinates (E,F), the class E=(1,0) has anticanonical energy one.
The dimension equation for one marking requires codimension plus psi power three.
Every canonical state of F1 with energy at most one has plane degree zero, so
the original boundary suffices for evaluating the full descendant reduction.
-/

@[expose] public section

namespace AxiomaticGW.BlowupF1ExceptionalOneMarkingRequest
open SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupDescendants

/-- The effective class of the exceptional curve. -/
def exceptional : SurfaceTarget.hirzebruchOne.Curve := ![1, 0]

/-- The four possible basis insertions with the powers fixed by dimension. -/
def requests : Fin 4 → SurfaceQuery .hirzebruchOne :=
  ![⟨2, exceptional, [⟨.unit, 3⟩]⟩,
    ⟨2, exceptional, [⟨.hyperplane, 2⟩]⟩,
    ⟨2, exceptional, [⟨.exceptional 0, 2⟩]⟩,
    ⟨2, exceptional, [⟨.point, 1⟩]⟩]

/-- The four queries retain the full class and satisfy the stable dimension condition. -/
theorem requests_domain (j : Fin 4) :
    (requests j).genus = 2 ∧ (requests j).beta = exceptional ∧
      (requests j).insertions.length = 1 ∧ (requests j).DimensionCompatible ∧
      (requests j).GeometricDomain := by
  fin_cases j <;> decide +kernel

/-- The chosen energy bound covers each full query. -/
theorem requests_energy (j : Fin 4) :
    SurfaceTarget.hirzebruchOne.effective.energy (requests j).beta ≤ 1 := by
  fin_cases j <;> decide +kernel

/-- The existing plane-degree-zero canonical values on F1. -/
def boundary (s : State .hirzebruchOne) : ℚ :=
  SurfaceGenusTwoBlowupBoundary.value s.1 s.2

/-- On F1, energy at most one forces the fiber coordinate to vanish. -/
theorem boundary_eq_values (s : State .hirzebruchOne)
    (hs : SurfaceTarget.hirzebruchOne.effective.energy s.1 ≤ 1) :
    boundary s = SurfaceGenusTwoBlowupRecursion.values 0 s := by
  have he : s.1 0 + 2 * s.1 1 ≤ 1 := by
    change (∑ k : Fin 2, (![1, 2] : Fin 2 → ℕ) k * s.1 k) ≤ 1 at hs
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Nat.one_mul] using hs
  have hd : SurfaceTarget.hirzebruchOne.planeDegree s.1 = 0 := by
    change s.1 1 = 0
    omega
  exact (SurfaceGenusTwoBlowupRecursion.values_boundary 0 s hd).symm

/-- The complete descendant calculation with the determined canonical terminals. -/
def computed (j : Fin 4) : Option ℚ := queryValueWith? boundary (requests j)

/-- Substituting the boundary gives the original blowup descendant evaluator. -/
theorem computed_eq_reconstruction (j : Fin 4) :
    computed j = queryValue? 0 (requests j) :=
  queryValueWith?_eq_of_table 0 1 boundary boundary_eq_values (requests j) (requests_energy j)

/-- The point request is the canonical first-descendant P state at E. -/
theorem point_request_eq : requests 3 = (Family.point).query exceptional := by
  decide +kernel

end AxiomaticGW.BlowupF1ExceptionalOneMarkingRequest

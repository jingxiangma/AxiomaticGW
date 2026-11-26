/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneLineBoundaryClass
public import AxiomaticGW.Surfaces.GenusZeroRecursion
public import AxiomaticGW.Tautological.RationalTailPullback

/-!
# The separating boundary carrying the first point and the added unit

On this section the four-point main factor retains the basis state dual to
the three-point degree-zero tail. The positive-degree tail vanishes for every
node state. The full splitting identity therefore uses just the held class,
even when all other four-point coefficients are left arbitrary.
-/

@[expose] public section
namespace AxiomaticGW.GKM.PlaneLineBoundaryClass
open PlaneLineBoundaryData TensorProduct
noncomputable section

/-- Three ordinary primary invariants, in the node-state order of the native packet. -/
def tail (beta : SurfaceTarget.plane.Curve) (a : SurfaceBasisLabel .plane) : ℚ :=
  SurfaceGenusZero.primaryValue .plane beta {.point, .unit, a}

/-- All three states at both effective tail degrees agree with the original reconstruction. -/
theorem tail_replay : ∀ i : Fin 3,
    tail0 i = tail 0 (![.unit, .hyperplane, .point] i) ∧
    tail1 i = tail ![1] (![.unit, .hyperplane, .point] i) := by decide +kernel

/-- Contract the complete inverse metric over every ordered splitting of the actual line.
The other four-point coefficients cancel for every choice in a rational module. -/
theorem tail_contraction {V : Type*} [AddCommGroup V] [Module ℚ V]
    (v : SurfaceTarget.plane.Curve → SurfaceBasisLabel .plane → V) :
    (∑ b ∈ SurfaceTarget.plane.splittings ![1], ∑ a : SurfaceBasisLabel .plane,
      (a.inverseWeight * tail b.1 a) • v b.2 a.dual) = v ![1] .point := by
  have hsplit : SurfaceTarget.plane.splittings ![1] =
      {(0, ![1]), (![1], 0)} := by decide +kernel
  have he : ((0, ![1]) : SurfaceTarget.plane.Curve × SurfaceTarget.plane.Curve) ≠
      (![1], 0) := by decide +kernel
  rw [hsplit, Finset.sum_pair he, SurfaceBasisLabel.sum_labels, SurfaceBasisLabel.sum_labels]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, SurfaceBasisLabel.inverseWeight,
    SurfaceBasisLabel.dual, one_mul]
  have h0 := tail_replay 0
  have h1 := tail_replay 1
  have h2 := tail_replay 2
  change (1 : ℚ) = tail 0 .unit ∧ 0 = tail ![1] .unit at h0
  change (0 : ℚ) = tail 0 .hyperplane ∧ 0 = tail ![1] .hyperplane at h1
  change (0 : ℚ) = tail 0 .point ∧ 0 = tail ![1] .point at h2
  rw [← h0.1, ← h1.1, ← h2.1, ← h0.2, ← h1.2, ← h2.2]
  simp only [one_smul, zero_smul, add_zero]

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- Restriction of the five-point packet to the 15|234 boundary equals the full
degree-split inverse-metric contraction. The main factor has the order node, 2, 3, 4.
Only its single surviving coefficient is fixed to the actual four-point packet. -/
theorem map_section (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N) (Htail : PsiBoundaryExpansion.TailForgetCompatible C)
    (hbase : (WDVV.expression 0).Compatible A F N)
    (hup : ∀ z ∈ (WDVV.expression 0).addMarkings 1, z.Compatible A F N)
    (v : SurfaceTarget.plane.Curve → SurfaceBasisLabel .plane → C.H 0 (Fin 4))
    (hmain : v ![1] .point = (A 0 (Fin 4)).map baseClass) :
    PsiBoundaryExpansion.tailRestriction C WDVV.stableArity 0
        ((A 0 (Option (Fin 4))).map (StrataModule.relabel labels unitClass)) =
      C.rename 0 (Fin 4) (Option {t : Fin 4 // t ≠ 0}) WDVV.stableArity
        (PsiBoundaryExpansion.tailMainStable WDVV.stableArity 0) (Equiv.optionSubtypeNe 0).symm
        (∑ b ∈ SurfaceTarget.plane.splittings ![1], ∑ a : SurfaceBasisLabel .plane,
          (a.inverseWeight * tail b.1 a) • v b.2 a.dual) ⊗ₜ[R] 1 := by
  rw [tail_contraction, hmain, map_unit A F N H hbase hup]
  exact Htail 0 (Fin 4) WDVV.stableArity 0 _

end
end AxiomaticGW.GKM.PlaneLineBoundaryClass

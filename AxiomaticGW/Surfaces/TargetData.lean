/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Cohomology
public import AxiomaticGW.Surfaces.CurveClasses

/-!
# Algebraic target data for the three fixed surfaces

The actual divisor subspace pairs with the effective curve coordinates. The
class `3H - ∑ Eᵢ` recovers the anticanonical degree, and the genus-one parameters
are `(r+3)/24` and `D ↦ -∫ D c₁ / 24`. These are proved algebraic formulas.
Identifying this model with geometric cohomology, its class with `c₁(TX)`, and
these parameters with GW initial values remains a separate geometric input.
-/

@[expose] public section

namespace AxiomaticGW

namespace SurfaceCohomology

/-- The hyperplane as an actual codimension-one state. -/
def hyperplaneDivisor (r : ℕ) : degree r 1 :=
  ⟨hyperplane r, hyperplane_mem_degree_one r⟩

/-- An exceptional divisor as an actual codimension-one state. -/
def exceptionalDivisor (r : ℕ) (i : Fin r) : degree r 1 :=
  ⟨exceptional r i, exceptional_mem_degree_one r i⟩

/-- The algebraic anticanonical class `3H - ∑ Eᵢ`. -/
def firstChernDivisor (r : ℕ) : degree r 1 :=
  (3 : ℚ) • hyperplaneDivisor r - ∑ i, exceptionalDivisor r i

/-- The anticanonical state has no scalar or point component; its divisor
coordinates are three for the hyperplane and minus one for each exception. -/
theorem firstChernDivisor_val (r : ℕ) :
    (firstChernDivisor r).val = (0, (3, fun _ ↦ -1), 0) := by
  apply (coordinates r).injective
  simp only [firstChernDivisor, Submodule.coe_sub, Submodule.coe_smul,
    Submodule.coe_sum, hyperplaneDivisor, exceptionalDivisor, map_sub, map_smul, map_sum]
  change ((3 : ℚ) • (0, (1, 0), 0) -
    ∑ i : Fin r, (0, (0, Pi.single i 1), 0) : ℚ × (ℚ × (Fin r → ℚ)) × ℚ) =
      (0, (3, fun _ ↦ -1), 0)
  ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.sub_apply, Pi.smul_apply,
    Pi.zero_apply, smul_eq_mul, mul_zero, mul_one, Finset.sum_const_zero,
    sub_zero, sub_self, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, zero_sub]

/-- Pairing with the anticanonical class reads the signed divisor coordinates. -/
theorem tracePairing_firstChernDivisor (r : ℕ) (x : SurfaceCohomology r) :
    tracePairing (counit r) x (firstChernDivisor r).val =
      3 * x.2.1.1 + ∑ i, x.2.1.2 i := by
  simp only [firstChernDivisor, Submodule.coe_sub, Submodule.coe_smul,
    Submodule.coe_sum, hyperplaneDivisor, exceptionalDivisor, map_sub,
    map_smul, map_sum, tracePairing_counit_hyperplane,
    tracePairing_counit_exceptional, smul_eq_mul, Finset.sum_neg_distrib,
    sub_neg_eq_add]

end SurfaceCohomology

namespace SurfaceTarget

/-- Divisors in the fixed target's graded cohomology model. -/
abbrev Divisor (X : SurfaceTarget) := SurfaceCohomology.degree X.blowups 1

private theorem divisorIntersections_zero (X : SurfaceTarget) :
    X.divisorIntersections 0 = 0 := by
  cases X <;> decide

private theorem divisorIntersections_add (X : SurfaceTarget) (a b : X.Curve) :
    X.divisorIntersections (a + b) = X.divisorIntersections a + X.divisorIntersections b := by
  funext i
  simp only [divisorIntersections, latticeCoordinates_add, Pi.add_apply]
  split_ifs
  · rfl
  · exact neg_add _ _

/-- Divisor--curve intersection, linear in the actual divisor state and
additive in the full curve class. -/
def divisorPairing (X : SurfaceTarget) : X.Divisor →ₗ[ℚ] (X.Curve →+ ℚ) where
  toFun D :=
    { toFun beta := D.val.2.1.1 * (X.divisorIntersections beta 0 : ℚ) +
        ∑ i : Fin X.blowups, D.val.2.1.2 i * (X.divisorIntersections beta i.succ : ℚ)
      map_zero' := by
        rw [divisorIntersections_zero]
        simp only [Pi.zero_apply, Int.cast_zero, mul_zero, Finset.sum_const_zero,
          add_zero]
      map_add' a b := by
        rw [divisorIntersections_add]
        simp only [Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
        ring }
  map_add' D E := by
    apply AddMonoidHom.ext
    intro beta
    change (D.val.2.1.1 + E.val.2.1.1) * (X.divisorIntersections beta 0 : ℚ) +
        (∑ i, (D.val.2.1.2 i + E.val.2.1.2 i) *
          (X.divisorIntersections beta i.succ : ℚ)) =
      (D.val.2.1.1 * (X.divisorIntersections beta 0 : ℚ) +
        ∑ i, D.val.2.1.2 i * (X.divisorIntersections beta i.succ : ℚ)) +
      (E.val.2.1.1 * (X.divisorIntersections beta 0 : ℚ) +
        ∑ i, E.val.2.1.2 i * (X.divisorIntersections beta i.succ : ℚ))
    simp only [add_mul, Finset.sum_add_distrib]
    ring
  map_smul' c D := by
    apply AddMonoidHom.ext
    intro beta
    change (c * D.val.2.1.1) * (X.divisorIntersections beta 0 : ℚ) +
        (∑ i, (c * D.val.2.1.2 i) * (X.divisorIntersections beta i.succ : ℚ)) =
      c * (D.val.2.1.1 * (X.divisorIntersections beta 0 : ℚ) +
        ∑ i, D.val.2.1.2 i * (X.divisorIntersections beta i.succ : ℚ))
    simp only [mul_assoc, ← Finset.mul_sum, mul_add]

/-- Hyperplane evaluation agrees with the integer curve-intersection API. -/
theorem divisorPairing_hyperplane (X : SurfaceTarget) (beta : X.Curve) :
    X.divisorPairing (SurfaceCohomology.hyperplaneDivisor X.blowups) beta =
      (X.divisorIntersections beta 0 : ℚ) := by
  simp only [divisorPairing, LinearMap.coe_mk, AddHom.coe_mk,
    AddMonoidHom.coe_mk, SurfaceCohomology.hyperplaneDivisor,
    SurfaceCohomology.hyperplane, Pi.zero_apply, one_mul, zero_mul,
    Finset.sum_const_zero, add_zero]
  rfl

/-- Exceptional evaluation retains the negative self-intersection sign. -/
theorem divisorPairing_exceptional (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) :
    X.divisorPairing (SurfaceCohomology.exceptionalDivisor X.blowups i) beta =
      (X.divisorIntersections beta i.succ : ℚ) := by
  classical
  simp only [divisorPairing, LinearMap.coe_mk, AddHom.coe_mk,
    AddMonoidHom.coe_mk, SurfaceCohomology.exceptionalDivisor,
    SurfaceCohomology.exceptional, zero_mul, zero_add, Pi.single_apply,
    ite_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rfl

/-- Evaluating the divisor pairing on the anticanonical class recovers the
existing first-Chern degree homomorphism. -/
theorem divisorPairing_firstChernDivisor (X : SurfaceTarget) (beta : X.Curve) :
    X.divisorPairing (SurfaceCohomology.firstChernDivisor X.blowups) beta =
      (X.c1Degree beta : ℚ) := by
  simp only [SurfaceCohomology.firstChernDivisor, map_sub, map_smul, map_sum,
    AddMonoidHom.sub_apply, AddMonoidHom.smul_apply, AddMonoidHom.finsetSum_apply,
    smul_eq_mul, divisorPairing_hyperplane, divisorPairing_exceptional]
  rw [c1Degree_eq_intersection]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_sum]

/-- Algebraic genus-one unit-dilaton parameter. Its interpretation as
`χ(X)/24` requires the geometric Euler characteristic of the target. -/
def genusOneDilaton (X : SurfaceTarget) : ℚ :=
  ((X.blowups + 3 : ℕ) : ℚ) / 24

theorem genusOneDilaton_plane : plane.genusOneDilaton = 1 / 8 := by
  norm_num [genusOneDilaton, blowups]

theorem genusOneDilaton_hirzebruchOne : hirzebruchOne.genusOneDilaton = 1 / 6 := by
  norm_num [genusOneDilaton, blowups]

theorem genusOneDilaton_blowupTwo : blowupTwo.genusOneDilaton = 5 / 24 := by
  norm_num [genusOneDilaton, blowups]

/-- The actual cup-trace functional `D ↦ -∫ D c₁/24` on divisor states.
Identifying it with a geometric genus-one invariant is a separate input. -/
def genusOneDivisor (X : SurfaceTarget) : X.Divisor →ₗ[ℚ] ℚ :=
  ((-1 / 24 : ℚ) •
    ((tracePairing (SurfaceCohomology.counit X.blowups)).flip
      (SurfaceCohomology.firstChernDivisor X.blowups).val)).comp
        (SurfaceCohomology.degree X.blowups 1).subtype

theorem genusOneDivisor_apply (X : SurfaceTarget) (D : X.Divisor) :
    X.genusOneDivisor D =
      -SurfaceCohomology.counit X.blowups
        (D.val * (SurfaceCohomology.firstChernDivisor X.blowups).val) / 24 := by
  change (-1 / 24 : ℚ) * SurfaceCohomology.counit X.blowups
      (D.val * (SurfaceCohomology.firstChernDivisor X.blowups).val) = _
  ring

/-- The hyperplane's genus-one parameter is minus one eighth for all three targets. -/
theorem genusOneDivisor_hyperplane (X : SurfaceTarget) :
    X.genusOneDivisor (SurfaceCohomology.hyperplaneDivisor X.blowups) = -1 / 8 := by
  change (-1 / 24 : ℚ) *
    tracePairing (SurfaceCohomology.counit X.blowups)
      (SurfaceCohomology.hyperplane X.blowups)
      (SurfaceCohomology.firstChernDivisor X.blowups).val = -1 / 8
  rw [SurfaceCohomology.tracePairing_firstChernDivisor]
  norm_num [SurfaceCohomology.hyperplane]

/-- Each exceptional divisor's parameter is minus one twenty-fourth. -/
theorem genusOneDivisor_exceptional (X : SurfaceTarget) (i : Fin X.blowups) :
    X.genusOneDivisor (SurfaceCohomology.exceptionalDivisor X.blowups i) = -1 / 24 := by
  classical
  change (-1 / 24 : ℚ) *
    tracePairing (SurfaceCohomology.counit X.blowups)
      (SurfaceCohomology.exceptional X.blowups i)
      (SurfaceCohomology.firstChernDivisor X.blowups).val = -1 / 24
  rw [SurfaceCohomology.tracePairing_firstChernDivisor]
  simp only [SurfaceCohomology.exceptional, mul_zero, zero_add, Pi.single_apply,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, mul_one]

end SurfaceTarget

end AxiomaticGW

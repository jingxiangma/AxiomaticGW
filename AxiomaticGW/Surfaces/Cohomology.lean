/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.CohFT.Basic
public import AxiomaticGW.Frobenius.Constructions
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Algebraic cohomology models of plane blowups

The carrier has coordinates for the unit, the hyperplane, `r` exceptional
classes, and the point class. Its product models rational even cohomology of
a plane blown up at `r` points. This constructs an algebraic model only; it
does not identify it with geometric cohomology or construct GW invariants.
The three fixed reconstruction targets use `r = 0, 1, 2`.
-/

@[expose] public section

namespace AxiomaticGW

/-- A separate carrier keeps the surface cup product distinct from the
componentwise product on the coordinate vector space. -/
def SurfaceCohomology (r : ℕ) := ℚ × (ℚ × (Fin r → ℚ)) × ℚ

namespace SurfaceCohomology

open DirectSum

instance (r : ℕ) : AddCommGroup (SurfaceCohomology r) :=
  inferInstanceAs (AddCommGroup (ℚ × (ℚ × (Fin r → ℚ)) × ℚ))

instance (r : ℕ) : Module ℚ (SurfaceCohomology r) :=
  inferInstanceAs (Module ℚ (ℚ × (ℚ × (Fin r → ℚ)) × ℚ))

instance (r : ℕ) : Module.Free ℚ (SurfaceCohomology r) :=
  inferInstanceAs (Module.Free ℚ (ℚ × (ℚ × (Fin r → ℚ)) × ℚ))

instance (r : ℕ) : Module.Finite ℚ (SurfaceCohomology r) :=
  inferInstanceAs (Module.Finite ℚ (ℚ × (ℚ × (Fin r → ℚ)) × ℚ))

/-- Coordinates of a surface state, ordered as unit, divisors, and point. -/
def coordinates (r : ℕ) :
    SurfaceCohomology r ≃ₗ[ℚ] ℚ × (ℚ × (Fin r → ℚ)) × ℚ :=
  LinearEquiv.refl ℚ _

/-- Intersection form on the divisor coordinates: the hyperplane has square
one and each exceptional class has square minus one. -/
def divisorIntersection {r : ℕ} (x y : ℚ × (Fin r → ℚ)) : ℚ :=
  x.1 * y.1 - ∑ i, x.2 i * y.2 i

theorem divisorIntersection_comm {r : ℕ} (x y : ℚ × (Fin r → ℚ)) :
    divisorIntersection x y = divisorIntersection y x := by
  simp only [divisorIntersection, mul_comm]

theorem divisorIntersection_add_left {r : ℕ} (x y z : ℚ × (Fin r → ℚ)) :
    divisorIntersection (x + y) z = divisorIntersection x z + divisorIntersection y z := by
  simp only [divisorIntersection, Prod.fst_add, Prod.snd_add, Pi.add_apply,
    add_mul, Finset.sum_add_distrib]
  ring

theorem divisorIntersection_add_right {r : ℕ} (x y z : ℚ × (Fin r → ℚ)) :
    divisorIntersection x (y + z) = divisorIntersection x y + divisorIntersection x z := by
  rw [divisorIntersection_comm x (y + z), divisorIntersection_add_left,
    divisorIntersection_comm y x, divisorIntersection_comm z x]

theorem divisorIntersection_smul_left {r : ℕ} (c : ℚ) (x y : ℚ × (Fin r → ℚ)) :
    divisorIntersection (c • x) y = c * divisorIntersection x y := by
  simp only [divisorIntersection, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
    smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

theorem divisorIntersection_smul_right {r : ℕ} (c : ℚ) (x y : ℚ × (Fin r → ℚ)) :
    divisorIntersection x (c • y) = c * divisorIntersection x y := by
  rw [divisorIntersection_comm x (c • y), divisorIntersection_smul_left,
    divisorIntersection_comm y x]

/-- The surface cup product in unit/divisor/point coordinates. -/
def cupProduct {r : ℕ} (x y : SurfaceCohomology r) : SurfaceCohomology r :=
  (x.1 * y.1, x.1 • y.2.1 + y.1 • x.2.1,
    x.1 * y.2.2 + y.1 * x.2.2 + divisorIntersection x.2.1 y.2.1)

theorem cupProduct_assoc {r : ℕ} (x y z : SurfaceCohomology r) :
    cupProduct (cupProduct x y) z = cupProduct x (cupProduct y z) := by
  apply Prod.ext
  · dsimp only [cupProduct]
    ring
  apply Prod.ext
  · apply Prod.ext
    · dsimp only [cupProduct, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      ring
    · funext i
      dsimp only [cupProduct, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      ring
  · dsimp only [cupProduct]
    rw [divisorIntersection_add_left, divisorIntersection_add_right,
      divisorIntersection_smul_left, divisorIntersection_smul_left,
      divisorIntersection_smul_right, divisorIntersection_smul_right]
    ring

theorem cupProduct_comm {r : ℕ} (x y : SurfaceCohomology r) :
    cupProduct x y = cupProduct y x := by
  dsimp only [cupProduct]
  rw [divisorIntersection_comm x.2.1 y.2.1]
  congr 1
  · ring
  · congr 1
    · exact add_comm _ _
    · ring

instance (r : ℕ) : CommRing (SurfaceCohomology r) where
  __ := (inferInstance : AddCommGroup (SurfaceCohomology r))
  mul := cupProduct
  one := (1, 0, 0)
  mul_assoc := cupProduct_assoc
  mul_comm := cupProduct_comm
  one_mul x := by
    change cupProduct (1, 0, 0) x = x
    simp only [cupProduct, one_mul, one_smul, smul_zero, add_zero,
      mul_zero, divisorIntersection, Prod.fst_zero, Prod.snd_zero,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_self]
    rfl
  mul_one x := by
    change cupProduct x (1, 0, 0) = x
    rw [cupProduct_comm]
    simp only [cupProduct, one_mul, one_smul, smul_zero, add_zero,
      mul_zero, divisorIntersection, Prod.fst_zero, Prod.snd_zero,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_self]
    rfl
  zero_mul x := by
    change cupProduct (0, 0, 0) x = 0
    simp only [cupProduct, zero_mul, zero_smul, smul_zero, add_zero,
      mul_zero, divisorIntersection, Prod.fst_zero, Prod.snd_zero,
      Pi.zero_apply, Finset.sum_const_zero, sub_self]
    rfl
  mul_zero x := by
    change cupProduct x (0, 0, 0) = 0
    rw [cupProduct_comm]
    simp only [cupProduct, zero_mul, zero_smul, smul_zero, add_zero,
      mul_zero, divisorIntersection, Prod.fst_zero, Prod.snd_zero,
      Pi.zero_apply, Finset.sum_const_zero, sub_self]
    rfl
  left_distrib x y z := by
    change cupProduct x (y + z) = cupProduct x y + cupProduct x z
    apply Prod.ext
    · change x.1 * (y.1 + z.1) = x.1 * y.1 + x.1 * z.1
      ring
    apply Prod.ext
    · change x.1 • (y.2.1 + z.2.1) + (y.1 + z.1) • x.2.1 =
        (x.1 • y.2.1 + y.1 • x.2.1) + (x.1 • z.2.1 + z.1 • x.2.1)
      rw [smul_add, add_smul]
      abel
    · change x.1 * (y.2.2 + z.2.2) + (y.1 + z.1) * x.2.2 +
          divisorIntersection x.2.1 (y.2.1 + z.2.1) =
        (x.1 * y.2.2 + y.1 * x.2.2 + divisorIntersection x.2.1 y.2.1) +
        (x.1 * z.2.2 + z.1 * x.2.2 + divisorIntersection x.2.1 z.2.1)
      rw [divisorIntersection_add_right]
      ring
  right_distrib x y z := by
    change cupProduct (x + y) z = cupProduct x z + cupProduct y z
    apply Prod.ext
    · change (x.1 + y.1) * z.1 = x.1 * z.1 + y.1 * z.1
      ring
    apply Prod.ext
    · change (x.1 + y.1) • z.2.1 + z.1 • (x.2.1 + y.2.1) =
        (x.1 • z.2.1 + z.1 • x.2.1) + (y.1 • z.2.1 + z.1 • y.2.1)
      rw [add_smul, smul_add]
      abel
    · change (x.1 + y.1) * z.2.2 + z.1 * (x.2.2 + y.2.2) +
          divisorIntersection (x.2.1 + y.2.1) z.2.1 =
        (x.1 * z.2.2 + z.1 * x.2.2 + divisorIntersection x.2.1 z.2.1) +
        (y.1 * z.2.2 + z.1 * y.2.2 + divisorIntersection y.2.1 z.2.1)
      rw [divisorIntersection_add_left]
      ring

/-- The unit in the explicit scalar/divisor/point coordinates. -/
theorem one_coordinates (r : ℕ) : (1 : SurfaceCohomology r) = (1, 0, 0) := rfl

instance (r : ℕ) : Algebra ℚ (SurfaceCohomology r) :=
  Algebra.ofModule
    (fun c x y ↦ by
      change cupProduct (c • x) y = c • cupProduct x y
      apply Prod.ext
      · change (c * x.1) * y.1 = c * (x.1 * y.1)
        ring
      apply Prod.ext
      · change (c * x.1) • y.2.1 + y.1 • (c • x.2.1) =
          c • (x.1 • y.2.1 + y.1 • x.2.1)
        simp only [smul_add, smul_smul]
        rw [mul_comm y.1 c]
      · change (c * x.1) * y.2.2 + y.1 * (c * x.2.2) +
          divisorIntersection (c • x.2.1) y.2.1 =
          c * (x.1 * y.2.2 + y.1 * x.2.2 + divisorIntersection x.2.1 y.2.1)
        rw [divisorIntersection_smul_left]
        ring)
    (fun c x y ↦ by
      change cupProduct x (c • y) = c • cupProduct x y
      rw [cupProduct_comm x (c • y)]
      apply Prod.ext
      · change (c * y.1) * x.1 = c * (x.1 * y.1)
        ring
      apply Prod.ext
      · change (c * y.1) • x.2.1 + x.1 • (c • y.2.1) =
          c • (x.1 • y.2.1 + y.1 • x.2.1)
        simp only [smul_add, smul_smul]
        rw [mul_comm x.1 c, add_comm]
      · change (c * y.1) * x.2.2 + x.1 * (c * y.2.2) +
          divisorIntersection (c • y.2.1) x.2.1 =
          c * (x.1 * y.2.2 + y.1 * x.2.2 + divisorIntersection x.2.1 y.2.1)
        rw [divisorIntersection_smul_left, divisorIntersection_comm y.2.1 x.2.1]
        ring)

/-- The pullback of the plane hyperplane class. -/
def hyperplane (r : ℕ) : SurfaceCohomology r := (0, (1, 0), 0)

/-- The class of one exceptional divisor. -/
def exceptional (r : ℕ) (i : Fin r) : SurfaceCohomology r :=
  (0, (0, Pi.single i 1), 0)

/-- The normalized class of a point. -/
def point (r : ℕ) : SurfaceCohomology r := (0, 0, 1)

/-- The hyperplane intersects itself in one point. -/
theorem hyperplane_mul_hyperplane (r : ℕ) : hyperplane r * hyperplane r = point r := by
  change cupProduct (0, (1, 0), 0) (0, (1, 0), 0) = (0, 0, 1)
  simp only [cupProduct, zero_mul, zero_smul, add_zero, divisorIntersection,
    one_mul, Pi.zero_apply, Finset.sum_const_zero, sub_zero, zero_add]

/-- A pulled-back hyperplane has zero intersection with an exceptional divisor. -/
theorem hyperplane_mul_exceptional (r : ℕ) (i : Fin r) :
    hyperplane r * exceptional r i = 0 := by
  change cupProduct (0, (1, 0), 0) (0, (0, Pi.single i 1), 0) = 0
  simp only [cupProduct, zero_mul, zero_smul, add_zero, divisorIntersection,
    mul_zero, Pi.zero_apply, Finset.sum_const_zero, sub_self]
  rfl

/-- Distinct exceptional divisors are disjoint, and each has square minus
the point class. -/
theorem exceptional_mul_exceptional (r : ℕ) (i j : Fin r) :
    exceptional r i * exceptional r j = if i = j then -point r else 0 := by
  classical
  change cupProduct (0, (0, Pi.single i 1), 0) (0, (0, Pi.single j 1), 0) = _
  simp only [cupProduct, zero_mul, zero_smul, add_zero, divisorIntersection,
    Pi.single_apply, ite_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, zero_sub, zero_add]
  split_ifs with hij
  · subst j
    rfl
  · change (0, 0, -(0 : ℚ)) = (0, 0, (0 : ℚ))
    rw [neg_zero]

/-- A point class times a divisor has degree above the surface dimension. -/
theorem point_mul_hyperplane (r : ℕ) : point r * hyperplane r = 0 := by
  change cupProduct (0, 0, 1) (0, (1, 0), 0) = 0
  simp only [cupProduct, zero_mul, zero_smul, add_zero, divisorIntersection,
    Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, Finset.sum_const_zero, sub_self]
  rfl

theorem point_mul_exceptional (r : ℕ) (i : Fin r) : point r * exceptional r i = 0 := by
  change cupProduct (0, 0, 1) (0, (0, Pi.single i 1), 0) = 0
  simp only [cupProduct, zero_mul, zero_smul, add_zero, divisorIntersection,
    Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, Finset.sum_const_zero, sub_self]
  rfl

theorem point_mul_point (r : ℕ) : point r * point r = 0 := by
  change cupProduct (0, 0, 1) (0, 0, 1) = 0
  simp only [cupProduct, zero_mul, zero_smul, add_zero, divisorIntersection,
    Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, Finset.sum_const_zero, sub_self]
  rfl

/-- Integration over the surface extracts the point coefficient. -/
def counit (r : ℕ) : SurfaceCohomology r →ₗ[ℚ] ℚ where
  toFun x := x.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem counit_point (r : ℕ) : counit r (point r) = 1 := rfl

/-- The trace pairing in coordinates; the two extreme degrees pair with
one another and the divisor block is the intersection form. -/
theorem tracePairing_counit_apply (r : ℕ) (x y : SurfaceCohomology r) :
    tracePairing (counit r) x y =
      x.1 * y.2.2 + y.1 * x.2.2 + divisorIntersection x.2.1 y.2.1 := rfl

theorem tracePairing_counit_point (r : ℕ) (x : SurfaceCohomology r) :
    tracePairing (counit r) x (point r) = x.1 := by
  rw [tracePairing_counit_apply]
  simp only [point, mul_one, zero_mul, add_zero, divisorIntersection,
    Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    sub_self]

theorem tracePairing_counit_one (r : ℕ) (x : SurfaceCohomology r) :
    tracePairing (counit r) x 1 = x.2.2 := by
  change x.1 * 0 + 1 * x.2.2 + divisorIntersection x.2.1 0 = x.2.2
  simp only [mul_zero, one_mul, zero_add, divisorIntersection,
    Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, Finset.sum_const_zero,
    sub_self, add_zero]

theorem tracePairing_counit_hyperplane (r : ℕ) (x : SurfaceCohomology r) :
    tracePairing (counit r) x (hyperplane r) = x.2.1.1 := by
  rw [tracePairing_counit_apply]
  simp only [hyperplane, mul_zero, zero_mul, zero_add, divisorIntersection,
    mul_one, Pi.zero_apply, Finset.sum_const_zero, sub_zero]

theorem tracePairing_counit_exceptional (r : ℕ) (x : SurfaceCohomology r) (i : Fin r) :
    tracePairing (counit r) x (exceptional r i) = -x.2.1.2 i := by
  classical
  rw [tracePairing_counit_apply]
  simp only [exceptional, mul_zero, zero_mul, zero_add, divisorIntersection,
    Pi.single_apply, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, zero_sub]

theorem tracePairing_counit_injective (r : ℕ) :
    Function.Injective (tracePairing (counit r)) := by
  intro x y h
  have hs := congrArg (fun f : Module.Dual ℚ (SurfaceCohomology r) ↦ f (point r)) h
  have hp := congrArg (fun f : Module.Dual ℚ (SurfaceCohomology r) ↦ f 1) h
  have hh := congrArg (fun f : Module.Dual ℚ (SurfaceCohomology r) ↦ f (hyperplane r)) h
  simp only [tracePairing_counit_point] at hs
  simp only [tracePairing_counit_one] at hp
  simp only [tracePairing_counit_hyperplane] at hh
  apply Prod.ext hs
  apply Prod.ext _ hp
  apply Prod.ext hh
  funext i
  have he := congrArg
    (fun f : Module.Dual ℚ (SurfaceCohomology r) ↦ f (exceptional r i)) h
  simpa only [tracePairing_counit_exceptional, neg_inj] using he

/-- The surface algebra is a commutative Frobenius algebra. -/
def frobenius (r : ℕ) : CommFrobeniusAlgebra ℚ (SurfaceCohomology r) where
  counit := counit r
  isPerfPair := by
    apply LinearMap.IsPerfPair.of_injective (tracePairing_counit_injective r)
    intro x y h
    apply tracePairing_counit_injective r
    ext z
    have hz := congrArg (fun f : Module.Dual ℚ (SurfaceCohomology r) ↦ f z) h
    simpa only [LinearMap.flip_apply, tracePairing_apply, mul_comm] using hz

/-- Explicit basis indexed by the unit, hyperplane, exceptional divisors,
and point, in that order of summands. -/
noncomputable def basis (r : ℕ) :
    Module.Basis (Unit ⊕ (Unit ⊕ Fin r) ⊕ Unit) ℚ (SurfaceCohomology r) :=
  ((Module.Basis.singleton Unit ℚ).prod
    (((Module.Basis.singleton Unit ℚ).prod (Pi.basisFun ℚ (Fin r))).prod
      (Module.Basis.singleton Unit ℚ))).map (coordinates r).symm

theorem basis_unit (r : ℕ) : basis r (Sum.inl ()) = 1 := by
  simp only [basis, Module.Basis.map_apply, Module.Basis.prod_apply,
    Function.comp_apply, Sum.elim_inl, LinearMap.inl_apply,
    Module.Basis.singleton_apply, coordinates]
  rfl

theorem basis_hyperplane (r : ℕ) :
    basis r (Sum.inr (Sum.inl (Sum.inl ()))) = hyperplane r := by
  simp only [basis, Module.Basis.map_apply, Module.Basis.prod_apply,
    Function.comp_apply, Sum.elim_inl, Sum.elim_inr, LinearMap.inl_apply,
    LinearMap.inr_apply, Module.Basis.singleton_apply, coordinates, hyperplane]
  rfl

theorem basis_exceptional (r : ℕ) (i : Fin r) :
    basis r (Sum.inr (Sum.inl (Sum.inr i))) = exceptional r i := by
  simp only [basis, Module.Basis.map_apply, Module.Basis.prod_apply,
    Function.comp_apply, Sum.elim_inl, Sum.elim_inr, LinearMap.inl_apply,
    LinearMap.inr_apply, Pi.basisFun_apply, coordinates, exceptional]
  rfl

theorem basis_point (r : ℕ) :
    basis r (Sum.inr (Sum.inr ())) = point r := by
  simp only [basis, Module.Basis.map_apply, Module.Basis.prod_apply,
    Function.comp_apply, Sum.elim_inr, LinearMap.inr_apply,
    Module.Basis.singleton_apply, coordinates, point]
  rfl

/-- The codimension grading: scalar, divisor, and point coordinates occupy
degrees zero, one, and two respectively. -/
def degree (r n : ℕ) : Submodule ℚ (SurfaceCohomology r) where
  carrier := {x | (n ≠ 0 → x.1 = 0) ∧ (n ≠ 1 → x.2.1 = 0) ∧
    (n ≠ 2 → x.2.2 = 0)}
  zero_mem' := ⟨fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩
  add_mem' := by
    intro x y hx hy
    refine ⟨fun h ↦ ?_, (fun h ↦ ?_), fun h ↦ ?_⟩
    · change x.1 + y.1 = 0
      rw [hx.1 h, hy.1 h, add_zero]
    · change x.2.1 + y.2.1 = 0
      rw [hx.2.1 h, hy.2.1 h, add_zero]
    · change x.2.2 + y.2.2 = 0
      rw [hx.2.2 h, hy.2.2 h, add_zero]
  smul_mem' := by
    intro c x hx
    refine ⟨fun h ↦ ?_, (fun h ↦ ?_), fun h ↦ ?_⟩
    · change c * x.1 = 0
      rw [hx.1 h, mul_zero]
    · change c • x.2.1 = 0
      rw [hx.2.1 h, smul_zero]
    · change c * x.2.2 = 0
      rw [hx.2.2 h, mul_zero]

/-- Homogeneous scalar component. -/
def scalarPart (r : ℕ) : SurfaceCohomology r →ₗ[ℚ] degree r 0 where
  toFun x := ⟨(x.1, 0, 0), (fun h ↦ (h rfl).elim), fun _ ↦ rfl, fun _ ↦ rfl⟩
  map_add' x y := by
    apply Subtype.ext
    change (x.1 + y.1, (0 : ℚ × (Fin r → ℚ)), (0 : ℚ)) =
      (x.1 + y.1, 0 + 0, 0 + 0)
    rw [add_zero, add_zero]
  map_smul' c x := by
    apply Subtype.ext
    change (c * x.1, (0 : ℚ × (Fin r → ℚ)), (0 : ℚ)) =
      (c * x.1, c • 0, c * 0)
    rw [smul_zero, mul_zero]

/-- Homogeneous divisor component. -/
def divisorPart (r : ℕ) : SurfaceCohomology r →ₗ[ℚ] degree r 1 where
  toFun x := ⟨(0, x.2.1, 0), (fun _ ↦ rfl), (fun h ↦ (h rfl).elim), fun _ ↦ rfl⟩
  map_add' x y := by
    apply Subtype.ext
    change ((0 : ℚ), x.2.1 + y.2.1, (0 : ℚ)) = (0 + 0, x.2.1 + y.2.1, 0 + 0)
    rw [add_zero]
  map_smul' c x := by
    apply Subtype.ext
    change ((0 : ℚ), c • x.2.1, (0 : ℚ)) = (c * 0, c • x.2.1, c * 0)
    rw [mul_zero]

/-- Homogeneous point component. -/
def pointPart (r : ℕ) : SurfaceCohomology r →ₗ[ℚ] degree r 2 where
  toFun x := ⟨(0, 0, x.2.2), (fun _ ↦ rfl), (fun _ ↦ rfl), fun h ↦ (h rfl).elim⟩
  map_add' x y := by
    apply Subtype.ext
    change ((0 : ℚ), (0 : ℚ × (Fin r → ℚ)), x.2.2 + y.2.2) =
      (0 + 0, 0 + 0, x.2.2 + y.2.2)
    rw [add_zero, add_zero]
  map_smul' c x := by
    apply Subtype.ext
    change ((0 : ℚ), (0 : ℚ × (Fin r → ℚ)), c * x.2.2) =
      (c * 0, c • 0, c * x.2.2)
    rw [mul_zero, smul_zero]

/-- Explicit decomposition into the three nonzero homogeneous summands. -/
def decompose (r : ℕ) : SurfaceCohomology r →+ ⨁ n, degree r n :=
  ((DirectSum.of (fun n ↦ ↥(degree r n)) 0).comp (scalarPart r).toAddMonoidHom +
    (DirectSum.of (fun n ↦ ↥(degree r n)) 1).comp (divisorPart r).toAddMonoidHom) +
    (DirectSum.of (fun n ↦ ↥(degree r n)) 2).comp (pointPart r).toAddMonoidHom

theorem decompose_apply (r : ℕ) (x : SurfaceCohomology r) :
    decompose r x =
      DirectSum.of (fun n ↦ ↥(degree r n)) 0 (scalarPart r x) +
        DirectSum.of (fun n ↦ ↥(degree r n)) 1 (divisorPart r x) +
        DirectSum.of (fun n ↦ ↥(degree r n)) 2 (pointPart r x) := rfl

theorem decompose_homogeneous (r n : ℕ) (x : degree r n) :
    decompose r x = DirectSum.of (fun n ↦ ↥(degree r n)) n x := by
  by_cases hn0 : n = 0
  · subst n
    have hd := x.property.2.1 (by decide : (0 : ℕ) ≠ 1)
    have hp := x.property.2.2 (by decide : (0 : ℕ) ≠ 2)
    have h0 : scalarPart r x = x := by
      apply Subtype.ext
      exact Prod.ext rfl (Prod.ext hd.symm hp.symm)
    have h1 : divisorPart r x = 0 := by
      apply Subtype.ext
      change (0, x.val.2.1, 0) = (0, 0, 0)
      rw [hd]
    have h2 : pointPart r x = 0 := by
      apply Subtype.ext
      change (0, 0, x.val.2.2) = (0, 0, 0)
      rw [hp]
    rw [decompose_apply, h0, h1, h2, map_zero, map_zero, add_zero, add_zero]
  by_cases hn1 : n = 1
  · subst n
    have hs := x.property.1 (by decide : (1 : ℕ) ≠ 0)
    have hp := x.property.2.2 (by decide : (1 : ℕ) ≠ 2)
    have h0 : scalarPart r x = 0 := by
      apply Subtype.ext
      change (x.val.1, 0, 0) = (0, 0, 0)
      rw [hs]
    have h1 : divisorPart r x = x := by
      apply Subtype.ext
      exact Prod.ext hs.symm (Prod.ext rfl hp.symm)
    have h2 : pointPart r x = 0 := by
      apply Subtype.ext
      change (0, 0, x.val.2.2) = (0, 0, 0)
      rw [hp]
    rw [decompose_apply, h0, h1, h2, map_zero, map_zero, zero_add, add_zero]
  by_cases hn2 : n = 2
  · subst n
    have hs := x.property.1 (by decide : (2 : ℕ) ≠ 0)
    have hd := x.property.2.1 (by decide : (2 : ℕ) ≠ 1)
    have h0 : scalarPart r x = 0 := by
      apply Subtype.ext
      change (x.val.1, 0, 0) = (0, 0, 0)
      rw [hs]
    have h1 : divisorPart r x = 0 := by
      apply Subtype.ext
      change (0, x.val.2.1, 0) = (0, 0, 0)
      rw [hd]
    have h2 : pointPart r x = x := by
      apply Subtype.ext
      exact Prod.ext hs.symm (Prod.ext hd.symm rfl)
    rw [decompose_apply, h0, h1, h2, map_zero, map_zero, zero_add, zero_add]
  · have hx : x = 0 := by
      apply Subtype.ext
      exact Prod.ext (x.property.1 hn0)
        (Prod.ext (x.property.2.1 hn1) (x.property.2.2 hn2))
    subst x
    rw [ZeroMemClass.coe_zero, map_zero, map_zero]

instance (r : ℕ) : DirectSum.Decomposition (degree r) where
  decompose' := decompose r
  left_inv x := by
    rw [decompose_apply, map_add, map_add, DirectSum.coeAddMonoidHom_of,
      DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
    change ((x.1, 0, 0) : SurfaceCohomology r) +
      ((0, x.2.1, 0) : SurfaceCohomology r) +
      ((0, 0, x.2.2) : SurfaceCohomology r) = x
    apply Prod.ext
    · change x.1 + 0 + 0 = x.1
      rw [add_zero, add_zero]
    apply Prod.ext
    · change (0 : ℚ × (Fin r → ℚ)) + x.2.1 + 0 = x.2.1
      rw [zero_add, add_zero]
    · change (0 : ℚ) + 0 + x.2.2 = x.2.2
      rw [zero_add, zero_add]
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero =>
        change decompose r 0 = 0
        exact map_zero (decompose r)
    | of n x =>
        rw [DirectSum.coeAddMonoidHom_of]
        exact decompose_homogeneous r n x
    | add x y hx hy =>
        change decompose r (DirectSum.coeAddMonoidHom (degree r) (x + y)) = x + y
        rw [map_add, map_add, hx, hy]

/-- The Poincare pairing has complementary codimension two. -/
theorem pairing_vanishes (r : ℕ) {p q : ℕ} {x y : SurfaceCohomology r}
    (hx : x ∈ degree r p) (hy : y ∈ degree r q) (hpq : p + q ≠ 2) :
    (frobenius r).pairing.form x y = 0 := by
  change x.1 * y.2.2 + y.1 * x.2.2 + divisorIntersection x.2.1 y.2.1 = 0
  have hfirst : x.1 * y.2.2 = 0 := by
    by_cases hp : p = 0
    · have hq : q ≠ 2 := by omega
      rw [hy.2.2 hq, mul_zero]
    · rw [hx.1 hp, zero_mul]
  have hsecond : y.1 * x.2.2 = 0 := by
    by_cases hp : p = 2
    · have hq : q ≠ 0 := by omega
      rw [hy.1 hq, zero_mul]
    · rw [hx.2.2 hp, mul_zero]
  have hdiv : divisorIntersection x.2.1 y.2.1 = 0 := by
    by_cases hp : p = 1
    · have hq : q ≠ 1 := by omega
      rw [hy.2.1 hq]
      simp only [divisorIntersection, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply,
        mul_zero, Finset.sum_const_zero, sub_self]
    · rw [hx.2.1 hp]
      simp only [divisorIntersection, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply,
        zero_mul, Finset.sum_const_zero, sub_self]
  rw [hfirst, hsecond, hdiv, add_zero, add_zero]

theorem one_mem_degree_zero (r : ℕ) : (1 : SurfaceCohomology r) ∈ degree r 0 :=
  ⟨(fun h ↦ (h rfl).elim), fun _ ↦ rfl, fun _ ↦ rfl⟩

theorem hyperplane_mem_degree_one (r : ℕ) : hyperplane r ∈ degree r 1 :=
  ⟨(fun _ ↦ rfl), (fun h ↦ (h rfl).elim), fun _ ↦ rfl⟩

theorem exceptional_mem_degree_one (r : ℕ) (i : Fin r) : exceptional r i ∈ degree r 1 :=
  ⟨(fun _ ↦ rfl), (fun h ↦ (h rfl).elim), fun _ ↦ rfl⟩

theorem point_mem_degree_two (r : ℕ) : point r ∈ degree r 2 :=
  ⟨(fun _ ↦ rfl), (fun _ ↦ rfl), fun h ↦ (h rfl).elim⟩

/-- The cohomology model has no classes above codimension two. -/
theorem degree_eq_bot_of_two_lt (r n : ℕ) (hn : 2 < n) : degree r n = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  change x = 0
  exact Prod.ext (hx.1 (by omega))
    (Prod.ext (hx.2.1 (by omega)) (hx.2.2 (by omega)))

instance (r : ℕ) : SetLike.GradedMonoid (degree r) where
  one_mem := one_mem_degree_zero r
  mul_mem := by
    intro p q x y hx hy
    refine ⟨fun hpq ↦ ?_, (fun hpq ↦ ?_), fun hpq ↦ ?_⟩
    · change x.1 * y.1 = 0
      by_cases hp : p = 0
      · have hq : q ≠ 0 := by omega
        rw [hy.1 hq, mul_zero]
      · rw [hx.1 hp, zero_mul]
    · change x.1 • y.2.1 + y.1 • x.2.1 = 0
      have hfirst : x.1 • y.2.1 = 0 := by
        by_cases hp : p = 0
        · have hq : q ≠ 1 := by omega
          rw [hy.2.1 hq, smul_zero]
        · rw [hx.1 hp, zero_smul]
      have hsecond : y.1 • x.2.1 = 0 := by
        by_cases hp : p = 1
        · have hq : q ≠ 0 := by omega
          rw [hy.1 hq, zero_smul]
        · rw [hx.2.1 hp, smul_zero]
      rw [hfirst, hsecond, add_zero]
    · exact pairing_vanishes r hx hy hpq

instance (r : ℕ) : GradedAlgebra (degree r) where
  __ := (inferInstance : SetLike.GradedMonoid (degree r))
  __ := (inferInstance : DirectSum.Decomposition (degree r))

/-- The surface cup algebra with its internal codimension grading. -/
def evenGradedAlgebra (r : ℕ) : EvenGradedAlgebra ℚ where
  carrier := SurfaceCohomology r
  degree := degree r

/-- The graded state space for the algebraic surface model. -/
def gradedState (r : ℕ) :
    GradedStateSpace ℚ (SurfaceCohomology r) (frobenius r).pairing 1 where
  dimension := 2
  degree := degree r
  unit_mem_degree_zero := one_mem_degree_zero r
  pairing_vanishes := pairing_vanishes r

end SurfaceCohomology

end AxiomaticGW

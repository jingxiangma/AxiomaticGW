/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.CurveReplay
public import AxiomaticGW.GKM.Fixtures.SurfaceReplay

/-!
# Actual c00 coefficients of the compact degree-zero candidate

Input SHA256: 5be60671ddc68304610987123f048a6c010504cf27f3b690cd1e4d4e39227399
The digest records provenance; identities use the decoded field expressions.
All twelve fixed-point indices, cones and both ordered tangent characters remain.
This is symbolic arithmetic in the existing equivariant fraction field.
No ordinary grading, Hodge identification, GW class or CohFT geometry is assumed.
-/

@[expose] public section

namespace AxiomaticGW.GKM.HodgeDegreeZeroCoefficientReplay

open EquivariantCoefficients CurveConventionCertificate Matrix

noncomputable section

namespace Plane

/-- Actual complete degree-zero class from the incoming target record. -/
def fullCurveClass : SurfaceTarget.plane.Curve :=
  ![0]

/-- All effective coordinates are retained and checked. -/
theorem fullCurveClass_eq_zero : fullCurveClass = 0 := by decide +kernel

/-- Incoming fixed-point identifiers, without modular integer coercion. -/
def fixedPointIndex : Fin 3 → Fin 3 :=
  ![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

/-- Every fixed point occurs in the held order. -/
theorem fixedPointIndex_eq : fixedPointIndex = id := by decide +kernel

/-- Incoming cone labels in the fixed fan-ray frame. -/
def fixedPoints : Fin 3 → Fin 2 → Fin 3 :=
  ![
    ![⟨0, by decide⟩, ⟨1, by decide⟩],
    ![⟨0, by decide⟩, ⟨2, by decide⟩],
    ![⟨1, by decide⟩, ⟨2, by decide⟩]]

/-- Cone labels bind the same fixed-point interpretation as the existing request. -/
theorem fixedPoints_eq : fixedPoints = CurveFrames.Plane.request.points := by
  decide +kernel

/-- Both ordered incoming integer tangent characters. -/
def tangent : Fin 3 → Fin 2 → Fin 2 → ℤ :=
  ![![![0, 1], ![1, 0]], ![![1, -1], ![0, -1]], ![![-1, 0], ![-1, 1]]]

/-- The actual branch order agrees with the already replayed producer table. -/
theorem tangent_eq_replay : tangent = CurveReplay.Plane.tables.tangent := by
  decide +kernel

/-- Exact incoming sparse polynomial, without changing its fraction representative. -/
def c00Numerator : Fin 3 → Polynomial :=
  ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)^2]

/-- Exact incoming sparse polynomial, without changing its fraction representative. -/
def c00Denominator : Fin 3 → Polynomial :=
  ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))]

/-- The actual serialized numerator divided by its serialized denominator. -/
def coefficient00 (p : Fin 3) : Coefficient :=
  embed (c00Numerator p) / embed (c00Denominator p)

/-- Every serialized denominator is checked nonzero in the genuine coefficient field. -/
theorem c00_denominator_ne_zero (p : Fin 3) :
    embed (c00Denominator p) ≠ 0 := by
  fin_cases p
  all_goals norm_num only [c00Denominator, map_zero, map_one, map_add, map_mul, map_pow,
      embed_C, embed_X_zero, embed_X_one, one_mul, mul_one, zero_mul,
      mul_zero, zero_add, add_zero, div_one, pow_zero, pow_one,
      neg_one_mul, neg_zero, sub_zero, zero_sub, sub_self,
      Matrix.cons_val, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.mk.injEq,
      Fin.ext_iff, Fin.val_succ, Fin.val_zero, Fin.val_natCast,
      Fin.val_one', ite_true, ite_false]
  all_goals exact one_ne_zero

/-- Exact incoming sparse polynomial, without changing its fraction representative. -/
def serializedEulerNumerator : Fin 3 → Polynomial :=
  ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)^2]

/-- Exact incoming sparse polynomial, without changing its fraction representative. -/
def serializedEulerDenominator : Fin 3 → Polynomial :=
  ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))]

/-- The actual serialized numerator divided by its serialized denominator. -/
def serializedTangentEuler (p : Fin 3) : Coefficient :=
  embed (serializedEulerNumerator p) / embed (serializedEulerDenominator p)

/-- Every serialized denominator is checked nonzero in the genuine coefficient field. -/
theorem serializedEuler_denominator_ne_zero (p : Fin 3) :
    embed (serializedEulerDenominator p) ≠ 0 := by
  fin_cases p
  all_goals norm_num only [serializedEulerDenominator, map_zero, map_one, map_add, map_mul,
      map_pow, embed_C, embed_X_zero, embed_X_one, one_mul, mul_one,
      zero_mul, mul_zero, zero_add, add_zero, div_one, pow_zero, pow_one,
      neg_one_mul, neg_zero, sub_zero, zero_sub, sub_self,
      Matrix.cons_val, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.mk.injEq,
      Fin.ext_iff, Fin.val_succ, Fin.val_zero, Fin.val_natCast,
      Fin.val_one', ite_true, ite_false]
  all_goals exact one_ne_zero

/-- Exact incoming sparse polynomial, without changing its fraction representative. -/
def unitNumerator : Fin 3 → Polynomial :=
  ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))]

/-- Exact incoming sparse polynomial, without changing its fraction representative. -/
def unitDenominator : Fin 3 → Polynomial :=
  ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))]

/-- The actual serialized numerator divided by its serialized denominator. -/
def unitRestriction (p : Fin 3) : Coefficient :=
  embed (unitNumerator p) / embed (unitDenominator p)

/-- Every serialized denominator is checked nonzero in the genuine coefficient field. -/
theorem unit_denominator_ne_zero (p : Fin 3) :
    embed (unitDenominator p) ≠ 0 := by
  fin_cases p
  all_goals norm_num only [unitDenominator, map_zero, map_one, map_add, map_mul, map_pow,
      embed_C, embed_X_zero, embed_X_one, one_mul, mul_one, zero_mul,
      mul_zero, zero_add, add_zero, div_one, pow_zero, pow_one,
      neg_one_mul, neg_zero, sub_zero, zero_sub, sub_self,
      Matrix.cons_val, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.mk.injEq,
      Fin.ext_iff, Fin.val_succ, Fin.val_zero, Fin.val_natCast,
      Fin.val_one', ite_true, ite_false]
  all_goals exact one_ne_zero

/-- The actual c00 coefficient and serialized tangent Euler field agree. -/
theorem coefficient00_eq_serializedEuler (p : Fin 3) :
    coefficient00 p = serializedTangentEuler p := by
  rfl

/-- Exact symbolic multiplication of both incoming tangent characters. -/
theorem coefficient00_eq_tangentProduct (p : Fin 3) :
    coefficient00 p = character (tangent p 0) * character (tangent p 1) := by
  fin_cases p
  all_goals norm_num only [coefficient00, c00Numerator, c00Denominator, tangent, character,
      map_zero, map_one, map_add, map_mul, map_pow, embed_C,
      embed_X_zero, embed_X_one, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, div_one, pow_zero, pow_one, neg_one_mul,
      neg_zero, sub_zero, zero_sub, sub_self, Matrix.cons_val,
      Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.mk.injEq,
      Fin.ext_iff, Fin.val_succ, Fin.val_zero, Fin.val_natCast,
      Fin.val_one', ite_true, ite_false]
  all_goals ring

/-- The incoming unit restriction is exactly one at every fixed point. -/
theorem unitRestriction_eq_one (p : Fin 3) : unitRestriction p = 1 := by
  fin_cases p
  all_goals norm_num only [unitRestriction, unitNumerator, unitDenominator, map_zero, map_one,
      map_add, map_mul, map_pow, embed_C, embed_X_zero, embed_X_one,
      one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero, div_one,
      pow_zero, pow_one, neg_one_mul, neg_zero, sub_zero, zero_sub,
      sub_self, Matrix.cons_val, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.mk.injEq,
      Fin.ext_iff, Fin.val_succ, Fin.val_zero, Fin.val_natCast,
      Fin.val_one', ite_true, ite_false]

/-- The checked producer tangent pair gives the independently held Euler factor. -/
theorem coefficient00_eq_requestEuler (p : Fin 3) :
    coefficient00 p = SurfaceFrames.Plane.request.euler p := by
  rw [coefficient00_eq_tangentProduct, tangent_eq_replay]
  rcases CurveReplay.Plane.accepted.tangent_eq p with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1]
    exact (CurveReplay.Plane.accepted.state_euler p).symm
  · rw [h0, h1, mul_comm]
    exact (CurveReplay.Plane.accepted.state_euler p).symm

/-- This is the exact invertible Euler weight used by the existing fixed-point algebra. -/
theorem coefficient00_eq_eulerUnits (p : Fin 3) :
    coefficient00 p = (SurfaceReplay.Plane.accepted.eulerUnits p : Coefficient) := by
  change coefficient00 p = SurfaceReplay.Plane.tables.euler p
  rw [SurfaceReplay.Plane.accepted.euler_eq]
  exact coefficient00_eq_requestEuler p

end Plane

namespace OneBlowup

/-- Actual complete degree-zero class from the incoming target record. -/
def fullCurveClass : SurfaceTarget.hirzebruchOne.Curve :=
  ![0, 0]

/-- All effective coordinates are retained and checked. -/
theorem fullCurveClass_eq_zero : fullCurveClass = 0 := by decide +kernel

/-- Incoming fixed-point identifiers, without modular integer coercion. -/
def fixedPointIndex : Fin 4 → Fin 4 :=
  ![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]

/-- Every fixed point occurs in the held order. -/
theorem fixedPointIndex_eq : fixedPointIndex = id := by decide +kernel

/-- Incoming cone labels in the fixed fan-ray frame. -/
def fixedPoints : Fin 4 → Fin 2 → Fin 4 :=
  ![
    ![⟨0, by decide⟩, ⟨2, by decide⟩],
    ![⟨0, by decide⟩, ⟨3, by decide⟩],
    ![⟨1, by decide⟩, ⟨2, by decide⟩],
    ![⟨1, by decide⟩, ⟨3, by decide⟩]]

/-- Cone labels bind the same fixed-point interpretation as the existing request. -/
theorem fixedPoints_eq : fixedPoints = CurveFrames.OneBlowup.request.points := by
  decide +kernel

/-- Both ordered incoming integer tangent characters. -/
def tangent : Fin 4 → Fin 2 → Fin 2 → ℤ :=
  ![
    ![![0, -1], ![1, -1]],
    ![![1, -1], ![0, 1]],
    ![![-1, 0], ![-1, 1]],
    ![![-1, 1], ![1, 0]]]

/-- The actual branch order agrees with the already replayed producer table. -/
theorem tangent_eq_replay : tangent = CurveReplay.OneBlowup.tables.tangent := by
  decide +kernel

/-- Exact incoming sparse polynomial, without changing its fraction representative. -/
def c00Numerator : Fin 4 → Polynomial :=
  ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)^2,
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)^2]

/-- Exact incoming sparse polynomial, without changing its fraction representative. -/
def c00Denominator : Fin 4 → Polynomial :=
  ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))]

/-- The actual serialized numerator divided by its serialized denominator. -/
def coefficient00 (p : Fin 4) : Coefficient :=
  embed (c00Numerator p) / embed (c00Denominator p)

/-- Every serialized denominator is checked nonzero in the genuine coefficient field. -/
theorem c00_denominator_ne_zero (p : Fin 4) :
    embed (c00Denominator p) ≠ 0 := by
  fin_cases p
  all_goals norm_num only [c00Denominator, map_zero, map_one, map_add, map_mul, map_pow,
      embed_C, embed_X_zero, embed_X_one, one_mul, mul_one, zero_mul,
      mul_zero, zero_add, add_zero, div_one, pow_zero, pow_one,
      neg_one_mul, neg_zero, sub_zero, zero_sub, sub_self,
      Matrix.cons_val, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.mk.injEq,
      Fin.ext_iff, Fin.val_succ, Fin.val_zero, Fin.val_natCast,
      Fin.val_one', ite_true, ite_false]
  all_goals exact one_ne_zero

/-- Exact incoming sparse polynomial, without changing its fraction representative. -/
def serializedEulerNumerator : Fin 4 → Polynomial :=
  ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)^2,
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)^2]

/-- Exact incoming sparse polynomial, without changing its fraction representative. -/
def serializedEulerDenominator : Fin 4 → Polynomial :=
  ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))]

/-- The actual serialized numerator divided by its serialized denominator. -/
def serializedTangentEuler (p : Fin 4) : Coefficient :=
  embed (serializedEulerNumerator p) / embed (serializedEulerDenominator p)

/-- Every serialized denominator is checked nonzero in the genuine coefficient field. -/
theorem serializedEuler_denominator_ne_zero (p : Fin 4) :
    embed (serializedEulerDenominator p) ≠ 0 := by
  fin_cases p
  all_goals norm_num only [serializedEulerDenominator, map_zero, map_one, map_add, map_mul,
      map_pow, embed_C, embed_X_zero, embed_X_one, one_mul, mul_one,
      zero_mul, mul_zero, zero_add, add_zero, div_one, pow_zero, pow_one,
      neg_one_mul, neg_zero, sub_zero, zero_sub, sub_self,
      Matrix.cons_val, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.mk.injEq,
      Fin.ext_iff, Fin.val_succ, Fin.val_zero, Fin.val_natCast,
      Fin.val_one', ite_true, ite_false]
  all_goals exact one_ne_zero

/-- Exact incoming sparse polynomial, without changing its fraction representative. -/
def unitNumerator : Fin 4 → Polynomial :=
  ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))]

/-- Exact incoming sparse polynomial, without changing its fraction representative. -/
def unitDenominator : Fin 4 → Polynomial :=
  ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))]

/-- The actual serialized numerator divided by its serialized denominator. -/
def unitRestriction (p : Fin 4) : Coefficient :=
  embed (unitNumerator p) / embed (unitDenominator p)

/-- Every serialized denominator is checked nonzero in the genuine coefficient field. -/
theorem unit_denominator_ne_zero (p : Fin 4) :
    embed (unitDenominator p) ≠ 0 := by
  fin_cases p
  all_goals norm_num only [unitDenominator, map_zero, map_one, map_add, map_mul, map_pow,
      embed_C, embed_X_zero, embed_X_one, one_mul, mul_one, zero_mul,
      mul_zero, zero_add, add_zero, div_one, pow_zero, pow_one,
      neg_one_mul, neg_zero, sub_zero, zero_sub, sub_self,
      Matrix.cons_val, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.mk.injEq,
      Fin.ext_iff, Fin.val_succ, Fin.val_zero, Fin.val_natCast,
      Fin.val_one', ite_true, ite_false]
  all_goals exact one_ne_zero

/-- The actual c00 coefficient and serialized tangent Euler field agree. -/
theorem coefficient00_eq_serializedEuler (p : Fin 4) :
    coefficient00 p = serializedTangentEuler p := by
  rfl

/-- Exact symbolic multiplication of both incoming tangent characters. -/
theorem coefficient00_eq_tangentProduct (p : Fin 4) :
    coefficient00 p = character (tangent p 0) * character (tangent p 1) := by
  fin_cases p
  all_goals norm_num only [coefficient00, c00Numerator, c00Denominator, tangent, character,
      map_zero, map_one, map_add, map_mul, map_pow, embed_C,
      embed_X_zero, embed_X_one, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, div_one, pow_zero, pow_one, neg_one_mul,
      neg_zero, sub_zero, zero_sub, sub_self, Matrix.cons_val,
      Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.mk.injEq,
      Fin.ext_iff, Fin.val_succ, Fin.val_zero, Fin.val_natCast,
      Fin.val_one', ite_true, ite_false]
  all_goals ring

/-- The incoming unit restriction is exactly one at every fixed point. -/
theorem unitRestriction_eq_one (p : Fin 4) : unitRestriction p = 1 := by
  fin_cases p
  all_goals norm_num only [unitRestriction, unitNumerator, unitDenominator, map_zero, map_one,
      map_add, map_mul, map_pow, embed_C, embed_X_zero, embed_X_one,
      one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero, div_one,
      pow_zero, pow_one, neg_one_mul, neg_zero, sub_zero, zero_sub,
      sub_self, Matrix.cons_val, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.mk.injEq,
      Fin.ext_iff, Fin.val_succ, Fin.val_zero, Fin.val_natCast,
      Fin.val_one', ite_true, ite_false]

/-- The checked producer tangent pair gives the independently held Euler factor. -/
theorem coefficient00_eq_requestEuler (p : Fin 4) :
    coefficient00 p = SurfaceFrames.OneBlowup.request.euler p := by
  rw [coefficient00_eq_tangentProduct, tangent_eq_replay]
  rcases CurveReplay.OneBlowup.accepted.tangent_eq p with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1]
    exact (CurveReplay.OneBlowup.accepted.state_euler p).symm
  · rw [h0, h1, mul_comm]
    exact (CurveReplay.OneBlowup.accepted.state_euler p).symm

/-- This is the exact invertible Euler weight used by the existing fixed-point algebra. -/
theorem coefficient00_eq_eulerUnits (p : Fin 4) :
    coefficient00 p = (SurfaceReplay.OneBlowup.accepted.eulerUnits p : Coefficient) := by
  change coefficient00 p = SurfaceReplay.OneBlowup.tables.euler p
  rw [SurfaceReplay.OneBlowup.accepted.euler_eq]
  exact coefficient00_eq_requestEuler p

end OneBlowup

namespace TwoBlowups

/-- Actual complete degree-zero class from the incoming target record. -/
def fullCurveClass : SurfaceTarget.blowupTwo.Curve :=
  ![0, 0, 0]

/-- All effective coordinates are retained and checked. -/
theorem fullCurveClass_eq_zero : fullCurveClass = 0 := by decide +kernel

/-- Incoming fixed-point identifiers, without modular integer coercion. -/
def fixedPointIndex : Fin 5 → Fin 5 :=
  ![
    ⟨0, by decide⟩,
    ⟨1, by decide⟩,
    ⟨2, by decide⟩,
    ⟨3, by decide⟩,
    ⟨4, by decide⟩]

/-- Every fixed point occurs in the held order. -/
theorem fixedPointIndex_eq : fixedPointIndex = id := by decide +kernel

/-- Incoming cone labels in the fixed fan-ray frame. -/
def fixedPoints : Fin 5 → Fin 2 → Fin 5 :=
  ![
    ![⟨0, by decide⟩, ⟨2, by decide⟩],
    ![⟨0, by decide⟩, ⟨3, by decide⟩],
    ![⟨1, by decide⟩, ⟨3, by decide⟩],
    ![⟨1, by decide⟩, ⟨4, by decide⟩],
    ![⟨2, by decide⟩, ⟨4, by decide⟩]]

/-- Cone labels bind the same fixed-point interpretation as the existing request. -/
theorem fixedPoints_eq : fixedPoints = CurveFrames.TwoBlowups.request.points := by
  decide +kernel

/-- Both ordered incoming integer tangent characters. -/
def tangent : Fin 5 → Fin 2 → Fin 2 → ℤ :=
  ![
    ![![0, -1], ![1, -1]],
    ![![1, -1], ![0, 1]],
    ![![1, 0], ![-1, 1]],
    ![![0, 1], ![-1, 0]],
    ![![-1, 1], ![0, -1]]]

/-- The actual branch order agrees with the already replayed producer table. -/
theorem tangent_eq_replay : tangent = CurveReplay.TwoBlowups.tables.tangent := by
  decide +kernel

/-- Exact incoming sparse polynomial, without changing its fraction representative. -/
def c00Numerator : Fin 5 → Polynomial :=
  ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)^2,
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)]

/-- Exact incoming sparse polynomial, without changing its fraction representative. -/
def c00Denominator : Fin 5 → Polynomial :=
  ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))]

/-- The actual serialized numerator divided by its serialized denominator. -/
def coefficient00 (p : Fin 5) : Coefficient :=
  embed (c00Numerator p) / embed (c00Denominator p)

/-- Every serialized denominator is checked nonzero in the genuine coefficient field. -/
theorem c00_denominator_ne_zero (p : Fin 5) :
    embed (c00Denominator p) ≠ 0 := by
  fin_cases p
  all_goals norm_num only [c00Denominator, map_zero, map_one, map_add, map_mul, map_pow,
      embed_C, embed_X_zero, embed_X_one, one_mul, mul_one, zero_mul,
      mul_zero, zero_add, add_zero, div_one, pow_zero, pow_one,
      neg_one_mul, neg_zero, sub_zero, zero_sub, sub_self,
      Matrix.cons_val, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.mk.injEq,
      Fin.ext_iff, Fin.val_succ, Fin.val_zero, Fin.val_natCast,
      Fin.val_one', ite_true, ite_false]
  all_goals exact one_ne_zero

/-- Exact incoming sparse polynomial, without changing its fraction representative. -/
def serializedEulerNumerator : Fin 5 → Polynomial :=
  ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)^2,
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)]

/-- Exact incoming sparse polynomial, without changing its fraction representative. -/
def serializedEulerDenominator : Fin 5 → Polynomial :=
  ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))]

/-- The actual serialized numerator divided by its serialized denominator. -/
def serializedTangentEuler (p : Fin 5) : Coefficient :=
  embed (serializedEulerNumerator p) / embed (serializedEulerDenominator p)

/-- Every serialized denominator is checked nonzero in the genuine coefficient field. -/
theorem serializedEuler_denominator_ne_zero (p : Fin 5) :
    embed (serializedEulerDenominator p) ≠ 0 := by
  fin_cases p
  all_goals norm_num only [serializedEulerDenominator, map_zero, map_one, map_add, map_mul,
      map_pow, embed_C, embed_X_zero, embed_X_one, one_mul, mul_one,
      zero_mul, mul_zero, zero_add, add_zero, div_one, pow_zero, pow_one,
      neg_one_mul, neg_zero, sub_zero, zero_sub, sub_self,
      Matrix.cons_val, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.mk.injEq,
      Fin.ext_iff, Fin.val_succ, Fin.val_zero, Fin.val_natCast,
      Fin.val_one', ite_true, ite_false]
  all_goals exact one_ne_zero

/-- Exact incoming sparse polynomial, without changing its fraction representative. -/
def unitNumerator : Fin 5 → Polynomial :=
  ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))]

/-- Exact incoming sparse polynomial, without changing its fraction representative. -/
def unitDenominator : Fin 5 → Polynomial :=
  ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))]

/-- The actual serialized numerator divided by its serialized denominator. -/
def unitRestriction (p : Fin 5) : Coefficient :=
  embed (unitNumerator p) / embed (unitDenominator p)

/-- Every serialized denominator is checked nonzero in the genuine coefficient field. -/
theorem unit_denominator_ne_zero (p : Fin 5) :
    embed (unitDenominator p) ≠ 0 := by
  fin_cases p
  all_goals norm_num only [unitDenominator, map_zero, map_one, map_add, map_mul, map_pow,
      embed_C, embed_X_zero, embed_X_one, one_mul, mul_one, zero_mul,
      mul_zero, zero_add, add_zero, div_one, pow_zero, pow_one,
      neg_one_mul, neg_zero, sub_zero, zero_sub, sub_self,
      Matrix.cons_val, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.mk.injEq,
      Fin.ext_iff, Fin.val_succ, Fin.val_zero, Fin.val_natCast,
      Fin.val_one', ite_true, ite_false]
  all_goals exact one_ne_zero

/-- The actual c00 coefficient and serialized tangent Euler field agree. -/
theorem coefficient00_eq_serializedEuler (p : Fin 5) :
    coefficient00 p = serializedTangentEuler p := by
  rfl

/-- Exact symbolic multiplication of both incoming tangent characters. -/
theorem coefficient00_eq_tangentProduct (p : Fin 5) :
    coefficient00 p = character (tangent p 0) * character (tangent p 1) := by
  fin_cases p
  all_goals norm_num only [coefficient00, c00Numerator, c00Denominator, tangent, character,
      map_zero, map_one, map_add, map_mul, map_pow, embed_C,
      embed_X_zero, embed_X_one, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, div_one, pow_zero, pow_one, neg_one_mul,
      neg_zero, sub_zero, zero_sub, sub_self, Matrix.cons_val,
      Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.mk.injEq,
      Fin.ext_iff, Fin.val_succ, Fin.val_zero, Fin.val_natCast,
      Fin.val_one', ite_true, ite_false]
  all_goals ring

/-- The incoming unit restriction is exactly one at every fixed point. -/
theorem unitRestriction_eq_one (p : Fin 5) : unitRestriction p = 1 := by
  fin_cases p
  all_goals norm_num only [unitRestriction, unitNumerator, unitDenominator, map_zero, map_one,
      map_add, map_mul, map_pow, embed_C, embed_X_zero, embed_X_one,
      one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero, div_one,
      pow_zero, pow_one, neg_one_mul, neg_zero, sub_zero, zero_sub,
      sub_self, Matrix.cons_val, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.mk.injEq,
      Fin.ext_iff, Fin.val_succ, Fin.val_zero, Fin.val_natCast,
      Fin.val_one', ite_true, ite_false]

/-- The checked producer tangent pair gives the independently held Euler factor. -/
theorem coefficient00_eq_requestEuler (p : Fin 5) :
    coefficient00 p = SurfaceFrames.TwoBlowups.request.euler p := by
  rw [coefficient00_eq_tangentProduct, tangent_eq_replay]
  rcases CurveReplay.TwoBlowups.accepted.tangent_eq p with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1]
    exact (CurveReplay.TwoBlowups.accepted.state_euler p).symm
  · rw [h0, h1, mul_comm]
    exact (CurveReplay.TwoBlowups.accepted.state_euler p).symm

/-- This is the exact invertible Euler weight used by the existing fixed-point algebra. -/
theorem coefficient00_eq_eulerUnits (p : Fin 5) :
    coefficient00 p = (SurfaceReplay.TwoBlowups.accepted.eulerUnits p : Coefficient) := by
  change coefficient00 p = SurfaceReplay.TwoBlowups.tables.euler p
  rw [SurfaceReplay.TwoBlowups.accepted.euler_eq]
  exact coefficient00_eq_requestEuler p

end TwoBlowups

end

end AxiomaticGW.GKM.HodgeDegreeZeroCoefficientReplay

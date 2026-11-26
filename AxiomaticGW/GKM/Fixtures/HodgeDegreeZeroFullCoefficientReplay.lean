/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroCoefficientReplay
public import AxiomaticGW.GKM.AdmcyclesHodgeStrataNormalization

/-!
# Complete exact coefficient assembly for the fixed compact candidate

Input SHA256: 5be60671ddc68304610987123f048a6c010504cf27f3b690cd1e4d4e39227399
All 108 numerator/denominator pairs are actual incoming data, indexed by
fixed point and both ordered lambda labels; all 540 component references remain.
The realized sum contains every coefficient and all five raw degree components.
Only its scalar projection is identified with the existing TFT correlator.
No geometric Hodge/GRR identity, GW class, CohFT law or ordinary grading is assumed.
-/

@[expose] public section

namespace AxiomaticGW.GKM.HodgeDegreeZeroFullCoefficientReplay

open EquivariantCoefficients Matrix
open AdmcyclesHodgeStrataNormalization

noncomputable section

variable {C : StableCurveCohomology Coefficient}

attribute [local instance] strataRealizationModule

namespace Plane

/-- Every actual incoming sparse polynomial, indexed by its full ordered key. -/
def numerators : Fin 3 → Fin 3 → Fin 3 → Polynomial :=
  ![
    ![
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)],
    ![
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (-1 : ℚ))],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (-1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))]],
    ![
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))]],
    ![
    ![
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)^2,
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (-1 : ℚ))],
    ![
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (-1 : ℚ))]]]

/-- Every actual incoming sparse polynomial, indexed by its full ordered key. -/
def denominators : Fin 3 → Fin 3 → Fin 3 → Polynomial :=
  ![
    ![
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)]],
    ![
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)],
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)]],
    ![
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)^2]]]

/-- Every serialized fraction interpreted in the existing exact coefficient field. -/
def coefficients (p : Fin 3) (a b : Fin 3) : Coefficient :=
  embed (numerators p a b) / embed (denominators p a b)

/-- Evaluation certifies denominator nonvanishing only, never a symbolic identity. -/
theorem denominator_ne_zero (p : Fin 3) (a b : Fin 3) :
    embed (denominators p a b) ≠ 0 := by
  apply embed_ne_zero_of_eval _ ![2,3]
  fin_cases p <;> fin_cases a <;> fin_cases b
  all_goals norm_num only [denominators, map_zero, map_one, map_add, map_mul, map_pow,
      one_ne_zero, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      RingHom.id_apply, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]

/-- The full tensor retains exactly the already checked incoming c00 entries. -/
theorem coefficients_zero_zero (p : Fin 3) :
    coefficients p 0 0 = HodgeDegreeZeroCoefficientReplay.Plane.coefficient00 p := by
  fin_cases p <;> rfl

/-- The held c00 proof supplies the exact Euler units, with no new hypothesis. -/
theorem coefficients_zero_zero_eq_eulerUnits (p : Fin 3) :
    coefficients p 0 0 =
      (SurfaceReplay.Plane.accepted.eulerUnits p : Coefficient) :=
  (coefficients_zero_zero p).trans
    (HodgeDegreeZeroCoefficientReplay.Plane.coefficient00_eq_eulerUnits p)

/-- All actual coefficients and all actual raw components occur in this conditional class. -/
noncomputable def candidateClass (A : StrataRealization C 2 (Fin 1)) :
    C.H 2 (Fin 1) := assembly A coefficients

/-- Projection of the complete candidate matches the existing fixed-point TFT. -/
theorem scalar_candidateClass_eq_tft (D : ConnectedDegreeZero C)
    (A : StrataRealization C 2 (Fin 1))
    (hfund : A.map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) stable)) = 1) :
    D.scalar 2 (Fin 1) stable (candidateClass A) =
      (FixedPointAlgebra.algebra SurfaceReplay.Plane.accepted.eulerUnits).correlator
        2 (Fin 1) (fun _ ↦ 1) :=
  scalar_assembly_eq_tft D A hfund coefficients
    SurfaceReplay.Plane.accepted.eulerUnits coefficients_zero_zero_eq_eulerUnits

end Plane

namespace OneBlowup

/-- Every actual incoming sparse polynomial, indexed by its full ordered key. -/
def numerators : Fin 4 → Fin 3 → Fin 3 → Polynomial :=
  ![
    ![
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))]],
    ![
    ![
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (-1 : ℚ))],
    ![
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (-1 : ℚ))]],
    ![
    ![
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)^2,
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (-1 : ℚ))],
    ![
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (-1 : ℚ))]],
    ![
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)^2,
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (-1 : ℚ))],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (-1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))]]]

/-- Every actual incoming sparse polynomial, indexed by its full ordered key. -/
def denominators : Fin 4 → Fin 3 → Fin 3 → Polynomial :=
  ![
    ![
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)]],
    ![
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)],
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)]],
    ![
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)^2]],
    ![
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)^2]]]

/-- Every serialized fraction interpreted in the existing exact coefficient field. -/
def coefficients (p : Fin 4) (a b : Fin 3) : Coefficient :=
  embed (numerators p a b) / embed (denominators p a b)

/-- Evaluation certifies denominator nonvanishing only, never a symbolic identity. -/
theorem denominator_ne_zero (p : Fin 4) (a b : Fin 3) :
    embed (denominators p a b) ≠ 0 := by
  apply embed_ne_zero_of_eval _ ![2,3]
  fin_cases p <;> fin_cases a <;> fin_cases b
  all_goals norm_num only [denominators, map_zero, map_one, map_add, map_mul, map_pow,
      one_ne_zero, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      RingHom.id_apply, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]

/-- The full tensor retains exactly the already checked incoming c00 entries. -/
theorem coefficients_zero_zero (p : Fin 4) :
    coefficients p 0 0 = HodgeDegreeZeroCoefficientReplay.OneBlowup.coefficient00 p := by
  fin_cases p <;> rfl

/-- The held c00 proof supplies the exact Euler units, with no new hypothesis. -/
theorem coefficients_zero_zero_eq_eulerUnits (p : Fin 4) :
    coefficients p 0 0 =
      (SurfaceReplay.OneBlowup.accepted.eulerUnits p : Coefficient) :=
  (coefficients_zero_zero p).trans
    (HodgeDegreeZeroCoefficientReplay.OneBlowup.coefficient00_eq_eulerUnits p)

/-- All actual coefficients and all actual raw components occur in this conditional class. -/
noncomputable def candidateClass (A : StrataRealization C 2 (Fin 1)) :
    C.H 2 (Fin 1) := assembly A coefficients

/-- Projection of the complete candidate matches the existing fixed-point TFT. -/
theorem scalar_candidateClass_eq_tft (D : ConnectedDegreeZero C)
    (A : StrataRealization C 2 (Fin 1))
    (hfund : A.map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) stable)) = 1) :
    D.scalar 2 (Fin 1) stable (candidateClass A) =
      (FixedPointAlgebra.algebra SurfaceReplay.OneBlowup.accepted.eulerUnits).correlator
        2 (Fin 1) (fun _ ↦ 1) :=
  scalar_assembly_eq_tft D A hfund coefficients
    SurfaceReplay.OneBlowup.accepted.eulerUnits coefficients_zero_zero_eq_eulerUnits

end OneBlowup

namespace TwoBlowups

/-- Every actual incoming sparse polynomial, indexed by its full ordered key. -/
def numerators : Fin 5 → Fin 3 → Fin 3 → Polynomial :=
  ![
    ![
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))]],
    ![
    ![
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (-1 : ℚ))],
    ![
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (-1 : ℚ))]],
    ![
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)^2,
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (-1 : ℚ))],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (-1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))]],
    ![
    ![
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1),
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1)],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))],
    ![
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (-1 : ℚ)),
    (MvPolynomial.C (-1 : ℚ))]],
    ![
    ![
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1),
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))],
    ![
    (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 1),
    (MvPolynomial.C (-1 : ℚ)),
    (MvPolynomial.C (-1 : ℚ))]]]

/-- Every actual incoming sparse polynomial, indexed by its full ordered key. -/
def denominators : Fin 5 → Fin 3 → Fin 3 → Polynomial :=
  ![
    ![
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)]],
    ![
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)],
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)]],
    ![
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)^2]],
    ![
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)]],
    ![
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)],
    ![
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ)),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)],
    ![
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0),
    (MvPolynomial.C (1 : ℚ))*(MvPolynomial.X 1)^2
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)*(MvPolynomial.X 1)]]]

/-- Every serialized fraction interpreted in the existing exact coefficient field. -/
def coefficients (p : Fin 5) (a b : Fin 3) : Coefficient :=
  embed (numerators p a b) / embed (denominators p a b)

/-- Evaluation certifies denominator nonvanishing only, never a symbolic identity. -/
theorem denominator_ne_zero (p : Fin 5) (a b : Fin 3) :
    embed (denominators p a b) ≠ 0 := by
  apply embed_ne_zero_of_eval _ ![2,3]
  fin_cases p <;> fin_cases a <;> fin_cases b
  all_goals norm_num only [denominators, map_zero, map_one, map_add, map_mul, map_pow,
      one_ne_zero, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      RingHom.id_apply, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]

/-- The full tensor retains exactly the already checked incoming c00 entries. -/
theorem coefficients_zero_zero (p : Fin 5) :
    coefficients p 0 0 = HodgeDegreeZeroCoefficientReplay.TwoBlowups.coefficient00 p := by
  fin_cases p <;> rfl

/-- The held c00 proof supplies the exact Euler units, with no new hypothesis. -/
theorem coefficients_zero_zero_eq_eulerUnits (p : Fin 5) :
    coefficients p 0 0 =
      (SurfaceReplay.TwoBlowups.accepted.eulerUnits p : Coefficient) :=
  (coefficients_zero_zero p).trans
    (HodgeDegreeZeroCoefficientReplay.TwoBlowups.coefficient00_eq_eulerUnits p)

/-- All actual coefficients and all actual raw components occur in this conditional class. -/
noncomputable def candidateClass (A : StrataRealization C 2 (Fin 1)) :
    C.H 2 (Fin 1) := assembly A coefficients

/-- Projection of the complete candidate matches the existing fixed-point TFT. -/
theorem scalar_candidateClass_eq_tft (D : ConnectedDegreeZero C)
    (A : StrataRealization C 2 (Fin 1))
    (hfund : A.map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) stable)) = 1) :
    D.scalar 2 (Fin 1) stable (candidateClass A) =
      (FixedPointAlgebra.algebra SurfaceReplay.TwoBlowups.accepted.eulerUnits).correlator
        2 (Fin 1) (fun _ ↦ 1) :=
  scalar_assembly_eq_tft D A hfund coefficients
    SurfaceReplay.TwoBlowups.accepted.eulerUnits coefficients_zero_zero_eq_eulerUnits

end TwoBlowups

end

end AxiomaticGW.GKM.HodgeDegreeZeroFullCoefficientReplay

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.EquivariantCalibrationData
public import AxiomaticGW.GKM.Fixtures.BlowupQuantumIdempotents

/-!
# Exact primitive-class comparison of the first three equivariant calibration tensors

The inverse-loop power is one larger than the cotangent exponent, with the node
first. The primary coefficient is the anticanonical slice of the incoming quantum
three-point function, divided by the anticanonical degree. Multiplication by c₁
in the undeformed state space yields the next two tensors by the commutator.
-/

@[expose] public section
namespace AxiomaticGW.GKM.EquivariantCalibrationReplay
open EquivariantCoefficients Matrix SmallQuantumGeneratorComparison
open BlowupQuantumIdempotents (Direction Index)
noncomputable section

def request : (X : SurfaceTarget) → StateSpaceCertificate.Request (X.blowups + 3)
  | .plane => SurfaceFrames.Plane.request
  | .hirzebruchOne => SurfaceFrames.OneBlowup.request
  | .blowupTwo => SurfaceFrames.TwoBlowups.request

def tables : (X : SurfaceTarget) → StateSpaceCertificate.Tables (X.blowups + 3)
  | .plane => SurfaceReplay.Plane.tables
  | .hirzebruchOne => SurfaceReplay.OneBlowup.tables
  | .blowupTwo => SurfaceReplay.TwoBlowups.tables

def c1 : (X : SurfaceTarget) → Index X → Coefficient
  | .plane => EquivariantCalibrationData.Plane.c1 x y
  | .hirzebruchOne => EquivariantCalibrationData.OneBlowup.c1 x y
  | .blowupTwo => EquivariantCalibrationData.TwoBlowups.c1 x y

def energy : (X : SurfaceTarget) → Direction X → ℕ
  | .plane => EquivariantCalibrationData.Plane.energy
  | .hirzebruchOne => EquivariantCalibrationData.OneBlowup.energy
  | .blowupTwo => EquivariantCalibrationData.TwoBlowups.energy

def cup : (X : SurfaceTarget) → Matrix (Index X) (Index X) Coefficient
  | .plane => EquivariantCalibrationData.Plane.cup x y
  | .hirzebruchOne => EquivariantCalibrationData.OneBlowup.cup x y
  | .blowupTwo => EquivariantCalibrationData.TwoBlowups.cup x y

def paired : (X : SurfaceTarget) →
    Fin 3 → Direction X → Matrix (Index X) (Index X) Coefficient
  | .plane => EquivariantCalibrationData.Plane.paired x y
  | .hirzebruchOne => EquivariantCalibrationData.OneBlowup.paired x y
  | .blowupTwo => EquivariantCalibrationData.TwoBlowups.paired x y

theorem accepted (X : SurfaceTarget) : StateSpaceCertificate.Accepts (request X) (tables X) := by
  cases X
  · exact SurfaceReplay.Plane.accepted
  · exact SurfaceReplay.OneBlowup.accepted
  · exact SurfaceReplay.TwoBlowups.accepted

theorem energy_correct (X : SurfaceTarget) :
    ∀ d, energy X d = X.effective.energy (generator X d) := by
  cases X <;> decide +kernel

theorem energy_pos (X : SurfaceTarget) : ∀ d, 0 < energy X d := by cases X <;> decide +kernel

namespace Plane
open EquivariantCalibrationData.Plane (poly)
open EquivariantCalibrationData.Plane renaming cup → sourceCup, c1 → sourceC1,
  paired → sourcePaired, energy → sourceEnergy

set_option maxHeartbeats 1000000 in
-- Expand both held restriction matrices at every ordered toric basis entry.
theorem classical :
    (request .plane).restrictions * cup .plane =
      diagonal (request .plane).tangentSum * (request .plane).restrictions ∧
    (request .plane).restrictions *ᵥ c1 .plane = (request .plane).tangentSum := by
  constructor
  · funext i j
    rw [diagonal_mul]
    change (SurfaceFrames.Plane.request.restrictions * sourceCup x y) i j = _
    fin_cases i <;> fin_cases j <;>
      simp +decide [request, Matrix.mul_apply, Fin.sum_univ_three, SurfaceFrames.Plane.request,
        sourceCup, poly, Matrix.cons_val_two] <;> ring
  · funext i
    change (SurfaceFrames.Plane.request.restrictions *ᵥ sourceC1 x y) i = _
    fin_cases i <;>
      simp +decide [request, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        SurfaceFrames.Plane.request, sourceC1, poly, Matrix.cons_val_two] <;> ring

set_option maxHeartbeats 5000000 in
-- Compare every ordered pair at every primitive full class with the tensor's divisor slice.
theorem divisor (d : Fin 1) (i j : Fin 3) :
    (sourceEnergy d : Coefficient) * sourcePaired x y 0 d i j =
      ∑ h, sourceC1 x y h * SmallQuantumGeneratorData.plane x y d h i j := by
  fin_cases d
  fin_cases i <;> fin_cases j <;>
    simp +decide [Fin.sum_univ_three, sourceEnergy, sourcePaired,
      sourceC1, poly, SmallQuantumGeneratorData.plane, Matrix.cons_val_two]

set_option maxHeartbeats 7000000 in
-- Verify both native adjacent powers in every finite matrix coordinate, including zero entries.
theorem recursion (m : Fin 2) (d : Fin 1) :
    (sourceEnergy d : Coefficient) • sourcePaired x y m.succ d =
      (sourceCup x y).transpose * sourcePaired x y m.castSucc d -
        sourcePaired x y m.castSucc d * sourceCup x y := by
  funext i j
  fin_cases m <;> fin_cases d <;> fin_cases i <;> fin_cases j <;>
    simp +decide [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      transpose_apply, Fin.sum_univ_three, sourceEnergy, sourcePaired,
      sourceCup, poly, Matrix.cons_val_two] <;> ring

end Plane

namespace OneBlowup
open EquivariantCalibrationData.OneBlowup (poly)
open EquivariantCalibrationData.OneBlowup renaming cup → sourceCup, c1 → sourceC1,
  paired → sourcePaired, energy → sourceEnergy

set_option maxHeartbeats 1000000 in
-- Expand both held restriction matrices at every ordered toric basis entry.
theorem classical :
    (request .hirzebruchOne).restrictions * cup .hirzebruchOne =
      diagonal (request .hirzebruchOne).tangentSum * (request .hirzebruchOne).restrictions ∧
    (request .hirzebruchOne).restrictions *ᵥ c1 .hirzebruchOne =
      (request .hirzebruchOne).tangentSum := by
  constructor
  · funext i j
    rw [diagonal_mul]
    change (SurfaceFrames.OneBlowup.request.restrictions * sourceCup x y) i j = _
    fin_cases i <;> fin_cases j <;>
      simp +decide [request, Matrix.mul_apply, Fin.sum_univ_four, SurfaceFrames.OneBlowup.request,
        sourceCup, poly, Matrix.cons_val_two, Matrix.cons_val_three] <;> ring
  · funext i
    change (SurfaceFrames.OneBlowup.request.restrictions *ᵥ sourceC1 x y) i = _
    fin_cases i <;>
      simp +decide [request, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
        SurfaceFrames.OneBlowup.request, sourceC1, poly, Matrix.cons_val_two,
        Matrix.cons_val_three] <;> ring

set_option maxHeartbeats 5000000 in
-- Compare every ordered pair at every primitive full class with the tensor's divisor slice.
theorem divisor (d : Fin 2) (i j : Fin 4) :
    (sourceEnergy d : Coefficient) * sourcePaired x y 0 d i j =
      ∑ h, sourceC1 x y h * SmallQuantumGeneratorData.one x y d h i j := by
  fin_cases d <;> fin_cases i <;> fin_cases j <;>
    simp +decide [Fin.sum_univ_four, sourceEnergy, sourcePaired,
      sourceC1, poly, SmallQuantumGeneratorData.one, Matrix.cons_val_two,
      Matrix.cons_val_three] <;> ring

set_option maxHeartbeats 7000000 in
-- Verify both native adjacent powers in every finite matrix coordinate, including zero entries.
theorem recursion (m : Fin 2) (d : Fin 2) :
    (sourceEnergy d : Coefficient) • sourcePaired x y m.succ d =
      (sourceCup x y).transpose * sourcePaired x y m.castSucc d -
        sourcePaired x y m.castSucc d * sourceCup x y := by
  funext i j
  fin_cases m <;> fin_cases d <;> fin_cases i <;> fin_cases j <;>
    simp +decide [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      transpose_apply, Fin.sum_univ_four, sourceEnergy, sourcePaired,
      sourceCup, poly, Matrix.cons_val_two, Matrix.cons_val_three] <;> ring

end OneBlowup

namespace TwoBlowups
open EquivariantCalibrationData.TwoBlowups (poly)
open EquivariantCalibrationData.TwoBlowups renaming cup → sourceCup, c1 → sourceC1,
  paired → sourcePaired, energy → sourceEnergy

private theorem sum_five (f : Fin 5 → Coefficient) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_four]
  abel

set_option maxHeartbeats 1000000 in
-- Expand both held restriction matrices at every ordered toric basis entry.
theorem classical :
    (request .blowupTwo).restrictions * cup .blowupTwo =
      diagonal (request .blowupTwo).tangentSum * (request .blowupTwo).restrictions ∧
    (request .blowupTwo).restrictions *ᵥ c1 .blowupTwo =
        (request .blowupTwo).tangentSum := by
  constructor
  · funext i j
    rw [diagonal_mul]
    change (SurfaceFrames.TwoBlowups.request.restrictions * sourceCup x y) i j = _
    fin_cases i <;> fin_cases j <;>
      simp +decide [request, Matrix.mul_apply, sum_five, SurfaceFrames.TwoBlowups.request,
        sourceCup, poly, Matrix.cons_val_two, Matrix.cons_val_three] <;> ring
  · funext i
    change (SurfaceFrames.TwoBlowups.request.restrictions *ᵥ sourceC1 x y) i = _
    fin_cases i <;>
      simp +decide [request, Matrix.mulVec, dotProduct, sum_five, SurfaceFrames.TwoBlowups.request,
        sourceC1, poly, Matrix.cons_val_two, Matrix.cons_val_three] <;> ring

set_option maxHeartbeats 5000000 in
-- Compare every ordered pair at every primitive full class with the tensor's divisor slice.
theorem divisor (d : Fin 3) (i j : Fin 5) :
    (sourceEnergy d : Coefficient) * sourcePaired x y 0 d i j =
      ∑ h, sourceC1 x y h * SmallQuantumGeneratorData.two x y d h i j := by
  fin_cases d <;> fin_cases i <;> fin_cases j <;>
    simp +decide [sum_five, sourceEnergy, sourcePaired,
      sourceC1, poly, SmallQuantumGeneratorData.two, Matrix.cons_val_two,
      Matrix.cons_val_three] <;> ring

set_option maxHeartbeats 7000000 in
-- Verify both native adjacent powers in every finite matrix coordinate, including zero entries.
theorem recursion (m : Fin 2) (d : Fin 3) :
    (sourceEnergy d : Coefficient) • sourcePaired x y m.succ d =
      (sourceCup x y).transpose * sourcePaired x y m.castSucc d -
        sourcePaired x y m.castSucc d * sourceCup x y := by
  funext i j
  fin_cases m <;> fin_cases d <;> fin_cases i <;> fin_cases j <;>
    simp +decide [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      transpose_apply, sum_five, sourceEnergy, sourcePaired,
      sourceCup, poly, Matrix.cons_val_two, Matrix.cons_val_three] <;> ring

end TwoBlowups

theorem cup_restrict (X : SurfaceTarget) :
    (request X).restrictions * cup X =
      diagonal (request X).tangentSum * (request X).restrictions ∧
    (request X).restrictions *ᵥ c1 X = (request X).tangentSum := by
  cases X
  · exact Plane.classical
  · exact OneBlowup.classical
  · exact TwoBlowups.classical

theorem divisor_identity (X : SurfaceTarget) (d : Direction X) (i j : Index X) :
    (energy X d : Coefficient) * paired X 0 d i j =
      ∑ h, c1 X h * tensor x y X d h i j := by
  cases X
  · exact Plane.divisor d i j
  · exact OneBlowup.divisor d i j
  · exact TwoBlowups.divisor d i j

theorem commutator (X : SurfaceTarget) (m : Fin 2) (d : Direction X) :
    (energy X d : Coefficient) • paired X m.succ d =
      (cup X).transpose * paired X m.castSucc d - paired X m.castSucc d * cup X := by
  cases X
  · exact Plane.recursion m d
  · exact OneBlowup.recursion m d
  · exact TwoBlowups.recursion m d

end
end AxiomaticGW.GKM.EquivariantCalibrationReplay

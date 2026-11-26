/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupQuantumIdempotents

/-! # Pair decomposition of the plane line tensor for the common spectral calibration -/

@[expose] public section
namespace AxiomaticGW.GKM.PlaneQuantumPairs
open EquivariantCoefficients FirstOrderFixedPoints BlowupQuantumIdempotents Matrix
noncomputable section

def pairs : Fin 3 → Pair (Fin 3) := ![⟨0,1⟩,⟨0,2⟩,⟨1,2⟩]
def weights (_d : Fin 1) : Fin 3 → Coefficient :=
  ![-1/(x*y^3*(x-y)), 1/(x^3*y*(x-y)), -1/(x*y*(x-y)^3)]

private def scale : Fin 3 → Coefficient := ![-y,-x,y-x]
private def covector : Matrix (Fin 3) (Fin 3) Coefficient := !![0,1,x-y;0,1,0;0,1,-y]
private def factor : Fin 3 → Coefficient := ![1/(x*(x-y)),-1/(y*(x-y)),1/(x*y)]

private theorem diff (t i : Fin 3) :
    (pairs t).diff (SurfaceFrames.Plane.request.restrictions.col i) =
    scale t * covector t i := by
  fin_cases t <;> fin_cases i <;>
    simp +decide [pairs, Pair.diff, SurfaceFrames.Plane.request, scale, covector,
      Matrix.col, Matrix.cons_val_two] <;> ring

private theorem factor_correct (d : Fin 1) (t : Fin 3) : weights d t * (scale t)^3 = factor t := by
  fin_cases t <;> simp +decide [weights, scale, factor, Matrix.cons_val_two] <;>
    field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero]
  ring

private theorem source (d : Fin 1) (i j k : Fin 3) :
    (∑ t, factor t * (covector t i * covector t j * covector t k)) =
      SmallQuantumGeneratorData.plane x y d i j k := by
  fin_cases d
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp +decide [Fin.sum_univ_three, factor, covector, SmallQuantumGeneratorData.plane,
      Matrix.cons_val_two] <;> field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero] <;> ring

def presentation : Presentation .plane where
  request := SurfaceFrames.Plane.request
  tables := SurfaceReplay.Plane.tables
  accepted := SurfaceReplay.Plane.accepted
  pairs := pairs
  weights := weights
  cubic_basis d i j k := by
    change cubic pairs weights d (SurfaceFrames.Plane.request.restrictions.col i)
      (SurfaceFrames.Plane.request.restrictions.col j)
      (SurfaceFrames.Plane.request.restrictions.col k) =
        SmallQuantumGeneratorData.plane x y d i j k
    unfold cubic
    rw [← source]
    apply Finset.sum_congr rfl
    intro t _
    rw [diff, diff, diff, ← factor_correct d]
    ring

end
end AxiomaticGW.GKM.PlaneQuantumPairs

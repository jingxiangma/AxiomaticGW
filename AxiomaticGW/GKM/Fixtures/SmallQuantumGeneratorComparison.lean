/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.SmallQuantumGeneratorData
public import AxiomaticGW.GKM.Fixtures.FirstCalibrationReplay
public import AxiomaticGW.Surfaces.GenusZeroRecursion

/-! # Ordinary three-point comparison at each primitive surface generator -/

@[expose] public section
namespace AxiomaticGW.GKM.SmallQuantumGeneratorComparison
open SmallQuantumGeneratorData

/-- Basis order used by the existing equivariant calibration exchange. -/
def state : (X : SurfaceTarget) → Fin (X.blowups + 3) → SurfaceBasisLabel X
  | .plane => FirstCalibrationReplay.Plane.labels
  | .hirzebruchOne => FirstCalibrationReplay.OneBlowup.labels
  | .blowupTwo => FirstCalibrationReplay.TwoBlowups.labels

/-- Each positively indexed class is a full effective generator in curve coordinates. -/
def generator (X : SurfaceTarget) (d : Fin (X.blowups + 1)) : X.Curve := Pi.single d 1

/-- Evaluate the native polynomial on the two torus parameters in any coefficient ring. -/
def tensor {R : Type*} [CommRing R] (u v : R) : (X : SurfaceTarget) →
    Fin (X.blowups + 1) → Fin (X.blowups + 3) → Fin (X.blowups + 3) → Fin (X.blowups + 3) → R
  | .plane => plane u v
  | .hirzebruchOne => one u v
  | .blowupTwo => two u v

/-- All six primitive generators and all ordered triples of basis states agree
at the ordinary origin with the established genus-zero reconstruction. -/
theorem ordinary_replay (X : SurfaceTarget) : ∀ d i j k,
    tensor (0 : ℚ) 0 X d i j k =
      SurfaceGenusZero.primaryValue X (generator X d) {state X i, state X j, state X k} := by
  cases X <;> decide +kernel

end AxiomaticGW.GKM.SmallQuantumGeneratorComparison

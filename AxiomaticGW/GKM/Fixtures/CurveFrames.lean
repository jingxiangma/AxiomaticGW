/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.CurveConventionCertificate
public import AxiomaticGW.GKM.Fixtures.SurfaceFrames

/-!
# Fixed fan requests for full curve and invariant-edge replay

The ray pairs and dual characters follow the fixed toric presentations in
GKMExchange.md. Effective coordinates are H, (E,F), and (E₁,E₂,L), with
generator walls 0, (3,0), and (3,4,1). These requests are independent of the
candidate export. Their geometric surface identification remains an input.
-/

@[expose] public section

namespace AxiomaticGW.GKM.CurveFrames

open CurveConventionCertificate
open Matrix

noncomputable section

namespace Plane

/-- Fixed fan, full curve, and state-space conventions for the plane. -/
def request : Request .plane 3 3 where
  state := SurfaceFrames.Plane.request
  divisorState := ![1]
  rays := ![![1,0], ![0,1], ![-1,-1]]
  points := ![![0,1], ![0,2], ![1,2]]
  tangent := ![![![1,0], ![0,1]], ![![1,-1], ![0,-1]], ![![-1,1], ![-1,0]]]
  wallClasses := ![![1], ![1], ![1]]
  generatorWalls := ![0]

end Plane

namespace OneBlowup

/-- Fixed fan, full curve, and state-space conventions for F₁. -/
def request : Request .hirzebruchOne 4 4 where
  state := SurfaceFrames.OneBlowup.request
  divisorState := ![1,2]
  rays := ![![1,0], ![0,1], ![-1,-1], ![1,1]]
  points := ![![0,2], ![0,3], ![1,2], ![1,3]]
  tangent := ![![![1,-1], ![0,-1]], ![![1,-1], ![0,1]],
    ![![-1,1], ![-1,0]], ![![-1,1], ![1,0]]]
  wallClasses := ![![0,1], ![0,1], ![1,1], ![1,0]]
  generatorWalls := ![3,0]

end OneBlowup

namespace TwoBlowups

/-- Fixed fan, full curve, and state-space conventions for the two-point blowup. -/
def request : Request .blowupTwo 5 5 where
  state := SurfaceFrames.TwoBlowups.request
  divisorState := ![1,2,3]
  rays := ![![1,0], ![0,1], ![-1,-1], ![1,1], ![-1,0]]
  points := ![![0,2], ![0,3], ![1,3], ![1,4], ![2,4]]
  tangent := ![![![1,-1], ![0,-1]], ![![1,-1], ![0,1]],
    ![![-1,1], ![1,0]], ![![0,1], ![-1,0]], ![![0,-1], ![-1,1]]]
  wallClasses := ![![0,1,1], ![0,0,1], ![1,0,1], ![1,0,0], ![0,1,0]]
  generatorWalls := ![3,4,1]

end TwoBlowups

end

end AxiomaticGW.GKM.CurveFrames

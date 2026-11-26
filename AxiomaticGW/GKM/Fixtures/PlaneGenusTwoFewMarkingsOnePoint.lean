/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoFewMarkingsData

/-!
# Plane few-marking arithmetic: OnePoint

Every displayed query is evaluated against the literal canonical candidate table.
Final acceptance separately identifies that table with the certified line table.
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536
set_option cbv.maxSteps 4000000

namespace AxiomaticGW.GKM.PlaneGenusTwoFewMarkingsReplay.OnePoint

open BelorousskiPandharipande

attribute [local cbv_eval] vectorLookup rationalCached ellipticCached

set_option maxHeartbeats 4000000 in
-- Kernel proof of this complete finite descendant calculation.
private theorem value_0 : planeQueryValueWith? canonicalValues
    (requests 0) = some (values 0) := by cbv

set_option maxHeartbeats 4000000 in
-- Kernel proof of this complete finite descendant calculation.
private theorem value_1 : planeQueryValueWith? canonicalValues
    (requests 1) = some (values 1) := by cbv

set_option maxHeartbeats 4000000 in
-- Kernel proof of this complete finite descendant calculation.
private theorem value_2 : planeQueryValueWith? canonicalValues
    (requests 2) = some (values 2) := by cbv

/-- Every request in this sector is checked, including its full ordered insertions. -/
theorem computed (i : Fin 3) : planeQueryValueWith? canonicalValues
    (requests ⟨0 + i.val, by omega⟩) =
      some (values ⟨0 + i.val, by omega⟩) := by
  fin_cases i
  · exact value_0
  · exact value_1
  · exact value_2

end AxiomaticGW.GKM.PlaneGenusTwoFewMarkingsReplay.OnePoint

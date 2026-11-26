/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootReplayFlatContext
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1SelectedComponentsRow0175

@[expose] public section
set_option maxRecDepth 65536
set_option Elab.async false
set_option maxHeartbeats 0

namespace AxiomaticGW.BlowupF1FullRootReplay.Representative0175

open AxiomaticGW BlowupF1RootAssembly
open scoped BigOperators

/-- Exact certified selection; missing full keys retain the proved-equal fallback. -/
abbrev certifiedCache := AxiomaticGW.BlowupF1SelectedComponentsRow0175.cache

def claimed : ℚ := (1525 / 75816)

theorem coefficient_eq : L24CorrectionsReplay.fullClaim 175 = (-3050 / 1053) := by
  decide +kernel

theorem maximum_genus_eq : (L24Gluing.term 175).expression.maxComponentGenus = 1 := by
  decide +kernel

theorem root_code_eq : rootCode (L24Gluing.term 175).expression = 1 := by
  decide +kernel

def fundamentalClaim : ℚ := 0

def separatingClaim (i : Fin 4) (b : SurfaceBasisLabel X) (k : Fin 2) : ℚ :=
  match b with
  | .unit =>
      (![
        ![0, 0],
        ![0, 0],
        ![0, 0],
        ![0, 0]
      ] : Fin 4 → Fin 2 → ℚ) i k
  | .hyperplane =>
      (![
        ![(1525 / 50544), 0],
        ![0, 0],
        ![0, 0],
        ![0, 0]
      ] : Fin 4 → Fin 2 → ℚ) i k
  | .exceptional _ =>
      (![
        ![(-1525 / 151632), 0],
        ![0, 0],
        ![0, 0],
        ![0, 0]
      ] : Fin 4 → Fin 2 → ℚ) i k
  | .point =>
      (![
        ![0, 0],
        ![0, 0],
        ![0, 0],
        ![0, 0]
      ] : Fin 4 → Fin 2 → ℚ) i k

def nonseparatingClaim (b : SurfaceBasisLabel X) : ℚ :=
  match b with
  | .unit => 0
  | .hyperplane => 0
  | .exceptional _ => 0
  | .point => 0


end AxiomaticGW.BlowupF1FullRootReplay.Representative0175

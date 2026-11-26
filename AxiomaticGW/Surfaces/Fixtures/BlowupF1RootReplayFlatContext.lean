/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsFlat
public import AxiomaticGW.Surfaces.GenusTwoBlowupScalar

@[expose] public section
set_option maxRecDepth 65536
set_option Elab.async false
set_option maxHeartbeats 0

namespace AxiomaticGW.BlowupF1FullRootReplay

open AxiomaticGW BlowupF1RootAssembly
open scoped BigOperators

/-- Exact original722-key cache, via the checked `BlowupF1CompleteHComponentsFlat.cache_eq`. -/
abbrev certifiedCache := BlowupF1CompleteHComponentsFlat.cache

/-- Finite provenance tag only; no graph semantics or constructor is replaced. -/
def rootCode {g : ℕ} {S : Type} [Fintype S] : GluingExpression g S → ℕ
  | @GluingExpression.fundamental _ _ _ _ => 0
  | @GluingExpression.relabel _ _ _ _ _ _ x => rootCode x
  | @GluingExpression.separating _ _ _ _ _ _ _ _ => 1
  | @GluingExpression.nonseparating _ _ _ _ => 2

end AxiomaticGW.BlowupF1FullRootReplay

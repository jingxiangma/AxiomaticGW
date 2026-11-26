/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.ThreePointDescendants

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.MixedAncestorReduction
open AxiomaticGW SurfaceDescendant

/-- Genus-two degree-zero comparison transfers powers without erasing ancestors. -/
example : mixedAncestorTerms (X := .blowupTwo) 2 (Fin 1) (by norm_num [StableArity])
    [0] 0 ![2] ![3] ![.exceptional 1] =
      RationalTerms.term 1 {SurfaceAncestorKey.ofLabels 2 (Fin 1)
        (by norm_num [StableArity]) 0 ![5] ![.exceptional 1]} := by decide +kernel

/-- Repeating a processed marking does not lower another marking's power. -/
example : mixedAncestorTerms (X := .plane) 1 (Fin 2) (by norm_num [StableArity])
    [0,0,1] 0 ![2,1] ![1,3] ![.point,.hyperplane] =
      RationalTerms.term 1 {SurfaceAncestorKey.ofLabels 1 (Fin 2)
        (by norm_num [StableArity]) 0 ![3,4] ![.point,.hyperplane]} := by decide +kernel

/-- Each main replacement retains its ancestor exponent and the exceptional sign. -/
example : mixedAncestorTerms (X := .hirzebruchOne) 1 (Fin 1)
    (by norm_num [StableArity]) [0] ![1,0] ![1] ![2] ![.exceptional 0] =
      RationalTerms.term 1 {SurfaceAncestorKey.ofLabels 1 (Fin 1)
        (by norm_num [StableArity]) ![1,0] ![3] ![.exceptional 0]} +
      RationalTerms.term (-1) {SurfaceAncestorKey.ofLabels 1 (Fin 1)
        (by norm_num [StableArity]) 0 ![2] ![.exceptional 0]} := by decide +kernel

/-- Both descendant markings can carry a positive rational tail. -/
example : threePointValue .plane ![2] ![2,2,0] ![.point,.point,.unit] = 1 := by
  decide +kernel

/-- Equal-energy exceptional classes must not be merged. -/
example : threePointValue .blowupTwo ![1,0,0] ![1,0,0]
      ![.exceptional 0,.exceptional 0,.unit] = 1 ∧
    threePointValue .blowupTwo ![0,1,0] ![1,0,0]
      ![.exceptional 0,.exceptional 0,.unit] = 0 := by decide +kernel

/-- Descendants and exceptional multiple covers can have negative values. -/
example : threePointValue .plane ![1] ![3,0,0] ![.hyperplane,.hyperplane,.unit] = -2 ∧
    threePointValue .hirzebruchOne ![2,0] ![1,1,0]
      ![.exceptional 0,.exceptional 0,.unit] = -1 := by decide +kernel

/-- Three-point degree-zero descendants are distinguished from classical primaries. -/
example : threePointValue .hirzebruchOne 0 ![0,0,0]
      ![.exceptional 0,.exceptional 0,.unit] = -1 ∧
    threePointValue .hirzebruchOne 0 ![1,0,0]
      ![.exceptional 0,.unit,.unit] = 0 := by decide +kernel

end AxiomaticGWTest.Surfaces.MixedAncestorReduction

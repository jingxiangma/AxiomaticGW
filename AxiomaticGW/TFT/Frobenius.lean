/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.TFT.Basic
public import AxiomaticGW.TFT.Sewing

/-!
# The correlator theory associated to a Frobenius algebra

This file bundles the correlators of a finite-free commutative Frobenius
algebra and the gluing theorems already proved for them.
-/

@[expose] public section

namespace AxiomaticGW

namespace CommFrobeniusAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]

/-- The topological correlator theory canonically associated to a
finite-free commutative Frobenius algebra. -/
noncomputable def toTopologicalCorrelatorTheory
    (F : CommFrobeniusAlgebra R A) :
    TopologicalCorrelatorTheory R A where
  pairing := F.pairing
  unit := 1
  correlator := F.correlator
  relabel := F.correlator_domDomCongr
  unit_insert := F.correlator_option_one_apply
  nonseparating := F.selfContract_correlator
  separating := F.pairContract_correlator
  normalization := F.correlator_zero_fin_two_apply

end CommFrobeniusAlgebra

end AxiomaticGW

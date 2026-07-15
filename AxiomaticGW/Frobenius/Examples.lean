/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
import AxiomaticGW.Frobenius.Constructions

/-!
# Frobenius algebra examples

This file is the home for concrete examples and API regression tests.
-/

namespace AxiomaticGW

open TensorProduct

namespace CommFrobeniusAlgebra

/-- The base ring is a Frobenius algebra over itself, with counit the identity
linear map. -/
def baseRing (R : Type*) [CommRing R] : CommFrobeniusAlgebra R R where
  counit := LinearMap.id
  isPerfPair := by
    constructor
    · constructor
      · intro x y h
        have h1 := DFunLike.congr_fun h 1
        simpa using h1
      · intro f
        refine ⟨f 1, ?_⟩
        apply LinearMap.ext
        intro y
        simpa [smul_eq_mul, mul_comm] using (f.map_smul y 1).symm
    · constructor
      · intro x y h
        have h1 := DFunLike.congr_fun h 1
        simpa using h1
      · intro f
        refine ⟨f 1, ?_⟩
        apply LinearMap.ext
        intro y
        simpa [smul_eq_mul, mul_comm] using (f.map_smul y 1).symm

@[simp]
theorem baseRing_counit_apply (R : Type*) [CommRing R] (x : R) :
    (baseRing R).counit x = x := rfl

@[simp]
theorem baseRing_pairing_apply (R : Type*) [CommRing R] (x y : R) :
    (baseRing R).pairing.form x y = x * y := rfl

@[simp]
theorem baseRing_casimir (R : Type*) [CommRing R] :
    (baseRing R).casimir = 1 ⊗ₜ[R] 1 := by
  apply (baseRing R).pairing.tensorEndEquiv.injective
  apply LinearMap.ext
  intro x
  simp

@[simp]
theorem baseRing_handleElement (R : Type*) [CommRing R] :
    (baseRing R).handleElement = 1 := by
  simp [handleElement]

end CommFrobeniusAlgebra

end AxiomaticGW

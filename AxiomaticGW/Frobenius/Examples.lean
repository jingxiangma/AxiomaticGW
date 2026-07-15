/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
import AxiomaticGW.Frobenius.Constructions

/-!
# Frobenius algebra examples

This file is the home for concrete examples and API regression tests.

The first example is deliberately elementary, but its perfectness proof shows
the shape of the definitions.  `LinearMap.IsPerfPair` asks for bijectivity in
both arguments.  Lean's `constructor` tactic splits a conjunction-like goal
into its fields, while `intro` introduces variables and hypotheses.
-/

namespace AxiomaticGW

open TensorProduct

namespace CommFrobeniusAlgebra

/-- The base ring is a Frobenius algebra over itself, with counit the identity
linear map.  Its pairing is ordinary multiplication: `η(x,y) = x*y`. -/
def baseRing (R : Type*) [CommRing R] : CommFrobeniusAlgebra R R where
  counit := LinearMap.id
  isPerfPair := by
    -- Perfectness asks for bijectivity in the left and right arguments.
    constructor
    -- Left argument: x is sent to the functional y ↦ x*y.
    · constructor
      -- Injectivity: equal functionals are equal at 1, hence x = y.
      · intro x y h
        have h1 := DFunLike.congr_fun h 1
        simpa using h1
      -- Surjectivity: every linear functional f : R → R is multiplication by
      -- f(1), because linearity gives f(y) = y*f(1).
      · intro f
        refine ⟨f 1, ?_⟩
        apply LinearMap.ext
        intro y
        simpa [smul_eq_mul, mul_comm] using (f.map_smul y 1).symm
    -- Right argument: the same proof works, using commutativity of R.
    · constructor
      · intro x y h
        have h1 := DFunLike.congr_fun h 1
        simpa using h1
      · intro f
        refine ⟨f 1, ?_⟩
        apply LinearMap.ext
        intro y
        simpa [smul_eq_mul, mul_comm] using (f.map_smul y 1).symm

/-- In the base-ring example, the counit really is the identity function. -/
@[simp]
theorem baseRing_counit_apply (R : Type*) [CommRing R] (x : R) :
    (baseRing R).counit x = x := rfl

/-- The derived Frobenius pairing on the base ring is multiplication. -/
@[simp]
theorem baseRing_pairing_apply (R : Type*) [CommRing R] (x y : R) :
    (baseRing R).pairing.form x y = x * y := rfl

/-- The inverse metric for the pairing `η(x,y)=x*y` is `1 ⊗ 1`.

The proof applies the injective map `tensorEndEquiv` to both sides, reducing a
tensor equality to an equality of endomorphisms.  `ext x` then reduces that to
pointwise equality on an arbitrary element. -/
@[simp]
theorem baseRing_casimir (R : Type*) [CommRing R] :
    (baseRing R).casimir = 1 ⊗ₜ[R] 1 := by
  apply (baseRing R).pairing.tensorEndEquiv.injective
  apply LinearMap.ext
  intro x
  simp

/-- Multiplying the two legs of `1 ⊗ 1` gives the handle element `1`. -/
@[simp]
theorem baseRing_handleElement (R : Type*) [CommRing R] :
    (baseRing R).handleElement = 1 := by
  simp [handleElement]

end CommFrobeniusAlgebra

end AxiomaticGW

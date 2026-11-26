/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.CohFT.GluingForgetful

/-!
# A kappa product derived from proper-map composition

The new input below is proper pushforward functoriality
for two equal composites of the universal forgetful and nonseparating gluing
maps. It is quantified over arbitrary source classes; it mentions neither
kappa nor a Hodge packet nor a product. It is not proved or installed as an axiom.

Bae--Schmitt, `Chow rings of stacks of prestable curves I`, Theorem 1.1 and
Proposition 3.11 (stable remaining vertex), justify the geometric mechanism:
https://arxiv.org/pdf/2012.09887 . Supplying this input in an actual geometric
model remains a separate obligation.

Together with the already existing forgetful base change, cotangent pullback,
and two projection formulas, the input derives an actual kappa-times-boundary
identity. The exponent is arbitrary; no numerical product value is supplied.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW

universe u

/-- Covariant functoriality for forgetting and gluing the same ordered node.
The relabelling moves the new marking past the two node labels. -/
structure ForgetfulNonseparatingComposition {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (Fforget : ForgetfulPushforward C I) (N : NonseparatingPushforward C I) : Prop where
  push_comp : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity (g + 1) S)
      (z : C.H g (Option (Option (Option S)))),
    Fforget.push (g + 1) S h
        (N.push g (Option S) h.option
          (C.rename g (Option (Option (Option S))) (Option (Option (Option S)))
            (StableArity.option (StableArity.double_option_iff.mpr h))
            (StableArity.double_option_iff.mpr h.option)
            (forgetNonseparatingEquiv S).symm z)) =
      N.push g S h
        (Fforget.push g (Option (Option S)) (StableArity.double_option_iff.mpr h) z)

namespace ForgetfulNonseparatingComposition

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
  {Fforget : ForgetfulPushforward C I} {N : NonseparatingPushforward C I}

/-- A target kappa factor can be moved to the node source. This is derived
from primitive map laws and retains an arbitrary source insertion. -/
theorem kappa_mul_push (T : ForgetfulNonseparatingComposition Fforget N)
    (P : PsiClasses C) (F : SeparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity (g + 1) S)
    (m : ℕ) (x : C.H g (Option (Option S))) :
    P.kappa Fforget (g + 1) S h m * N.push g S h x =
      N.push g S h
        (P.kappa Fforget g (Option (Option S))
          (StableArity.double_option_iff.mpr h) m * x) := by
  let hsource := StableArity.double_option_iff.mpr h
  let transport := C.rename g (Option (Option (Option S)))
    (Option (Option (Option S))) hsource.option
    (StableArity.double_option_iff.mpr h.option) (forgetNonseparatingEquiv S).symm
  let ptarget := P.psi (g + 1) (Option S) h.option none ^ (m + 1)
  let psource := P.psi g (Option (Option (Option S))) hsource.option none ^ (m + 1)
  have hp : C.nonseparating g (Option S) h.option ptarget = transport psource := by
    dsimp only [ptarget, psource, transport]
    rw [map_pow, P.nonseparating_psi, map_pow, P.rename_psi]
    rfl
  calc
    P.kappa Fforget (g + 1) S h m * N.push g S h x =
        Fforget.push (g + 1) S h (C.forget (g + 1) S h (N.push g S h x) *
          ptarget) := by
      rw [Fforget.projection_formula]
      exact mul_comm _ _
    _ = Fforget.push (g + 1) S h
        (N.push g (Option S) h.option
          (transport (C.forget g (Option (Option S)) hsource x)) * ptarget) := by
      rw [H.nonseparating]
    _ = Fforget.push (g + 1) S h
        (N.push g (Option S) h.option
          (C.nonseparating g (Option S) h.option ptarget *
            transport (C.forget g (Option (Option S)) hsource x))) := by
      rw [N.projection_formula]
      congr 1
      exact mul_comm _ _
    _ = Fforget.push (g + 1) S h
        (N.push g (Option S) h.option
          (transport (psource * C.forget g (Option (Option S)) hsource x))) := by
      rw [hp, map_mul transport]
    _ = N.push g S h
        (Fforget.push g (Option (Option S)) hsource
          (psource * C.forget g (Option (Option S)) hsource x)) :=
      T.push_comp g S h _
    _ = N.push g S h
        (P.kappa Fforget g (Option (Option S)) hsource m * x) := by
      congr 1
      calc
        Fforget.push g (Option (Option S)) hsource
            (psource * C.forget g (Option (Option S)) hsource x) =
            Fforget.push g (Option (Option S)) hsource
              (C.forget g (Option (Option S)) hsource x * psource) := by
          rw [mul_comm psource]
        _ = x * P.kappa Fforget g (Option (Option S)) hsource m :=
          Fforget.projection_formula g (Option (Option S)) hsource x psource
        _ = P.kappa Fforget g (Option (Option S)) hsource m * x := mul_comm _ _

end ForgetfulNonseparatingComposition

end AxiomaticGW

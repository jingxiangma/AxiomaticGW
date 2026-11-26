/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.GenusTwoHodgeGeometricVertex
public import AxiomaticGW.GKM.Fixtures.GenusTwoHodgeNormalizedPacket
public import AxiomaticGW.GKM.Fixtures.ExceptionalGenusTwoCubicReplay
public import AxiomaticGW.GKM.EllipticLocalizationVertex

/-! # Stable-curve integration on the primitive exceptional cubic-descendant loci

There are two elliptic splits and four choices with the full genus on a single
endpoint. The signed sum retains the primitive edge, tangent normalization,
own-divisor restriction and the original unstable-endpoint convention.
-/

@[expose] public noncomputable section
namespace AxiomaticGW.GKM.ExceptionalCubicGeometricLoci
open EquivariantCoefficients ExceptionalBoundaryData
open ExceptionalGenusTwoCubic ExceptionalGenusTwoCubicReplay GenusTwoVertexHodgeReduction
open GenusTwoLocalizationVertex GenusTwoLocalizationClass
open ExceptionalGenusTwoVertexValues (seed)
open GenusTwoHodgeGeometricVertex GenusTwoHodgePicardMoments GenusTwoHodgeNormalization
open PsiBoundaryExpansion

/-- The cubic marking sits either on the genus-two vertex or on its opposite rational end. -/
def powers (marked : Bool) : List ℕ := if marked then [3] else []

private theorem one_flag_profiles : ∀ (m : Bool) (i j : Fin 3),
    profiles 1 (powers m) i j = if i.val + j.val ≤ available m then
      {fun _ ↦ available m - i.val - j.val} else ∅ := by decide +kernel

private theorem signed_moment : ∀ (m : Bool) (i j : Fin 3), i.val + j.val ≤ available m →
    (-1 : ℚ) ^ (i.val + j.val) * evaluate seed (min i j) (max i j) min_le_max
      (powers m ++ [available m - i.val - j.val]) = hodge m i j := by decide +kernel

/-- The all-valence genus-two source recovers the primitive endpoint factor, including
the native convention that the external marking precedes the flag in the Hodge integral. -/
theorem reduced_one_flag (m : Bool) (w t : Coefficient) (hw : w ≠ 0) :
    reduced seed (powers m) w t (fun _ : Fin 1 ↦ w) = stableVertex m w t := by
  rw [stable_expansion m w t hw]
  unfold reduced source
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [one_flag_profiles]
  by_cases h : i.val + j.val ≤ available m
  · simp only [if_pos h, Finset.sum_singleton, Fin.prod_univ_one]
    rw [show (List.ofFn (fun _ : Fin 1 ↦ available m - i.val - j.val)) =
      [available m - i.val - j.val] by rfl, signed_moment m i j h]
  · simp only [if_neg h, Finset.sum_empty, hodge, Rat.cast_zero, zero_mul]


/-- Geometric elliptic source with one incident flag and either marking placement. The Hodge
line is left arbitrary because the cubic marking already exceeds the dimension of its vertex. -/
def ellipticEnd {C : StableCurveCohomology ℚ} (P : PsiClasses C) (I : StableCurveIntegration C)
    (hodgeLine : ∀ n, C.H 1 (Fin n ⊕ Fin 1)) (marked : Bool) (w t : Coefficient) : Coefficient :=
  let p := powers marked
  have h : StableArity 1 (Fin p.length ⊕ Fin 1) := by
    simp only [StableArity, Fintype.card_sum, Fintype.card_fin]
    omega
  EllipticHodge.source p w t (fun _ : Fin 1 ↦ w) fun i j d ↦
    I.integrate 1 _ h (P.monomial 1 _ h d *
      ((if i = 0 then 1 else hodgeLine _) * (if j = 0 then 1 else hodgeLine _)))

/-- Supply the two stable-vertex functions to the original degree-one graph factors.
On an elliptic split the first vertex here is the marked one. On the other four loci
the genus-two vertex is first. These orderings determine the restrictions of the divisor. -/
def assemble (c : Case) (elliptic genusTwo : Bool → Coefficient → Coefficient → Coefficient)
    (g : Fin 3) (m : Fin 2) : Coefficient :=
  let edge := (factors c).edge * (factors c).tangent
  if g = 1 then
    let w := characters c (if m = 0 then x - y else y - x)
    let t := characters c (if m = 0 then y else x)
    let u := characters c (if m = 0 then x else y)
    edge * t * elliptic true w t * elliptic false (-w) u
  else
    let w := characters c (if g = 2 then x - y else y - x)
    let t := characters c (if g = 2 then y else x)
    let u := characters c (if g = 2 then x else y)
    let marked := decide ((g = 2 ∧ m = 0) ∨ (g = 0 ∧ m = 1))
    edge * (if marked then t else u) * genusTwo marked w t *
      ((if marked then -w else (-(-w)) ^ 3) / ((-w) * u))

/-- All six fixed-locus contributions are obtained by integrating stable-curve classes.
The sum gives the full two-character expression on each of the three exceptional axes. -/
theorem geometric_sum {C : StableCurveCohomology ℚ} {I : StableCurveIntegration C}
    {D : HodgeClasses C} (H : D.Natural) (U : ForgetfulPushforward C I)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (P : PsiClasses C) (K : PsiForgetFormula P) (hK : TailCompatible K F N)
    (T : TailForgetCompatible C) (Q : ForgetfulSquareCompatibility U F)
    (G : GluingForgetfulCompatibility F N)
    {A : ∀ g S, [Fintype S] → StrataRealization C g S}
    (B : PicardRealization D F N A) (E : Normalization D N) (ell : EllipticPsi P F N A)
    (vol : I.integrate 0 (Option Bool) tailStable 1 = 1)
    (base : P.kappa U 2 (Fin 0) (stable 0) 0 = 2)
    (second : GenusTwoHodgeNormalizedPacket.SecondRealization D F N A)
    (dvv : PointTarget.DVVRecursion P I) (hodgeLine : ∀ n, C.H 1 (Fin n ⊕ Fin 1)) (c : Case) :
    (∑ g : Fin 3, ∑ m : Fin 2,
      assemble c (ellipticEnd P I hodgeLine) (fun marked w t ↦
        integrate I _ (integrand D P (powers marked) w t (fun _ : Fin 1 ↦ w))) g m) =
      equivariant c := by
  rw [← ExceptionalGenusTwoCubicReplay.sum_loci c]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro m _
  by_cases hg : g = 1
  · have zero (w t : Coefficient) : ellipticEnd P I hodgeLine true w t = 0 := by
      unfold ellipticEnd
      apply EllipticHodge.source_zero_of_excess
      decide
    simp only [assemble, locus, if_pos hg, zero, mul_zero, zero_mul]
  · have hw : characters c (if g = 2 then x - y else y - x) ≠ 0 := by
      apply (map_ne_zero (characters c)).mpr
      split <;> first | exact x_sub_y_ne_zero | exact y_sub_x_ne_zero
    have square := GenusTwoHodgeNormalizedPacket.square B E second
    simp only [assemble, locus, if_neg hg,
      integrated_vertex H U F N P K hK T Q G B E ell vol base square dvv, reduced_one_flag _ _ _ hw]

end AxiomaticGW.GKM.ExceptionalCubicGeometricLoci

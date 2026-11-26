/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneMixedPointContractions

/-!
# Source-degree cancellation in the shifted plane equations

The HHP, HPP and PPP equations have no genus-two coefficient at their source
degree. With zero effective remainder, every rational component is classical.
A rational pair containing a point and another positive-codimension state
vanishes; a rational quadruple also vanishes. These facts apply before any
choice of requested variable. In HHP the two surviving single-psi terms
cancel because their main states are equal points and their coefficients are opposite.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open SurfacePolynomialReduction SurfaceGenusTwo GluingExpression

/-- Relabelling acts on the external states of the actual remainder contraction. -/
theorem plane_remainder_orbit (v : Variable .plane) (n : ℕ)
    (delta : SurfaceTarget.plane.Curve) (a : Fin 3 → SurfaceBasisLabel .plane)
    (i : Fin 20) (e : Fin 6) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (orbitCotangentTerm i e) delta n a =
      remainderPointCoefficient .plane v (planeCoefficientVertex v)
        (paperCotangentTerm i) delta n (a ∘ labelPermutation e) := by
  simp only [orbitCotangentTerm, CotangentTerm.relabel, remainderPointCoefficient,
    GluingExpression.maxComponentGenus, remainderContraction]

/-- The six labelled occurrences are retained, without averaging even when
some external states agree. -/
theorem sum_plane_remainder_orbit (v : Variable .plane) (n : ℕ)
    (delta : SurfaceTarget.plane.Curve) (a : Fin 3 → SurfaceBasisLabel .plane)
    (i : Fin 20) :
    let f := fun b ↦ remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm i) delta n b
    (∑ e : Fin 6, remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (orbitCotangentTerm i e) delta n a) =
      f ![a 0, a 1, a 2] + f ![a 0, a 2, a 1] + f ![a 1, a 0, a 2] +
        f ![a 2, a 0, a 1] + f ![a 1, a 2, a 0] + f ![a 2, a 1, a 0] := by
  have hl (e : Fin 6) : a ∘ labelPermutation e =
      (![![a 0, a 1, a 2], ![a 0, a 2, a 1], ![a 1, a 0, a 2],
        ![a 2, a 0, a 1], ![a 1, a 2, a 0], ![a 2, a 1, a 0]] :
          Fin 6 → Fin 3 → SurfaceBasisLabel .plane) e := by
    funext j
    fin_cases e <;> fin_cases j <;> rfl
  simp only [plane_remainder_orbit, hl, Fin.sum_univ_six]
  rfl

/-- The second diagram cannot have zero remainder: its classical rational
component already has four markings before any points are added. -/
theorem plane_paper_one_zero_remainder (v : Variable .plane) (n : ℕ)
    (a : Fin 3 → SurfaceBasisLabel .plane) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm 1) 0 n a = 0 := by
  rw [plane_paper_one_sum,
    (SurfaceTarget.plane.splittings_eq 0).trans SurfaceTarget.plane.effective.splittings_zero]
  simp only [Finset.sum_singleton, SurfaceGenusZero.primaryScalar_plane_zero_four,
    mul_zero, Finset.sum_const_zero]

private theorem paper_zero_remainder_pair (v : Variable .plane) (n : ℕ)
    (i : Fin 4) (a b : SurfaceBasisLabel .plane) (hb : b = .hyperplane ∨ b = .point) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm (Fin.castAdd 16 i)) 0 n ![a, b, .point] = 0 := by
  fin_cases i
  · change remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm 0) 0 n ![a, b, .point] = 0
    rw [plane_paper_zero_pair]
    exact remainderContraction_plane_pair_zero_of_point v _ n _ _ _ a b hb
  · exact plane_paper_one_zero_remainder v n _
  · change remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm (if (0 : Fin 2) = 0 then 2 else 3)) 0 n ![a, b, .point] = 0
    rw [plane_paper_onePsi_pair]
    exact remainderContraction_plane_pair_zero_of_point v _ n _ _ _ a b hb
  · change remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm (if (1 : Fin 2) = 0 then 2 else 3)) 0 n ![a, b, .point] = 0
    rw [plane_paper_onePsi_pair]
    exact remainderContraction_plane_pair_zero_of_point v _ n _ _ _ a b hb

private theorem paper_zero_remainder_pair_swapped (v : Variable .plane) (n : ℕ)
    (i : Fin 4) (a b : SurfaceBasisLabel .plane) (hb : b = .hyperplane ∨ b = .point) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm (Fin.castAdd 16 i)) 0 n ![a, .point, b] = 0 := by
  fin_cases i
  · change remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm 0) 0 n ![a, .point, b] = 0
    rw [plane_paper_zero_pair]
    erw [remainderContraction_plane_pair_swap]
    exact remainderContraction_plane_pair_zero_of_point v _ n _ _ _ a b hb
  · exact plane_paper_one_zero_remainder v n _
  · change remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm (if (0 : Fin 2) = 0 then 2 else 3)) 0 n ![a, .point, b] = 0
    rw [plane_paper_onePsi_pair, remainderContraction_plane_pair_swap]
    exact remainderContraction_plane_pair_zero_of_point v _ n _ _ _ a b hb
  · change remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm (if (1 : Fin 2) = 0 then 2 else 3)) 0 n ![a, .point, b] = 0
    rw [plane_paper_onePsi_pair, remainderContraction_plane_pair_swap]
    exact remainderContraction_plane_pair_zero_of_point v _ n _ _ _ a b hb

/-- Every requested variable has zero coefficient at zero remainder in HPP
and PPP. The arbitrary main family is eliminated by classical rational factors. -/
theorem planeRemainderPointCoefficient_two_points_zero (v : Variable .plane) (n : ℕ)
    (a : SurfaceBasisLabel .plane) (ha : a = .hyperplane ∨ a = .point) :
    planeRemainderPointCoefficient n 0 ![a, .point, .point] v = 0 := by
  unfold planeRemainderPointCoefficient
  apply Finset.sum_eq_zero
  intro i _
  apply mul_eq_zero_of_right
  rw [sum_plane_remainder_orbit]
  change
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
        (paperCotangentTerm (Fin.castAdd 16 i)) 0 n ![a, .point, .point] +
      remainderPointCoefficient .plane v (planeCoefficientVertex v)
        (paperCotangentTerm (Fin.castAdd 16 i)) 0 n ![a, .point, .point] +
      remainderPointCoefficient .plane v (planeCoefficientVertex v)
        (paperCotangentTerm (Fin.castAdd 16 i)) 0 n ![.point, a, .point] +
      remainderPointCoefficient .plane v (planeCoefficientVertex v)
        (paperCotangentTerm (Fin.castAdd 16 i)) 0 n ![.point, a, .point] +
      remainderPointCoefficient .plane v (planeCoefficientVertex v)
        (paperCotangentTerm (Fin.castAdd 16 i)) 0 n ![.point, .point, a] +
      remainderPointCoefficient .plane v (planeCoefficientVertex v)
        (paperCotangentTerm (Fin.castAdd 16 i)) 0 n ![.point, .point, a] = 0
  rw [paper_zero_remainder_pair v n i a .point (Or.inr rfl),
    paper_zero_remainder_pair v n i .point a ha,
    paper_zero_remainder_pair_swapped v n i .point a ha]
  norm_num

/-- The zero-remainder result is a coefficient theorem for the entire
normalized BP equation, at the requested variable's exact full curve class. -/
theorem normalized_plane_two_points_source_degree (v : Variable .plane) (n : ℕ)
    (a : SurfaceBasisLabel .plane) (ha : a = .hyperplane ∨ a = .point) :
    RationalTerms.coefficient
      (normalizedGenusTwoTerms .plane n (SurfaceGenusZero.variableCurve v) 0
        (SurfaceGenusZero.pointLabels ![a, .point, .point] n)) {v} = 0 := by
  rw [← pointCoefficient_eq_full]
  have h := planeRemainderPointCoefficient_eq n 0 ![a, .point, .point] v
  rw [add_zero] at h
  rw [← h, planeRemainderPointCoefficient_two_points_zero v n a ha]

/-- In the first HHP diagram, the outer classical component leaves a point
at the inner rational node, whose two point states force vanishing. -/
theorem plane_paper_zero_point_two_hyperplanes_zero (v : Variable .plane) (n : ℕ) :
    remainderPointCoefficient .plane v (planeCoefficientVertex v)
      (paperCotangentTerm 0) 0 n ![.point, .hyperplane, .hyperplane] = 0 := by
  rw [plane_paper_zero_pair]
  erw [remainderContraction_plane_two_hyperplanes_zero]
  exact remainderContraction_plane_inner_two_points_zero v _ n ![0]

/-- Source-degree HHP terms cancel in the actual raw BP sum. The two
single-psi diagrams survive separately; their equal point states and opposite
coefficients, rather than dimension vanishing, give the cancellation. -/
theorem planeRemainderPointCoefficient_two_hyperplanes_zero (v : Variable .plane) (n : ℕ) :
    planeRemainderPointCoefficient n 0 ![.hyperplane, .hyperplane, .point] v = 0 := by
  have horbit (i : Fin 4) :
      (∑ e : Fin 6, remainderPointCoefficient .plane v (planeCoefficientVertex v)
        (orbitCotangentTerm (Fin.castAdd 16 i) e) 0 n ![.hyperplane, .hyperplane, .point]) =
        2 * remainderPointCoefficient .plane v (planeCoefficientVertex v)
          (paperCotangentTerm (Fin.castAdd 16 i)) 0 n ![.point, .hyperplane, .hyperplane] := by
    rw [sum_plane_remainder_orbit]
    change
      remainderPointCoefficient .plane v (planeCoefficientVertex v)
          (paperCotangentTerm (Fin.castAdd 16 i)) 0 n ![.hyperplane, .hyperplane, .point] +
        remainderPointCoefficient .plane v (planeCoefficientVertex v)
          (paperCotangentTerm (Fin.castAdd 16 i)) 0 n ![.hyperplane, .point, .hyperplane] +
        remainderPointCoefficient .plane v (planeCoefficientVertex v)
          (paperCotangentTerm (Fin.castAdd 16 i)) 0 n ![.hyperplane, .hyperplane, .point] +
        remainderPointCoefficient .plane v (planeCoefficientVertex v)
          (paperCotangentTerm (Fin.castAdd 16 i)) 0 n ![.point, .hyperplane, .hyperplane] +
        remainderPointCoefficient .plane v (planeCoefficientVertex v)
          (paperCotangentTerm (Fin.castAdd 16 i)) 0 n ![.hyperplane, .point, .hyperplane] +
        remainderPointCoefficient .plane v (planeCoefficientVertex v)
          (paperCotangentTerm (Fin.castAdd 16 i)) 0 n ![.point, .hyperplane, .hyperplane] = _
    rw [paper_zero_remainder_pair v n i .hyperplane .hyperplane (Or.inl rfl),
      paper_zero_remainder_pair_swapped v n i .hyperplane .hyperplane (Or.inl rfl)]
    ring
  simp only [planeRemainderPointCoefficient, horbit, Fin.sum_univ_four]
  simp only [show Fin.castAdd 16 (0 : Fin 4) = (0 : Fin 20) from rfl,
    show Fin.castAdd 16 (1 : Fin 4) = (1 : Fin 20) from rfl,
    show Fin.castAdd 16 (2 : Fin 4) = (2 : Fin 20) from rfl,
    show Fin.castAdd 16 (3 : Fin 4) = (3 : Fin 20) from rfl]
  rw [plane_paper_zero_point_two_hyperplanes_zero, plane_paper_one_zero_remainder]
  have h0 := plane_paper_onePsi_two_hyperplanes_zero v n (0 : Fin 2) .point
  have h1 := plane_paper_onePsi_two_hyperplanes_zero v n (1 : Fin 2) .point
  simp only [ite_true] at h0
  simp only [if_neg (by decide : (1 : Fin 2) ≠ 0)] at h1
  rw [h0, h1, remainderVertex_plane_two_points_onePsi_zero_swap]
  change (-2 : ℚ) * (2 * 0) + 2 * (2 * 0) + 3 * (2 * _) + (-3) * (2 * _) = 0
  ring

/-- HHP source-degree cancellation also holds in the complete normalized
equation, for every primary, first-descendant or higher-ancestor variable. -/
theorem normalized_plane_two_hyperplanes_source_degree (v : Variable .plane) (n : ℕ) :
    RationalTerms.coefficient
      (normalizedGenusTwoTerms .plane n (SurfaceGenusZero.variableCurve v) 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .point] n)) {v} = 0 := by
  rw [← pointCoefficient_eq_full]
  have h := planeRemainderPointCoefficient_eq n 0 ![.hyperplane, .hyperplane, .point] v
  rw [add_zero] at h
  rw [← h, planeRemainderPointCoefficient_two_hyperplanes_zero]

private theorem degree_lt_of_source_zero (v : Variable .plane) (n source : ℕ)
    (a : Fin 3 → SurfaceBasisLabel .plane)
    (hs : RationalTerms.coefficient
      (normalizedGenusTwoTerms .plane n (SurfaceGenusZero.variableCurve v) 0
        (SurfaceGenusZero.pointLabels a n)) {v} = 0)
    (hc : RationalTerms.coefficient
      (normalizedGenusTwoTerms .plane n ![source] 0
        (SurfaceGenusZero.pointLabels a n)) {v} ≠ 0) :
    SurfaceGenusZero.variableCurve v 0 < source := by
  by_contra hlt
  have hle : source ≤ SurfaceGenusZero.variableCurve v 0 := by omega
  by_cases he : SurfaceGenusZero.variableCurve v 0 = source
  · have hb : SurfaceGenusZero.variableCurve v = ![source] := by
      funext i
      fin_cases i
      exact he
    rw [hb] at hs
    exact hc hs
  · have hgt : ¬SurfaceGenusZero.variableCurve v 0 ≤ source := by omega
    apply hc
    rw [← pointCoefficient_eq_full, ← planePointCoefficientByRemainder_eq,
      planePointCoefficientByRemainder, if_neg hgt]

/-- Every nonzero genus-two coefficient in HPP or PPP has degree strictly
below the equation degree. This does not yet identify all variables at the
next degree or prove a reconstruction pivot. -/
theorem normalized_plane_two_points_degree_lt (v : Variable .plane) (n source : ℕ)
    (a : SurfaceBasisLabel .plane) (ha : a = .hyperplane ∨ a = .point)
    (hc : RationalTerms.coefficient
      (normalizedGenusTwoTerms .plane n ![source] 0
        (SurfaceGenusZero.pointLabels ![a, .point, .point] n)) {v} ≠ 0) :
    SurfaceGenusZero.variableCurve v 0 < source :=
  degree_lt_of_source_zero v n source ![a, .point, .point]
    (normalized_plane_two_points_source_degree v n a ha) hc

/-- The same strict source-degree support holds for HHP after the actual
cancellation of its two single-psi diagrams. -/
theorem normalized_plane_two_hyperplanes_degree_lt (v : Variable .plane) (n source : ℕ)
    (hc : RationalTerms.coefficient
      (normalizedGenusTwoTerms .plane n ![source] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .point] n)) {v} ≠ 0) :
    SurfaceGenusZero.variableCurve v 0 < source :=
  degree_lt_of_source_zero v n source ![.hyperplane, .hyperplane, .point]
    (normalized_plane_two_hyperplanes_source_degree v n) hc

end AxiomaticGW.BelorousskiPandharipande

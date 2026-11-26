/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroMarkings
public import AxiomaticGW.Surfaces.GenusZeroStep

/-!
# A uniform primary genus-zero WDVV pivot

The hyperplane has square the point class on all three fixed surfaces. The
`H,H,pt,pt` request, with the remaining points added by the original forgetful
construction, therefore has leading coefficient one at energy at least four.
Low-energy classes remain separate reconstruction obligations.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusZero

private theorem constant_fundamental {X : SurfaceTarget} (S : Type) [Fintype S]
    (h : StableArity 0 S) (a : S → SurfaceBasisLabel X) :
    constantCoefficient (GluingExpression.fundamental 0 S h) a =
      if ((∑ s, (a s).codimension : ℕ) : ℤ) = -1 + (Fintype.card S : ℤ) then
        if Fintype.card S = 3 then
          SurfaceCohomology.counit X.blowups (∏ s, (a s).value) else 0
      else 0 := by
  rw [constantCoefficient_fundamental]
  simp only [SurfaceAncestorKey.DimensionCompatible, SurfaceAncestorKey.totalCodimension,
    SurfaceAncestorKey.primaryLabels, SurfaceAncestorKey.ofLabels, SurfacePrimary.classicalValue,
    Multiset.map_map, Function.comp_def, Pi.zero_apply, add_zero, Nat.cast_zero,
    map_zero, zero_sub, Multiset.card_map, Finset.card_val, Finset.card_univ]
  rfl

private theorem constant_hyperplanes {X : SurfaceTarget} (b : SurfaceBasisLabel X) :
    constantCoefficient
      (GluingExpression.fundamental 0 (Option (Fin 2)) StableArity.zero_option_fin_two)
      (Option.elim · b (fun _ ↦ .hyperplane)) = if b = .unit then 1 else 0 := by
  -- This is a finite three-flag codimension and classical-ring calculation.
  cases b <;>
    norm_num [constant_fundamental, Fintype.sum_option, Fin.sum_univ_two,
      Fintype.prod_option, Fin.prod_univ_two, SurfaceBasisLabel.codimension,
      SurfaceBasisLabel.value, SurfaceCohomology.hyperplane_mul_hyperplane,
      SurfaceCohomology.counit_point, reduceCtorEq, pow_two]
  all_goals
    intro h
    cases h

private theorem constant_points {X : SurfaceTarget} (b : SurfaceBasisLabel X) :
    constantCoefficient
      (GluingExpression.fundamental 0 (Option (Fin 2)) StableArity.zero_option_fin_two)
      (Option.elim · b (fun _ ↦ .point)) = 0 := by
  cases b <;>
    norm_num [constant_fundamental, Fintype.sum_option, Fin.sum_univ_two,
      SurfaceBasisLabel.codimension]

private theorem constant_hyperplane_point {X : SurfaceTarget} (b : SurfaceBasisLabel X) :
    constantCoefficient
      (GluingExpression.fundamental 0 (Option (Fin 2)) StableArity.zero_option_fin_two)
      (Option.elim · b ![.hyperplane, .point]) = 0 := by
  cases b <;>
    norm_num [constant_fundamental, Fintype.sum_option, Fin.sum_univ_two,
      SurfaceBasisLabel.codimension]

private theorem constant_point_hyperplane {X : SurfaceTarget} (b : SurfaceBasisLabel X) :
    constantCoefficient
      (GluingExpression.fundamental 0 (Option (Fin 2)) StableArity.zero_option_fin_two)
      (Option.elim · b ![.point, .hyperplane]) = 0 := by
  cases b <;>
    norm_num [constant_fundamental, Fintype.sum_option, Fin.sum_univ_two,
      SurfaceBasisLabel.codimension]

/-- The shifted singleton coefficient keeps the original signed node contraction. -/
theorem shiftedPointCoefficient_separating {X : SurfaceTarget} (beta : X.Curve) (n : ℕ)
    {S T : Type} [Fintype S] [Fintype T]
    (x : GluingExpression 0 (Option S)) (y : GluingExpression 0 (Option T))
    (a : S ⊕ T → SurfaceBasisLabel X) :
    shiftedPointCoefficient X beta n (x.separating y) rfl a =
      ∑ b : SurfaceBasisLabel X, b.inverseWeight *
        (constantCoefficient x (Option.elim · b (a ∘ Sum.inl)) *
            shiftedPointCoefficient X beta n y rfl (Option.elim · b.dual (a ∘ Sum.inr)) +
          shiftedPointCoefficient X beta n x rfl (Option.elim · b (a ∘ Sum.inl)) *
            constantCoefficient y (Option.elim · b.dual (a ∘ Sum.inr))) := rfl

end AxiomaticGW.SurfaceGenusZero

namespace AxiomaticGW.WDVV

open SurfaceGenusZero

/-- The same four original states work on each fixed surface above the low-energy range. -/
def reconstructionLabels (X : SurfaceTarget) : Fin 4 → SurfaceBasisLabel X :=
  ![.hyperplane, .hyperplane, .point, .point]

private theorem shifted_reconstruction_left (X : SurfaceTarget) (beta : X.Curve) (n : ℕ) :
    shiftedPointCoefficient X beta n (expression 0) rfl (reconstructionLabels X) =
      pointVertexCoefficient X beta n (fun _ : Option (Fin 2) ↦ .point) := by
  have hl : ((reconstructionLabels X) ∘ labels 0) ∘ Sum.inl =
      (fun _ : Fin 2 ↦ SurfaceBasisLabel.hyperplane) := by
    funext i
    fin_cases i <;> rfl
  have hr : ((reconstructionLabels X) ∘ labels 0) ∘ Sum.inr =
      (fun _ : Fin 2 ↦ SurfaceBasisLabel.point) := by
    funext i
    fin_cases i <;> rfl
  change shiftedPointCoefficient X beta n
    ((GluingExpression.fundamental 0 (Option (Fin 2)) StableArity.zero_option_fin_two).separating
      (.fundamental 0 (Option (Fin 2)) StableArity.zero_option_fin_two)) rfl
        ((reconstructionLabels X) ∘ labels 0) = _
  rw [shiftedPointCoefficient_separating]
  simp only [hl, hr, constant_hyperplanes, constant_points, mul_zero, add_zero]
  rw [Finset.sum_eq_single SurfaceBasisLabel.unit]
  · have hp : (Option.elim · (SurfaceBasisLabel.point : SurfaceBasisLabel X)
        (fun _ : Fin 2 ↦ .point)) = (fun _ : Option (Fin 2) ↦ .point) := by
      funext s
      cases s <;> rfl
    simp only [ite_true, SurfaceBasisLabel.inverseWeight, SurfaceBasisLabel.dual,
      one_mul, shiftedPointCoefficient, hp]
  · intro b _ hb
    rw [if_neg hb, zero_mul, mul_zero]
  · exact fun hn ↦ (hn (Finset.mem_univ _)).elim

private theorem shifted_reconstruction_cross (X : SurfaceTarget) (beta : X.Curve) (n : ℕ) :
    shiftedPointCoefficient X beta n (expression 2) rfl (reconstructionLabels X) = 0 := by
  have hl : ((reconstructionLabels X) ∘ labels 2) ∘ Sum.inl =
      ![SurfaceBasisLabel.hyperplane, SurfaceBasisLabel.point] := by
    funext i
    fin_cases i <;> rfl
  have hr : ((reconstructionLabels X) ∘ labels 2) ∘ Sum.inr =
      ![SurfaceBasisLabel.point, SurfaceBasisLabel.hyperplane] := by
    funext i
    fin_cases i <;> rfl
  change shiftedPointCoefficient X beta n
    ((GluingExpression.fundamental 0 (Option (Fin 2)) StableArity.zero_option_fin_two).separating
      (.fundamental 0 (Option (Fin 2)) StableArity.zero_option_fin_two)) rfl
        ((reconstructionLabels X) ∘ labels 2) = _
  rw [shiftedPointCoefficient_separating]
  simp only [hl, hr, constant_hyperplane_point, constant_point_hyperplane,
    zero_mul, mul_zero, add_zero, Finset.sum_const_zero]

/-- The `H,H,pt,pt` coefficient is one on all three targets whenever the
additional point count matches the signed dimension equation. -/
theorem pointMarkedCoefficient_reconstruction (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (henergy : X.effective.energy beta = n + 4) :
    pointMarkedCoefficient X n beta (reconstructionLabels X) = 1 := by
  have hp : pointVertexCoefficient X beta n (fun _ : Option (Fin 2) ↦ .point) = 1 := by
    unfold pointVertexCoefficient
    have hd : ((∑ _ : Option (Fin 2), SurfaceBasisLabel.codimension
          (SurfaceBasisLabel.point : SurfaceBasisLabel X) : ℕ) : ℤ) + (n : ℤ) =
        X.c1Degree beta - 1 + (Fintype.card (Option (Fin 2)) : ℤ) := by
      change (6 : ℤ) + (n : ℤ) = (X.effective.energy beta : ℤ) - 1 + 3
      rw [henergy]
      omega
    rw [if_pos hd]
    simp only [SurfaceBasisLabel.primaryFactor, Finset.prod_const_one]
  norm_num [pointMarkedCoefficient, requested, Fin.sum_univ_three,
    shifted_reconstruction_left, shifted_reconstruction_cross, hp]

/-- Above the finite low-energy sector, the original fully expanded WDVV
request has exactly unit leading coefficient, without a coefficient hypothesis. -/
theorem primaryTerms_reconstruction_coefficient (X : SurfaceTarget) (beta : X.Curve)
    (henergy : 4 ≤ X.effective.energy beta) :
    RationalTerms.coefficient
      (primaryTerms X (X.effective.energy beta - 4) beta 0
        (pointLabels (reconstructionLabels X) (X.effective.energy beta - 4)))
      {pointVariable X beta} = 1 := by
  have hbeta : beta ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at henergy
    omega
  rw [← pointMarkedCoefficient_eq X _ beta hbeta]
  exact pointMarkedCoefficient_reconstruction X _ beta (Nat.sub_add_cancel henergy).symm

/-- The two energy-three classes on F₁ use the existing divisor profiles. -/
def hirzebruchEnergyThreeLabels (beta : SurfaceTarget.hirzebruchOne.Curve) :
    Fin 4 → SurfaceBasisLabel .hirzebruchOne :=
  if beta 1 = 0 then ![.hyperplane, .hyperplane, .point, .exceptional 0]
  else ![.hyperplane, .point, .exceptional 0, .exceptional 0]

/-- Retain the actual nonzero coordinate when choosing the energy-three profile
on the two-point blowup; E₁ and E₂ are not interchangeable. -/
def blowupEnergyThreeLabels (beta : SurfaceTarget.blowupTwo.Curve) :
    Fin 4 → SurfaceBasisLabel .blowupTwo :=
  if beta 2 ≠ 0 then ![.hyperplane, .point, .exceptional 0, .exceptional 0]
  else if beta 0 ≠ 0 then ![.hyperplane, .hyperplane, .point, .exceptional 0]
  else ![.hyperplane, .hyperplane, .point, .exceptional 1]

private theorem hirzebruch_energy_three_checked :
    ∀ beta ∈ SurfaceTarget.hirzebruchOne.bounded 3,
      SurfaceTarget.hirzebruchOne.effective.energy beta = 3 →
        pointMarkedCoefficient .hirzebruchOne 0 beta (hirzebruchEnergyThreeLabels beta) ≠ 0 := by
  decide +kernel

private theorem blowup_energy_three_checked :
    ∀ beta ∈ SurfaceTarget.blowupTwo.bounded 3,
      SurfaceTarget.blowupTwo.effective.energy beta = 3 →
        pointMarkedCoefficient .blowupTwo 0 beta (blowupEnergyThreeLabels beta) ≠ 0 := by
  decide +kernel

/-- Exhaustive kernel checking covers every F₁ class at energy three, using
the proved completeness of the full-coordinate bounded enumeration. -/
theorem primaryTerms_hirzebruch_energy_three_coefficient_ne_zero
    (beta : SurfaceTarget.hirzebruchOne.Curve)
    (henergy : SurfaceTarget.hirzebruchOne.effective.energy beta = 3) :
    RationalTerms.coefficient
      (primaryTerms .hirzebruchOne 0 beta 0 (hirzebruchEnergyThreeLabels beta))
      {pointVariable .hirzebruchOne beta} ≠ 0 := by
  have hb : beta ≠ 0 := by
    intro h
    rw [h, map_zero] at henergy
    omega
  have hc := pointMarkedCoefficient_eq .hirzebruchOne 0 beta hb (hirzebruchEnergyThreeLabels beta)
  simp only [pointLabels] at hc
  rw [← hc]
  apply hirzebruch_energy_three_checked beta _ henergy
  rw [SurfaceTarget.bounded_eq, SurfaceTarget.hirzebruchOne.effective.mem_bounded, henergy]

/-- Exhaustive kernel checking covers every full class at energy three on Bl₂P². -/
theorem primaryTerms_blowup_energy_three_coefficient_ne_zero
    (beta : SurfaceTarget.blowupTwo.Curve)
    (henergy : SurfaceTarget.blowupTwo.effective.energy beta = 3) :
    RationalTerms.coefficient
      (primaryTerms .blowupTwo 0 beta 0 (blowupEnergyThreeLabels beta))
      {pointVariable .blowupTwo beta} ≠ 0 := by
  have hb : beta ≠ 0 := by
    intro h
    rw [h, map_zero] at henergy
    omega
  have hc := pointMarkedCoefficient_eq .blowupTwo 0 beta hb (blowupEnergyThreeLabels beta)
  simp only [pointLabels] at hc
  rw [← hc]
  apply blowup_energy_three_checked beta _ henergy
  rw [SurfaceTarget.bounded_eq, SurfaceTarget.blowupTwo.effective.mem_bounded, henergy]

/-- The plane's energy-three sector is precisely the existing line seed class. -/
theorem plane_energy_three_eq_line (beta : SurfaceTarget.plane.Curve)
    (henergy : SurfaceTarget.plane.effective.energy beta = 3) :
    beta = SurfaceTarget.plane.lineCurve := by
  have hchecked : ∀ b ∈ SurfaceTarget.plane.bounded 3,
      SurfaceTarget.plane.effective.energy b = 3 → b = SurfaceTarget.plane.lineCurve := by
    decide +kernel
  apply hchecked beta _ henergy
  rw [SurfaceTarget.bounded_eq, SurfaceTarget.plane.effective.mem_bounded, henergy]

/-- The original checked WDVV relation now gives a decreasing reconstruction
step at every energy at least four, with no separately supplied pivot proof.
The geometric inputs and the original certificate remain explicit. -/
theorem primary_point_eq_reconstruction {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (expression i).Compatible A F N)
    (hboundary : BoundaryClassesEqual F)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
    (S : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible Adiv)
    (beta : X.Curve) (henergy : 4 ≤ X.effective.energy beta)
    (houtput : ∀ i z, z ∈ (expression i).addMarkings (X.effective.energy beta - 4) →
      z.Compatible A F N)
    (p : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hp : AcceptsExchange p) :
    (SurfaceQuery.points X 0 beta (X.effective.energy beta - 1)).eval U =
      -RationalTerms.eval (SurfacePolynomialReduction.variableEval U P)
        (lowerTerms X beta (primaryTerms X (X.effective.energy beta - 4) beta 0
          (pointLabels (reconstructionLabels X) (X.effective.energy beta - 4)))) := by
  have h := primary_point_eq A I F N H hsource hboundary Omega P T U S Hdiv hpair
    (X.effective.energy beta - 4) houtput beta
    (pointLabels (reconstructionLabels X) (X.effective.energy beta - 4))
    (by rw [primaryTerms_reconstruction_coefficient X beta henergy]; exact one_ne_zero) p hp
  simpa only [primaryTerms_reconstruction_coefficient X beta henergy, div_one] using h

end AxiomaticGW.WDVV

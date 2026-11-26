/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.GenusTwoHodgeNormalization
public import AxiomaticGW.Tautological.Fixtures.GenusOnePsiReplay

/-! # Genus-two localization vertices from geometric relations

The genus-two Picard row, the Hodge restrictions to its two normalizations, the rank-two
square, and the point-target DVV equations recover all eight admcycles Hodge entries.
The genus-one cotangent row supplies its one-point normalization from the three-point volume.
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoHodgeGeometricVertex
open GenusTwoLocalizationClass GenusTwoHodgePicardMoments GenusTwoHodgeNormalization
open PointTarget.DVVCalculation PsiBoundaryExpansion
open GenusTwoHodgeDVV (fourKeys)
open ExceptionalGenusTwoVertexValues (seed)

variable {C : StableCurveCohomology ℚ} {I : StableCurveIntegration C} {D : HodgeClasses C}

/-- Realization of the original genus-one cotangent row and the labeled nonseparating gluing. -/
structure EllipticPsi (P : PsiClasses C) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I)
    (A : ∀ g S, [Fintype S] → StrataRealization C g S) : Prop where
  psi : (A 1 (Fin 1)).LegPsiCompatible P GenusOnePsi.stableArity
  fund : (A 1 (Fin 1)).map (StrataModule.basis
    (TautologicalStratum.fundamental 1 (Fin 1) GenusOnePsi.stableArity)) = 1
  rows : ∀ i, (A 1 (Fin 1)).map (RelationCertificate.interpret
    GenusOnePsi.columns (GenusOnePsi.rows i)) = 0
  loop : GenusOnePsi.loopExpression.Compatible A F N

/-- The genus-one cotangent row fixes the elliptic normalization from the three-point volume. -/
theorem elliptic_integral (P : PsiClasses C) {F : SeparatingPushforward C I}
    {N : NonseparatingPushforward C I} {A : ∀ g S, [Fintype S] → StrataRealization C g S}
    (E : EllipticPsi P F N A) (vol : I.integrate 0 (Option Bool) tailStable 1 = 1) :
    I.integrate 1 (Fin 1) PointTarget.genusOne_one_stable
      (P.psi 1 _ PointTarget.genusOne_one_stable 0) = 1 / 24 := by
  have h := GenusOnePsi.realized_psi GenusOnePsiReplay.presentation GenusOnePsiReplay.accepted
    (A 1 (Fin 1)) P E.psi E.fund E.rows
  rw [GenusOnePsi.loopExpression.map_stratum_eq_classValue A F N E.loop] at h
  rw [h, map_smul]
  change (1 / 24 : ℚ) * I.integrate 1 _ _ (N.push 0 (Fin 1) GenusOnePsi.stableArity 1) = _
  rw [N.integrate_push]
  let e : Option (Option (Fin 1)) ≃ Option Bool := Fintype.equivOfCardEq (by decide)
  have hvol := I.integrate_rename 0 _ _ (StableArity.double_option_iff.mpr GenusOnePsi.stableArity)
    tailStable e 1
  rw [map_one, vol] at hvol
  rw [← hvol, mul_one]

/-- The four positive-Hodge-index seed numbers follow from the class-level geometry. -/
theorem positive_moments (H : D.Natural) (U : ForgetfulPushforward C I)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (P : PsiClasses C) (K : PsiForgetFormula P) (hK : TailCompatible K F N)
    (T : TailForgetCompatible C) (Q : ForgetfulSquareCompatibility U F)
    (G : GluingForgetfulCompatibility F N)
    {A : ∀ g S, [Fintype S] → StrataRealization C g S}
    (B : PicardRealization D F N A) (E : Normalization D N)
    (base : P.kappa U 2 (Fin 0) (stable 0) 0 = 2)
    (square : (D.first 1 : C.H 2 (Fin 1)) ^ 2 = 2 * (D.second 1 : C.H 2 (Fin 1)))
    (dvv : PointTarget.DVVRecursion P I) (zero : value P I 0 [0, 0, 0] = 1)
    (one : value P I 1 [1] = 1 / 24)
    (i j : Fin 3) (_hij : i ≤ j) (p : List ℕ) (hk : ((i : ℕ), (j : ℕ), p) ∈ fourKeys) :
    seed ⟨_, (Finset.mem_erase.mp (Finset.mem_filter.mp hk).1).2⟩ = moment D P I i j p := by
  have mixed := moment_dilaton H U F N P K hK T Q base 1 2 []
  rw [first_second_marked P F N E B dvv zero one] at mixed
  have bare : moment D P I 1 2 [] = 1 / 5760 := by
    change (1 / 2880 : ℚ) = 2 * _ at mixed
    linarith
  have casesFour : ∀ t : ↥fourKeys, t.val = (0,1,[3]) ∨ t.val = (0,1,[2,2]) ∨
      t.val = (0,2,[2]) ∨ t.val = (1,2,[]) := by decide +kernel
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  rcases casesFour ⟨_, hk⟩ with he | he | he | he
  all_goals change (i,j,p) = _ at he; cases he
  · exact (first_cube P F N B dvv zero one).symm
  · exact (first_two_squares H P F N G B dvv zero one).symm
  · exact (second_square P F N E B square dvv zero one).symm
  · exact bare.symm

/-- The integral at every valence equals the native vertex reduction under the geometric inputs.
A flag series in this expression is an inverse Euler class at nonzero flag character. -/
theorem integrated_vertex (H : D.Natural) (U : ForgetfulPushforward C I)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (P : PsiClasses C) (K : PsiForgetFormula P) (hK : TailCompatible K F N)
    (T : TailForgetCompatible C) (Q : ForgetfulSquareCompatibility U F)
    (G : GluingForgetfulCompatibility F N)
    {A : ∀ g S, [Fintype S] → StrataRealization C g S}
    (B : PicardRealization D F N A) (E : Normalization D N) (ell : EllipticPsi P F N A)
    (vol : I.integrate 0 (Option Bool) tailStable 1 = 1)
    (base : P.kappa U 2 (Fin 0) (stable 0) 0 = 2)
    (square : (D.first 1 : C.H 2 (Fin 1)) ^ 2 = 2 * (D.second 1 : C.H 2 (Fin 1)))
    (dvv : PointTarget.DVVRecursion P I)
    {L : Type*} [Field L] [CharZero L] {f : ℕ} (m : List ℕ) (u v : L) (flag : Fin f → L) :
    integrate I _ (integrand D P m u v flag) =
      GenusTwoLocalizationVertex.reduced seed m u v flag := by
  have zero := initial_zero P I (by decide : Fintype.card (Option Bool) = 3) tailStable vol
  have one := elliptic_integral P ell vol
  exact GenusTwoHodgeDVV.integrated_vertex H U F N P K hK T Q vol base square dvv one
    (positive_moments H U F N P K hK T Q G B E base square dvv zero (initial_one P I one))
    m u v flag

end AxiomaticGW.GKM.GenusTwoHodgeGeometricVertex

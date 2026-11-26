/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.GenusTwoHodgeProducts
public import AxiomaticGW.GKM.Fixtures.ExceptionalGenusTwoVertexValues
public import AxiomaticGW.GKM.Fixtures.AdmcyclesHodgeStrataCandidates

/-! # Geometric inputs for the genus-two vertex seed ledger

The one-marked rank-two square determines the λ₁² seed from the λ₂ seed.
The actual decoded square has a proof in HodgeFullSquare under its stated
realization and Gysin hypotheses. Identifying its two Hodge classes is geometric.
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoHodgeSeedGeometry
open GenusTwoLocalizationClass GenusTwoVertexHodgeReduction
open ExceptionalGenusTwoVertexValues (seed)
open AdmcyclesHodgeStrataCandidates PsiBoundaryExpansion

/-- The remaining seed signatures after eliminating the one-marked λ₁² integral. -/
def sevenKeys : Finset (ℕ × ℕ × List ℕ) := seeds.erase (1,1,[2])

/-- Seven directly matched source integrals suffice under the one-marked square comparison. -/
theorem card_sevenKeys : sevenKeys.card = 7 := by decide +kernel

variable {C : StableCurveCohomology ℚ} {D : HodgeClasses C}

/-- Transfer the full decoded square to the two actual Hodge classes. The packet equality
is the conclusion of HodgeFullSquare.map_raw_0_2_eq_half_square. -/
theorem square_from_packet (A : StrataRealization C 2 (Fin 1))
    (first : (D.first 1 : C.H 2 (Fin 1)) = A.map raw01Degree1)
    (second : (D.second 1 : C.H 2 (Fin 1)) = A.map raw02Degree2)
    (packet : A.map raw02Degree2 = (1 / 2 : ℚ) • (A.map raw01Degree1) ^ 2) :
    (D.first 1 : C.H 2 (Fin 1)) ^ 2 = 2 * (D.second 1 : C.H 2 (Fin 1)) := by
  rw [first, second, packet, two_mul, ← two_smul ℚ, smul_smul]
  norm_num

/-- All eight certified ledger values from the seven remaining signatures. -/
theorem all_seeds (H : D.Natural) {I : StableCurveIntegration C}
    (U : ForgetfulPushforward C I) (P : PsiClasses C)
    (base : P.kappa U 2 (Fin 0) (stable 0) 0 = 2)
    (square : (D.first 1 : C.H 2 (Fin 1)) ^ 2 = 2 * (D.second 1 : C.H 2 (Fin 1)))
    (seven : ∀ (i j : Fin 3), i ≤ j → ∀ p (hk : ((i : ℕ), (j : ℕ), p) ∈ sevenKeys),
      seed ⟨_, (Finset.mem_erase.mp hk).2⟩ = moment D P I i j p)
    (i j : Fin 3) (h : i ≤ j) (p : List ℕ) (hk : ((i : ℕ), (j : ℕ), p) ∈ seeds) :
    seed ⟨_, hk⟩ = moment D P I i j p := by
  by_cases he : ((i : ℕ), (j : ℕ), p) = (1,1,[2])
  · obtain ⟨hi, hj, rfl⟩ := Prod.mk.inj he |>.imp_right Prod.mk.inj
    have hi' : i = 1 := Fin.ext hi
    have hj' : j = 1 := Fin.ext hj
    subst i
    subst j
    have h02 := seven 0 2 (by decide) [2] (by decide +kernel)
    rw [square_moment H U P base square, ← h02]
    norm_num [seed]
  · exact seven i j h p (Finset.mem_erase.mpr ⟨he, hk⟩)

/-- Every stable genus-two surface vertex integrates to the native reduced source
under the universal-curve laws, two normalizations and the seven matched seed integrals. -/
theorem integrated_vertex (H : D.Natural) {I : StableCurveIntegration C}
    (U : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (hK : TailCompatible K F N) (T : TailForgetCompatible C) (Q : ForgetfulSquareCompatibility U F)
    (vol : I.integrate 0 (Option Bool) tailStable 1 = 1)
    (base : P.kappa U 2 (Fin 0) (stable 0) 0 = 2)
    (square : (D.first 1 : C.H 2 (Fin 1)) ^ 2 = 2 * (D.second 1 : C.H 2 (Fin 1)))
    (seven : ∀ (i j : Fin 3), i ≤ j → ∀ p (hk : ((i : ℕ), (j : ℕ), p) ∈ sevenKeys),
      seed ⟨_, (Finset.mem_erase.mp hk).2⟩ = moment D P I i j p)
    {L : Type*} [Field L] [CharZero L] {f : ℕ} (m : List ℕ) (u v : L) (flag : Fin f → L) :
    integrate I _ (integrand D P m u v flag) = GenusTwoLocalizationVertex.reduced seed m u v flag :=
  integral_from_geometry H U F N P K hK T Q vol base seed
    (all_seeds H U P base square seven) m u v flag

end AxiomaticGW.GKM.GenusTwoHodgeSeedGeometry

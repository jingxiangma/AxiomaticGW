/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.GenusTwoHodgeDVV
public import AxiomaticGW.GKM.Fixtures.HodgeGenusTwoPicard
public import AxiomaticGW.PointTarget.DVVGluing
import all Mathlib.Data.List.Sort

/-! # Integrating the genus-two Picard row

The raw loop carries coefficient one half and the separating component carries coefficient two
in the discriminant. Pairing this class with cotangent powers reduces the two positive
first-Chern-class seeds to genus-one point-target integrals.
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoHodgePicardMoments
open GenusTwoLocalizationClass
open HodgeDegreeOneRealization (loop separatingMarkedLeft)
open PointTarget.DVVCalculation

variable {C : StableCurveCohomology ℚ} {I : StableCurveIntegration C} {D : HodgeClasses C}

/-- The actual one-marked Hodge class is identified with the incoming degree-one class packet.
The vanishing of the named PPZ row and the two raw pushforward realizations are explicit. -/
structure PicardRealization (D : HodgeClasses C) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I)
    (A : ∀ g S, [Fintype S] → StrataRealization C g S) : Prop where
  first : (D.first 1 : C.H 2 (Fin 1)) =
    (A 2 (Fin 1)).map AdmcyclesHodgeStrataCandidates.raw01Degree1
  row : (A 2 (Fin 1)).map (RelationCertificate.interpret HodgeGenusTwoPicard.columns
    HodgeGenusTwoPicard.row) = 0
  loopMap : loop.Compatible A F N
  separatingMap : separatingMarkedLeft.Compatible A F N

/-- The discriminant's coefficients in the raw gluing convention, paired with any linear test. -/
theorem pairing {F : SeparatingPushforward C I} {N : NonseparatingPushforward C I}
    {A : ∀ g S, [Fintype S] → StrataRealization C g S} (B : PicardRealization D F N A)
    (L : C.H 2 (Fin 1) →ₗ[ℚ] ℚ) :
    L (D.first 1) = (1 / 10 : ℚ) * ((1 / 2 : ℚ) * L (loop.classValue F N) +
      2 * L (separatingMarkedLeft.classValue F N)) := by
  rw [B.first, HodgeGenusTwoPicard.map_degree_one _ B.row,
    HodgeGenusTwoPicard.map_boundary A F N B.loopMap B.separatingMap]
  simp only [map_smul, map_add, smul_eq_mul]

/-- The two boundary contributions before the discriminant weights are applied. -/
theorem one_marked_rows :
    RationalTerms.collect (graphExpansion 4 loop (fun _ ↦ 3)) =
      RationalTerms.term (1 / 24) 0 ∧
    RationalTerms.collect (graphExpansion 4 separatingMarkedLeft (fun _ ↦ 3)) = 0 := by
  decide +kernel

/-- With two cotangent squares, the loop contributes one sixth. Exactly one separating
placement contributes the product of two genus-one integrals. -/
theorem two_marked_rows :
    RationalTerms.collect ((loop.addMarking.map fun x ↦ graphExpansion 4 x (fun _ ↦ 2)).sum) =
      RationalTerms.term (1 / 6) 0 ∧
    RationalTerms.collect ((separatingMarkedLeft.addMarking.map fun x ↦
      graphExpansion 4 x (fun _ ↦ 2)).sum) = RationalTerms.term (1 / 576) 0 := by
  decide +kernel

/-- Integrating the one-marked Picard class times the cotangent cube. -/
theorem first_cube (P : PsiClasses C) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) {A : ∀ g S, [Fintype S] → StrataRealization C g S}
    (B : PicardRealization D F N A) (dvv : PointTarget.DVVRecursion P I)
    (zero : value P I 0 [0, 0, 0] = 1) (one : value P I 1 [1] = 1 / 24) :
    moment D P I 0 1 [3] = 1 / 480 := by
  let k : Fin 1 → ℕ := fun _ ↦ 3
  let L := (I.integrate 2 (Fin 1) (stable 1)).comp
    (LinearMap.mulLeft ℚ (P.monomial 2 (Fin 1) (stable 1) k))
  have contribution (x : GluingExpression 2 (Fin 1)) (v : ℚ)
      (hv : RationalTerms.collect (graphExpansion 4 x k) = RationalTerms.term v 0) :
      L (x.classValue F N) = v := by
    simpa only [L, LinearMap.comp_apply, LinearMap.mulLeft_apply, List.map_singleton,
      List.sum_singleton] using
      graphList_constant P F N dvv zero one 4 [x] (stable 1) k v (by
        simpa only [List.map_singleton, List.sum_singleton] using hv)
  have h := pairing B L
  rw [contribution _ _ one_marked_rows.1, contribution _ 0 one_marked_rows.2] at h
  have hk : ([3] : List ℕ).get = k := by funext i; fin_cases i; rfl
  change I.integrate 2 (Fin 1) (stable 1)
    ((1 * (D.first 1 : C.H 2 (Fin 1))) * P.monomial 2 (Fin 1) (stable 1) [3].get) = _
  rw [one_mul, hk, mul_comm]
  exact h.trans (by norm_num)

/-- Pull the one-marked Picard row to two markings before integrating both cotangent squares. -/
theorem first_two_squares (H : D.Natural) (P : PsiClasses C) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (G : GluingForgetfulCompatibility F N)
    {A : ∀ g S, [Fintype S] → StrataRealization C g S} (B : PicardRealization D F N A)
    (dvv : PointTarget.DVVRecursion P I)
    (zero : value P I 0 [0, 0, 0] = 1) (one : value P I 1 [1] = 1 / 24) :
    moment D P I 0 1 [2, 2] = 5 / 576 := by
  let k : Option (Fin 1) → ℕ := fun _ ↦ 2
  let L := ((I.integrate 2 (Option (Fin 1)) (stable 1).option).comp
    (LinearMap.mulLeft ℚ (P.monomial 2 _ (stable 1).option k))).comp
      (C.forget 2 (Fin 1) (stable 1)).toLinearMap
  have contribution (x : GluingExpression 2 (Fin 1)) (v : ℚ)
      (hv : RationalTerms.collect ((x.addMarking.map fun z ↦ graphExpansion 4 z k).sum) =
        RationalTerms.term v 0) : L (x.classValue F N) = v := by
    have h := graphList_constant P F N dvv zero one 4 x.addMarking (stable 1).option k v hv
    rw [x.sum_classValue_addMarking F N G] at h
    simpa only [L, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply] using h
  have h := pairing B L
  rw [contribution _ _ two_marked_rows.1, contribution _ _ two_marked_rows.2] at h
  rw [moment_cons H P I 0 1 2 [2]]
  have hk : (fun t : Option (Fin 1) ↦ t.elim 2 ([2] : List ℕ).get) = k := by
    funext t
    rcases t with _ | i
    · rfl
    · fin_cases i; rfl
  change I.integrate 2 (Option (Fin 1)) (stable 1).option
    (C.forget 2 (Fin 1) (stable 1) (1 * (D.first 1 : C.H 2 (Fin 1))) *
      P.monomial 2 _ (stable 1).option (fun t ↦ t.elim 2 ([2] : List ℕ).get)) = _
  rw [one_mul, hk, mul_comm]
  exact h.trans (by norm_num)

end AxiomaticGW.GKM.GenusTwoHodgePicardMoments

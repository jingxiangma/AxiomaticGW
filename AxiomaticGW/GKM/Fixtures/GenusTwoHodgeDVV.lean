/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.GenusTwoHodgeSeedGeometry
public import AxiomaticGW.PointTarget.DVVCalculation
-- Closed profiles reduce through mathlib's structurally recursive insertion sort.
import all Mathlib.Data.List.Sort

/-! # Point-target certificates for the three pure cotangent vertex seeds

The three finite DVV expansions have constant collected polynomials. Geometric interpretation
uses the point-target DVV relation, the three-point volume and the elliptic one-point integral.
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoHodgeDVV
open GenusTwoVertexHodgeReduction GenusTwoLocalizationClass GenusTwoHodgeSeedGeometry
open PointTarget.DVVCalculation PsiBoundaryExpansion
open ExceptionalGenusTwoVertexValues (seed)

variable {C : StableCurveCohomology ℚ} {D : HodgeClasses C}

/-- The four signatures with a positive Hodge index left after the square and pure ψ deductions. -/
def fourKeys : Finset (ℕ × ℕ × List ℕ) := sevenKeys.filter (fun t ↦ t.1 + t.2.1 > 0)

/-- Exactly four Hodge comparisons remain beyond the point-target relation and its initial data. -/
theorem card_fourKeys : fourKeys.card = 4 := by decide +kernel

/-- DVV depths three, four and five settle the three pure cotangent signatures, respectively. -/
def purePowers : Fin 3 → List ℕ := ![[4], [2, 3], [2, 2, 2]]

/-- Native seed values in the same order as the three fixed cotangent profiles. -/
def pureValue : Fin 3 → ℚ := ![1 / 1152, 29 / 5760, 7 / 240]

set_option maxRecDepth 65536 in
/-- The original point-target equations eliminate every unresolved variable for these requests. -/
theorem constant_rows : ∀ j : Fin 3,
    RationalTerms.collect (expand (j.val + 3) 2 (purePowers j)) =
      RationalTerms.term (pureValue j) 0 := by
  intro j
  fin_cases j <;> decide +kernel

/-- The three ledger values follow from the geometric point-target DVV relation and its seeds. -/
theorem pure_moments (P : PsiClasses C) (I : StableCurveIntegration C)
    (dvv : PointTarget.DVVRecursion P I) (zero : value P I 0 [0, 0, 0] = 1)
    (one : value P I 1 [1] = 1 / 24) (j : Fin 3) :
    moment D P I 0 0 (purePowers j) = pureValue j := by
  have h := expand_value P I dvv zero one (j.val + 3) 2 (purePowers j)
  rw [← RationalTerms.eval_collect, constant_rows j, RationalTerms.eval_term, Multiset.map_zero,
    Multiset.prod_zero, Algebra.algebraMap_self_apply, mul_one] at h
  simpa only [moment, monomial, HodgeClasses.coefficient, one_mul, value,
    PointTarget.intersectionNumber_of_stable P I _ _ (stable _)] using h.symm

/-- Pure ψ comparisons and the four remaining Hodge signatures recover the seven source seeds. -/
theorem seven_from_DVV (P : PsiClasses C) (I : StableCurveIntegration C)
    (dvv : PointTarget.DVVRecursion P I) (vol : I.integrate 0 (Option Bool) tailStable 1 = 1)
    (one : I.integrate 1 (Fin 1) PointTarget.genusOne_one_stable
      (P.psi 1 _ PointTarget.genusOne_one_stable 0) = (1 / 24 : ℚ))
    (four : ∀ (i j : Fin 3), i ≤ j → ∀ p (hk : ((i : ℕ), (j : ℕ), p) ∈ fourKeys),
      seed ⟨_, (Finset.mem_erase.mp (Finset.mem_filter.mp hk).1).2⟩ = moment D P I i j p)
    (i j : Fin 3) (hij : i ≤ j) (p : List ℕ) (hk : ((i : ℕ), (j : ℕ), p) ∈ sevenKeys) :
    seed ⟨_, (Finset.mem_erase.mp hk).2⟩ = moment D P I i j p := by
  by_cases hp : 0 < i.val + j.val
  · exact four i j hij p (Finset.mem_filter.mpr ⟨hk, hp⟩)
  have hi : i = 0 := Fin.ext (by omega)
  have hj : j = 0 := Fin.ext (by omega)
  subst i
  subst j
  have frame : ∀ t : ↥sevenKeys, t.val.1 = 0 → t.val.2.1 = 0 →
      ∃ a : Fin 3, t.val.2.2 = purePowers a ∧
        seed ⟨t.val, (Finset.mem_erase.mp t.property).2⟩ = pureValue a := by decide +kernel
  obtain ⟨a, ha, hv⟩ := frame ⟨_, hk⟩ rfl rfl
  change p = purePowers a at ha
  subst p
  have zero := initial_zero P I (by decide : Fintype.card (Option Bool) = 3) tailStable vol
  exact hv.trans (pure_moments P I dvv zero (initial_one P I one) a).symm

/-- Class-level genus-two localization at all valences from four geometric Hodge moments,
the original point-target DVV relation and its elliptic normalization. -/
theorem integrated_vertex (H : D.Natural) {I : StableCurveIntegration C}
    (U : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (hK : TailCompatible K F N) (T : TailForgetCompatible C) (Q : ForgetfulSquareCompatibility U F)
    (vol : I.integrate 0 (Option Bool) tailStable 1 = 1)
    (base : P.kappa U 2 (Fin 0) (stable 0) 0 = 2)
    (square : (D.first 1 : C.H 2 (Fin 1)) ^ 2 = 2 * (D.second 1 : C.H 2 (Fin 1)))
    (dvv : PointTarget.DVVRecursion P I)
    (one : I.integrate 1 (Fin 1) PointTarget.genusOne_one_stable
      (P.psi 1 _ PointTarget.genusOne_one_stable 0) = (1 / 24 : ℚ))
    (four : ∀ (i j : Fin 3), i ≤ j → ∀ p (hk : ((i : ℕ), (j : ℕ), p) ∈ fourKeys),
      seed ⟨_, (Finset.mem_erase.mp (Finset.mem_filter.mp hk).1).2⟩ = moment D P I i j p)
    {L : Type*} [Field L] [CharZero L] {f : ℕ} (m : List ℕ) (u v : L) (flag : Fin f → L) :
    integrate I _ (integrand D P m u v flag) = GenusTwoLocalizationVertex.reduced seed m u v flag :=
  GenusTwoHodgeSeedGeometry.integrated_vertex H U F N P K hK T Q vol base square
    (seven_from_DVV P I dvv vol one four) m u v flag

end AxiomaticGW.GKM.GenusTwoHodgeDVV

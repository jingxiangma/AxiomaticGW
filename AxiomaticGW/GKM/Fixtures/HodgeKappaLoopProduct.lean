/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.CohFT.ForgetfulNonseparatingKappa
public import AxiomaticGW.GKM.Fixtures.HodgeDegreeOneRealization

/-!
# The actual kappa-loop packet column as a class product

This binds rawGraph17 (original degree-two position 10)
to the gluing of a kappa-decorated genus-one corolla. Under the named proper-map
composition input and existing primitive laws, its realized class equals the
target kappa class times the realized actual rawGraph3 loop column.

This supplies no geometric Hodge identity and no product value as a hypothesis.
The new composition input itself remains a geometric obligation.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.GKM.HodgeKappaLoopProduct

open AdmcyclesHodgeStrataCandidates

/-- The component carrying the two ordered branches and the old marking. -/
theorem sourceStable : StableArity 1 (Option (Option (Fin 1))) := by
  unfold StableArity
  decide

/-- Bind the actual decoded kappa-loop graph to an existing graph operation. -/
theorem rawGraph17_eq_kappa_gluing :
    rawGraph17 = (TautologicalStratum.kappaGenerator 1
      (Option (Option (Fin 1))) sourceStable 1).nonseparating := by
  have hvector :
      DecoratedStableGraph.kappaVector 4 (![1, 0, 0, 0] : Fin 4 → ℕ) =
        (Finsupp.single 1 1 : ℕ+ →₀ ℕ) := by
    have hcoordinates :
        (fun i : Fin 4 ↦ (Finsupp.single 1 1 : ℕ+ →₀ ℕ)
          (DecoratedStableGraph.kappaIndex 4 i)) = ![1, 0, 0, 0] := by
      funext i
      fin_cases i
      · exact Finsupp.single_eq_same
      · exact Finsupp.single_eq_of_ne (by decide)
      · exact Finsupp.single_eq_of_ne (by decide)
      · exact Finsupp.single_eq_of_ne (by decide)
    rw [← hcoordinates]
    apply DecoratedStableGraph.kappaVector_truncate
    intro i hi
    apply Finsupp.single_eq_of_ne
    intro heq
    subst i
    norm_num at hi
  change rawGraph17 = (TautologicalStratum.oneVertex 1
    (Option (Option (Fin 1))) sourceStable (Finsupp.single 1 1) (fun _ ↦ 0)).nonseparating
  rw [← hvector]
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

attribute [local instance] strataRealizationModule

/-- The packet column receives an actual product interpretation from primitive
functoriality, rather than an assumed packet/product equality. -/
theorem map_rawGraph17_eq_kappa_mul_loop
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (Fforget : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (T : ForgetfulNonseparatingComposition Fforget N)
    (H : GluingForgetfulCompatibility F N)
    (hloop : HodgeDegreeOneRealization.loop.Compatible A F N)
    (hκ : (A 1 (Option (Option (Fin 1)))).KappaForgetfulCompatible
      (A 1 (Option (Option (Option (Fin 1))))) Fforget sourceStable 1)
    (hpsi : (A 1 (Option (Option (Option (Fin 1))))).LegPsiCompatible P
      sourceStable.option)
    (hfund : (A 1 (Option (Option (Option (Fin 1))))).map
      (StrataModule.basis (TautologicalStratum.fundamental 1
        (Option (Option (Option (Fin 1)))) sourceStable.option)) = 1) :
    (A 2 (Fin 1)).map (StrataModule.basis rawGraph17) =
      P.kappa Fforget 2 (Fin 1) HodgeDegreeOneRealization.stable 1 *
        (A 2 (Fin 1)).map (StrataModule.basis rawGraph3) := by
  rw [rawGraph17_eq_kappa_gluing, ← StrataModule.nonseparating_basis,
    (A 1 (Option (Option (Fin 1)))).map_nonseparating (A 2 (Fin 1)) N
      HodgeDegreeOneRealization.stable hloop.2,
    (A 1 (Option (Option (Fin 1)))).map_kappaGenerator
      (A 1 (Option (Option (Option (Fin 1))))) Fforget P sourceStable 1 hκ hpsi hfund,
    HodgeDegreeOneRealization.rawGraph3_eq_loop,
    HodgeDegreeOneRealization.loop.map_stratum_eq_classValue A F N hloop]
  change N.push 1 (Fin 1) HodgeDegreeOneRealization.stable
      (P.kappa Fforget 1 (Option (Option (Fin 1))) sourceStable 1) =
    P.kappa Fforget 2 (Fin 1) HodgeDegreeOneRealization.stable 1 *
      N.push 1 (Fin 1) HodgeDegreeOneRealization.stable 1
  rw [T.kappa_mul_push P F H, mul_one]

end AxiomaticGW.GKM.HodgeKappaLoopProduct

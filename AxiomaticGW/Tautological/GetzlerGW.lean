/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GetzlerGluing
public import AxiomaticGW.Tautological.GluingEvaluation
public import AxiomaticGW.Tautological.GetzlerRealization

/-!
# The marked Getzler certificate as an iterated GW equation

All 33 held graph columns have explicit gluing expressions. The general
evaluation theorem identifies their primary GW integrals with finite iterated
metric contractions of actual component invariants. The original geometric
Getzler class relation and normalized-cycle identification then give the
claim-bound equation, with exactly the previously checked rational weights.

No numerical recurrence is assumed. The geometric realization and Getzler
relation remain inputs. Additional markings, external ancestor powers, and
the stable-map descendant comparison are separate reconstruction obligations.
-/

@[expose] public section

namespace AxiomaticGW.GetzlerGraphs

universe u

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

attribute [local instance] strataRealizationModule

/-- Actual primary component integrals, joined by two node contractions and
the required full-curve-class sums, with the fixed marking transport. -/
noncomputable def gwChannel (Omega : GromovWittenTheory R V B D C)
    (I : StableCurveIntegration C) (beta : B) (a : Fin 4 → V) (i : Fin 33) : R :=
  (expression i).gwContraction Omega I beta a

variable (A : ∀ g S, [Fintype S] → StrataRealization C g S)
  (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
  (hcompat : ∀ i, (expression i).Compatible A F N)

include hcompat

/-- Evaluation of each held raw graph is its derived iterated contraction.
This identification does not use the Getzler relation. -/
theorem integrate_column_gw (Omega : GromovWittenTheory R V B D C)
    (beta : B) (a : Fin 4 → V) (i : Fin 33) :
    (A 1 (Fin 4)).integrateAgainst I stableArity
      (Omega.omega 1 (Fin 4) stableArity beta a)
      (StrataModule.basis (columns i)) = gwChannel Omega I beta a i := by
  rw [← expression_stratum i]
  exact congrArg (fun f ↦ f a)
    ((expression i).gwIntegral_eq_contraction A F N Omega (hcompat i) beta)

variable (G : GetzlerRelationGeometry C)
  (hcycle : ∀ x, (A 1 (Fin 4)).map (cycle x) = G.cycle x)

include G hcycle

/-- The independently held Getzler consequence is an equation between
actual iterated GW contractions, with all 33 marking and automorphism weights. -/
theorem certificate_gw_eq_zero (Omega : GromovWittenTheory R V B D C)
    (beta : B) (a : Fin 4 → V) (c : RelationCertificate.Certificate 1)
    (hcheck : RelationCertificate.check rows requested c = true) :
    (∑ i, algebraMap ℚ R (requested i) * gwChannel Omega I beta a i) = 0 := by
  have h := certificate_integral_sum_eq_zero (A 1 (Fin 4)) G hcycle I
    (Omega.omega 1 (Fin 4) stableArity beta a) c hcheck
  simpa only [integrate_column_gw A F N hcompat Omega beta a] using h

/-- Accepted incoming data proves exactly the requested equation in the
fixed graph frame, without trusting Sage's numerical output or zero flag. -/
theorem exchange_gw_eq_zero (Omega : GromovWittenTheory R V B D C)
    (beta : B) (a : Fin 4 → V)
    (p : RelationCertificate.Presentation 1 (Fin 4) 1 33) (hp : AcceptsExchange p) :
    (∑ i, algebraMap ℚ R (requested i) * gwChannel Omega I beta a i) = 0 :=
  certificate_gw_eq_zero A F N hcompat G hcycle Omega beta a p.certificate
    ((RelationCertificate.check_eq_true_iff _ _ _).mpr hp.2)

end AxiomaticGW.GetzlerGraphs

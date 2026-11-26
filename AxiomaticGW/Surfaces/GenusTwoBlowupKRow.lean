/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoCanonicalRelations
public import AxiomaticGW.Surfaces.GenusTwoBlowupKCoefficients

/-!
# A solved exceptional row with strictly earlier canonical dependencies

The complete normalized BP equation with three copies of `E_i` has K_i
coefficient minus eighteen at every positive-energy full effective class.
Collection removes cancelled dependencies before this column is isolated.
Every remaining nonconstant term is a canonical query strictly earlier in
the established plane-degree/family/energy order. Other exceptional labels
at the same full class are excluded by their actual zero coefficients.

Thus the original row determines K_i as its unchanged remainder divided by
eighteen, including at zero plane degree and negative signed multiplicity.
This is a scalar step with uniqueness relative to earlier values. It does
not supply the primary N row, geometric validity, or a full reconstruction.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupKRow
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
variable (X : SurfaceTarget)

/-- The original complete exceptional-triple BP equation at its canonical point count. -/
def row (i : Fin X.blowups) (beta : X.Curve) : RationalTerms (Variable X) :=
  BelorousskiPandharipande.normalizedGenusTwoTerms X (X.effective.energy beta - 1)
    beta 0 (SurfaceGenusZero.pointLabels
      (![.exceptional i, .exceptional i, .exceptional i] : Fin 3 → SurfaceBasisLabel X)
      (X.effective.energy beta - 1))

/-- Collect cancellations before removing only the requested exceptional column.
All constants and every other original coefficient are retained. -/
def remainder (i : Fin X.blowups) (beta : X.Curve) : RationalTerms (Variable X) :=
  (RationalTerms.collect (row X i beta)).filter
    (fun t ↦ t.2 ≠ {Sum.inr ((Family.exceptional i).query beta)})

/-- The scalar step determined by the actual constant nonzero exceptional pivot. -/
def step (i : Fin X.blowups) (values : Variable X → ℚ) (beta : X.Curve) : ℚ :=
  RationalTerms.eval values (remainder X i beta) / 18

/-- Every nonconstant collected remainder term is an actual canonical query
strictly earlier than the requested exceptional variable. -/
theorem remainder_support (i : Fin X.blowups) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta)
    {t : ℚ × Multiset (Variable X)} (ht : t ∈ remainder X i beta) :
    t.2 = 0 ∨ ∃ gamma : X.Curve, ∃ family : Family X,
      t.2 = {Sum.inr (family.query gamma)} ∧
        Earlier X (gamma, family) (beta, .exceptional i) := by
  obtain ⟨ht, hne⟩ := Multiset.mem_filter.mp ht
  rcases BelorousskiPandharipande.collected_normalized_primary_canonical_support
    (X.effective.energy beta - 1) beta _ ht with hz | ⟨gamma, c, hc, hm, _⟩
  · exact Or.inl hz
  · have ha := RationalTerms.mem_collect.mp ht
    have hcoef : RationalTerms.coefficient (row X i beta) {Sum.inr c} ≠ 0 := by
      rw [← hm, ← ha.2.1]
      exact ha.2.2
    obtain ⟨family, hf⟩ := family_of_mem_canonicalQueries hc
    rw [← hf] at hm hcoef
    have hs := SurfaceGenusTwoBlowupKCoefficients.canonical_coefficient_support
      i beta gamma family hbeta hcoef
    refine Or.inr ⟨gamma, family, hm, ?_⟩
    rcases hs with ⟨rfl, rfl⟩ | hs
    · exact (hne hm).elim
    · exact hs

/-- The complete row splits into its constant exceptional pivot and the
unchanged collected remainder, with the lower-genus constant retained. -/
theorem eval_row (i : Fin X.blowups) (values : Variable X → ℚ) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta) :
    RationalTerms.eval values (row X i beta) =
      -18 * values (Sum.inr ((Family.exceptional i).query beta)) +
        RationalTerms.eval values (remainder X i beta) := by
  rw [← RationalTerms.eval_collect values (row X i beta),
    RationalTerms.eval_isolate_singleton values _
      (Sum.inr ((Family.exceptional i).query beta)), RationalTerms.coefficient_collect]
  have hp := SurfaceGenusTwoBlowupKCoefficients.exceptional_coefficient_self i beta hbeta
  change RationalTerms.coefficient (row X i beta)
    {Sum.inr ((Family.exceptional i).query beta)} = _ at hp
  rw [hp, Algebra.algebraMap_self_apply]
  rfl

/-- Any valuation satisfying the original exceptional-triple equation has
the computed K_i value. Positive energy suffices even at zero plane degree. -/
theorem value_eq_step (i : Fin X.blowups) (values : Variable X → ℚ) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta)
    (he : RationalTerms.eval values (row X i beta) = 0) :
    values (Sum.inr ((Family.exceptional i).query beta)) = step X i values beta := by
  have heq := eval_row X i values beta hbeta
  rw [he] at heq
  apply (eq_div_iff (show (18 : ℚ) ≠ 0 by norm_num)).mpr
  change values (Sum.inr ((Family.exceptional i).query beta)) * 18 =
    RationalTerms.eval values (remainder X i beta)
  linarith

/-- Only strictly earlier canonical values can affect the computed K_i step. -/
theorem step_congr (i : Fin X.blowups) (values other : Variable X → ℚ) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta)
    (h : ∀ gamma : X.Curve, ∀ family : Family X,
      Earlier X (gamma, family) (beta, .exceptional i) →
        values (Sum.inr (family.query gamma)) = other (Sum.inr (family.query gamma))) :
    step X i values beta = step X i other beta := by
  apply congrArg (fun r : ℚ ↦ r / 18)
  apply RationalTerms.eval_congr
  intro t ht v hv
  rcases remainder_support X i beta hbeta ht with hz | ⟨gamma, family, hm, he⟩
  · exact (Multiset.notMem_zero v (hz ▸ hv)).elim
  · rw [hm, Multiset.mem_singleton] at hv
    subst v
    exact h gamma family he

/-- The original row uniquely determines K_i once earlier canonical values
are fixed, with no positivity restriction on its signed intersection. -/
theorem value_unique (i : Fin X.blowups) (values other : Variable X → ℚ) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta)
    (he : RationalTerms.eval values (row X i beta) = 0)
    (ho : RationalTerms.eval other (row X i beta) = 0)
    (h : ∀ gamma : X.Curve, ∀ family : Family X,
      Earlier X (gamma, family) (beta, .exceptional i) →
        values (Sum.inr (family.query gamma)) = other (Sum.inr (family.query gamma))) :
    values (Sum.inr ((Family.exceptional i).query beta)) =
      other (Sum.inr ((Family.exceptional i).query beta)) := by
  rw [value_eq_step X i values beta hbeta he, value_eq_step X i other beta hbeta ho]
  exact step_congr X i values other beta hbeta h

end AxiomaticGW.SurfaceGenusTwoBlowupKRow

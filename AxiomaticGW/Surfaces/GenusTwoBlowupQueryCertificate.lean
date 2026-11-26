/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupDescendants
public import AxiomaticGW.Surfaces.GenusTwoBlowupBoundedCertificate
public import AxiomaticGW.Surfaces.MixedAncestorBounds

/-!
# Bounded certificates for genus-two descendants on the blowups

Each ancestor term in the mixed cotangent expansion has energy at most the
input energy. Agreement on canonical states through this bound therefore
suffices for substitution in the complete descendant evaluator.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupDescendants
open SurfaceGenusTwoBlowupOrder
variable {X : SurfaceTarget}

/-- Evaluate the mixed expression using the supplied canonical values at ancestor terminals. -/
def descendantValueWith (values : State X → ℚ) (n : ℕ) (beta : X.Curve)
    (d : Fin n → ℕ) (a : Fin n → SurfaceBasisLabel X) : ℚ :=
  RationalTerms.eval (ancestorValueWith values)
    (SurfaceDescendant.mixedAncestorTerms 2 (Fin n)
      (by simp only [StableArity, Fintype.card_fin]; omega)
      (List.finRange n) beta d 0 a)

/-- Bounded canonical agreement suffices for all finite descendant powers and markings. -/
theorem descendantValueWith_eq_of_table (i : Fin X.blowups) (bound : ℕ)
    (values : State X → ℚ)
    (hvalues : ∀ s : State X, X.effective.energy s.1 ≤ bound →
      values s = SurfaceGenusTwoBlowupRecursion.values i s)
    (n : ℕ) (beta : X.Curve) (hb : X.effective.energy beta ≤ bound)
    (d : Fin n → ℕ) (a : Fin n → SurfaceBasisLabel X) :
    descendantValueWith values n beta d a = descendantValue i n beta d a := by
  refine SurfaceDescendant.eval_mixedAncestorTerms_congr_of_energy_le _ _ bound
    2 (Fin n) _ ?_ (List.finRange n) beta d 0 a hb
  intro b hbound e labels
  apply ancestorValueWith_eq_of_table i bound values hvalues _ rfl
  exact hbound

/-- Ordered query evaluation for genus two with an explicit canonical table. -/
def queryValueWith? (values : State X → ℚ) (q : SurfaceQuery X) : Option ℚ :=
  if q.genus = 2 then
    some (descendantValueWith values q.insertions.length q.beta
      (fun j ↦ (q.insertions.get j).psi) (fun j ↦ (q.insertions.get j).label))
  else none

/-- Substitution preserves the original result for every full query in the energy range. -/
theorem queryValueWith?_eq_of_table (i : Fin X.blowups) (bound : ℕ)
    (values : State X → ℚ)
    (hvalues : ∀ s : State X, X.effective.energy s.1 ≤ bound →
      values s = SurfaceGenusTwoBlowupRecursion.values i s)
    (q : SurfaceQuery X) (hb : X.effective.energy q.beta ≤ bound) :
    queryValueWith? values q = queryValue? i q := by
  rw [queryValueWith?, queryValue?]
  split_ifs
  · exact congrArg some (descendantValueWith_eq_of_table i bound values hvalues
      _ q.beta hb _ _)
  · rfl

/-- Checking the original bounded rows establishes the required canonical agreement. -/
theorem queryValueWith?_eq (i : Fin X.blowups) (bound : ℕ) (values : State X → ℚ)
    (hcheck : SurfaceGenusTwoBlowupBoundedCertificate.checkTable i bound values = true)
    (q : SurfaceQuery X) (hb : X.effective.energy q.beta ≤ bound) :
    queryValueWith? values q = queryValue? i q :=
  queryValueWith?_eq_of_table i bound values
    (SurfaceGenusTwoBlowupBoundedCertificate.checkTable_sound i bound values hcheck) q hb

/-- Check genus, full descendant request, canonical table and incoming rational value. -/
def checkDescendantClaim (i : Fin X.blowups) (bound : ℕ) (values : State X → ℚ)
    (q : SurfaceQuery X) (claimed : ℚ) : Bool :=
  decide (q.genus = 2 ∧ X.effective.energy q.beta ≤ bound) &&
    SurfaceGenusTwoBlowupBoundedCertificate.checkTable i bound values &&
    decide (queryValueWith? values q = some claimed)

/-- A successful certificate binds the supplied value to the original genus-two evaluator. -/
theorem checkDescendantClaim_sound (i : Fin X.blowups) (bound : ℕ)
    (values : State X → ℚ) (q : SurfaceQuery X) (claimed : ℚ)
    (h : checkDescendantClaim i bound values q claimed = true) :
    q.genus = 2 ∧ X.effective.energy q.beta ≤ bound ∧
      queryValue? i q = some claimed := by
  simp only [checkDescendantClaim, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1.1, h.1.1.2, ?_⟩
  rw [← queryValueWith?_eq i bound values h.1.2 q h.1.1.2]
  exact h.2

end AxiomaticGW.SurfaceGenusTwoBlowupDescendants

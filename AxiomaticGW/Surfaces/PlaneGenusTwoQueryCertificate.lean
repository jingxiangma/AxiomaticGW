/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneGenusTwoDescendants
public import AxiomaticGW.Surfaces.MixedAncestorBounds

/-!
# Bounded certificates for arbitrary plane genus-two descendant queries

The canonical table is checked against the original BP equations. Every
ancestor and calibration tail retains a class within the requested bound,
so that table can replace the terminal canonical recursion for the complete
descendant query. The claim checker binds genus, full class, ordered states
and powers to the claimed exact rational value. Geometric interpretation
uses `planeQueryValue?_eq_checkedEval` with its original hypotheses.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande

/-- Evaluate descendants using the supplied canonical table at ancestor terminals. -/
def planeDescendantValueWith (values : ℕ → Fin 3 → ℚ) (n : ℕ)
    (beta : SurfaceTarget.plane.Curve) (d : Fin n → ℕ)
    (a : Fin n → SurfaceBasisLabel .plane) : ℚ :=
  RationalTerms.eval (planeAncestorValueWith values)
    (SurfaceDescendant.mixedAncestorTerms 2 (Fin n)
      (by simp only [StableArity, Fintype.card_fin]; omega)
      (List.finRange n) beta d 0 a)

/-- A checked table suffices for all descendant powers within its degree range. -/
theorem planeDescendantValueWith_eq (bound : ℕ) (values : ℕ → Fin 3 → ℚ)
    (hcheck : planeCheckCanonicalTable bound values = true) (n : ℕ)
    (beta : SurfaceTarget.plane.Curve) (hb : beta 0 ≤ bound)
    (d : Fin n → ℕ) (a : Fin n → SurfaceBasisLabel .plane) :
    planeDescendantValueWith values n beta d a = planeDescendantValue n beta d a := by
  have he (b : SurfaceTarget.plane.Curve) :
      SurfaceTarget.plane.effective.energy b = 3 * b 0 := by
    change (∑ i : Fin 1, (![3] : Fin 1 → ℕ) i * b i) = _
    rw [Fin.sum_univ_one]
    rfl
  refine SurfaceDescendant.eval_mixedAncestorTerms_congr_of_energy_le _ _ (3 * bound)
    2 (Fin n) _ ?_ (List.finRange n) beta d 0 a ?_
  · intro b hbound e labels
    rw [he] at hbound
    apply planeAncestorValueWith_eq bound values hcheck _ rfl
    change b 0 ≤ bound
    omega
  · rw [he]
    omega

/-- Ordered query evaluation using an explicit canonical table. -/
def planeQueryValueWith? (values : ℕ → Fin 3 → ℚ) (q : SurfaceQuery .plane) : Option ℚ :=
  if q.genus = 2 then
    some (planeDescendantValueWith values q.insertions.length q.beta
      (fun i ↦ (q.insertions.get i).psi) (fun i ↦ (q.insertions.get i).label))
  else none

/-- Unsupported genera remain unsupported; valid genera preserve the entire query. -/
theorem planeQueryValueWith?_eq (bound : ℕ) (values : ℕ → Fin 3 → ℚ)
    (hcheck : planeCheckCanonicalTable bound values = true)
    (q : SurfaceQuery .plane) (hb : q.beta 0 ≤ bound) :
    planeQueryValueWith? values q = planeQueryValue? q := by
  rw [planeQueryValueWith?, planeQueryValue?]
  split_ifs
  · exact congrArg some (planeDescendantValueWith_eq bound values hcheck _ q.beta hb _ _)
  · rfl

/-- Check the complete requested descendant and the table that computes it. -/
def planeCheckDescendantClaim (bound : ℕ) (values : ℕ → Fin 3 → ℚ)
    (q : SurfaceQuery .plane) (claimed : ℚ) : Bool :=
  decide (q.genus = 2 ∧ q.beta 0 ≤ bound) && planeCheckCanonicalTable bound values &&
    decide (planeQueryValueWith? values q = some claimed)

/-- Acceptance certifies this exact query against the original terminating algorithm. -/
theorem planeCheckDescendantClaim_sound (bound : ℕ) (values : ℕ → Fin 3 → ℚ)
    (q : SurfaceQuery .plane) (claimed : ℚ)
    (h : planeCheckDescendantClaim bound values q claimed = true) :
    q.genus = 2 ∧ q.beta 0 ≤ bound ∧ planeQueryValue? q = some claimed := by
  simp only [planeCheckDescendantClaim, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1.1, h.1.1.2, ?_⟩
  rw [← planeQueryValueWith?_eq bound values h.1.2 q h.1.1.2]
  exact h.2

end AxiomaticGW.BelorousskiPandharipande

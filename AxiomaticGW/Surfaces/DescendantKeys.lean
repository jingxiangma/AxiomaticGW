/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.AncestorMarkings

/-!
# Stable-map evaluation of symmetric surface insertion keys

The existing occurrence and sorting API transports states and powers together.
Descendant evaluation is distinct from ancestor evaluation; any equality between
them still requires a geometric cotangent comparison. These genus-independent
declarations are shared by the genus-zero/one and genus-two consumers.
-/

@[expose] public section
namespace AxiomaticGW

namespace SurfaceAncestorKey
variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- Interpret the insertion data as stable-map descendants. This is a separate
interpretation of the key, not an identification of descendant and ancestor powers. -/
noncomputable def descendantEval (U : UnstableDescendantConventions M I)
    (q : SurfaceAncestorKey X) : ℚ :=
  U.invariant q.genus q.insertions q.beta
    (fun s ↦ (s : SurfaceInsertion X).psi)
    (fun s ↦ (s : SurfaceInsertion X).label.value)

/-- Collecting insertion occurrences preserves the actual descendant invariant. -/
theorem descendantEval_ofLabels (U : UnstableDescendantConventions M I)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    (ofLabels g S h beta k a).descendantEval U =
      U.invariant g S beta k (fun s ↦ (a s).value) := by
  let q := ofLabels g S h beta k a
  let e := occurrenceEquiv g S h beta k a
  have hk : (fun t : q.insertions ↦ k (e.symm t)) =
      (fun t : q.insertions ↦ (t : SurfaceInsertion X).psi) := by
    funext t
    have ht := congrArg SurfaceInsertion.psi (occurrenceEquiv_apply g S h beta k a (e.symm t))
    change ((e (e.symm t) : q.insertions) : SurfaceInsertion X).psi = k (e.symm t) at ht
    simpa only [Equiv.apply_symm_apply] using ht.symm
  have ha : (fun s ↦ ((e s : q.insertions) : SurfaceInsertion X).label.value) =
      (fun s ↦ (a s).value) := by
    funext s
    rw [occurrenceEquiv_apply]
  have hr := congrArg
    (fun f ↦ f (fun t : q.insertions ↦ (t : SurfaceInsertion X).label.value))
    (U.invariant_relabel g S q.insertions e beta k)
  rw [MultilinearMap.domDomCongr_apply, hk, ha] at hr
  rw [U.invariantMap_apply g S beta k,
    U.invariantMap_apply g q.insertions beta (fun t ↦ (t : SurfaceInsertion X).psi)] at hr
  exact hr.symm

/-- Sorting carries powers and states together, including repeated insertions. -/
theorem descendantEval_eq_ordered (U : UnstableDescendantConventions M I)
    (q : SurfaceAncestorKey X) :
    q.descendantEval U = U.invariant q.genus (Fin q.orderedInsertions.length) q.beta
      q.orderedPowers (fun s ↦ (q.orderedLabels s).value) := by
  have h := descendantEval_ofLabels U q.genus (Fin q.orderedInsertions.length)
    q.ordered_stable q.beta q.orderedPowers q.orderedLabels
  rw [q.of_ordered_eq] at h
  exact h

end SurfaceAncestorKey

end AxiomaticGW

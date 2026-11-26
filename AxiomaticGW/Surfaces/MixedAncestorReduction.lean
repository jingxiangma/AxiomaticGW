/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GW.Descendants.MixedComparison
public import AxiomaticGW.Surfaces.CalibrationRecursion
public import AxiomaticGW.Surfaces.AncestorPolynomial
public import AxiomaticGW.Coefficients.RationalTerms

/-!
# Executable descendant-to-ancestor reduction for the fixed surfaces

Each selected marking is eliminated by the proved mixed cotangent formula.
The shifted branch lowers its stable-map power; each rational-tail branch
uses the reconstructed calibration matrix and clears that power entirely.
The remaining markings are then processed in a finite list. This is nested
structural recursion, valid for every genus and every stable marking set.

Output uses the existing symmetric ancestor keys and exact rational terms.
It is a finite linear expression in actual ancestor invariants, not a claim
that the ancestor reconstruction problem has already been solved. Soundness
uses the original WDVV inputs, finite genus-zero seeds, and primitive virtual
cotangent geometry; no stable-descendant callback or solved recurrence is
assumed.
-/

@[expose] public section

namespace AxiomaticGW

namespace SurfaceBasisLabel

/-- Expansion of one arbitrary state in the existing surface basis. -/
theorem multilinear_update_eq_sum {X : SurfaceTarget} {S : Type}
    [DecidableEq S] (f : MultilinearMap ℚ (fun _ : S ↦ SurfaceCohomology X.blowups) ℚ)
    (a : S → SurfaceBasisLabel X) (s : S) (v : SurfaceCohomology X.blowups) :
    f (Function.update (fun t ↦ (a t).value) s v) =
      ∑ b : SurfaceBasisLabel X, b.coordinate v *
        f (fun t ↦ (Function.update a s b t).value) := by
  have hv := (labelBasis X).sum_repr v
  simp only [labelBasis_apply, labelBasis_repr] at hv
  conv_lhs => rw [← hv]
  rw [f.map_update_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [f.map_update_smul, smul_eq_mul]
  congr 2
  funext t
  by_cases ht : t = s
  · subst t
    simp only [Function.update_self]
  · simp only [Function.update_of_ne ht]

end SurfaceBasisLabel

namespace SurfaceDescendant

/-- Clear one stable-map power. The continuation describes the same markings
with that power already zero; every ancestor exponent remains on the main side. -/
def transferMark {X : SurfaceTarget} {S : Type} [DecidableEq S]
    (s : S) (next : X.Curve → (S → ℕ) → (S → SurfaceBasisLabel X) →
      RationalTerms (SurfaceAncestorKey X)) :
    ℕ → X.Curve → (S → ℕ) → (S → SurfaceBasisLabel X) →
      RationalTerms (SurfaceAncestorKey X)
  | 0, beta, e, a => next beta e a
  | m+1, beta, e, a =>
      transferMark s next m beta (Function.update e s (e s + 1)) a +
        ∑ split ∈ X.positiveTailSplittings beta, ∑ b : SurfaceBasisLabel X,
          RationalTerms.scale (reconstructedCalibrationMatrix X (m+1) split.2 b (a s))
            (next split.1 e (Function.update a s b))

/-- Process an explicit finite list of markings. Correctness requires every
unlisted marking to have zero remaining descendant power. Repeated markings
are harmless: their remaining power is zero after their first occurrence. -/
def mixedAncestorTerms {X : SurfaceTarget} (g : ℕ) (S : Type) [Fintype S]
    [DecidableEq S] (h : StableArity g S) :
    List S → X.Curve → (S → ℕ) → (S → ℕ) → (S → SurfaceBasisLabel X) →
      RationalTerms (SurfaceAncestorKey X)
  | [], beta, _, e, a => RationalTerms.term 1 {SurfaceAncestorKey.ofLabels g S h beta e a}
  | s :: marks, beta, d, e, a => transferMark s
      (fun b e' a' ↦ mixedAncestorTerms g S h marks b (Function.update d s 0) e' a')
        (d s) beta e a

/-- Interpretation of a one-mark reduction depends only on its continuation. -/
theorem eval_transferMark_congr {X : SurfaceTarget} {S : Type} [DecidableEq S]
    (v w : SurfaceAncestorKey X → ℚ) (s : S)
    (next : X.Curve → (S → ℕ) → (S → SurfaceBasisLabel X) →
      RationalTerms (SurfaceAncestorKey X))
    (hn : ∀ beta e a, RationalTerms.eval v (next beta e a) =
      RationalTerms.eval w (next beta e a))
    (m : ℕ) (beta : X.Curve) (e : S → ℕ) (a : S → SurfaceBasisLabel X) :
    RationalTerms.eval v (transferMark s next m beta e a) =
      RationalTerms.eval w (transferMark s next m beta e a) := by
  induction m generalizing e with
  | zero => exact hn beta e a
  | succ m ih =>
    simp only [transferMark, RationalTerms.eval_add, RationalTerms.eval_sum,
      RationalTerms.eval_scale, hn, ih]

/-- Only ancestor values with the original genus and marking count are used.
The curve class, powers and labels may change, and remain explicit in each key. -/
theorem eval_mixedAncestorTerms_congr {X : SurfaceTarget}
    (v w : SurfaceAncestorKey X → ℚ) (g : ℕ) (S : Type) [Fintype S]
    [DecidableEq S] (h : StableArity g S)
    (hv : ∀ beta e a, v (SurfaceAncestorKey.ofLabels g S h beta e a) =
      w (SurfaceAncestorKey.ofLabels g S h beta e a))
    (marks : List S) (beta : X.Curve) (d e : S → ℕ) (a : S → SurfaceBasisLabel X) :
    RationalTerms.eval v (mixedAncestorTerms g S h marks beta d e a) =
      RationalTerms.eval w (mixedAncestorTerms g S h marks beta d e a) := by
  induction marks generalizing beta d e a with
  | nil =>
    simp only [mixedAncestorTerms, RationalTerms.eval_term, Multiset.map_singleton,
      Multiset.prod_singleton, hv]
  | cons s marks ih =>
    rw [mixedAncestorTerms]
    exact eval_transferMark_congr v w s _ (fun b e' a' ↦ ih b _ e' a') (d s) beta e a

section Soundness
variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  {U : UnstableDescendantConventions M I} {G : StableMapIntersection U}
  {St : StableMapStabilization G} {P : PsiClasses C}
  (K : RationalTailIntersection G St P)
  (hcal : ∀ power beta row col, reconstructedCalibrationMatrix X power beta row col =
    row.coordinate (U.calibrationCoefficient power beta col.value))

include K hcal

/-- Coordinate expansion of the derived geometric comparison. No cotangent
power at another marking, curve coordinate, or exceptional sign is discarded. -/
theorem mixed_step_labels (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (h : StableArity g S) (s : S) (beta : X.Curve) (m : ℕ)
    (d e : S → ℕ) (a : S → SurfaceBasisLabel X) :
    M.mixedInvariant P I g S h beta (Function.update d s (m+1)) e
        (fun t ↦ (a t).value) =
      M.mixedInvariant P I g S h beta (Function.update d s m)
          (Function.update e s (e s + 1)) (fun t ↦ (a t).value) +
        ∑ split ∈ X.positiveTailSplittings beta, ∑ b : SurfaceBasisLabel X,
          reconstructedCalibrationMatrix X (m+1) split.2 b (a s) *
            M.mixedInvariant P I g S h split.1 (Function.update d s 0) e
              (fun t ↦ (Function.update a s b t).value) := by
  rw [K.mixed_step_at]
  congr 1
  conv_rhs => rw [X.positiveTailSplittings_eq, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro split _
  rw [SurfaceBasisLabel.multilinear_update_eq_sum]
  simp only [hcal]

/-- Clearing one power terminates by structural recursion and preserves the
actual mixed invariant when its continuation has the stated interpretation. -/
theorem eval_transferMark (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (h : StableArity g S) (s : S) (d : S → ℕ)
    (next : X.Curve → (S → ℕ) → (S → SurfaceBasisLabel X) →
      RationalTerms (SurfaceAncestorKey X))
    (hnext : ∀ beta e a, RationalTerms.eval (SurfaceAncestorKey.eval Omega P I)
      (next beta e a) = M.mixedInvariant P I g S h beta (Function.update d s 0) e
        (fun t ↦ (a t).value))
    (m : ℕ) (beta : X.Curve) (e : S → ℕ) (a : S → SurfaceBasisLabel X) :
    RationalTerms.eval (SurfaceAncestorKey.eval Omega P I) (transferMark s next m beta e a) =
      M.mixedInvariant P I g S h beta (Function.update d s m) e
        (fun t ↦ (a t).value) := by
  induction m generalizing e with
  | zero => exact hnext beta e a
  | succ m ih =>
    simp only [transferMark, RationalTerms.eval_add, RationalTerms.eval_sum,
      RationalTerms.eval_scale, hnext, ih]
    exact (mixed_step_labels K hcal g S h s beta m d e a).symm

/-- The finite expression evaluates to the original mixed invariant once all
nonzero descendant powers have been included in the processing list. -/
theorem eval_mixedAncestorTerms (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (h : StableArity g S) (marks : List S) (beta : X.Curve) (d e : S → ℕ)
    (a : S → SurfaceBasisLabel X) (hz : ∀ s, s ∉ marks → d s = 0) :
    RationalTerms.eval (SurfaceAncestorKey.eval Omega P I)
        (mixedAncestorTerms g S h marks beta d e a) =
      M.mixedInvariant P I g S h beta d e (fun t ↦ (a t).value) := by
  induction marks generalizing beta d e a with
  | nil =>
    have hd : d = 0 := funext fun s ↦ hz s List.not_mem_nil
    simp only [mixedAncestorTerms, RationalTerms.eval_term, map_one,
      Multiset.map_singleton, Multiset.prod_singleton, one_mul,
      SurfaceAncestorKey.eval_ofLabels, hd, M.mixedInvariant_zero_descendant]
    rfl
  | cons s marks ih =>
    rw [mixedAncestorTerms]
    have he := eval_transferMark K hcal g S h s d
      (fun b e' a' ↦ mixedAncestorTerms g S h marks b (Function.update d s 0) e' a')
      (by
        intro b e' a'
        apply ih
        intro t ht
        by_cases hts : t = s
        · subst t
          exact Function.update_self s 0 d
        · rw [Function.update_of_ne hts]
          exact hz t (by simpa only [List.mem_cons, not_or] using And.intro hts ht))
      (d s) beta e a
    simpa only [Function.update_eq_self] using he

end Soundness
end SurfaceDescendant

namespace SurfaceQuery

/-- A total finite ancestor expression for any curve-stable descendant query,
including degree zero and genus two. Its output is independent of geometric inputs. -/
def ancestorTerms {X : SurfaceTarget} (q : SurfaceQuery X)
    (h : StableArity q.genus (Fin q.insertions.length)) : RationalTerms (SurfaceAncestorKey X) :=
  SurfaceDescendant.mixedAncestorTerms q.genus (Fin q.insertions.length) h
    (List.finRange q.insertions.length) q.beta (fun i ↦ (q.insertions.get i).psi) 0
    (fun i ↦ (q.insertions.get i).label)

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  (U : UnstableDescendantConventions M I)

/-- Intermediate soundness, exposing the calibration identification separately
so it can be discharged once for a family of queries. -/
theorem eval_ancestorTerms_of_calibration {G : StableMapIntersection U}
    {St : StableMapStabilization G} {P : PsiClasses C}
    (K : RationalTailIntersection G St P)
    (hcal : ∀ power beta row col, SurfaceDescendant.reconstructedCalibrationMatrix
      X power beta row col = row.coordinate (U.calibrationCoefficient power beta col.value))
    (q : SurfaceQuery X) (h : StableArity q.genus (Fin q.insertions.length)) :
    RationalTerms.eval (SurfaceAncestorKey.eval Omega P I) (q.ancestorTerms h) = q.eval U := by
  rw [ancestorTerms, SurfaceDescendant.eval_mixedAncestorTerms K hcal,
    M.mixedInvariant_zero_ancestor, eval, U.invariant_of_stable _ _ h]
  intro s hs
  exact False.elim (hs (List.mem_finRange s))

/-- Descendants reduce to a finite ancestor expression using only the original
geometric input and audited genus-zero seeds. The required higher calibration
coefficients are reconstructed, rather than supplied as further inputs. -/
theorem eval_ancestorTerms
    (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A)
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (Fsep : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (J : GluingForgetfulCompatibility Fsep N)
    (hsource : ∀ i, (WDVV.expression i).Compatible Z Fsep N)
    (hboundary : WDVV.BoundaryClassesEqual Fsep)
    (p : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hp : WDVV.AcceptsExchange p)
    (P : PsiClasses C)
    (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
    (hE : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
    (houtput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible Z Fsep N)
    {G : StableMapIntersection U} {St : StableMapStabilization G}
    (K : RationalTailIntersection G St P)
    (q : SurfaceQuery X) (h : StableArity q.genus (Fin q.insertions.length)) :
    RationalTerms.eval (SurfaceAncestorKey.eval Omega P I) (q.ancestorTerms h) = q.eval U :=
  eval_ancestorTerms_of_calibration U K
    (SurfaceDescendant.reconstructedCalibrationMatrix_eq U T laws H hpair Z Fsep N J
      hsource hboundary p hp P hline hE houtput K) q h

end SurfaceQuery
end AxiomaticGW

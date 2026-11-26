/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroAncestors
public import AxiomaticGW.Surfaces.MixedAncestorReduction

/-!
# Stable genus-zero descendants at arbitrary marking count

The finite mixed reduction is evaluated by the total ancestor reconstruction.
Both components are executable and have geometric interpretation theorems
from the existing finite seeds and primitive class-level laws. No stable
descendant or ancestor values are additional inputs to the final algorithm.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusZero

/-- Exact genus-zero descendant evaluation for any numbered stable marking set. -/
def stableValue (X : SurfaceTarget) (n : ℕ) (hn : 3 ≤ n) (beta : X.Curve)
    (d : Fin n → ℕ) (a : Fin n → SurfaceBasisLabel X) : ℚ :=
  RationalTerms.eval (ancestorValue X)
    (SurfaceDescendant.mixedAncestorTerms 0 (Fin n)
      (by simpa only [StableArity, Fintype.card_fin, Nat.mul_zero, Nat.zero_add] using hn)
      (List.finRange n) beta d 0 a)

/-- Use the existing query type without changing its ordered insertion data. -/
def stableQueryValue {X : SurfaceTarget} (q : SurfaceQuery X) (hg : q.genus = 0)
    (h : StableArity q.genus (Fin q.insertions.length)) : ℚ :=
  stableValue X q.insertions.length
    (by simpa only [StableArity, hg, Fintype.card_fin, Nat.mul_zero, Nat.zero_add] using h)
    q.beta (fun i ↦ (q.insertions.get i).psi) (fun i ↦ (q.insertions.get i).label)

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  (U : UnstableDescendantConventions M I) (P : PsiClasses C)

/-- Modular composition; the final theorem discharges both family identifications
with the original finite-seed reconstruction results. -/
theorem stableValue_eq_of_identifications
    {G : StableMapIntersection U} {St : StableMapStabilization G}
    (Tail : RationalTailIntersection G St P)
    (hcal : ∀ power beta row col,
      SurfaceDescendant.reconstructedCalibrationMatrix X power beta row col =
        row.coordinate (U.calibrationCoefficient power beta col.value))
    (hancestor : ∀ q : SurfaceAncestorKey X, q.genus = 0 →
      ancestorValue X q = q.eval Omega P I)
    (n : ℕ) (hn : 3 ≤ n) (beta : X.Curve)
    (d : Fin n → ℕ) (a : Fin n → SurfaceBasisLabel X) :
    stableValue X n hn beta d a = U.invariant 0 (Fin n) beta d (fun s ↦ (a s).value) := by
  have h : StableArity 0 (Fin n) := by
    simpa only [StableArity, Fintype.card_fin, Nat.mul_zero, Nat.zero_add] using hn
  rw [stableValue, SurfaceDescendant.eval_mixedAncestorTerms_congr (ancestorValue X)
    (SurfaceAncestorKey.eval Omega P I) 0 (Fin n) h (fun beta e a ↦ hancestor _ rfl)]
  rw [SurfaceDescendant.eval_mixedAncestorTerms Tail hcal,
    M.mixedInvariant_zero_ancestor, U.invariant_of_stable 0 (Fin n) h]
  intro s hs
  exact False.elim (hs (List.mem_finRange s))

variable (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
  {Fdiv : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega Fdiv}
  {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
  (hpair : T.DivisorPairingCompatible A)
  (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
  (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
  (J : GluingForgetfulCompatibility F N)
  (hsource : ∀ i, (WDVV.expression i).Compatible Z F N)
  (hboundary : WDVV.BoundaryClassesEqual F)
  (p : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hp : WDVV.AcceptsExchange p)
  (K : PsiForgetFormula P) (hK : PsiBoundaryExpansion.TailCompatible K F N)
  (hterms : ∀ n t, t ∈ PsiBoundaryExpansion.genusZeroTerms 0 n → t.2.Compatible Z F N)
  (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
  (hE : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
  (houtput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible Z F N)
  {G : StableMapIntersection U} {St : StableMapStabilization G}
  (Tail : RationalTailIntersection G St P)

include T laws H hpair Z F N J hsource hboundary p hp K hK hterms hline hE houtput Tail

/-- Every stable genus-zero descendant is reconstructed from the original
finite line/exceptional seeds and explicit cotangent/virtual intersection geometry. -/
theorem stableValue_eq (n : ℕ) (hn : 3 ≤ n) (beta : X.Curve)
    (d : Fin n → ℕ) (a : Fin n → SurfaceBasisLabel X) :
    stableValue X n hn beta d a = U.invariant 0 (Fin n) beta d (fun s ↦ (a s).value) :=
  stableValue_eq_of_identifications U P Tail
    (SurfaceDescendant.reconstructedCalibrationMatrix_eq U T laws H hpair Z F N J
      hsource hboundary p hp P hline hE houtput Tail)
    (ancestorValue_eq_eval U T laws H hpair Z F N J hsource hboundary p hp P K hK hterms
      hline hE houtput) n hn beta d a

/-- The same reconstruction is available at the existing public query boundary. -/
theorem stableQueryValue_eq (q : SurfaceQuery X) (hg : q.genus = 0)
    (h : StableArity q.genus (Fin q.insertions.length)) :
    stableQueryValue q hg h = q.eval U := by
  rw [stableQueryValue, SurfaceQuery.eval, hg]
  exact stableValue_eq U P T laws H hpair Z F N J hsource hboundary p hp K hK hterms
    hline hE houtput Tail _ _ _ _ _

end AxiomaticGW.SurfaceGenusZero

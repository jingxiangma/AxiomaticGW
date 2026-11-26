/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Tautological.PsiBoundaryExpansion
import AxiomaticGW.Tautological.Fixtures.GenusOnePsiReplay

set_option linter.privateModule false

namespace AxiomaticGWTest.Tautological.PsiBoundaryExpansion
open AxiomaticGW PsiBoundaryExpansion RelationCertificate

/-- Consume the actual incoming Sage certificate, including its graph proofs. -/
example : GenusOnePsi.AcceptsExchange GenusOnePsiReplay.presentation :=
  GenusOnePsiReplay.accepted

/-- Normalized-boundary coefficient 1/12 is invalid for the raw loop frame. -/
example : check GenusOnePsi.rows (![0,1,-(1/12)] : Coordinates 3)
    GenusOnePsi.certificate = false := by decide +kernel

/-- The full frame rejects a jointly changed zero request and zero relation system. -/
example : ¬GenusOnePsi.AcceptsExchange
    { GenusOnePsiReplay.presentation with
      rows := 0
      claimedRequest := 0
      certificate := ⟨0⟩ } := by
  intro h
  have hi := congrArg (fun f ↦ f 0 0) h.1.2.2.1
  norm_num [GenusOnePsi.rows] at hi

/-- The raw loop retains both node-branch automorphisms. -/
example : GenusOnePsi.loopExpression.graph.automorphismCount = 2 := by decide +kernel

/-- Original labels retain their order in the existing numbered-label adapter. -/
example : ∀ s : Fin 3, ExtraMarkings.finEquiv 4 3 (ExtraMarkings.oldLabel 4 s) =
    (⟨s.val, by omega⟩ : Fin 7) := by decide +kernel

/-- Primitive tail labels preserve the old mark and the newly forgotten mark. -/
example : tailLabels (0 : Fin 3) (.inr false) = some 0 ∧
    tailLabels (0 : Fin 3) (.inr true) = none ∧
    tailLabels (0 : Fin 3) (.inl ⟨1, by decide +kernel⟩) = some 1 := by decide +kernel

/-- Exactly one node joins two rational components in the first genus-zero tail. -/
example : let x := tailExpression 0 (Fin 3) StableArity.zero_fin_three 0
    x.graph.graph.vertexCount = 2 ∧ x.graph.graph.edgeCount = 1 ∧
    x.graph.graph.genus = 0 ∧
    x.graph.graph.legVertex none = x.graph.graph.legVertex (some 0) ∧
    x.graph.graph.legVertex none ≠ x.graph.graph.legVertex (some 1) := by decide +kernel

/-- The zero base relation produces no graph before adding a marking. -/
example : (genusZeroTerms 0 0).length = 0 ∧ (genusZeroTerms 0 1).length = 1 ∧
    (genusZeroTerms 0 2).length = 3 ∧ (genusZeroTerms 0 3).length = 7 := by decide +kernel

/-- Genus one keeps its loop along with every rational-tail placement. -/
example : (genusOneTerms 0).length = 1 ∧ (genusOneTerms 1).length = 2 ∧
    (genusOneTerms 2).length = 4 ∧ (genusOneTerms 3).length = 8 := by decide +kernel

/-- The loop coefficient occurs once; the seven rational tails keep coefficient one. -/
example : ((genusOneTerms 3).map Prod.fst) = [(1/24 : ℚ),1,1,1,1,1,1,1] := by decide +kernel

/-- Pullback placements preserve one-edge codimension in a larger finite case. -/
example : ∀ t ∈ genusOneTerms 4, t.2.graph.graph.edgeCount = 1 := by decide +kernel

/-- The original psi marking can be chosen independently of the other two base labels. -/
example : ∀ t ∈ genusZeroTerms 2 3, t.1 = 1 ∧ t.2.graph.graph.edgeCount = 1 := by
  decide +kernel

section GeometricConsumers
variable {R V B : Type} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
  (A : ∀ g S, [Fintype S] → StrataRealization C g S)
  (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
  (H : GluingForgetfulCompatibility F N)
  (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C) (K : PsiForgetFormula P)
  (hK : TailCompatible K F N)

attribute [local instance] strataRealizationModule

/-- The four-point ancestor equation is an actual contraction, with the full class retained. -/
example (hl : ∀ t ∈ genusZeroTerms 0 1, t.2.Compatible A F N)
    (beta : B) (k : Option (Fin 3) → ℕ) (a : Option (Fin 3) → V) :
    Omega.ancestorInvariant P I 0 (Option (Fin 3)) StableArity.zero_fin_three.option beta
        (k + Pi.single (some 0) 1) a =
      ((genusZeroTerms 0 1).map fun t ↦ (algebraMap ℚ R t.1) *
        t.2.gwAncestorContraction Omega P I beta k a).sum :=
  genusZero_ancestor_eq_contractions A F N H Omega P K hK 0 1 hl beta k a

/-- Dimension proves the genus-zero base without a supplied psi intersection table. -/
example (s : Fin 3) : P.psi 0 (Fin 3) StableArity.zero_fin_three s = 0 :=
  psi_zero_three P _ s

/-- The actual accepted incoming frame gives the genus-one recursion at arbitrary arity. -/
example
    (hpsi : (A 1 (Fin 1)).LegPsiCompatible P GenusOnePsi.stableArity)
    (hfund : (A 1 (Fin 1)).map (StrataModule.basis
      (TautologicalStratum.fundamental 1 (Fin 1) GenusOnePsi.stableArity)) = 1)
    (hrows : ∀ i, (A 1 (Fin 1)).map
      (interpret GenusOnePsi.columns (GenusOnePsi.rows i)) = 0)
    (hloop : GenusOnePsi.loopExpression.Compatible A F N) (n : ℕ)
    (hl : ∀ t ∈ genusOneTerms n, t.2.Compatible A F N)
    (beta : B) (k : ExtraMarkings n (Fin 1) → ℕ) (a : ExtraMarkings n (Fin 1) → V) :
    letI := ExtraMarkings.decidableEq (Fin 1) n
    Omega.ancestorInvariant P I 1 (ExtraMarkings n (Fin 1))
        (GenusOnePsi.stableArity.extraMarkings n) beta
        (k + Pi.single (ExtraMarkings.oldLabel n (0 : Fin 1)) 1) a =
      ((genusOneTerms n).map fun t ↦ (algebraMap ℚ R t.1) *
        t.2.gwAncestorContraction Omega P I beta k a).sum :=
  genusOne_ancestor_eq_contractions A F N H Omega P K hK
    GenusOnePsiReplay.presentation GenusOnePsiReplay.accepted hpsi hfund hrows hloop n hl beta k a

end GeometricConsumers
end AxiomaticGWTest.Tautological.PsiBoundaryExpansion

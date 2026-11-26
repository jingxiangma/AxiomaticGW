/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24InitialCoverage
public import AxiomaticGW.Tautological.Fixtures.L24InitialReplay

/-!
# The realized BP initial class and its checked coordinates

The comparison uses the actual signed BP pullback. Component dimension excesses
vanish by the proved geometric theorem, every retained graph has checked
coverage, and exact averaging cancels all auxiliary coefficients. This is an
equality of realized classes; it does not identify dimension-zero monomials
with zero in the free strata module.
-/

@[expose] public section

namespace AxiomaticGW.L24InitialClass
open RelationCertificate GluingExpression

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- Original pullback compatibility transports through the final marking bijection. -/
theorem pullback_compatible
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (hout : ∀ t ∈ L24Initial.bp, ∀ z ∈ t.2.addMarkings 1,
      z.2.expression.Compatible A F N ∧ z.2.expression.CotangentCompatible A P)
    (hl : (A 2 (ExtraMarkings 1 (Fin 3))).RelabelCompatible (A 2 (Fin 4))
      (BelorousskiPandharipande.stableArity.extraMarkings 1) L24Symmetry.stableArity
      L24Initial.labels) : ∀ t ∈ L24Initial.pullback,
      t.2.expression.Compatible A F N ∧ t.2.expression.CotangentCompatible A P := by
  unfold L24Initial.pullback CotangentCombination.relabel CotangentCombination.pullback
  generalize L24Initial.bp = r at hout ⊢
  intro result hresult
  rcases Multiset.mem_map.mp hresult with ⟨s, hspullback, rfl⟩
  rcases Multiset.mem_bind.mp hspullback with ⟨source, hsource, hmapped⟩
  rcases Multiset.mem_map.mp hmapped with ⟨term, hterm, rfl⟩
  exact ⟨⟨(hout source hsource term hterm).1, hl⟩, (hout source hsource term hterm).2⟩

/-- The initial coordinate row is exactly the actual BP-derived realized class. -/
theorem expression_eq_initial
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (hc : ∀ t ∈ L24Initial.pullback, t.2.expression.Compatible A F N ∧
      t.2.expression.CotangentCompatible A P)
    (hp : (A 2 (Fin 4)).LegPsiCompatible P L24Symmetry.stableArity)
    (hs : ∀ p, (A 2 (Fin 4)).RelabelCompatible (A 2 (Fin 4))
      L24Symmetry.stableArity L24Symmetry.stableArity (L24Symmetry.labels p)) :
    (A 2 (Fin 4)).map L24Initial.expression =
      (A 2 (Fin 4)).map (interpret L24Graphs.columns L24CorrectionsReplay.initialClaim) := by
  have ht (k : Fin 4) : (A 2 (Fin 4)).map
      (StrataModule.mulLegPsi (Pi.single k 1) L24Initial.pullback.strata) =
      (A 2 (Fin 4)).map (interpret L24InitialGraphs.columns (L24InitialReplay.raw k)) := by
    rw [← L24InitialReplay.coordinates_checked k]
    exact CotangentCombination.map_mulLegPsi_eq_interpret_dimensionRecords A F N P
      L24InitialGraphs.graph L24InitialGraphs.graph_totalGenus L24InitialHints.columnIndex
      (Pi.single k 1) L24Initial.pullback hc (fun _ _ ↦ hp) (L24InitialCoverage.covered k)
  let x : StrataModule 2 (Fin 4) := (1 / 12 : ℚ) • ∑ k : Fin 4,
    L24Initial.psiWeights k • StrataModule.mulLegPsi (Pi.single k 1) L24Initial.pullback.strata
  let y := interpret L24InitialGraphs.columns L24InitialReplay.beforeAverageClaim
  have hxy : (A 2 (Fin 4)).map x = (A 2 (Fin 4)).map y := by
    simp only [x, y, ← L24InitialReplay.beforeAverage_checked, map_smul, map_sum, ht]
  have hzero : (A 2 (Fin 4)).map (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have havg := L24Symmetry.average_vanishes (A 2 (Fin 4)) hs (x - y) hzero
  have he : (A 2 (Fin 4)).map (L24Symmetry.average x) =
      (A 2 (Fin 4)).map (L24Symmetry.average y) := by
    exact sub_eq_zero.mp (by simpa only [map_sub] using havg)
  have hy : L24Symmetry.average y =
      interpret L24Graphs.columns L24CorrectionsReplay.initialClaim := by
    dsimp only [y]
    rw [L24InitialGraphs.average_interpret, L24InitialReplay.initial_checked,
      L24InitialGraphs.interpret_extend]
  rw [hy] at he
  exact he

/-- The checked initial row vanishes from the original BP equation and primitive geometry. -/
theorem initial_vanishes
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (K : PsiForgetFormula P) (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (H : PsiBoundaryExpansion.TailForgetCompatible C) (G : GluingForgetfulCompatibility F N)
    (hbp : (A 2 (Fin 3)).map BelorousskiPandharipande.paperRelation = 0)
    (hin : ∀ t ∈ L24Initial.bp, t.2.expression.Compatible A F N ∧
      t.2.expression.CotangentCompatible A P)
    (hout : ∀ t ∈ L24Initial.bp, ∀ z ∈ t.2.addMarkings 1,
      z.2.expression.Compatible A F N ∧ z.2.expression.CotangentCompatible A P)
    (hl : (A 2 (ExtraMarkings 1 (Fin 3))).RelabelCompatible (A 2 (Fin 4))
      (BelorousskiPandharipande.stableArity.extraMarkings 1) L24Symmetry.stableArity
      L24Initial.labels)
    (hp : (A 2 (Fin 4)).LegPsiCompatible P L24Symmetry.stableArity)
    (hs : ∀ p, (A 2 (Fin 4)).RelabelCompatible (A 2 (Fin 4))
      L24Symmetry.stableArity L24Symmetry.stableArity (L24Symmetry.labels p)) :
    (A 2 (Fin 4)).map (interpret L24Graphs.columns L24CorrectionsReplay.initialClaim) = 0 := by
  rw [← expression_eq_initial A F N P (pullback_compatible A F N P hout hl) hp hs]
  exact L24Initial.expression_vanishes A F N P K hK H G hbp hin hout hl hp hs

end AxiomaticGW.L24InitialClass

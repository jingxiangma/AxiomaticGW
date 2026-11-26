/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW
import AxiomaticGWTest.Tautological.WDVVReplay

set_option linter.privateModule false

/-!
# Marked boundary and label-transport regressions

External labels distinguish the three raw boundary divisors. The held frame
rejects another legitimate channel in the wrong slot, even though all channels
have the same genus, degree, and automorphism order. Label transport also
retains decorations and exact rational coefficients.
-/

namespace AxiomaticGWTest.Tautological.WDVV

open AxiomaticGW RelationCertificate

/-- All four incidences, rather than an unordered partition name, are fixed. -/
example : (fun s ↦ ((AxiomaticGW.WDVV.graph 0).graph.legVertex s).val) = ![0,0,1,1] ∧
    (fun s ↦ ((AxiomaticGW.WDVV.graph 1).graph.legVertex s).val) = ![0,1,0,1] ∧
    (fun s ↦ ((AxiomaticGW.WDVV.graph 2).graph.legVertex s).val) = ![0,1,1,0] := by decide

/-- The component state order follows the covariant channel labels. -/
example : (fun s ↦ AxiomaticGW.WDVV.labels 1 (.inl s)) = ![0,2] ∧
    (fun s ↦ AxiomaticGW.WDVV.labels 1 (.inr s)) = ![1,3] ∧
    (fun s ↦ AxiomaticGW.WDVV.labels 2 (.inl s)) = ![0,3] ∧
    (fun s ↦ AxiomaticGW.WDVV.labels 2 (.inr s)) = ![2,1] := by decide

/-- Distinct raw columns have equal degree and trivial automorphism groups. -/
example (i : Fin 3) : (AxiomaticGW.WDVV.graph i).codimension = 1 ∧
    (AxiomaticGW.WDVV.graph i).automorphismCount = 1 :=
  ⟨AxiomaticGW.WDVV.graph_codimension i, AxiomaticGW.WDVV.graph_automorphismCount i⟩

/-- Formal equality has not replaced the geometric relation hypothesis. -/
example : interpret AxiomaticGW.WDVV.columns AxiomaticGW.WDVV.requested ≠ 0 :=
  AxiomaticGW.WDVV.requested_ne_zero

private noncomputable def presentation : Presentation 0 (Fin 4) 2 3 where
  columns := AxiomaticGW.WDVV.columns
  columnFactors := 1
  rows := AxiomaticGW.WDVV.rows
  claimedRequest := AxiomaticGW.WDVV.requested
  certificate := AxiomaticGW.WDVV.certificate

/-- Both rows are needed by the accepted held consequence. -/
example : AxiomaticGW.WDVV.AcceptsExchange presentation :=
  ⟨⟨rfl, rfl, rfl, rfl⟩,
    (check_eq_true_iff _ _ _).mp AxiomaticGW.WDVV.check_requested⟩

/-- The Sage-generated marked data replay against the same held frame offline. -/
example : AxiomaticGW.WDVV.AcceptsExchange AxiomaticGW.WDVVReplay.presentation :=
  AxiomaticGW.WDVVReplay.accepted

/-- Another valid marked boundary cannot occupy the original slot. -/
example : ¬AxiomaticGW.WDVV.AcceptsExchange
    { presentation with columns :=
      (Function.update AxiomaticGW.WDVV.columns 0 (AxiomaticGW.WDVV.columns 1)) } := by
  intro h
  have hc := congrFun h.1.1 0
  simp only [Function.update_self] at hc
  exact (by decide : (1 : Fin 3) ≠ 0) (AxiomaticGW.WDVV.columns_injective hc)

/-- A spurious automorphism divisor fails the raw coefficient contract. -/
example : ¬AxiomaticGW.WDVV.AcceptsExchange
    { presentation with columnFactors := ![(1 / 2),1,1] } := by
  intro h
  have hc := congrFun h.1.2.1 0
  norm_num only [Matrix.cons_val_zero, Pi.one_apply] at hc

/-- The incoming witness cannot replace the separately held request. -/
example : ¬AxiomaticGW.WDVV.AcceptsExchange
    { presentation with claimedRequest := 0 } := by
  intro h
  have hc := congrFun h.1.2.2.2 0
  norm_num only [Pi.zero_apply, AxiomaticGW.WDVV.requested, Matrix.cons_val_zero] at hc

/-- Zero weights do not certify the fixed nonzero formal request. -/
example : ¬AxiomaticGW.WDVV.AcceptsExchange
    { presentation with certificate := ⟨0⟩ } := by
  intro h
  have hc := congrFun h.2 0
  norm_num only [combination, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    AxiomaticGW.WDVV.requested, Matrix.cons_val_zero] at hc

private noncomputable def decorated : DecoratedStableGraph (Fin 4) where
  graph := (AxiomaticGW.WDVV.graph 0).graph
  kappaPower := fun _ ↦ Finsupp.single ⟨1, by decide⟩ 2
  legPsiPower := ![1,2,3,4]
  halfEdgePsiPower := fun _ ↦ ![5,6]

/-- Incidence and psi powers move together; vertex and node data stay fixed. -/
example : ((decorated.relabel (Equiv.swap 1 2)).graph.legVertex 1).val = 1 ∧
    (decorated.relabel (Equiv.swap 1 2)).legPsiPower 1 = 3 ∧
    (decorated.relabel (Equiv.swap 1 2)).legPsiPower 2 = 2 ∧
    (decorated.relabel (Equiv.swap 1 2)).kappaPower = decorated.kappaPower ∧
    (decorated.relabel (Equiv.swap 1 2)).halfEdgePsiPower = decorated.halfEdgePsiPower := by
  exact ⟨by decide, by decide, by decide, rfl, rfl⟩

/-- Changing the label type and returning preserves every decoration. -/
example : (decorated.relabel (AxiomaticGW.WDVV.labels 0).symm).relabel
    (AxiomaticGW.WDVV.labels 0) = decorated := by
  rw [DecoratedStableGraph.relabel_trans, Equiv.symm_trans_self,
    DecoratedStableGraph.relabel_refl]

/-- Codimension is unchanged even with asymmetric external and node powers. -/
example : (decorated.relabel (Equiv.swap 1 2)).codimension = decorated.codimension :=
  decorated.relabel_codimension _

/-- Exact rational coefficients survive transport through a different label type. -/
example : StrataModule.relabel (AxiomaticGW.WDVV.labels 0).symm
      ((-7 / 3 : ℚ) • StrataModule.basis (AxiomaticGW.WDVV.columns 1)) =
    (-7 / 3 : ℚ) • StrataModule.basis
      ((AxiomaticGW.WDVV.columns 1).relabel (AxiomaticGW.WDVV.labels 0).symm) := by
  rw [map_smul, StrataModule.relabel_basis]

/-- Empty external labels retain the loop's full branch-sensitive automorphisms. -/
example : (DecoratedStableGraph.toDecoration AdmcyclesGenusTwo.graph5Candidate
      AdmcyclesGenusTwo.graph5Valid AdmcyclesGenusTwo.graph5Exponents).relabel
      (Equiv.refl (Fin 0)) =
    DecoratedStableGraph.toDecoration AdmcyclesGenusTwo.graph5Candidate
      AdmcyclesGenusTwo.graph5Valid AdmcyclesGenusTwo.graph5Exponents := rfl

/-- A label bijection preserves the nontrivial loop automorphism count. -/
example : ((DecoratedStableGraph.toDecoration AdmcyclesGenusTwo.graph4Candidate
      AdmcyclesGenusTwo.graph4Valid AdmcyclesGenusTwo.graph4Exponents).relabel
      (Equiv.refl (Fin 0))).automorphismCount = 2 := by
  rw [DecoratedStableGraph.relabel_automorphismCount]
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide

private def exceptionalSplits : Finset (SurfaceTarget.blowupTwo.Curve ×
    SurfaceTarget.blowupTwo.Curve) :=
  {(![0,0,0], ![1,1,0]), (![1,0,0], ![0,1,0]),
   (![0,1,0], ![1,0,0]), (![1,1,0], ![0,0,0])}

private theorem exceptionalSplits_eq :
    SurfaceTarget.blowupTwo.effective.splittings ![1,1,0] = exceptionalSplits := by
  rw [← SurfaceTarget.splittings_eq]
  decide

section Evaluation

variable {R V : Type} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  {C : StableCurveCohomology R} (I : StableCurveIntegration C) (P : PsiClasses C)
  (F : SeparatingPushforward C I)
  (A : StrataRealization C 0 (Option (Fin 2)))
  (U : StrataRealization C 0 (Fin 2 ⊕ Fin 2)) (W : StrataRealization C 0 (Fin 4))
  (hsep : A.SeparatingCompatible A U F
    StableArity.zero_option_fin_two StableArity.zero_option_fin_two)
  (hfund : A.map (StrataModule.basis (TautologicalStratum.fundamental
    0 (Option (Fin 2)) StableArity.zero_option_fin_two)) = 1)
  (hlabels : ∀ i, U.RelabelCompatible W
    (StableArity.separating StableArity.zero_option_fin_two
      StableArity.zero_option_fin_two) AxiomaticGW.WDVV.stableArity (AxiomaticGW.WDVV.labels i))
  (Omega : GromovWittenTheory R V SurfaceTarget.blowupTwo.Curve
    SurfaceTarget.blowupTwo.effective C) (a : Fin 4 → V)

include hsep hfund hlabels

/-- The actual graph evaluator keeps zero factors and both equal-energy
exceptional classes, with states in the `02|13` channel order. -/
example : W.integrateAgainst I AxiomaticGW.WDVV.stableArity
      (Omega.omega 0 (Fin 4) AxiomaticGW.WDVV.stableArity ![1,1,0] a)
      (StrataModule.basis (AxiomaticGW.WDVV.columns 1)) =
    ∑ split ∈ exceptionalSplits,
      Omega.pairing.pairContract
        (Omega.ancestorInvariant P I 0 (Option (Fin 2))
          StableArity.zero_option_fin_two split.1 (fun _ ↦ 0))
        (Omega.ancestorInvariant P I 0 (Option (Fin 2))
          StableArity.zero_option_fin_two split.2 (fun _ ↦ 0))
        (a ∘ AxiomaticGW.WDVV.labels 1) := by
  rw [AxiomaticGW.WDVV.integrate_column_gw A U W F hsep hfund hlabels Omega P,
    AxiomaticGW.WDVV.gwChannel, exceptionalSplits_eq]

/-- The decoded offline certificate supplies the exact GW consequence under
the named geometric boundary relation, with no final recurrence hypothesis. -/
example (hboundary : AxiomaticGW.WDVV.BoundaryClassesEqual F) :
    (∑ i, AxiomaticGW.WDVV.requested i •
      AxiomaticGW.WDVV.gwChannel Omega P I ![1,1,0] a i) = 0 :=
  AxiomaticGW.WDVV.exchange_gw_eq_zero A U W F hsep hfund hlabels hboundary
    Omega P _ a AxiomaticGW.WDVVReplay.presentation AxiomaticGW.WDVVReplay.accepted

end Evaluation

end AxiomaticGWTest.Tautological.WDVV

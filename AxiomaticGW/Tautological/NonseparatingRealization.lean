/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.NonseparatingGluing
public import AxiomaticGW.Tautological.LegPsiRealization
public import AxiomaticGW.GW.NonseparatingBoundary

/-!
# Realization and certificate transfer through nonseparating gluing

Composing a graph's raw gluing map with the elementary nonseparating map is
a geometric compatibility input on basis strata. Its linear extension,
kernel preservation, integrated pull-push equation, and certificate transfer
are proved here. The existing CohFT/GW boundary contraction then evaluates
the resulting graph operation, with the full curve class unchanged.

No geometric relation validity, general graph splitting, or stable-map
descendant comparison is inferred from the combinatorial construction.
-/

@[expose] public section

namespace AxiomaticGW

open scoped BigOperators

namespace RelationCertificate

/-- The same coordinates express the glued combination. Distinct source
columns may coincide after gluing; their coefficients then add. -/
theorem nonseparating_interpret {g n : ℕ} {S : Type} [Fintype S]
    (columns : Fin n → TautologicalStratum g (Option (Option S))) (x : Coordinates n) :
    StrataModule.nonseparating (interpret columns x) =
      interpret (fun i ↦ (columns i).nonseparating) x := by
  simp only [interpret_apply, map_sum, map_smul, StrataModule.nonseparating_basis]

end RelationCertificate

namespace StrataRealization

universe u

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
  {g : ℕ} {S : Type} [Fintype S]

attribute [local instance] strataRealizationModule

/-- Raw graph-map composition with the elementary nonseparating map. This
is a cohomology compatibility law, independent of any GW family or relation. -/
def NonseparatingCompatible (A : StrataRealization C g (Option (Option S)))
    (B : StrataRealization C (g + 1) S) (F : NonseparatingPushforward C I)
    (h : StableArity (g + 1) S) : Prop :=
  ∀ x, B.map (StrataModule.basis x.nonseparating) =
    F.push g S h (A.map (StrataModule.basis x))

/-- Compatibility on basis strata extends to every rational combination
through the actual linear graph operation. -/
theorem map_nonseparating (A : StrataRealization C g (Option (Option S)))
    (B : StrataRealization C (g + 1) S) (F : NonseparatingPushforward C I)
    (h : StableArity (g + 1) S) (hAB : A.NonseparatingCompatible B F h)
    (r : StrataModule g (Option (Option S))) :
    B.map (StrataModule.nonseparating r) = F.push g S h (A.map r) := by
  have heq : B.map.comp StrataModule.nonseparating =
      ((F.push g S h).restrictScalars ℚ).comp A.map := by
    apply Finsupp.lhom_ext
    intro x q
    have hsingle : Finsupp.single x q = q • StrataModule.basis x := by
      simp only [StrataModule.basis, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hsingle]
    simp only [LinearMap.comp_apply, map_smul, StrataModule.nonseparating_basis]
    exact congrArg (fun y : C.H (g + 1) S ↦ q • y) (hAB x)
  exact congrArg (fun f ↦ f r) heq

/-- A relation in the source realization remains a relation after gluing;
no final integrated equation is supplied as a hypothesis. -/
theorem nonseparating_mem_kernel (A : StrataRealization C g (Option (Option S)))
    (B : StrataRealization C (g + 1) S) (F : NonseparatingPushforward C I)
    (h : StableArity (g + 1) S) (hAB : A.NonseparatingCompatible B F h)
    {r : StrataModule g (Option (Option S))} (hr : r ∈ A.kernel) :
    StrataModule.nonseparating r ∈ B.kernel := by
  rw [B.mem_kernel_iff, A.map_nonseparating B F h hAB, (A.mem_kernel_iff r).mp hr, map_zero]

/-- The integrated graph operation is source evaluation against the
nonseparating pullback of the held insertion. -/
theorem integrateAgainst_nonseparating (A : StrataRealization C g (Option (Option S)))
    (B : StrataRealization C (g + 1) S) (F : NonseparatingPushforward C I)
    (h : StableArity (g + 1) S) (hAB : A.NonseparatingCompatible B F h)
    (w : C.H (g + 1) S) (r : StrataModule g (Option (Option S))) :
    B.integrateAgainst I h w (StrataModule.nonseparating r) =
      A.integrateAgainst I (StableArity.double_option_iff.mpr h)
        (C.nonseparating g S h w) r := by
  rw [integrateAgainst_apply, A.map_nonseparating B F h hAB,
    F.integrate_mul_push, integrateAgainst_apply]

/-- CohFT evaluation of the explicit graph operation is the boundary
functional whose inverse-metric contraction was proved from primitive laws. -/
theorem integrateAgainst_nonseparating_cohFT {V : Type u} [AddCommGroup V] [Module R V]
    [Module.Free R V] [Module.Finite R V]
    (A : StrataRealization C g (Option (Option S))) (B : StrataRealization C (g + 1) S)
    (F : NonseparatingPushforward C I) (h : StableArity (g + 1) S)
    (hAB : A.NonseparatingCompatible B F h) (Omega : CohFT R V C)
    (a : S → V) (r : StrataModule g (Option (Option S))) :
    B.integrateAgainst I h (Omega.omega (g + 1) S h a) (StrataModule.nonseparating r) =
      Omega.nonseparatingInvariant F g S h (A.map r) a := by
  rw [integrateAgainst_apply, A.map_nonseparating B F h hAB,
    CohFT.nonseparatingInvariant_apply]

/-- GW evaluation keeps the same full class on both sides of the node;
the existing boundary contraction theorem supplies its numerical equation. -/
theorem integrateAgainst_nonseparating_gw {V Bclass : Type u}
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid Bclass] {D : EffectiveCurveMonoid Bclass}
    (A : StrataRealization C g (Option (Option S))) (B : StrataRealization C (g + 1) S)
    (F : NonseparatingPushforward C I) (h : StableArity (g + 1) S)
    (hAB : A.NonseparatingCompatible B F h) (Omega : GromovWittenTheory R V Bclass D C)
    (beta : Bclass) (a : S → V) (r : StrataModule g (Option (Option S))) :
    B.integrateAgainst I h (Omega.omega (g + 1) S h beta a)
        (StrataModule.nonseparating r) =
      Omega.nonseparatingInvariant F g S h beta (A.map r) a := by
  rw [integrateAgainst_apply, A.map_nonseparating B F h hAB,
    GromovWittenTheory.nonseparatingInvariant_apply]

/-- A checked exact row witness transfers to the expanded integrated glued
equation. Only original row vanishing and geometric composition are inputs. -/
theorem certificate_nonseparating_eq_zero {m n : ℕ}
    (A : StrataRealization C g (Option (Option S))) (B : StrataRealization C (g + 1) S)
    (F : NonseparatingPushforward C I) (h : StableArity (g + 1) S)
    (hAB : A.NonseparatingCompatible B F h) (w : C.H (g + 1) S)
    (columns : Fin n → TautologicalStratum g (Option (Option S)))
    (rows : Fin m → RelationCertificate.Coordinates n)
    (requested : RelationCertificate.Coordinates n)
    (certificate : RelationCertificate.Certificate m)
    (hcheck : RelationCertificate.check rows requested certificate = true)
    (hrows : ∀ row, A.map (RelationCertificate.interpret columns (rows row)) = 0) :
    (∑ i, requested i • I.integrate (g + 1) S h
      (w * B.map (StrataModule.basis (columns i).nonseparating))) = 0 := by
  have hz := RelationCertificate.evaluation_eq_zero columns rows requested certificate hcheck
    ((B.integrateAgainst I h w).comp StrataModule.nonseparating) (by
      intro row
      rw [LinearMap.comp_apply, integrateAgainst_apply, A.map_nonseparating B F h hAB,
        hrows row, map_zero, mul_zero, map_zero])
  simpa only [LinearMap.comp_apply, RelationCertificate.interpret_apply,
    map_sum, map_smul, StrataModule.nonseparating_basis, integrateAgainst_apply] using hz

end StrataRealization

end AxiomaticGW

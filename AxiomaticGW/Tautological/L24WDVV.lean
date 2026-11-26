/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24Symmetry
public import AxiomaticGW.Tautological.WDVVForgetful

/-!
# The five WDVV corrections in L24

Each row substitutes the original four-point rational channel equation in
a specified decorated component, then takes the same sixfold marking average.
Geometric vanishing follows from primitive boundary equality and graph laws.
-/

@[expose] public section

namespace AxiomaticGW.L24WDVV
open RelationCertificate

set_option maxRecDepth 20000

open StrataOperation

/-- The retained component, including its original external and node powers. -/
def context0Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 2) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context0 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.refl _)).join (g₂ := 2)
    context0Fixed0 (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![1,
    2, 3, 0] ![3, 0, 1, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate destinations for this original four-point channel equation. -/
def destination0 : Fin 3 → Fin 815 := ![64, 0, 48]

/-- Node powers and every marking are checked on the actual contextual graph. -/
theorem covered0 : ∀ i, WDVV.requested i ≠ 0 →
    (context0.graph (WDVV.graph i)).isomorphic?
      (L24Graphs.graph (destination0 i)) = true := by
  decide +kernel

/-- The symmetrized WDVV image includes all rational raw coefficients. -/
theorem image0 :
    L24Symmetry.average (context0.map (interpret WDVV.columns WDVV.requested)) =
      interpret L24Graphs.columns (L24Symmetry.averageCoordinates (imageCoordinates destination0
        WDVV.requested)) := by
  rw [← L24Symmetry.average_interpret]
  exact congrArg L24Symmetry.average
    (context0.map_interpret _ WDVV.graph_totalGenus _ L24Graphs.graph_totalGenus
      _ _ covered0)

/-- The retained component, including its original external and node powers. -/
def context1Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 2) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context1 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.refl _)).join (g₂ := 2)
    context1Fixed0 (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![1,
    2, 3, 0] ![3, 0, 1, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate destinations for this original four-point channel equation. -/
def destination1 : Fin 3 → Fin 815 := ![65, 0, 49]

/-- Node powers and every marking are checked on the actual contextual graph. -/
theorem covered1 : ∀ i, WDVV.requested i ≠ 0 →
    (context1.graph (WDVV.graph i)).isomorphic?
      (L24Graphs.graph (destination1 i)) = true := by
  decide +kernel

/-- The symmetrized WDVV image includes all rational raw coefficients. -/
theorem image1 :
    L24Symmetry.average (context1.map (interpret WDVV.columns WDVV.requested)) =
      interpret L24Graphs.columns (L24Symmetry.averageCoordinates (imageCoordinates destination1
        WDVV.requested)) := by
  rw [← L24Symmetry.average_interpret]
  exact congrArg L24Symmetry.average
    (context1.map_interpret _ WDVV.graph_totalGenus _ L24Graphs.graph_totalGenus
      _ _ covered1)

/-- The retained component, including its original external and node powers. -/
def context2Fixed0 : DecoratedStableGraph (Fin 3) :=
  { graph :=
      ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![0] } :
        StableGraphCode.Candidate (Fin 3) 1 0).toGraph (g := 0) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0],
    halfEdgePsiPower := Fin.elim0 }

/-- The retained component, including its original external and node powers. -/
def context2Fixed1 : DecoratedStableGraph (Fin 1) :=
  { graph :=
      ({ legVertex := ![0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 1) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context2 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  (((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.refl _)).join (g₂ := 0)
    context2Fixed0 (by decide +kernel) (by norm_num [StableArity]) 2 2).join (g₂ := 2)
    context2Fixed1 (by decide +kernel) (by norm_num [StableArity]) 2 0).relabel (Equiv.refl _))

/-- Candidate destinations for this original four-point channel equation. -/
def destination2 : Fin 3 → Fin 815 := ![108, 107, 0]

/-- Node powers and every marking are checked on the actual contextual graph. -/
theorem covered2 : ∀ i, (WDVV.rows 0) i ≠ 0 →
    (context2.graph (WDVV.graph i)).isomorphic?
      (L24Graphs.graph (destination2 i)) = true := by
  decide +kernel

/-- The symmetrized WDVV image includes all rational raw coefficients. -/
theorem image2 :
    L24Symmetry.average (context2.map (interpret WDVV.columns (WDVV.rows 0))) =
      interpret L24Graphs.columns (L24Symmetry.averageCoordinates (imageCoordinates destination2
        (WDVV.rows 0))) := by
  rw [← L24Symmetry.average_interpret]
  exact congrArg L24Symmetry.average
    (context2.map_interpret _ WDVV.graph_totalGenus _ L24Graphs.graph_totalGenus
      _ _ covered2)

/-- The retained component, including its original external and node powers. -/
def context3Fixed0 : DecoratedStableGraph (Fin 3) :=
  { graph :=
      ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![0] } :
        StableGraphCode.Candidate (Fin 3) 1 0).toGraph (g := 0) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0],
    halfEdgePsiPower := Fin.elim0 }

/-- The retained component, including its original external and node powers. -/
def context3Fixed1 : DecoratedStableGraph (Fin 1) :=
  { graph :=
      ({ legVertex := ![0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 1) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context3 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  (((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.refl _)).join (g₂ := 0)
    context3Fixed0 (by decide +kernel) (by norm_num [StableArity]) 2 2).join (g₂ := 2)
    context3Fixed1 (by decide +kernel) (by norm_num [StableArity]) 2 0).relabel (Equiv.refl _))

/-- Candidate destinations for this original four-point channel equation. -/
def destination3 : Fin 3 → Fin 815 := ![108, 0, 106]

/-- Node powers and every marking are checked on the actual contextual graph. -/
theorem covered3 : ∀ i, WDVV.requested i ≠ 0 →
    (context3.graph (WDVV.graph i)).isomorphic?
      (L24Graphs.graph (destination3 i)) = true := by
  decide +kernel

/-- The symmetrized WDVV image includes all rational raw coefficients. -/
theorem image3 :
    L24Symmetry.average (context3.map (interpret WDVV.columns WDVV.requested)) =
      interpret L24Graphs.columns (L24Symmetry.averageCoordinates (imageCoordinates destination3
        WDVV.requested)) := by
  rw [← L24Symmetry.average_interpret]
  exact congrArg L24Symmetry.average
    (context3.map_interpret _ WDVV.graph_totalGenus _ L24Graphs.graph_totalGenus
      _ _ covered3)

/-- The retained component, including its original external and node powers. -/
def context4Fixed0 : DecoratedStableGraph (Fin 3) :=
  { graph :=
      ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![0] } :
        StableGraphCode.Candidate (Fin 3) 1 0).toGraph (g := 0) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0],
    halfEdgePsiPower := Fin.elim0 }

/-- The retained component, including its original external and node powers. -/
def context4Fixed1 : DecoratedStableGraph (Fin 1) :=
  { graph :=
      ({ legVertex := ![0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 1) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context4 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  (((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.refl _)).join (g₂ := 0)
    context4Fixed0 (by decide +kernel) (by norm_num [StableArity]) 2 2).join (g₂ := 2)
    context4Fixed1 (by decide +kernel) (by norm_num [StableArity]) 2 0).relabel (Equiv.mk ![0,
    2, 1, 3] ![0, 2, 1, 3] (by decide +kernel) (by decide +kernel) ))

/-- Candidate destinations for this original four-point channel equation. -/
def destination4 : Fin 3 → Fin 815 := ![111, 110, 0]

/-- Node powers and every marking are checked on the actual contextual graph. -/
theorem covered4 : ∀ i, (WDVV.rows 0) i ≠ 0 →
    (context4.graph (WDVV.graph i)).isomorphic?
      (L24Graphs.graph (destination4 i)) = true := by
  decide +kernel

/-- The symmetrized WDVV image includes all rational raw coefficients. -/
theorem image4 :
    L24Symmetry.average (context4.map (interpret WDVV.columns (WDVV.rows 0))) =
      interpret L24Graphs.columns (L24Symmetry.averageCoordinates (imageCoordinates destination4
        (WDVV.rows 0))) := by
  rw [← L24Symmetry.average_interpret]
  exact congrArg L24Symmetry.average
    (context4.map_interpret _ WDVV.graph_totalGenus _ L24Graphs.graph_totalGenus
      _ _ covered4)

/-- The five actual symmetrized channel corrections. -/
noncomputable def corrections : Fin 5 → StrataModule 2 (Fin 4) :=
  ![L24Symmetry.average (context0.map (interpret WDVV.columns WDVV.requested)),
    L24Symmetry.average (context1.map (interpret WDVV.columns WDVV.requested)),
    L24Symmetry.average (context2.map (interpret WDVV.columns (WDVV.rows 0))),
    L24Symmetry.average (context3.map (interpret WDVV.columns WDVV.requested)),
    L24Symmetry.average (context4.map (interpret WDVV.columns (WDVV.rows 0)))]

/-- Coordinates of all five verified graph operations. -/
def correctionCoordinates : Fin 5 → Coordinates 815 :=
  ![L24Symmetry.averageCoordinates (imageCoordinates destination0 WDVV.requested),
    L24Symmetry.averageCoordinates (imageCoordinates destination1 WDVV.requested),
    L24Symmetry.averageCoordinates (imageCoordinates destination2 (WDVV.rows 0)),
    L24Symmetry.averageCoordinates (imageCoordinates destination3 WDVV.requested),
    L24Symmetry.averageCoordinates (imageCoordinates destination4 (WDVV.rows 0))]

/-- Every row retains its actual operation and exact finite representation. -/
theorem corrections_eq_interpret (i : Fin 5) :
    corrections i = interpret L24Graphs.columns (correctionCoordinates i) := by
  fin_cases i
  · exact image0
  · exact image1
  · exact image2
  · exact image3
  · exact image4

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- Primitive naturality along these five specific decorated contexts. -/
def Compatible (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (P : PsiClasses C) : Prop :=
  ∀ i : Fin 5,
    (![context0.Compatible A F P WDVV.stableArity, context1.Compatible A F P WDVV.stableArity,
      context2.Compatible A F P WDVV.stableArity, context3.Compatible A F P WDVV.stableArity,
      context4.Compatible A F P WDVV.stableArity]) i

/-- Original boundary equality proves all attached, symmetrized WDVV corrections. -/
theorem corrections_vanish_from_geometry
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (hc : Compatible A F P)
    (hsource : ∀ i, (WDVV.expression i).Compatible A F N)
    (hboundary : WDVV.BoundaryClassesEqual F)
    (hl : ∀ p, (A 2 (Fin 4)).RelabelCompatible (A 2 (Fin 4))
      L24Symmetry.stableArity L24Symmetry.stableArity (L24Symmetry.labels p))
    (i : Fin 5) : (A 2 (Fin 4)).map (corrections i) = 0 := by
  have hr (j : Fin 2) := WDVV.map_relation_eq_zero_of_compatible A F N hsource hboundary j
  have hq : (A 0 (Fin 4)).map (interpret WDVV.columns WDVV.requested) = 0 :=
    RelationCertificate.evaluation_eq_zero WDVV.columns WDVV.rows WDVV.requested
      WDVV.certificate WDVV.check_requested (A 0 (Fin 4)).map hr
  fin_cases i
  · exact L24Symmetry.average_vanishes (A 2 (Fin 4)) hl _
      (context0.map_vanishes A F P _ (hc 0) _ hq)
  · exact L24Symmetry.average_vanishes (A 2 (Fin 4)) hl _
      (context1.map_vanishes A F P _ (hc 1) _ hq)
  · exact L24Symmetry.average_vanishes (A 2 (Fin 4)) hl _
      (context2.map_vanishes A F P _ (hc 2) _ (hr 0))
  · exact L24Symmetry.average_vanishes (A 2 (Fin 4)) hl _
      (context3.map_vanishes A F P _ (hc 3) _ hq)
  · exact L24Symmetry.average_vanishes (A 2 (Fin 4)) hl _
      (context4.map_vanishes A F P _ (hc 4) _ (hr 0))

end AxiomaticGW.L24WDVV

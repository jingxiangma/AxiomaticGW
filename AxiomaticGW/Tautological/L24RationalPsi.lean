/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24Graphs
public import AxiomaticGW.Tautological.StrataOperationReplay
public import AxiomaticGW.Tautological.RationalPsiRelation

/-!
# The 37 rational-component psi corrections in L24

These insert the derived four- and five-marked genus-zero psi expansions
into actual decorated trees. Each fixed component keeps its external and
node powers; every source flag and output label is explicit.
-/

@[expose] public section

namespace AxiomaticGW.L24RationalPsi
open RelationCertificate

set_option maxRecDepth 20000

open StrataOperation

/-- The retained component, including its original external and node powers. -/
def context85Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 2) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context85 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.refl _)).join (g₂ := 2)
    context85Fixed0 (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![1,
    2, 3, 0] ![3, 0, 1, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination85 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![10, 48]

/-- The kernel checks every actual decorated graph image. -/
theorem covered85 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context85.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination85 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image85 :
    context85.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination85
        (RationalPsiRelation.coordinates 1)) :=
  context85.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered85

/-- The retained component, including its original external and node powers. -/
def context88Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 2) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context88 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![1, 0, 2, 3] ![1, 0, 2,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context88Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![1, 2, 3, 0] ![3, 0,
    1, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination88 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![11, 58]

/-- The kernel checks every actual decorated graph image. -/
theorem covered88 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context88.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination88 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image88 :
    context88.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination88
        (RationalPsiRelation.coordinates 1)) :=
  context88.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered88

/-- The retained component, including its original external and node powers. -/
def context90Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 2) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context90 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![2, 0, 1, 3] ![1, 2, 0,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context90Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![1, 2, 3, 0] ![3, 0,
    1, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination90 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![12, 65]

/-- The kernel checks every actual decorated graph image. -/
theorem covered90 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context90.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination90 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image90 :
    context90.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination90
        (RationalPsiRelation.coordinates 1)) :=
  context90.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered90

/-- The retained component, including its original external and node powers. -/
def context129Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 2) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context129 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.refl _)).join (g₂ := 2)
    context129Fixed0 (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![0,
    2, 3, 1] ![0, 3, 1, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination129 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![23, 50]

/-- The kernel checks every actual decorated graph image. -/
theorem covered129 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context129.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination129 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image129 :
    context129.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination129
        (RationalPsiRelation.coordinates 1)) :=
  context129.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered129

/-- The retained component, including its original external and node powers. -/
def context130Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 2) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context130 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.refl _)).join (g₂ := 2)
    context130Fixed0 (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![0,
    2, 3, 1] ![0, 3, 1, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination130 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![24, 51]

/-- The kernel checks every actual decorated graph image. -/
theorem covered130 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context130.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination130 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image130 :
    context130.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination130
        (RationalPsiRelation.coordinates 1)) :=
  context130.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered130

/-- The retained component, including its original external and node powers. -/
def context131Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 2) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context131 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![1, 0, 2, 3] ![1, 0, 2,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context131Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![0, 2, 3, 1] ![0, 3,
    1, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination131 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![25, 75]

/-- The kernel checks every actual decorated graph image. -/
theorem covered131 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context131.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination131 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image131 :
    context131.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination131
        (RationalPsiRelation.coordinates 1)) :=
  context131.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered131

/-- The retained component, including its original external and node powers. -/
def context132Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 2) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context132 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![1, 0, 2, 3] ![1, 0, 2,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context132Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![0, 2, 3, 1] ![0, 3,
    1, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination132 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![26, 76]

/-- The kernel checks every actual decorated graph image. -/
theorem covered132 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context132.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination132 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image132 :
    context132.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination132
        (RationalPsiRelation.coordinates 1)) :=
  context132.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered132

/-- The retained component, including its original external and node powers. -/
def context133Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 2) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context133 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![2, 0, 1, 3] ![1, 2, 0,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context133Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![0, 2, 3, 1] ![0, 3,
    1, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination133 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![27, 82]

/-- The kernel checks every actual decorated graph image. -/
theorem covered133 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context133.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination133 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image133 :
    context133.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination133
        (RationalPsiRelation.coordinates 1)) :=
  context133.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered133

/-- The retained component, including its original external and node powers. -/
def context134Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 2) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context134 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![2, 0, 1, 3] ![1, 2, 0,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context134Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![0, 2, 3, 1] ![0, 3,
    1, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination134 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![28, 83]

/-- The kernel checks every actual decorated graph image. -/
theorem covered134 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context134.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination134 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image134 :
    context134.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination134
        (RationalPsiRelation.coordinates 1)) :=
  context134.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered134

/-- The retained component, including its original external and node powers. -/
def context163Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 2) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context163 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.refl _)).join (g₂ := 2)
    context163Fixed0 (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![0,
    1, 3, 2] ![0, 1, 3, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination163 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![34, 60]

/-- The kernel checks every actual decorated graph image. -/
theorem covered163 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context163.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination163 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image163 :
    context163.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination163
        (RationalPsiRelation.coordinates 1)) :=
  context163.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered163

/-- The retained component, including its original external and node powers. -/
def context164Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 2) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context164 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![1, 0, 2, 3] ![1, 0, 2,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context164Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![0, 1, 3, 2] ![0, 1,
    3, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination164 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![35, 77]

/-- The kernel checks every actual decorated graph image. -/
theorem covered164 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context164.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination164 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image164 :
    context164.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination164
        (RationalPsiRelation.coordinates 1)) :=
  context164.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered164

/-- The retained component, including its original external and node powers. -/
def context167Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 2) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context167 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![2, 0, 1, 3] ![1, 2, 0,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context167Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![0, 1, 3, 2] ![0, 1,
    3, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination167 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![36, 94]

/-- The kernel checks every actual decorated graph image. -/
theorem covered167 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context167.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination167 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image167 :
    context167.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination167
        (RationalPsiRelation.coordinates 1)) :=
  context167.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered167

/-- The retained component, including its original external and node powers. -/
def context185Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 2) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context185 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.refl _)).join (g₂ := 2)
    context185Fixed0 (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.refl
    _))

/-- Candidate lookup for the complete derived source. -/
def destination185 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![39, 67]

/-- The kernel checks every actual decorated graph image. -/
theorem covered185 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context185.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination185 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image185 :
    context185.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination185
        (RationalPsiRelation.coordinates 1)) :=
  context185.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered185

/-- The retained component, including its original external and node powers. -/
def context186Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 2) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context186 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![1, 0, 2, 3] ![1, 0, 2,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context186Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.refl _))

/-- Candidate lookup for the complete derived source. -/
def destination186 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![40, 84]

/-- The kernel checks every actual decorated graph image. -/
theorem covered186 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context186.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination186 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image186 :
    context186.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination186
        (RationalPsiRelation.coordinates 1)) :=
  context186.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered186

/-- The retained component, including its original external and node powers. -/
def context189Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 2) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context189 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![2, 0, 1, 3] ![1, 2, 0,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context189Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.refl _))

/-- Candidate lookup for the complete derived source. -/
def destination189 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![41, 96]

/-- The kernel checks every actual decorated graph image. -/
theorem covered189 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context189.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination189 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image189 :
    context189.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination189
        (RationalPsiRelation.coordinates 1)) :=
  context189.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered189

/-- The retained component, including its original external and node powers. -/
def context214Fixed0 : DecoratedStableGraph (Fin 1) :=
  { graph :=
      ({ legVertex := ![0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 1) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context214 : StrataOperation 0 (Fin 5) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 5) 0 (Fin 5)).relabel (Equiv.refl _)).join (g₂ := 2)
    context214Fixed0 (by decide +kernel) (by norm_num [StableArity]) 4 0).relabel (Equiv.refl
    _))

/-- Candidate lookup for the complete derived source. -/
def destination214 : Fin (RationalPsiRelation.size 2) → Fin 815 :=
  ![44, 81, 70, 74]

/-- The kernel checks every actual decorated graph image. -/
theorem covered214 : ∀ i, RationalPsiRelation.coordinates 2 i ≠ 0 →
    (context214.graph (RationalPsiRelation.graph 2 i)).isomorphic?
      (L24Graphs.graph (destination214 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image214 :
    context214.map (interpret (RationalPsiRelation.columns 2) (RationalPsiRelation.coordinates
      2)) =
      interpret L24Graphs.columns (imageCoordinates destination214
        (RationalPsiRelation.coordinates 2)) :=
  context214.map_interpret _ (RationalPsiRelation.graph_totalGenus 2)
    _ L24Graphs.graph_totalGenus _ _ covered214

/-- The retained component, including its original external and node powers. -/
def context219Fixed0 : DecoratedStableGraph (Fin 1) :=
  { graph :=
      ({ legVertex := ![0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 1) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context219 : StrataOperation 0 (Fin 5) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 5) 0 (Fin 5)).relabel (Equiv.mk ![1, 0, 2, 3, 4] ![1, 0,
    2, 3, 4] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context219Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 4 0).relabel (Equiv.refl _))

/-- Candidate lookup for the complete derived source. -/
def destination219 : Fin (RationalPsiRelation.size 2) → Fin 815 :=
  ![45, 63, 88, 92]

/-- The kernel checks every actual decorated graph image. -/
theorem covered219 : ∀ i, RationalPsiRelation.coordinates 2 i ≠ 0 →
    (context219.graph (RationalPsiRelation.graph 2 i)).isomorphic?
      (L24Graphs.graph (destination219 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image219 :
    context219.map (interpret (RationalPsiRelation.columns 2) (RationalPsiRelation.coordinates
      2)) =
      interpret L24Graphs.columns (imageCoordinates destination219
        (RationalPsiRelation.coordinates 2)) :=
  context219.map_interpret _ (RationalPsiRelation.graph_totalGenus 2)
    _ L24Graphs.graph_totalGenus _ _ covered219

/-- The retained component, including its original external and node powers. -/
def context223Fixed0 : DecoratedStableGraph (Fin 1) :=
  { graph :=
      ({ legVertex := ![0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 1) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context223 : StrataOperation 0 (Fin 5) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 5) 0 (Fin 5)).relabel (Equiv.mk ![2, 0, 1, 3, 4] ![1, 2,
    0, 3, 4] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context223Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 4 0).relabel (Equiv.refl _))

/-- Candidate lookup for the complete derived source. -/
def destination223 : Fin (RationalPsiRelation.size 2) → Fin 815 :=
  ![46, 56, 97, 101]

/-- The kernel checks every actual decorated graph image. -/
theorem covered223 : ∀ i, RationalPsiRelation.coordinates 2 i ≠ 0 →
    (context223.graph (RationalPsiRelation.graph 2 i)).isomorphic?
      (L24Graphs.graph (destination223 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image223 :
    context223.map (interpret (RationalPsiRelation.columns 2) (RationalPsiRelation.coordinates
      2)) =
      interpret L24Graphs.columns (imageCoordinates destination223
        (RationalPsiRelation.coordinates 2)) :=
  context223.map_interpret _ (RationalPsiRelation.graph_totalGenus 2)
    _ L24Graphs.graph_totalGenus _ _ covered223

/-- The retained component, including its original external and node powers. -/
def context226Fixed0 : DecoratedStableGraph (Fin 1) :=
  { graph :=
      ({ legVertex := ![0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 1) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context226 : StrataOperation 0 (Fin 5) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 5) 0 (Fin 5)).relabel (Equiv.mk ![3, 0, 1, 2, 4] ![1, 2,
    3, 0, 4] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context226Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 4 0).relabel (Equiv.refl _))

/-- Candidate lookup for the complete derived source. -/
def destination226 : Fin (RationalPsiRelation.size 2) → Fin 815 :=
  ![47, 56, 97, 105]

/-- The kernel checks every actual decorated graph image. -/
theorem covered226 : ∀ i, RationalPsiRelation.coordinates 2 i ≠ 0 →
    (context226.graph (RationalPsiRelation.graph 2 i)).isomorphic?
      (L24Graphs.graph (destination226 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image226 :
    context226.map (interpret (RationalPsiRelation.columns 2) (RationalPsiRelation.coordinates
      2)) =
      interpret L24Graphs.columns (imageCoordinates destination226
        (RationalPsiRelation.coordinates 2)) :=
  context226.map_interpret _ (RationalPsiRelation.graph_totalGenus 2)
    _ L24Graphs.graph_totalGenus _ _ covered226

/-- The retained component, including its original external and node powers. -/
def context240Fixed0 : DecoratedStableGraph (Fin 3) :=
  { graph :=
      ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![0] } :
        StableGraphCode.Candidate (Fin 3) 1 0).toGraph (g := 0) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0],
    halfEdgePsiPower := Fin.elim0 }

/-- The retained component, including its original external and node powers. -/
def context240Fixed1 : DecoratedStableGraph (Fin 1) :=
  { graph :=
      ({ legVertex := ![0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 1) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context240 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  (((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.refl _)).join (g₂ := 0)
    context240Fixed0 (by decide +kernel) (by norm_num [StableArity]) 2 2).join (g₂ := 2)
    context240Fixed1 (by decide +kernel) (by norm_num [StableArity]) 2 0).relabel (Equiv.refl
    _))

/-- Candidate lookup for the complete derived source. -/
def destination240 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![54, 106]

/-- The kernel checks every actual decorated graph image. -/
theorem covered240 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context240.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination240 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image240 :
    context240.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination240
        (RationalPsiRelation.coordinates 1)) :=
  context240.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered240

/-- The retained component, including its original external and node powers. -/
def context241Fixed0 : DecoratedStableGraph (Fin 3) :=
  { graph :=
      ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![0] } :
        StableGraphCode.Candidate (Fin 3) 1 0).toGraph (g := 0) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0],
    halfEdgePsiPower := Fin.elim0 }

/-- The retained component, including its original external and node powers. -/
def context241Fixed1 : DecoratedStableGraph (Fin 1) :=
  { graph :=
      ({ legVertex := ![0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 1) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context241 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  (((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![1, 0, 2, 3] ![1, 0, 2,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 0) context241Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 2 2).join (g₂ := 2) context241Fixed1
    (by decide +kernel) (by norm_num [StableArity]) 2 0).relabel (Equiv.refl _))

/-- Candidate lookup for the complete derived source. -/
def destination241 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![55, 107]

/-- The kernel checks every actual decorated graph image. -/
theorem covered241 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context241.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination241 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image241 :
    context241.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination241
        (RationalPsiRelation.coordinates 1)) :=
  context241.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered241

/-- The retained component, including its original external and node powers. -/
def context279Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 2) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context279 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.refl _)).join (g₂ := 2)
    context279Fixed0 (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![1,
    2, 3, 0] ![3, 0, 1, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination279 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![71, 106]

/-- The kernel checks every actual decorated graph image. -/
theorem covered279 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context279.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination279 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image279 :
    context279.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination279
        (RationalPsiRelation.coordinates 1)) :=
  context279.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered279

/-- The retained component, including its original external and node powers. -/
def context280Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 2) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context280 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![1, 0, 2, 3] ![1, 0, 2,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context280Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![1, 2, 3, 0] ![3, 0,
    1, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination280 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![72, 109]

/-- The kernel checks every actual decorated graph image. -/
theorem covered280 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context280.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination280 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image280 :
    context280.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination280
        (RationalPsiRelation.coordinates 1)) :=
  context280.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered280

/-- The retained component, including its original external and node powers. -/
def context281Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 2) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context281 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![2, 0, 1, 3] ![1, 2, 0,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context281Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![1, 2, 3, 0] ![3, 0,
    1, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination281 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![73, 112]

/-- The kernel checks every actual decorated graph image. -/
theorem covered281 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context281.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination281 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image281 :
    context281.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination281
        (RationalPsiRelation.coordinates 1)) :=
  context281.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered281

/-- The retained component, including its original external and node powers. -/
def context292Fixed0 : DecoratedStableGraph (Fin 3) :=
  { graph :=
      ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![0] } :
        StableGraphCode.Candidate (Fin 3) 1 0).toGraph (g := 0) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0],
    halfEdgePsiPower := Fin.elim0 }

/-- The retained component, including its original external and node powers. -/
def context292Fixed1 : DecoratedStableGraph (Fin 1) :=
  { graph :=
      ({ legVertex := ![0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 1) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context292 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  (((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.refl _)).join (g₂ := 0)
    context292Fixed0 (by decide +kernel) (by norm_num [StableArity]) 2 2).join (g₂ := 2)
    context292Fixed1 (by decide +kernel) (by norm_num [StableArity]) 2 0).relabel (Equiv.mk ![1,
    2, 0, 3] ![2, 0, 1, 3] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination292 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![79, 115]

/-- The kernel checks every actual decorated graph image. -/
theorem covered292 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context292.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination292 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image292 :
    context292.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination292
        (RationalPsiRelation.coordinates 1)) :=
  context292.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered292

/-- The retained component, including its original external and node powers. -/
def context293Fixed0 : DecoratedStableGraph (Fin 3) :=
  { graph :=
      ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![0] } :
        StableGraphCode.Candidate (Fin 3) 1 0).toGraph (g := 0) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0],
    halfEdgePsiPower := Fin.elim0 }

/-- The retained component, including its original external and node powers. -/
def context293Fixed1 : DecoratedStableGraph (Fin 1) :=
  { graph :=
      ({ legVertex := ![0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 1) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context293 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  (((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![1, 0, 2, 3] ![1, 0, 2,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 0) context293Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 2 2).join (g₂ := 2) context293Fixed1
    (by decide +kernel) (by norm_num [StableArity]) 2 0).relabel (Equiv.mk ![1, 2, 0, 3] ![2, 0,
    1, 3] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination293 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![80, 116]

/-- The kernel checks every actual decorated graph image. -/
theorem covered293 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context293.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination293 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image293 :
    context293.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination293
        (RationalPsiRelation.coordinates 1)) :=
  context293.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered293

/-- The retained component, including its original external and node powers. -/
def context305Fixed0 : DecoratedStableGraph (Fin 3) :=
  { graph :=
      ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![0] } :
        StableGraphCode.Candidate (Fin 3) 1 0).toGraph (g := 0) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0],
    halfEdgePsiPower := Fin.elim0 }

/-- The retained component, including its original external and node powers. -/
def context305Fixed1 : DecoratedStableGraph (Fin 1) :=
  { graph :=
      ({ legVertex := ![0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 1) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context305 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  (((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.refl _)).join (g₂ := 0)
    context305Fixed0 (by decide +kernel) (by norm_num [StableArity]) 2 2).join (g₂ := 2)
    context305Fixed1 (by decide +kernel) (by norm_num [StableArity]) 2 0).relabel (Equiv.mk ![1,
    3, 0, 2] ![2, 0, 3, 1] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination305 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![86, 117]

/-- The kernel checks every actual decorated graph image. -/
theorem covered305 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context305.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination305 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image305 :
    context305.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination305
        (RationalPsiRelation.coordinates 1)) :=
  context305.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered305

/-- The retained component, including its original external and node powers. -/
def context306Fixed0 : DecoratedStableGraph (Fin 3) :=
  { graph :=
      ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![0] } :
        StableGraphCode.Candidate (Fin 3) 1 0).toGraph (g := 0) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0],
    halfEdgePsiPower := Fin.elim0 }

/-- The retained component, including its original external and node powers. -/
def context306Fixed1 : DecoratedStableGraph (Fin 1) :=
  { graph :=
      ({ legVertex := ![0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 1) 1 0).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0],
    halfEdgePsiPower := Fin.elim0 }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context306 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  (((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![1, 0, 2, 3] ![1, 0, 2,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 0) context306Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 2 2).join (g₂ := 2) context306Fixed1
    (by decide +kernel) (by norm_num [StableArity]) 2 0).relabel (Equiv.mk ![1, 3, 0, 2] ![2, 0,
    3, 1] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination306 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![87, 118]

/-- The kernel checks every actual decorated graph image. -/
theorem covered306 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context306.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination306 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image306 :
    context306.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination306
        (RationalPsiRelation.coordinates 1)) :=
  context306.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered306

/-- The retained component, including its original external and node powers. -/
def context312Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 2) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context312 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.refl _)).join (g₂ := 2)
    context312Fixed0 (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![0,
    2, 3, 1] ![0, 3, 1, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination312 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![89, 107]

/-- The kernel checks every actual decorated graph image. -/
theorem covered312 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context312.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination312 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image312 :
    context312.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination312
        (RationalPsiRelation.coordinates 1)) :=
  context312.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered312

/-- The retained component, including its original external and node powers. -/
def context313Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 2) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context313 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![1, 0, 2, 3] ![1, 0, 2,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context313Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![0, 2, 3, 1] ![0, 3,
    1, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination313 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![90, 115]

/-- The kernel checks every actual decorated graph image. -/
theorem covered313 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context313.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination313 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image313 :
    context313.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination313
        (RationalPsiRelation.coordinates 1)) :=
  context313.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered313

/-- The retained component, including its original external and node powers. -/
def context314Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 2) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context314 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![2, 0, 1, 3] ![1, 2, 0,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context314Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![0, 2, 3, 1] ![0, 3,
    1, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination314 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![91, 117]

/-- The kernel checks every actual decorated graph image. -/
theorem covered314 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context314.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination314 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image314 :
    context314.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination314
        (RationalPsiRelation.coordinates 1)) :=
  context314.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered314

/-- The retained component, including its original external and node powers. -/
def context332Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 2) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context332 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.refl _)).join (g₂ := 2)
    context332Fixed0 (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![0,
    1, 3, 2] ![0, 1, 3, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination332 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![98, 110]

/-- The kernel checks every actual decorated graph image. -/
theorem covered332 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context332.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination332 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image332 :
    context332.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination332
        (RationalPsiRelation.coordinates 1)) :=
  context332.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered332

/-- The retained component, including its original external and node powers. -/
def context333Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 2) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context333 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![1, 0, 2, 3] ![1, 0, 2,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context333Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![0, 1, 3, 2] ![0, 1,
    3, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination333 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![99, 116]

/-- The kernel checks every actual decorated graph image. -/
theorem covered333 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context333.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination333 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image333 :
    context333.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination333
        (RationalPsiRelation.coordinates 1)) :=
  context333.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered333

/-- The retained component, including its original external and node powers. -/
def context334Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 2) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context334 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![2, 0, 1, 3] ![1, 2, 0,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context334Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.mk ![0, 1, 3, 2] ![0, 1,
    3, 2] (by decide +kernel) (by decide +kernel) ))

/-- Candidate lookup for the complete derived source. -/
def destination334 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![100, 119]

/-- The kernel checks every actual decorated graph image. -/
theorem covered334 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context334.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination334 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image334 :
    context334.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination334
        (RationalPsiRelation.coordinates 1)) :=
  context334.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered334

/-- The retained component, including its original external and node powers. -/
def context339Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 2) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context339 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.refl _)).join (g₂ := 2)
    context339Fixed0 (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.refl
    _))

/-- Candidate lookup for the complete derived source. -/
def destination339 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![102, 113]

/-- The kernel checks every actual decorated graph image. -/
theorem covered339 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context339.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination339 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image339 :
    context339.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination339
        (RationalPsiRelation.coordinates 1)) :=
  context339.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered339

/-- The retained component, including its original external and node powers. -/
def context340Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 2) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context340 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![1, 0, 2, 3] ![1, 0, 2,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context340Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.refl _))

/-- Candidate lookup for the complete derived source. -/
def destination340 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![103, 118]

/-- The kernel checks every actual decorated graph image. -/
theorem covered340 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context340.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination340 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image340 :
    context340.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination340
        (RationalPsiRelation.coordinates 1)) :=
  context340.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered340

/-- The retained component, including its original external and node powers. -/
def context341Fixed0 : DecoratedStableGraph (Fin 2) :=
  { graph :=
      ({ legVertex := ![0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 2) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Insert the source at the selected rational component using its ordered flags. -/
def context341 : StrataOperation 0 (Fin 4) 2 (Fin 4) :=
  ((((.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).relabel (Equiv.mk ![2, 0, 1, 3] ![1, 2, 0,
    3] (by decide +kernel) (by decide +kernel) )).join (g₂ := 2) context341Fixed0
    (by decide +kernel) (by norm_num [StableArity]) 3 1).relabel (Equiv.refl _))

/-- Candidate lookup for the complete derived source. -/
def destination341 : Fin (RationalPsiRelation.size 1) → Fin 815 :=
  ![104, 120]

/-- The kernel checks every actual decorated graph image. -/
theorem covered341 : ∀ i, RationalPsiRelation.coordinates 1 i ≠ 0 →
    (context341.graph (RationalPsiRelation.graph 1 i)).isomorphic?
      (L24Graphs.graph (destination341 i)) = true := by
  decide +kernel

/-- The graph check identifies the entire rational-component correction. -/
theorem image341 :
    context341.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
      1)) =
      interpret L24Graphs.columns (imageCoordinates destination341
        (RationalPsiRelation.coordinates 1)) :=
  context341.map_interpret _ (RationalPsiRelation.graph_totalGenus 1)
    _ L24Graphs.graph_totalGenus _ _ covered341

/-- All actual rational-component corrections in the retained reduction order. -/
noncomputable def corrections : Fin 37 → StrataModule 2 (Fin 4) :=
  ![context85.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
    1)), context88.map (interpret (RationalPsiRelation.columns 1)
    (RationalPsiRelation.coordinates 1)), context90.map (interpret (RationalPsiRelation.columns
    1) (RationalPsiRelation.coordinates 1)), context129.map (interpret
    (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates 1)), context130.map
    (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates 1)),
    context131.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
    1)), context132.map (interpret (RationalPsiRelation.columns 1)
    (RationalPsiRelation.coordinates 1)), context133.map (interpret (RationalPsiRelation.columns
    1) (RationalPsiRelation.coordinates 1)), context134.map (interpret
    (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates 1)), context163.map
    (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates 1)),
    context164.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
    1)), context167.map (interpret (RationalPsiRelation.columns 1)
    (RationalPsiRelation.coordinates 1)), context185.map (interpret (RationalPsiRelation.columns
    1) (RationalPsiRelation.coordinates 1)), context186.map (interpret
    (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates 1)), context189.map
    (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates 1)),
    context214.map (interpret (RationalPsiRelation.columns 2) (RationalPsiRelation.coordinates
    2)), context219.map (interpret (RationalPsiRelation.columns 2)
    (RationalPsiRelation.coordinates 2)), context223.map (interpret (RationalPsiRelation.columns
    2) (RationalPsiRelation.coordinates 2)), context226.map (interpret
    (RationalPsiRelation.columns 2) (RationalPsiRelation.coordinates 2)), context240.map
    (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates 1)),
    context241.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
    1)), context279.map (interpret (RationalPsiRelation.columns 1)
    (RationalPsiRelation.coordinates 1)), context280.map (interpret (RationalPsiRelation.columns
    1) (RationalPsiRelation.coordinates 1)), context281.map (interpret
    (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates 1)), context292.map
    (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates 1)),
    context293.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
    1)), context305.map (interpret (RationalPsiRelation.columns 1)
    (RationalPsiRelation.coordinates 1)), context306.map (interpret (RationalPsiRelation.columns
    1) (RationalPsiRelation.coordinates 1)), context312.map (interpret
    (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates 1)), context313.map
    (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates 1)),
    context314.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
    1)), context332.map (interpret (RationalPsiRelation.columns 1)
    (RationalPsiRelation.coordinates 1)), context333.map (interpret (RationalPsiRelation.columns
    1) (RationalPsiRelation.coordinates 1)), context334.map (interpret
    (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates 1)), context339.map
    (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates 1)),
    context340.map (interpret (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates
    1)), context341.map (interpret (RationalPsiRelation.columns 1)
    (RationalPsiRelation.coordinates 1))]

/-- Coordinates accumulated only after the graph coverage checks. -/
def correctionCoordinates : Fin 37 → Coordinates 815 :=
  ![imageCoordinates destination85 (RationalPsiRelation.coordinates 1), imageCoordinates
    destination88 (RationalPsiRelation.coordinates 1), imageCoordinates destination90
    (RationalPsiRelation.coordinates 1), imageCoordinates destination129
    (RationalPsiRelation.coordinates 1), imageCoordinates destination130
    (RationalPsiRelation.coordinates 1), imageCoordinates destination131
    (RationalPsiRelation.coordinates 1), imageCoordinates destination132
    (RationalPsiRelation.coordinates 1), imageCoordinates destination133
    (RationalPsiRelation.coordinates 1), imageCoordinates destination134
    (RationalPsiRelation.coordinates 1), imageCoordinates destination163
    (RationalPsiRelation.coordinates 1), imageCoordinates destination164
    (RationalPsiRelation.coordinates 1), imageCoordinates destination167
    (RationalPsiRelation.coordinates 1), imageCoordinates destination185
    (RationalPsiRelation.coordinates 1), imageCoordinates destination186
    (RationalPsiRelation.coordinates 1), imageCoordinates destination189
    (RationalPsiRelation.coordinates 1), imageCoordinates destination214
    (RationalPsiRelation.coordinates 2), imageCoordinates destination219
    (RationalPsiRelation.coordinates 2), imageCoordinates destination223
    (RationalPsiRelation.coordinates 2), imageCoordinates destination226
    (RationalPsiRelation.coordinates 2), imageCoordinates destination240
    (RationalPsiRelation.coordinates 1), imageCoordinates destination241
    (RationalPsiRelation.coordinates 1), imageCoordinates destination279
    (RationalPsiRelation.coordinates 1), imageCoordinates destination280
    (RationalPsiRelation.coordinates 1), imageCoordinates destination281
    (RationalPsiRelation.coordinates 1), imageCoordinates destination292
    (RationalPsiRelation.coordinates 1), imageCoordinates destination293
    (RationalPsiRelation.coordinates 1), imageCoordinates destination305
    (RationalPsiRelation.coordinates 1), imageCoordinates destination306
    (RationalPsiRelation.coordinates 1), imageCoordinates destination312
    (RationalPsiRelation.coordinates 1), imageCoordinates destination313
    (RationalPsiRelation.coordinates 1), imageCoordinates destination314
    (RationalPsiRelation.coordinates 1), imageCoordinates destination332
    (RationalPsiRelation.coordinates 1), imageCoordinates destination333
    (RationalPsiRelation.coordinates 1), imageCoordinates destination334
    (RationalPsiRelation.coordinates 1), imageCoordinates destination339
    (RationalPsiRelation.coordinates 1), imageCoordinates destination340
    (RationalPsiRelation.coordinates 1), imageCoordinates destination341
    (RationalPsiRelation.coordinates 1)]

/-- The entire correction family has the verified finite interpretation. -/
theorem corrections_eq_interpret (i : Fin 37) :
    corrections i = interpret L24Graphs.columns (correctionCoordinates i) := by
  fin_cases i
  · exact image85
  · exact image88
  · exact image90
  · exact image129
  · exact image130
  · exact image131
  · exact image132
  · exact image133
  · exact image134
  · exact image163
  · exact image164
  · exact image167
  · exact image185
  · exact image186
  · exact image189
  · exact image214
  · exact image219
  · exact image223
  · exact image226
  · exact image240
  · exact image241
  · exact image279
  · exact image280
  · exact image281
  · exact image292
  · exact image293
  · exact image305
  · exact image306
  · exact image312
  · exact image313
  · exact image314
  · exact image332
  · exact image333
  · exact image334
  · exact image339
  · exact image340
  · exact image341

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- Primitive laws along precisely the contexts used by the rational corrections. -/
def Compatible (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (P : PsiClasses C) : Prop :=
  ∀ i : Fin 37,
    (![context85.Compatible A F P (by norm_num [StableArity]) , context88.Compatible A F P
      (by norm_num [StableArity]) , context90.Compatible A F P (by norm_num [StableArity]) ,
      context129.Compatible A F P (by norm_num [StableArity]) , context130.Compatible A F P
      (by norm_num [StableArity]) , context131.Compatible A F P (by norm_num [StableArity]) ,
      context132.Compatible A F P (by norm_num [StableArity]) , context133.Compatible A F P
      (by norm_num [StableArity]) , context134.Compatible A F P (by norm_num [StableArity]) ,
      context163.Compatible A F P (by norm_num [StableArity]) , context164.Compatible A F P
      (by norm_num [StableArity]) , context167.Compatible A F P (by norm_num [StableArity]) ,
      context185.Compatible A F P (by norm_num [StableArity]) , context186.Compatible A F P
      (by norm_num [StableArity]) , context189.Compatible A F P (by norm_num [StableArity]) ,
      context214.Compatible A F P (by norm_num [StableArity]) , context219.Compatible A F P
      (by norm_num [StableArity]) , context223.Compatible A F P (by norm_num [StableArity]) ,
      context226.Compatible A F P (by norm_num [StableArity]) , context240.Compatible A F P
      (by norm_num [StableArity]) , context241.Compatible A F P (by norm_num [StableArity]) ,
      context279.Compatible A F P (by norm_num [StableArity]) , context280.Compatible A F P
      (by norm_num [StableArity]) , context281.Compatible A F P (by norm_num [StableArity]) ,
      context292.Compatible A F P (by norm_num [StableArity]) , context293.Compatible A F P
      (by norm_num [StableArity]) , context305.Compatible A F P (by norm_num [StableArity]) ,
      context306.Compatible A F P (by norm_num [StableArity]) , context312.Compatible A F P
      (by norm_num [StableArity]) , context313.Compatible A F P (by norm_num [StableArity]) ,
      context314.Compatible A F P (by norm_num [StableArity]) , context332.Compatible A F P
      (by norm_num [StableArity]) , context333.Compatible A F P (by norm_num [StableArity]) ,
      context334.Compatible A F P (by norm_num [StableArity]) , context339.Compatible A F P
      (by norm_num [StableArity]) , context340.Compatible A F P (by norm_num [StableArity]) ,
      context341.Compatible A F P (by norm_num [StableArity]) ]) i

/-- The two derived genus-zero psi relations annihilate every attached correction. -/
theorem corrections_vanish
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (P : PsiClasses C) (hc : Compatible A F P)
    (h4 : (A 0 (Fin 4)).map (interpret (RationalPsiRelation.columns 1)
      (RationalPsiRelation.coordinates 1)) = 0)
    (h5 : (A 0 (Fin 5)).map (interpret (RationalPsiRelation.columns 2)
      (RationalPsiRelation.coordinates 2)) = 0)
    (i : Fin 37) : (A 2 (Fin 4)).map (corrections i) = 0 := by
  fin_cases i
  · exact context85.map_vanishes A F P _ (hc 0) _ h4
  · exact context88.map_vanishes A F P _ (hc 1) _ h4
  · exact context90.map_vanishes A F P _ (hc 2) _ h4
  · exact context129.map_vanishes A F P _ (hc 3) _ h4
  · exact context130.map_vanishes A F P _ (hc 4) _ h4
  · exact context131.map_vanishes A F P _ (hc 5) _ h4
  · exact context132.map_vanishes A F P _ (hc 6) _ h4
  · exact context133.map_vanishes A F P _ (hc 7) _ h4
  · exact context134.map_vanishes A F P _ (hc 8) _ h4
  · exact context163.map_vanishes A F P _ (hc 9) _ h4
  · exact context164.map_vanishes A F P _ (hc 10) _ h4
  · exact context167.map_vanishes A F P _ (hc 11) _ h4
  · exact context185.map_vanishes A F P _ (hc 12) _ h4
  · exact context186.map_vanishes A F P _ (hc 13) _ h4
  · exact context189.map_vanishes A F P _ (hc 14) _ h4
  · exact context214.map_vanishes A F P _ (hc 15) _ h5
  · exact context219.map_vanishes A F P _ (hc 16) _ h5
  · exact context223.map_vanishes A F P _ (hc 17) _ h5
  · exact context226.map_vanishes A F P _ (hc 18) _ h5
  · exact context240.map_vanishes A F P _ (hc 19) _ h4
  · exact context241.map_vanishes A F P _ (hc 20) _ h4
  · exact context279.map_vanishes A F P _ (hc 21) _ h4
  · exact context280.map_vanishes A F P _ (hc 22) _ h4
  · exact context281.map_vanishes A F P _ (hc 23) _ h4
  · exact context292.map_vanishes A F P _ (hc 24) _ h4
  · exact context293.map_vanishes A F P _ (hc 25) _ h4
  · exact context305.map_vanishes A F P _ (hc 26) _ h4
  · exact context306.map_vanishes A F P _ (hc 27) _ h4
  · exact context312.map_vanishes A F P _ (hc 28) _ h4
  · exact context313.map_vanishes A F P _ (hc 29) _ h4
  · exact context314.map_vanishes A F P _ (hc 30) _ h4
  · exact context332.map_vanishes A F P _ (hc 31) _ h4
  · exact context333.map_vanishes A F P _ (hc 32) _ h4
  · exact context334.map_vanishes A F P _ (hc 33) _ h4
  · exact context339.map_vanishes A F P _ (hc 34) _ h4
  · exact context340.map_vanishes A F P _ (hc 35) _ h4
  · exact context341.map_vanishes A F P _ (hc 36) _ h4

end AxiomaticGW.L24RationalPsi

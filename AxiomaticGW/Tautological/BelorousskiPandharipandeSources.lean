/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.BelorousskiPandharipandeGraphs
public import AxiomaticGW.Tautological.SeparatingRealization

/-!
# Original component rows and separating provenance for the BP certificate

Seven codimension-one component frames supply sixteen original full-stable
3-spin rows. The (1,1) frame and its two rows reuse `GenusOnePsi`. The others
have (g,n) = (2,2), (0,4), (2,1), (1,4), (1,2), (1,3). Source parameters
are held in the exchange report; these are original FZ rows before row reduction.

Every source column is actually relabelled, glued with a stable fundamental
component, and relabelled into the three-marked target. Kernel graph
isomorphisms check the resulting destinations, including kappa and node powers.
Primitive realization compatibility then preserves vanishing of each original
source row. Neither a final BP vanishing nor a GW recurrence is a field.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open RelationCertificate

/-- Genera of the seven component frames. -/
abbrev sourceGenus : Fin 7 → ℕ := ![2, 0, 2, 1, 1, 1, 1]
/-- Arity includes the last marking, which is used as the separating branch. -/
abbrev sourceArity : Fin 7 → ℕ := ![2, 4, 1, 1, 4, 2, 3]
/-- Number of raw codimension-one columns in each component frame. -/
abbrev sourceSize : Fin 7 → ℕ := ![7, 8, 4, 3, 17, 5, 9]

/-- All component moduli spaces are stable, including the one-point cases. -/
theorem sourceStable (b : Fin 7) : StableArity (sourceGenus b) (Fin (sourceArity b)) := by
  fin_cases b <;> norm_num [sourceGenus, sourceArity, StableArity]

/-- Held component graphs; the existing one-point elliptic frame is reused verbatim. -/
def sourceGraph : (b : Fin 7) → Fin (sourceSize b) → DecoratedStableGraph (Fin (sourceArity b)) :=
  Fin.cases (![tableGraph 2 ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
    StableGraphCode.Candidate (Fin 2) 1 0) (by decide +kernel)
        ![![1, 0]] ![0, 0] Fin.elim0,
      tableGraph 2 ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 2) 1 0) (by decide +kernel)
        ![![0, 0]] ![1, 0] Fin.elim0,
      tableGraph 2 ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 2) 1 0) (by decide +kernel)
        ![![0, 0]] ![0, 1] Fin.elim0,
      tableGraph 2 ({ legVertex := ![0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 2) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0] ![![0, 0]],
      tableGraph 2 ({ legVertex := ![1, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
        StableGraphCode.Candidate (Fin 2) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0] ![![0, 0]],
      tableGraph 2 ({ legVertex := ![1, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
        StableGraphCode.Candidate (Fin 2) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0] ![![0, 0]],
      tableGraph 2 ({ legVertex := ![0, 0], endpoint := ![![0, 0]], genus := ![1] } :
        StableGraphCode.Candidate (Fin 2) 1 1) (by decide +kernel)
        ![![0, 0]] ![0, 0] ![![0, 0]]]) (
    Fin.cases (![tableGraph 0 ({ legVertex := ![0, 0, 0, 0], endpoint := Fin.elim0, genus := ![0]
      } :
    StableGraphCode.Candidate (Fin 4) 1 0) (by decide +kernel)
        ![![1, 0]] ![0, 0, 0, 0] Fin.elim0,
      tableGraph 0 ({ legVertex := ![0, 0, 0, 0], endpoint := Fin.elim0, genus := ![0] } :
        StableGraphCode.Candidate (Fin 4) 1 0) (by decide +kernel)
        ![![0, 0]] ![1, 0, 0, 0] Fin.elim0,
      tableGraph 0 ({ legVertex := ![0, 0, 0, 0], endpoint := Fin.elim0, genus := ![0] } :
        StableGraphCode.Candidate (Fin 4) 1 0) (by decide +kernel)
        ![![0, 0]] ![0, 1, 0, 0] Fin.elim0,
      tableGraph 0 ({ legVertex := ![0, 0, 0, 0], endpoint := Fin.elim0, genus := ![0] } :
        StableGraphCode.Candidate (Fin 4) 1 0) (by decide +kernel)
        ![![0, 0]] ![0, 0, 1, 0] Fin.elim0,
      tableGraph 0 ({ legVertex := ![0, 0, 0, 0], endpoint := Fin.elim0, genus := ![0] } :
        StableGraphCode.Candidate (Fin 4) 1 0) (by decide +kernel)
        ![![0, 0]] ![0, 0, 0, 1] Fin.elim0,
      tableGraph 0 ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 1]], genus := ![0, 0] } :
        StableGraphCode.Candidate (Fin 4) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]],
      tableGraph 0 ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 1]], genus := ![0, 0] } :
        StableGraphCode.Candidate (Fin 4) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]],
      tableGraph 0 ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 1]], genus := ![0, 0] } :
        StableGraphCode.Candidate (Fin 4) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]]]) (
    Fin.cases (![tableGraph 2 ({ legVertex := ![0], endpoint := Fin.elim0, genus := ![2] } :
    StableGraphCode.Candidate (Fin 1) 1 0) (by decide +kernel)
        ![![1, 0]] ![0] Fin.elim0,
      tableGraph 2 ({ legVertex := ![0], endpoint := Fin.elim0, genus := ![2] } :
        StableGraphCode.Candidate (Fin 1) 1 0) (by decide +kernel)
        ![![0, 0]] ![1] Fin.elim0,
      tableGraph 2 ({ legVertex := ![1], endpoint := ![![0, 1]], genus := ![1, 1] } :
        StableGraphCode.Candidate (Fin 1) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0] ![![0, 0]],
      tableGraph 2 ({ legVertex := ![0], endpoint := ![![0, 0]], genus := ![1] } :
        StableGraphCode.Candidate (Fin 1) 1 1) (by decide +kernel)
        ![![0, 0]] ![0] ![![0, 0]]]) (
    Fin.cases (GenusOnePsi.graph) (
    Fin.cases (![tableGraph 1 ({ legVertex := ![0, 0, 0, 0], endpoint := Fin.elim0, genus := ![1]
      } :
    StableGraphCode.Candidate (Fin 4) 1 0) (by decide +kernel)
        ![![1, 0]] ![0, 0, 0, 0] Fin.elim0,
      tableGraph 1 ({ legVertex := ![0, 0, 0, 0], endpoint := Fin.elim0, genus := ![1] } :
        StableGraphCode.Candidate (Fin 4) 1 0) (by decide +kernel)
        ![![0, 0]] ![1, 0, 0, 0] Fin.elim0,
      tableGraph 1 ({ legVertex := ![0, 0, 0, 0], endpoint := Fin.elim0, genus := ![1] } :
        StableGraphCode.Candidate (Fin 4) 1 0) (by decide +kernel)
        ![![0, 0]] ![0, 1, 0, 0] Fin.elim0,
      tableGraph 1 ({ legVertex := ![0, 0, 0, 0], endpoint := Fin.elim0, genus := ![1] } :
        StableGraphCode.Candidate (Fin 4) 1 0) (by decide +kernel)
        ![![0, 0]] ![0, 0, 1, 0] Fin.elim0,
      tableGraph 1 ({ legVertex := ![0, 0, 0, 0], endpoint := Fin.elim0, genus := ![1] } :
        StableGraphCode.Candidate (Fin 4) 1 0) (by decide +kernel)
        ![![0, 0]] ![0, 0, 0, 1] Fin.elim0,
      tableGraph 1 ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]],
      tableGraph 1 ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]],
      tableGraph 1 ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]],
      tableGraph 1 ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]],
      tableGraph 1 ({ legVertex := ![0, 1, 1, 0], endpoint := ![![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]],
      tableGraph 1 ({ legVertex := ![0, 1, 0, 1], endpoint := ![![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]],
      tableGraph 1 ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]],
      tableGraph 1 ({ legVertex := ![0, 0, 1, 1], endpoint := ![![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]],
      tableGraph 1 ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]],
      tableGraph 1 ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]],
      tableGraph 1 ({ legVertex := ![0, 0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0, 0, 0] ![![0, 0]],
      tableGraph 1 ({ legVertex := ![0, 0, 0, 0], endpoint := ![![0, 0]], genus := ![0] } :
        StableGraphCode.Candidate (Fin 4) 1 1) (by decide +kernel)
        ![![0, 0]] ![0, 0, 0, 0] ![![0, 0]]]) (
    Fin.cases (![tableGraph 1 ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![1] } :
    StableGraphCode.Candidate (Fin 2) 1 0) (by decide +kernel)
        ![![1, 0]] ![0, 0] Fin.elim0,
      tableGraph 1 ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![1] } :
        StableGraphCode.Candidate (Fin 2) 1 0) (by decide +kernel)
        ![![0, 0]] ![1, 0] Fin.elim0,
      tableGraph 1 ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![1] } :
        StableGraphCode.Candidate (Fin 2) 1 0) (by decide +kernel)
        ![![0, 0]] ![0, 1] Fin.elim0,
      tableGraph 1 ({ legVertex := ![0, 0], endpoint := ![![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 2) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0] ![![0, 0]],
      tableGraph 1 ({ legVertex := ![0, 0], endpoint := ![![0, 0]], genus := ![0] } :
        StableGraphCode.Candidate (Fin 2) 1 1) (by decide +kernel)
        ![![0, 0]] ![0, 0] ![![0, 0]]]) (
    Fin.cases (![tableGraph 1 ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![1] } :
    StableGraphCode.Candidate (Fin 3) 1 0) (by decide +kernel)
        ![![1, 0]] ![0, 0, 0] Fin.elim0,
      tableGraph 1 ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![1] } :
        StableGraphCode.Candidate (Fin 3) 1 0) (by decide +kernel)
        ![![0, 0]] ![1, 0, 0] Fin.elim0,
      tableGraph 1 ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![1] } :
        StableGraphCode.Candidate (Fin 3) 1 0) (by decide +kernel)
        ![![0, 0]] ![0, 1, 0] Fin.elim0,
      tableGraph 1 ({ legVertex := ![0, 0, 0], endpoint := Fin.elim0, genus := ![1] } :
        StableGraphCode.Candidate (Fin 3) 1 0) (by decide +kernel)
        ![![0, 0]] ![0, 0, 1] Fin.elim0,
      tableGraph 1 ({ legVertex := ![1, 0, 0], endpoint := ![![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0]],
      tableGraph 1 ({ legVertex := ![0, 1, 0], endpoint := ![![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0]],
      tableGraph 1 ({ legVertex := ![0, 0, 1], endpoint := ![![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0]],
      tableGraph 1 ({ legVertex := ![0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 3) 2 1) (by decide +kernel)
        ![![0, 0], ![0, 0]] ![0, 0, 0] ![![0, 0]],
      tableGraph 1 ({ legVertex := ![0, 0, 0], endpoint := ![![0, 0]], genus := ![0] } :
        StableGraphCode.Candidate (Fin 3) 1 1) (by decide +kernel)
        ![![0, 0]] ![0, 0, 0] ![![0, 0]]]) (
    fun i ↦ Fin.elim0 i)))))))


/-- Component graphs retain their source arithmetic genus. -/
theorem sourceGraph_totalGenus (b : Fin 7) (i : Fin (sourceSize b)) :
    (sourceGraph b i).graph.totalGenus = sourceGenus b := by
  fin_cases b <;> fin_cases i <;> decide +kernel

/-- Component columns in the pre-existing decorated-graph quotient. -/
def sourceColumns (b : Fin 7) (i : Fin (sourceSize b)) :
    TautologicalStratum (sourceGenus b) (Fin (sourceArity b)) :=
  .mk (sourceGraph b i) (sourceGraph_totalGenus b i)

/-- All original component rows are in codimension one. -/
theorem sourceColumns_codimension (b : Fin 7) : ∀ i, (sourceColumns b i).codimension = 1 := by
  fin_cases b <;>
    simp only [sourceColumns, sourceGraph, tableGraph, GenusOnePsi.graph,
      DecoratedStableGraph.toDecoration_eq_mk] <;> decide +kernel

/-- The elliptic component frame is exactly the already verified frame. -/
theorem elliptic_source_columns : sourceColumns 3 = GenusOnePsi.columns := rfl

/-- Source family for the sixteen selected separating rows. -/
abbrev sourceFamily : Fin 16 → Fin 7 := ![0, 1, 1, 1, 2, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6]

/-- Original unsymmetrized 3-spin component rows, with no final recurrence supplied. -/
def sourceRow : (i : Fin 16) → Coordinates (sourceSize (sourceFamily i)) :=
  Fin.cases (![-15, 15, 15, -15, 21, 21, (3 / 2)]) (
    Fin.cases (![(-153 / 4), (45 / 4), (45 / 4), (45 / 4), (45 / 4), (-9 / 4), (-9 / 4), (-9 /
      4)]) (
    Fin.cases (![(-33 / 2), (-21 / 2), (15 / 2), (15 / 2), (15 / 2), (3 / 2), (3 / 2), (3 / 2)]) (
    Fin.cases (![(-33 / 2), (15 / 2), (15 / 2), (15 / 2), (-21 / 2), (3 / 2), (3 / 2), (3 / 2)]) (
    Fin.cases (![-30, 30, 42, 3]) (
    Fin.cases (GenusOnePsi.rows 0) (
    Fin.cases (GenusOnePsi.rows 1) (
    Fin.cases (![24, -15, -15, -15, -15, 6, 6, 6, -3, 6, 6, -3, 6, -3, -3, -12, (-3 / 2)]) (
    Fin.cases (![(15 / 4), (21 / 4), (-15 / 4), (-15 / 4), (-15 / 4), (15 / 4), (15 / 4), (15 /
      4), (15
    / 4), (-21 / 4), (-21 / 4), (-21 / 4), (-21 / 4), (-21 / 4), (-21 / 4), (-21 / 4), (-3 / 8)]) (
    Fin.cases (![(15 / 4), (-15 / 4), (-15 / 4), (-15 / 4), (21 / 4), (-21 / 4), (-21 / 4), (15 /
      4),
    (-21 / 4), (-21 / 4), (15 / 4), (-21 / 4), (15 / 4), (-21 / 4), (15 / 4), (-21 / 4), (-3 /
      8)]) (
    Fin.cases (![66, -30, -30, -6, -3]) (
    Fin.cases (![15, 21, -15, -21, (-3 / 2)]) (
    Fin.cases (![15, -15, 21, -21, (-3 / 2)]) (
    Fin.cases (![(81 / 2), (-45 / 2), (-45 / 2), (-45 / 2), (9 / 2), (9 / 2), (9 / 2), (-27 / 2),
      (-9 /
    4)]) (
    Fin.cases (![(15 / 2), (21 / 2), (-15 / 2), (-15 / 2), (15 / 2), (-21 / 2), (-21 / 2), (-21 /
      2),
    (-3 / 4)]) (
    Fin.cases (![(15 / 2), (-15 / 2), (-15 / 2), (21 / 2), (-21 / 2), (-21 / 2), (15 / 2), (-21 /
      2),
    (-3 / 4)]) (
    fun i ↦ Fin.elim0 i))))))))))))))))


/-- Each original row has the actual component stratum meaning. -/
noncomputable def sourceExpression (i : Fin 16) :
    StrataModule (sourceGenus (sourceFamily i)) (Fin (sourceArity (sourceFamily i))) :=
  interpret (sourceColumns (sourceFamily i)) (sourceRow i)

/-- Source-to-target slots, proved below from elementary graph operations. -/
def sourceDestinations : (b : Fin 7) → Fin (sourceSize b) → Fin 100 :=
  Fin.cases (![11, 12, 13, 27, 56, 57, 80]) (
    Fin.cases (![20, 22, 23, 24, 25, 29, 28, 27]) (
    Fin.cases (![21, 26, 62, 83]) (
    Fin.cases (![73, 74, 91]) (
    Fin.cases (![30, 31, 32, 33, 34, 63, 64, 56, 65, 66, 58, 67, 60, 68, 62, 69, 98]) (
    Fin.cases (![35, 37, 38, 63, 92]) (
    Fin.cases (![36, 39, 40, 41, 70, 71, 61, 68, 97]) (
    fun i ↦ Fin.elim0 i)))))))


/-- Raw attachment to a fixed stable component, with the source branch selected explicitly. -/
noncomputable def attach {g h m n : ℕ} (i : Fin (m + 1))
    (hh : StableArity h (Option (Fin n))) :
    StrataModule g (Fin (m + 1)) →ₗ[ℚ] StrataModule (g + h) (Fin (m + n)) :=
  (StrataModule.relabel finSumFinEquiv).comp
    ((StrataModule.separating.flip (StrataModule.basis
      (TautologicalStratum.fundamental h (Option (Fin n)) hh))).comp
        (StrataModule.relabel (finSuccEquiv' i)))

/-- The attachment's graph map is the same actual gluing on every basis vector. -/
theorem attach_basis {g h m n : ℕ} (i : Fin (m + 1))
    (hh : StableArity h (Option (Fin n))) (x : TautologicalStratum g (Fin (m + 1))) :
    attach i hh (StrataModule.basis x) = StrataModule.basis
      (((x.relabel (finSuccEquiv' i)).separating
        (TautologicalStratum.fundamental h (Option (Fin n)) hh)).relabel finSumFinEquiv) := by
  simp only [attach, LinearMap.comp_apply, LinearMap.flip_apply,
    StrataModule.relabel_basis, StrataModule.separating_basis_basis]

/-- Seven concrete attachment maps; source family 5 restores the external order 0,1,2. -/
noncomputable def sourceMap : (b : Fin 7) →
    StrataModule (sourceGenus b) (Fin (sourceArity b)) →ₗ[ℚ] StrataModule 2 (Fin 3) :=
  Fin.cases (attach (g := 2) (h := 0) (m := 1) (n := 2) 1 (by norm_num [StableArity])) (
    Fin.cases (attach (g := 0) (h := 2) (m := 3) (n := 0) 3 (by norm_num [StableArity])) (
    Fin.cases (attach (g := 2) (h := 0) (m := 0) (n := 3) 0 (by norm_num [StableArity])) (
    Fin.cases (attach (g := 1) (h := 1) (m := 0) (n := 3) 0 (by norm_num [StableArity])) (
    Fin.cases (attach (g := 1) (h := 1) (m := 3) (n := 0) 3 (by norm_num [StableArity])) (
    Fin.cases ((StrataModule.relabel (labelPermutation 3)).comp (attach (g := 1) (h := 1) (m := 1)
      (n
    := 2) 1 (by norm_num [StableArity]))) (
    Fin.cases (attach (g := 1) (h := 1) (m := 2) (n := 1) 2 (by norm_num [StableArity])) (
    fun i ↦ Fin.elim0 i)))))))


/-- The same seven attachments on graph classes, before linear extension. -/
noncomputable def sourceImage : (b : Fin 7) →
    TautologicalStratum (sourceGenus b) (Fin (sourceArity b)) → TautologicalStratum 2 (Fin 3) :=
  Fin.cases (fun x ↦ (((x.relabel (finSuccEquiv' (1 : Fin 2))).separating
      (TautologicalStratum.fundamental 0 (Option (Fin 2)) (by norm_num [StableArity]))).relabel
        finSumFinEquiv)) (
    Fin.cases (fun x ↦ (((x.relabel (finSuccEquiv' (3 : Fin 4))).separating
      (TautologicalStratum.fundamental 2 (Option (Fin 0)) (by norm_num [StableArity]))).relabel
        finSumFinEquiv)) (
    Fin.cases (fun x ↦ (((x.relabel (finSuccEquiv' (0 : Fin 1))).separating
      (TautologicalStratum.fundamental 0 (Option (Fin 3)) (by norm_num [StableArity]))).relabel
        finSumFinEquiv)) (
    Fin.cases (fun x ↦ (((x.relabel (finSuccEquiv' (0 : Fin 1))).separating
      (TautologicalStratum.fundamental 1 (Option (Fin 3)) (by norm_num [StableArity]))).relabel
        finSumFinEquiv)) (
    Fin.cases (fun x ↦ (((x.relabel (finSuccEquiv' (3 : Fin 4))).separating
      (TautologicalStratum.fundamental 1 (Option (Fin 0)) (by norm_num [StableArity]))).relabel
        finSumFinEquiv)) (
    Fin.cases (fun x ↦ (((x.relabel (finSuccEquiv' (1 : Fin 2))).separating
      (TautologicalStratum.fundamental 1 (Option (Fin 2)) (by norm_num [StableArity]))).relabel
        finSumFinEquiv).relabel (labelPermutation 3)) (
    Fin.cases (fun x ↦ (((x.relabel (finSuccEquiv' (2 : Fin 3))).separating
      (TautologicalStratum.fundamental 1 (Option (Fin 1)) (by norm_num [StableArity]))).relabel
        finSumFinEquiv)) (
    fun i ↦ Fin.elim0 i)))))))

/-- The linear maps are exactly the specified graph operations on basis strata. -/
theorem sourceMap_basis (b : Fin 7) (x : TautologicalStratum (sourceGenus b)
    (Fin (sourceArity b))) : sourceMap b (StrataModule.basis x) =
      StrataModule.basis (sourceImage b x) := by
  fin_cases b
  · exact attach_basis (g := 2) (h := 0) (m := 1) (n := 2) 1 _ x
  · exact attach_basis (g := 0) (h := 2) (m := 3) (n := 0) 3 _ x
  · exact attach_basis (g := 2) (h := 0) (m := 0) (n := 3) 0 _ x
  · exact attach_basis (g := 1) (h := 1) (m := 0) (n := 3) 0 _ x
  · exact attach_basis (g := 1) (h := 1) (m := 3) (n := 0) 3 _ x
  · change StrataModule.relabel (labelPermutation 3) (attach (g := 1) (h := 1)
      (m := 1) (n := 2) 1 _ (StrataModule.basis x)) = _
    rw [attach_basis, StrataModule.relabel_basis]
    rfl
  · exact attach_basis (g := 1) (h := 1) (m := 2) (n := 1) 2 _ x

/-- Every destination is checked by decorated-graph isomorphism with its actual source image. -/
theorem sourceImage_columns : ∀ b i,
    sourceImage b (sourceColumns b i) = columns (sourceDestinations b i) := by
  simp only [sourceImage, sourceColumns, sourceGraph, columns, graph, tableGraph,
    GenusOnePsi.graph, DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Every destination is a checked decorated gluing, not a numerical column assertion. -/
theorem sourceMap_columns (b : Fin 7) (i : Fin (sourceSize b)) :
    sourceMap b (StrataModule.basis (sourceColumns b i)) =
      StrataModule.basis (columns (sourceDestinations b i)) := by
  rw [sourceMap_basis, sourceImage_columns]

/-- A complete component row is sent to its formal target coordinate combination. -/
theorem sourceMap_interpret (b : Fin 7) (r : Coordinates (sourceSize b)) :
    sourceMap b (interpret (sourceColumns b) r) =
      interpret columns (combination (fun i ↦ Pi.single (sourceDestinations b i) 1) ⟨r⟩) := by
  rw [interpret_combination]
  simp only [interpret, Fintype.linearCombination_apply_single, one_smul]
  change sourceMap b (∑ i, r i • StrataModule.basis (sourceColumns b i)) = _
  simp only [map_sum, map_smul, sourceMap_columns]

universe u
attribute [local instance] strataRealizationModule

/-- Exactly the three primitive realization laws used by an attachment. -/
def AttachCompatible {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S) (F : SeparatingPushforward C I)
    {g h m n : ℕ} (i : Fin (m + 1)) (hg : StableArity g (Fin (m + 1)))
    (hh : StableArity h (Option (Fin n))) : Prop :=
  let hl := (StableArity.equiv (finSuccEquiv' i)).mp hg
  let hs := StableArity.separating hl hh
  (Z g (Fin (m + 1))).RelabelCompatible (Z g (Option (Fin m))) hg hl (finSuccEquiv' i) ∧
  (Z g (Option (Fin m))).SeparatingCompatible (Z h (Option (Fin n)))
    (Z (g + h) (Fin m ⊕ Fin n)) F hl hh ∧
  (Z (g + h) (Fin m ⊕ Fin n)).RelabelCompatible (Z (g + h) (Fin (m + n))) hs
    ((StableArity.equiv finSumFinEquiv).mp hs) finSumFinEquiv

/-- Source-row vanishing is preserved by the primitive attachment laws. -/
theorem attach_vanishes {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S) (F : SeparatingPushforward C I)
    {g h m n : ℕ} (i : Fin (m + 1)) (hg : StableArity g (Fin (m + 1)))
    (hh : StableArity h (Option (Fin n))) (hc : AttachCompatible Z F i hg hh)
    (r : StrataModule g (Fin (m + 1))) (hr : (Z g (Fin (m + 1))).map r = 0) :
    (Z (g + h) (Fin (m + n))).map (attach i hh r) = 0 := by
  rcases hc with ⟨hl, hs, ht⟩
  simp only [attach, LinearMap.comp_apply, LinearMap.flip_apply]
  rw [StrataRealization.map_relabel _ _ _ _ _ ht,
    StrataRealization.map_separating _ _ _ F _ _ hs,
    StrataRealization.map_relabel _ _ _ _ _ hl, hr, map_zero,
    TensorProduct.zero_tmul, map_zero, map_zero]

/-- The seven specifically used primitive attachment compatibilities. -/
def SourceMapCompatible {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S) (F : SeparatingPushforward C I) :
    Fin 7 → Prop :=
  Fin.cases (AttachCompatible Z F (g := 2) (h := 0) (m := 1) (n := 2) 1
      (sourceStable 0) (by norm_num [StableArity])) (
    Fin.cases (AttachCompatible Z F (g := 0) (h := 2) (m := 3) (n := 0) 3
      (sourceStable 1) (by norm_num [StableArity])) (
    Fin.cases (AttachCompatible Z F (g := 2) (h := 0) (m := 0) (n := 3) 0
      (sourceStable 2) (by norm_num [StableArity])) (
    Fin.cases (AttachCompatible Z F (g := 1) (h := 1) (m := 0) (n := 3) 0
      (sourceStable 3) (by norm_num [StableArity])) (
    Fin.cases (AttachCompatible Z F (g := 1) (h := 1) (m := 3) (n := 0) 3
      (sourceStable 4) (by norm_num [StableArity])) (
    Fin.cases (AttachCompatible Z F (g := 1) (h := 1) (m := 1) (n := 2) 1
      (sourceStable 5) (by norm_num [StableArity])) (
    Fin.cases (AttachCompatible Z F (g := 1) (h := 1) (m := 2) (n := 1) 2
      (sourceStable 6) (by norm_num [StableArity])) (
    fun i ↦ Fin.elim0 i)))))))


/-- Glued original rows vanish from their source vanishing, not from an assumed BP equation. -/
theorem sourceMap_vanishes {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S) (F : SeparatingPushforward C I)
    (hc : ∀ b, SourceMapCompatible Z F b)
    (hl : ∀ p, (Z 2 (Fin 3)).RelabelCompatible (Z 2 (Fin 3))
      stableArity stableArity (labelPermutation p))
    (b : Fin 7) (r : StrataModule (sourceGenus b) (Fin (sourceArity b)))
    (hr : (Z (sourceGenus b) (Fin (sourceArity b))).map r = 0) :
    (Z 2 (Fin 3)).map (sourceMap b r) = 0 := by
  fin_cases b
  · exact attach_vanishes Z F 1 (sourceStable 0) _ (hc 0) r hr
  · exact attach_vanishes Z F 3 (sourceStable 1) _ (hc 1) r hr
  · exact attach_vanishes Z F 0 (sourceStable 2) _ (hc 2) r hr
  · exact attach_vanishes Z F 0 (sourceStable 3) _ (hc 3) r hr
  · exact attach_vanishes Z F 3 (sourceStable 4) _ (hc 4) r hr
  · change (Z 2 (Fin 3)).map (StrataModule.relabel (labelPermutation 3)
      (attach (g := 1) (h := 1) (m := 1) (n := 2) 1 _ r)) = 0
    have he : (Z 2 (Fin 3)).map (attach (g := 1) (h := 1) (m := 1) (n := 2) 1 _ r) = 0 :=
      attach_vanishes Z F 1 (sourceStable 5) _ (hc 5) r hr
    rw [StrataRealization.map_relabel _ _ _ _ _ (hl 3), he, map_zero]
  · exact attach_vanishes Z F 2 (sourceStable 6) _ (hc 6) r hr

end AxiomaticGW.BelorousskiPandharipande

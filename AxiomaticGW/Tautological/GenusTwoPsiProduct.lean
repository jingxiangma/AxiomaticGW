/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.BelorousskiPandharipandeSources

/-!
# A complete two-marked genus-two cotangent-product relation

Ten original 3-spin rows on Mbar(2,2), and three actual separating images
of previously held component rows, express psi_1 psi_2 as a kappa-free
boundary. The sole genus-two term is three times the rational tail with
both external markings and psi on its genus-two attaching branch.
It lowers component arity, not genus; the other 24 terms have genus at most one.

This is an independently held claim. Incoming graphs, normalization, rows,
coordinate conversions and the complete requested expression are checked.
Source-row geometric validity remains explicit. No invariant value, full
L24 relation, or uniform reconstruction algorithm is assumed or claimed.
-/

@[expose] public section

namespace AxiomaticGW.GenusTwoPsiProduct
open RelationCertificate
universe u

/-- The two-marked genus-two curve is stable. -/
theorem stableArity : StableArity 2 (Fin 2) := by norm_num [StableArity]

/-- Held raw monomial columns, including all original branch decorations. -/
def graph : Fin 38 → DecoratedStableGraph (Fin 2) :=
  ![BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
      StableGraphCode.Candidate (Fin 2) 1 0) (by decide +kernel)
    ![![0, 1]] ![0, 0] Fin.elim0,
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
      StableGraphCode.Candidate (Fin 2) 1 0) (by decide +kernel)
    ![![2, 0]] ![0, 0] Fin.elim0,
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
      StableGraphCode.Candidate (Fin 2) 1 0) (by decide +kernel)
    ![![1, 0]] ![1, 0] Fin.elim0,
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
      StableGraphCode.Candidate (Fin 2) 1 0) (by decide +kernel)
    ![![1, 0]] ![0, 1] Fin.elim0,
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
      StableGraphCode.Candidate (Fin 2) 1 0) (by decide +kernel)
    ![![0, 0]] ![2, 0] Fin.elim0,
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
      StableGraphCode.Candidate (Fin 2) 1 0) (by decide +kernel)
    ![![0, 0]] ![1, 1] Fin.elim0,
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![0, 0], endpoint := Fin.elim0, genus := ![2] } :
      StableGraphCode.Candidate (Fin 2) 1 0) (by decide +kernel)
    ![![0, 0]] ![0, 2] Fin.elim0,
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
      StableGraphCode.Candidate (Fin 2) 2 1) (by decide +kernel)
    ![![0, 0], ![1, 0]] ![0, 0] ![![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
      StableGraphCode.Candidate (Fin 2) 2 1) (by decide +kernel)
    ![![0, 0], ![0, 0]] ![0, 0] ![![0, 1]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![1, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 2) 2 1) (by decide +kernel)
    ![![0, 0], ![1, 0]] ![0, 0] ![![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![1, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 2) 2 1) (by decide +kernel)
    ![![0, 0], ![0, 0]] ![1, 0] ![![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![1, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 2) 2 1) (by decide +kernel)
    ![![0, 0], ![0, 0]] ![0, 1] ![![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![1, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 2) 2 1) (by decide +kernel)
    ![![0, 0], ![0, 0]] ![0, 0] ![![0, 1]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![1, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 2) 2 1) (by decide +kernel)
    ![![1, 0], ![0, 0]] ![0, 0] ![![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![1, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 2) 2 1) (by decide +kernel)
    ![![0, 0], ![1, 0]] ![0, 0] ![![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![1, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 2) 2 1) (by decide +kernel)
    ![![0, 0], ![0, 0]] ![0, 1] ![![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![1, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 2) 2 1) (by decide +kernel)
    ![![0, 0], ![0, 0]] ![0, 0] ![![1, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![1, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 2) 2 1) (by decide +kernel)
    ![![0, 0], ![0, 0]] ![1, 0] ![![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![1, 0], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 2) 2 1) (by decide +kernel)
    ![![0, 0], ![0, 0]] ![0, 0] ![![0, 1]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
      StableGraphCode.Candidate (Fin 2) 3 2) (by decide +kernel)
    ![![0, 0], ![0, 0], ![0, 0]] ![0, 0] ![![0, 0], ![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
      StableGraphCode.Candidate (Fin 2) 3 2) (by decide +kernel)
    ![![0, 0], ![0, 0], ![0, 0]] ![0, 0] ![![0, 0], ![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
      StableGraphCode.Candidate (Fin 2) 3 2) (by decide +kernel)
    ![![0, 0], ![0, 0], ![0, 0]] ![0, 0] ![![0, 0], ![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
      StableGraphCode.Candidate (Fin 2) 3 2) (by decide +kernel)
    ![![0, 0], ![0, 0], ![0, 0]] ![0, 0] ![![0, 0], ![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![1, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 2) 2 1) (by decide +kernel)
    ![![1, 0], ![0, 0]] ![0, 0] ![![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![1, 1], endpoint := ![![0, 1]], genus := ![1, 1] } :
      StableGraphCode.Candidate (Fin 2) 2 1) (by decide +kernel)
    ![![0, 0], ![0, 0]] ![0, 0] ![![1, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![0, 0], endpoint := ![![0, 0]], genus := ![1] } :
      StableGraphCode.Candidate (Fin 2) 1 1) (by decide +kernel)
    ![![1, 0]] ![0, 0] ![![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![0, 0], endpoint := ![![0, 0]], genus := ![1] } :
      StableGraphCode.Candidate (Fin 2) 1 1) (by decide +kernel)
    ![![0, 0]] ![0, 0] ![![1, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![0, 0], endpoint := ![![0, 0]], genus := ![1] } :
      StableGraphCode.Candidate (Fin 2) 1 1) (by decide +kernel)
    ![![0, 0]] ![1, 0] ![![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![0, 0], endpoint := ![![0, 0]], genus := ![1] } :
      StableGraphCode.Candidate (Fin 2) 1 1) (by decide +kernel)
    ![![0, 0]] ![0, 1] ![![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 2) 2 2) (by decide +kernel)
    ![![0, 0], ![0, 0]] ![0, 0] ![![0, 0], ![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![1, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 2) 2 2) (by decide +kernel)
    ![![0, 0], ![0, 0]] ![0, 0] ![![0, 0], ![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![0, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 2) 2 2) (by decide +kernel)
    ![![0, 0], ![0, 0]] ![0, 0] ![![0, 0], ![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![0, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 2) 2 2) (by decide +kernel)
    ![![0, 0], ![0, 0]] ![0, 0] ![![0, 0], ![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 2) 2 2) (by decide +kernel)
    ![![0, 0], ![0, 0]] ![0, 0] ![![0, 0], ![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![1, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 2) 2 2) (by decide +kernel)
    ![![0, 0], ![0, 0]] ![0, 0] ![![0, 0], ![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![0, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 2) 2 2) (by decide +kernel)
    ![![0, 0], ![0, 0]] ![0, 0] ![![0, 0], ![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![0, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
      StableGraphCode.Candidate (Fin 2) 2 2) (by decide +kernel)
    ![![0, 0], ![0, 0]] ![0, 0] ![![0, 0], ![0, 0]],
    BelorousskiPandharipande.tableGraph 2
    ({ legVertex := ![0, 0], endpoint := ![![0, 0], ![0, 0]], genus := ![0] } :
      StableGraphCode.Candidate (Fin 2) 1 2) (by decide +kernel)
    ![![0, 0]] ![0, 0] ![![0, 0], ![0, 0]]]

/-- Each held graph has the required arithmetic genus. -/
theorem graph_totalGenus (i : Fin 38) : (graph i).graph.totalGenus = 2 := by
  fin_cases i <;> decide +kernel

/-- The existing decorated-stratum quotient supplies semantic columns. -/
def columns (i : Fin 38) : TautologicalStratum 2 (Fin 2) :=
  .mk (graph i) (graph_totalGenus i)

/-- Every column has codimension two. -/
theorem columns_codimension : ∀ i, (columns i).codimension = 2 := by
  simp only [columns, graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- No two held columns identify different requests in the free strata module. -/
theorem columns_injective : Function.Injective columns := by
  simp only [Function.Injective, columns, graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The leading column is the product of the two external cotangent classes. -/
theorem psi_product_column : columns 5 =
    (TautologicalStratum.fundamental 2 (Fin 2) stableArity).addLegPsi (fun _ ↦ 1) := by
  apply Quotient.sound
  apply (DecoratedStableGraph.isomorphic?_eq_true_iff _ _).mp
  simp only [graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Decorated automorphisms; these do not rescale raw columns. -/
def automorphismOrders : Fin 38 → ℕ :=
  ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 8]

/-- Ten original genus-two rows and three separating images. -/
def rows : Fin 13 → Coordinates 38 :=
  ![![0, -15, 15, 15, 0, 0, 0, -15, 0, 21, 0, 0, 0, 21, 21, 0, 0, 0, 0, 0, 0, 0, 0, 21, 0, (3 /
    2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![308448, -56952, 50400, 50400, -138600, -18000, -138600, -14544, 32760, 34704, -10080,
      -10080, -57960, 17856, 17856, -3600, -12600, -3600, -12600, -720, 5760, 5760, -1656, 11376,
      32760, 5040, -12600, -1800, -1800, 288, 3528, 3528, -360, 288, -360, -360, -1008, -90],
    ![127008, -17892, -27720, 19800, 81900, 12600, -69300, 16056, -36540, 16056, 8568, -6120,
      -36540, -792, 8712, 360, 8820, 5544, -21420, -4680, 4392, -6840, -2340, 2232, 23940, 1980,
      -6300, 1260, -900, -612, 2412, -2772, -1476, 252, 36, -396, -612, -45],
    ![127008, -17892, 19800, -27720, -69300, 12600, 81900, 16056, -36540, 16056, -6120, 8568,
      -36540, 8712, -792, 5544, -21420, 360, 8820, -4680, -6840, 4392, -2340, 2232, 23940, 1980,
      -6300, -900, 1260, -612, -2772, 2412, -1476, 252, -396, 36, -612, -45],
    ![38880, -3960, -8064, -8064, 32760, -7056, 32760, -3600, 12600, 5904, 4032, 4032, -17640,
      -1440, -1440, 1008, -2520, 1008, -2520, -144, -3168, -3168, -504, 1584, 12600, 576, -2520,
      504, 504, 144, -1368, -1368, -72, 144, -72, -72, -288, -18],
    ![0, 0, -15, 0, 15, 15, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3 /
      2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -15, 0, 15, 15, 0, 0, 0, 0, 21, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3
      / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![38880, -3960, 5760, 5760, -27720, -3600, -27720, -3600, 12600, 5904, -2880, -2880, -17640,
      3744, 3744, -720, -2520, -720, -2520, -144, 2016, 2016, -504, 1584, 12600, 576, -2520, -360,
      -360, 144, 1224, 1224, -72, 144, -72, -72, -288, -18],
    ![6480, -450, -1260, 900, 8190, 1260, -6930, 1260, -8190, 1260, 1764, -1260, -8190, -900,
      1260, 900, 6930, 1764, -8190, -1764, 1260, -1764, -882, -900, 6930, 90, -630, 126, -90,
      -126, 630, -666, -666, 90, 90, -126, -126, (-9 / 2)],
    ![6480, -450, 900, -1260, -6930, 1260, 8190, 1260, -8190, 1260, -1260, 1764, -8190, 1260,
      -900, 1764, -8190, 900, 6930, -1764, -1764, 1260, -882, -900, 6930, 90, -630, -90, 126,
      -126, -666, 630, -666, 90, -126, 90, -126, (-9 / 2)],
    ![0, 0, 0, 0, 0, 0, 0, -30, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      3, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 102, -30, 0, 0, 0, 0,
      0, 0, 0, 0, -3, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, (81 / 2), (-45 / 2), (-45 / 2), (-45 / 2), 0, 0, 0, 0, 0, 0, (9 /
      2), (9 / 2), (9 / 2), (-27 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-9 / 4), 0]]

/-- The same original rows in kappa-pushforward coordinates. -/
def pushforwardRows : Fin 13 → Coordinates 38 :=
  ![![15, -15, 15, 15, 0, 0, 0, -15, 0, 21, 0, 0, 0, 21, 21, 0, 0, 0, 0, 0, 0, 0, 0, 21, 0, (3 /
    2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![365400, -56952, 50400, 50400, -138600, -18000, -138600, -14544, 32760, 34704, -10080,
      -10080, -57960, 17856, 17856, -3600, -12600, -3600, -12600, -720, 5760, 5760, -1656, 11376,
      32760, 5040, -12600, -1800, -1800, 288, 3528, 3528, -360, 288, -360, -360, -1008, -90],
    ![144900, -17892, -27720, 19800, 81900, 12600, -69300, 16056, -36540, 16056, 8568, -6120,
      -36540, -792, 8712, 360, 8820, 5544, -21420, -4680, 4392, -6840, -2340, 2232, 23940, 1980,
      -6300, 1260, -900, -612, 2412, -2772, -1476, 252, 36, -396, -612, -45],
    ![144900, -17892, 19800, -27720, -69300, 12600, 81900, 16056, -36540, 16056, -6120, 8568,
      -36540, 8712, -792, 5544, -21420, 360, 8820, -4680, -6840, 4392, -2340, 2232, 23940, 1980,
      -6300, -900, 1260, -612, -2772, 2412, -1476, 252, -396, 36, -612, -45],
    ![42840, -3960, -8064, -8064, 32760, -7056, 32760, -3600, 12600, 5904, 4032, 4032, -17640,
      -1440, -1440, 1008, -2520, 1008, -2520, -144, -3168, -3168, -504, 1584, 12600, 576, -2520,
      504, 504, 144, -1368, -1368, -72, 144, -72, -72, -288, -18],
    ![0, 0, -15, 0, 15, 15, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3 /
      2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -15, 0, 15, 15, 0, 0, 0, 0, 21, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3
      / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![42840, -3960, 5760, 5760, -27720, -3600, -27720, -3600, 12600, 5904, -2880, -2880, -17640,
      3744, 3744, -720, -2520, -720, -2520, -144, 2016, 2016, -504, 1584, 12600, 576, -2520, -360,
      -360, 144, 1224, 1224, -72, 144, -72, -72, -288, -18],
    ![6930, -450, -1260, 900, 8190, 1260, -6930, 1260, -8190, 1260, 1764, -1260, -8190, -900,
      1260, 900, 6930, 1764, -8190, -1764, 1260, -1764, -882, -900, 6930, 90, -630, 126, -90,
      -126, 630, -666, -666, 90, 90, -126, -126, (-9 / 2)],
    ![6930, -450, 900, -1260, -6930, 1260, 8190, 1260, -8190, 1260, -1260, 1764, -8190, 1260,
      -900, 1764, -8190, 900, 6930, -1764, -1764, 1260, -882, -900, 6930, 90, -630, -90, 126,
      -126, -666, 630, -666, 90, -126, 90, -126, (-9 / 2)],
    ![0, 0, 0, 0, 0, 0, 0, -30, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      3, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 102, -30, 0, 0, 0, 0,
      0, 0, 0, 0, -3, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, (81 / 2), (-45 / 2), (-45 / 2), (-45 / 2), 0, 0, 0, 0, 0, 0, (9 /
      2), (9 / 2), (9 / 2), (-27 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-9 / 4), 0]]

/-- The complete independently held relation, including its remainder. -/
def requested : Coordinates 38 :=
  ![0, 0, 0, 0, 0, 1, 0, 0, -3, 0, (161 / 90), (161 / 90), (-40 / 9), 0, 0, (407 / 180), (-7 /
    36), (407 / 180), (-7 / 36), (-25 / 9), (-19 / 90), (-19 / 90), (-13 / 30), 0, (206 / 51), 0,
    (-7 / 36), (67 / 720), (67 / 720), (-11 / 72), (-1 / 40), (-1 / 40), (-37 / 90), (473 /
    12240), (-1 / 180), (-1 / 180), (-37 / 720), (-1 / 720)]

/-- All 25 signed terms on the boundary side. -/
def boundary (i : Fin 38) : ℚ :=
  (#[0, 0, 0, 0, 0, 0, 0, 0, 3, 0, (-161 / 90), (-161 / 90), (40 / 9), 0, 0, (-407 / 180), (7 /
    36), (-407 / 180), (7 / 36), (25 / 9), (19 / 90), (19 / 90), (13 / 30), 0, (-206 / 51), 0, (7
    / 36), (-67 / 720), (-67 / 720), (11 / 72), (1 / 40), (1 / 40), (37 / 90), (-473 / 12240), (1
    / 180), (1 / 180), (37 / 720), (1 / 720)] : Array ℚ)[i.val]

/-- Orders are checked by the decorated graph-isomorphism enumerator. -/
theorem automorphismOrders_correct : ∀ i, (graph i).automorphismCount = automorphismOrders i := by
  simp only [graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The source conversion retains the kappa_2 correction to kappa_1 squared. -/
def pushforwardToMonomial (i : Fin 38) : Coordinates 38 :=
  Pi.single i 1 + if i = 1 then Pi.single 0 1 else 0

/-- The inverse uses the same slot and the opposite correction. -/
def monomialToPushforward (i : Fin 38) : Coordinates 38 :=
  Pi.single i 1 - if i = 1 then Pi.single 0 1 else 0

/-- Every row retains its original source-coordinate meaning. -/
theorem rows_conversion : ∀ i,
    combination pushforwardToMonomial ⟨pushforwardRows i⟩ = rows i := by decide +kernel

/-- Both conversion tables are inverses on the standard coordinate basis. -/
theorem conversion_inverse_basis : ∀ i,
    combination monomialToPushforward ⟨pushforwardToMonomial i⟩ = Pi.single i 1 ∧
    combination pushforwardToMonomial ⟨monomialToPushforward i⟩ = Pi.single i 1 := by
  intro i
  constructor <;> rw [← linearCombination_eq_combination] <;> by_cases h : i = 1
  · subst i
    norm_num [pushforwardToMonomial, monomialToPushforward, map_add, map_sub,
      Fintype.linearCombination_apply_single]
  · simp only [pushforwardToMonomial, monomialToPushforward, if_neg h, add_zero, sub_zero,
      Fintype.linearCombination_apply_single, one_smul]
  · subst i
    norm_num [pushforwardToMonomial, monomialToPushforward, map_add, map_sub,
      Fintype.linearCombination_apply_single]
  · simp only [pushforwardToMonomial, monomialToPushforward, if_neg h, add_zero, sub_zero,
      Fintype.linearCombination_apply_single, one_smul]

/-- Rational weights for the thirteen independently held source rows. -/
def certificate : Certificate 13 :=
  ⟨![(7 / 3240), (7 / 248832), (-43 / 746496), (-43 / 746496), (41 / 746496), (91 / 1296), (91 /
    1296), (-83 / 1866240), (799 / 1866240), (799 / 1866240), (-1 / 24), (31 / 4896), (-5 / 648)]⟩

/-- The entire coordinate equality is checked by Lean's kernel. -/
theorem checked : check rows requested certificate = true := by decide +kernel

/-- The held expression isolates the actual cotangent product. -/
theorem requested_eq : requested = Pi.single 5 1 - boundary := by decide +kernel

/-- No kappa terms remain; the unique genus-two vertex has one incident flag. -/
theorem boundary_reduces : ∀ i, boundary i ≠ 0 →
    0 < (graph i).graph.edgeCount ∧ (graph i).kappaCodimension = 0 ∧
    (graph i).legPsiCodimension + (graph i).halfEdgePsiCodimension ≤ 1 ∧
    (i = 8 ∨ ∀ v, (graph i).graph.genus v < 2) := by
  simp only [graph, BelorousskiPandharipande.tableGraph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- This formal combination is product minus the complete boundary. -/
theorem interpret_request : interpret columns requested =
    StrataModule.basis (columns 5) - interpret columns boundary := by
  rw [requested_eq, map_sub, interpret, Fintype.linearCombination_apply_single, one_smul]

/-- The relation is nonzero before any geometric relation is imposed. -/
theorem requested_ne_zero : interpret columns requested ≠ 0 := by
  intro h
  have hi := congrArg (fun r ↦ r (columns 5)) h
  rw [interpret_apply_column columns columns_injective] at hi
  exact (one_ne_zero : (1 : ℚ) ≠ 0) hi

/-- Exact incoming mathematical data, with no substituted requested expression. -/
structure Exchange where
  /-- Graphs, normalization, rows, request and candidate weights. -/
  presentation : Presentation 2 (Fin 2) 13 38
  /-- Original kappa-pushforward rows. -/
  sourceRows : Fin 13 → Coordinates 38
  /-- Forward monomial conversion. -/
  sourceToMonomial : Fin 38 → Coordinates 38
  /-- Inverse coordinate conversion. -/
  monomialToSource : Fin 38 → Coordinates 38
  /-- Complete claimed boundary. -/
  claimedBoundary : Coordinates 38
  /-- Decorated automorphism orders. -/
  automorphisms : Fin 38 → ℕ

/-- Every incoming field is bound to the independently held mathematical claim. -/
def AcceptsExchange (p : Exchange) : Prop :=
  RelationCertificate.AcceptsPresentation columns rows requested p.presentation ∧
  p.sourceRows = pushforwardRows ∧ p.sourceToMonomial = pushforwardToMonomial ∧
  p.monomialToSource = monomialToPushforward ∧ p.claimedBoundary = boundary ∧
  ∀ i, p.automorphisms i = (graph i).automorphismCount

/-- Replay transfers only explicit source vanishing to the complete equation. -/
theorem evaluated_relation {V : Type*} [AddCommGroup V] [Module ℚ V]
    (p : Exchange) (hp : AcceptsExchange p) (ev : StrataModule 2 (Fin 2) →ₗ[ℚ] V)
    (hrows : ∀ i, ev (interpret columns (rows i)) = 0) :
    ev (StrataModule.basis (columns 5)) = ev (interpret columns boundary) := by
  have he := evaluation_eq_zero columns rows requested p.presentation.certificate
    ((check_eq_true_iff _ _ _).mpr hp.1.2) ev hrows
  rw [interpret_request, map_sub, sub_eq_zero] at he
  exact he

end AxiomaticGW.GenusTwoPsiProduct

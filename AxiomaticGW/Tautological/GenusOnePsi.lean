/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GluingExpression
public import AxiomaticGW.Tautological.GraphEnumeration
public import AxiomaticGW.Tautological.LegPsiRealization
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

/-!
# A held genus-one cotangent relation

The raw Mbar(1,1) columns are kappa_1, psi_1 and the nonseparating pushforward
of the genus-zero three-point fundamental class. The latter has two branch
automorphisms; its coefficient is 1/24, not the 1/12 coefficient of the
normalized boundary divisor. The source is Getzler, arXiv:math/9801003,
Section 4, equation (10).

The two fixed full-stable 3-spin rows come from admcycles 1.4 with parameters
(sigma=(1), a_1=0) and (sigma=(), a_1=1), following arXiv:1303.1043. Incoming
graphs, rows, normalization and the requested psi relation must agree with
this independent frame. Arithmetic and graph proofs do not prove geometric
row vanishing; that remains an explicit class-level hypothesis. No numerical
GW recurrence is assumed.
-/

@[expose] public section

namespace AxiomaticGW.GenusOnePsi
open RelationCertificate

/-- The one-point genus-one curve arity is stable. -/
theorem stableArity : StableArity 1 (Fin 1) := by norm_num [StableArity]

/-- Raw self-gluing with both ordered node flags present. -/
def loopExpression : GluingExpression 1 (Fin 1) :=
  (GluingExpression.fundamental 0 (Option (Option (Fin 1)))
    (by norm_num [StableArity])).nonseparating

/-- One elliptic vertex with one external marking and no edges. -/
def ellipticCandidate : StableGraphCode.Candidate (Fin 1) 1 0 where
  legVertex := ![0]
  endpoint := Fin.elim0
  genus := ![1]

/-- The finite candidate has the prescribed stable genus. -/
theorem ellipticValid : ellipticCandidate.Valid 1 := by decide +kernel

/-- Independent kappa_1 and external psi exponents on the elliptic vertex. -/
def ellipticExponents (k p : ℕ) : DecoratedStableGraph.DecorationIndex (Fin 1) 1 0 1 → ℕ
  | .inl _ => k
  | .inr (.inl _) => p
  | .inr (.inr (e, _)) => Fin.elim0 e

/-- The three raw decorated graph representatives, with fixed external labels. -/
def graph : Fin 3 → DecoratedStableGraph (Fin 1) :=
  ![DecoratedStableGraph.toDecoration ellipticCandidate ellipticValid (ellipticExponents 1 0),
    DecoratedStableGraph.toDecoration ellipticCandidate ellipticValid (ellipticExponents 0 1),
    loopExpression.graph]

/-- Each representative has arithmetic genus one. -/
theorem graph_totalGenus (i : Fin 3) : (graph i).graph.totalGenus = 1 := by
  fin_cases i <;> decide +kernel

/-- The held frame in the existing graph-isomorphism quotient. -/
def columns (i : Fin 3) : TautologicalStratum 1 (Fin 1) :=
  .mk (graph i) (graph_totalGenus i)

/-- Every column has exactly codimension one. -/
theorem columns_codimension : ∀ i, (columns i).codimension = 1 := by
  simp only [columns, graph, DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The held columns are distinct formal strata. -/
theorem columns_injective : Function.Injective columns := by
  simp only [Function.Injective, columns, graph, DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Exchanging the two loop branches gives the raw graph order two. -/
theorem loop_automorphisms : loopExpression.graph.automorphismCount = 2 := by
  decide +kernel

/-- The second column is actual external psi decoration of the fundamental stratum. -/
theorem psi_column : columns 1 =
    (TautologicalStratum.fundamental 1 (Fin 1) stableArity).addLegPsi (Pi.single 0 1) := by
  apply Quotient.sound
  apply (DecoratedStableGraph.isomorphic?_eq_true_iff _ _).mp
  simp only [graph, DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The third column is the explicit raw gluing construction. -/
theorem loop_column : columns 2 = loopExpression.stratum := rfl

/-- The original unsymmetrized full-stable 3-spin rows in monomial kappa coordinates. -/
def rows : Fin 2 → Coordinates 3 := ![![102, -30, -3], ![30, 42, -3]]
/-- The held raw equation psi_1 - (1/24) times the loop pushforward. -/
def requested : Coordinates 3 := ![0, 1, -(1 / 24)]
/-- An exact witness; incoming witnesses must satisfy this same held equation. -/
def certificate : Certificate 2 := ⟨![-5 / 864, 17 / 864]⟩

/-- Kernel arithmetic verifies the row combination. -/
theorem checked : check rows requested certificate = true := by decide +kernel

/-- Acceptance binds all incoming data to the caller-fixed columns, rows and claim. -/
def AcceptsExchange (p : Presentation 1 (Fin 1) 2 3) : Prop :=
  AcceptsPresentation columns rows requested p

/-- The exact coordinate request denotes the claimed formal psi/loop difference. -/
theorem interpret_request :
    interpret columns requested = StrataModule.basis (columns 1) -
      (1 / 24 : ℚ) • StrataModule.basis loopExpression.stratum := by
  rw [interpret_apply, Fin.sum_univ_three]
  change (0 : ℚ) • StrataModule.basis (columns 0) +
    (1 : ℚ) • StrataModule.basis (columns 1) +
      (-(1 / 24) : ℚ) • StrataModule.basis loopExpression.stratum = _
  simp only [zero_smul, one_smul, zero_add, neg_smul, sub_eq_add_neg]

/-- The claim is nonzero in the free strata module before geometric relations. -/
theorem requested_ne_zero : interpret columns requested ≠ 0 := by
  intro h
  have hi := congrArg (fun r ↦ r (columns 1)) h
  rw [interpret_apply_column columns columns_injective] at hi
  norm_num [requested] at hi

/-- An accepted incoming certificate transfers the original row vanishings. -/
theorem evaluated_relation {V : Type*} [AddCommGroup V] [Module ℚ V]
    (p : Presentation 1 (Fin 1) 2 3) (hp : AcceptsExchange p)
    (ev : StrataModule 1 (Fin 1) →ₗ[ℚ] V)
    (hrows : ∀ i, ev (interpret columns (rows i)) = 0) :
    ev (StrataModule.basis (columns 1)) =
      (1 / 24 : ℚ) • ev (StrataModule.basis loopExpression.stratum) := by
  have he := evaluation_eq_zero columns rows requested p.certificate
    ((check_eq_true_iff _ _ _).mpr hp.2) ev hrows
  rw [interpret_request, map_sub, map_smul, sub_eq_zero] at he
  exact he

attribute [local instance] strataRealizationModule

/-- Primitive external psi compatibility interprets the accepted relation as a class identity. -/
theorem realized_psi {R : Type*} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R}
    (p : Presentation 1 (Fin 1) 2 3) (hp : AcceptsExchange p)
    (A : StrataRealization C 1 (Fin 1)) (P : PsiClasses C)
    (hA : A.LegPsiCompatible P stableArity)
    (hfund : A.map (StrataModule.basis
      (TautologicalStratum.fundamental 1 (Fin 1) stableArity)) = 1)
    (hrows : ∀ i, A.map (interpret columns (rows i)) = 0) :
    P.psi 1 (Fin 1) stableArity 0 =
      (1 / 24 : ℚ) • A.map (StrataModule.basis loopExpression.stratum) := by
  have he := evaluated_relation p hp A.map hrows
  rw [psi_column, A.map_addLegPsi_one P _ hA, hfund, one_mul] at he
  exact he
end AxiomaticGW.GenusOnePsi

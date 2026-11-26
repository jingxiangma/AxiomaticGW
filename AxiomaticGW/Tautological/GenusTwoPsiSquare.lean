/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GenusOnePsi
public import AxiomaticGW.Tautological.SeparatingRealization
public import AxiomaticGW.Tautological.RelabelRealization

/-!
# A held marked genus-two cotangent-square relation

The seventeen columns are raw gluing pushforwards in codimension two on
Mbar(2,1), with monomial kappa decorations and a fixed external marking.
Six original full-stable 3-spin rows (arXiv:1303.1043, admcycles 1.4) and one
elliptic boundary row imply psi_1 squared equals a kappa-free combination
of ten boundary strata. Every vertex on the right has genus at most one.
Node cotangent powers are retained, including the branch that carries them.

The tables and requested equation are held independently of incoming replay.
Kernel arithmetic checks the consequence, not geometric vanishing of 3-spin
rows. The latter and primitive realization laws remain explicit inputs.
This is a marked relation for reconstruction, not a genus-two GW evaluator.
-/

@[expose] public section

namespace AxiomaticGW.GenusTwoPsiSquare
open RelationCertificate
universe u

/-- The curve arity for the single marked genus-two relation. -/
theorem stableArity : StableArity 2 (Fin 1) := by norm_num [StableArity]

/-- Monomial decorations with kappa indices one and two. -/
def decorate {v e : ℕ} (c : StableGraphCode.Candidate (Fin 1) v e)
    (h : c.Valid 2) (k : Fin v → Fin 2 → ℕ) (p : Fin 1 → ℕ)
    (q : Fin e → Fin 2 → ℕ) : DecoratedStableGraph (Fin 1) :=
  DecoratedStableGraph.toDecoration c h (fun
    | .inl (vertex, index) => k vertex index
    | .inr (.inl label) => p label
    | .inr (.inr (edge, branch)) => q edge branch)

/-- A single genus-two vertex. -/
def smoothCandidate : StableGraphCode.Candidate (Fin 1) 1 0 where
  legVertex := ![0]
  endpoint := Fin.elim0
  genus := ![2]

/-- Stability and arithmetic genus of this incidence presentation. -/
theorem smoothValid : smoothCandidate.Valid 2 := by decide +kernel

/-- Two elliptic vertices; the second carries the external marking. -/
def separatingCandidate : StableGraphCode.Candidate (Fin 1) 2 1 where
  legVertex := ![1]
  endpoint := ![![0, 1]]
  genus := ![1, 1]

/-- Stability and arithmetic genus of this incidence presentation. -/
theorem separatingValid : separatingCandidate.Valid 2 := by decide +kernel

/-- Two elliptic tails on a marked rational vertex. -/
def chainCandidate : StableGraphCode.Candidate (Fin 1) 3 2 where
  legVertex := ![1]
  endpoint := ![![0, 1], ![1, 2]]
  genus := ![1, 0, 1]

/-- Stability and arithmetic genus of this incidence presentation. -/
theorem chainValid : chainCandidate.Valid 2 := by decide +kernel

/-- A marked elliptic vertex with one loop. -/
def loopCandidate : StableGraphCode.Candidate (Fin 1) 1 1 where
  legVertex := ![0]
  endpoint := ![![0, 0]]
  genus := ![1]

/-- Stability and arithmetic genus of this incidence presentation. -/
theorem loopValid : loopCandidate.Valid 2 := by decide +kernel

/-- A marked rational vertex joined twice to an elliptic vertex. -/
def parallelCandidate : StableGraphCode.Candidate (Fin 1) 2 2 where
  legVertex := ![0]
  endpoint := ![![0, 1], ![0, 1]]
  genus := ![0, 1]

/-- Stability and arithmetic genus of this incidence presentation. -/
theorem parallelValid : parallelCandidate.Valid 2 := by decide +kernel

/-- A rational loop joined to the marked elliptic vertex. -/
def loopBridgeMarkedEllipticCandidate : StableGraphCode.Candidate (Fin 1) 2 2 where
  legVertex := ![1]
  endpoint := ![![0, 0], ![0, 1]]
  genus := ![0, 1]

/-- Stability and arithmetic genus of this incidence presentation. -/
theorem loopBridgeMarkedEllipticValid : loopBridgeMarkedEllipticCandidate.Valid 2 := by
  decide +kernel

/-- A marked rational loop joined to an elliptic vertex. -/
def loopBridgeMarkedRationalCandidate : StableGraphCode.Candidate (Fin 1) 2 2 where
  legVertex := ![0]
  endpoint := ![![0, 0], ![0, 1]]
  genus := ![0, 1]

/-- Stability and arithmetic genus of this incidence presentation. -/
theorem loopBridgeMarkedRationalValid : loopBridgeMarkedRationalCandidate.Valid 2 := by
  decide +kernel

/-- A marked rational vertex with two loops. -/
def twoLoopsCandidate : StableGraphCode.Candidate (Fin 1) 1 2 where
  legVertex := ![0]
  endpoint := ![![0, 0], ![0, 0]]
  genus := ![0]

/-- Stability and arithmetic genus of this incidence presentation. -/
theorem twoLoopsValid : twoLoopsCandidate.Valid 2 := by decide +kernel

/-- The held raw graph frame; kappa and node powers are part of its meaning. -/
def graph : Fin 17 → DecoratedStableGraph (Fin 1) :=
  ![decorate smoothCandidate smoothValid ![![0, 1]] ![0] Fin.elim0,
    decorate smoothCandidate smoothValid ![![2, 0]] ![0] Fin.elim0,
    decorate smoothCandidate smoothValid ![![1, 0]] ![1] Fin.elim0,
    decorate smoothCandidate smoothValid ![![0, 0]] ![2] Fin.elim0,
    decorate separatingCandidate separatingValid ![![0, 0], ![1, 0]] ![0] ![![0, 0]],
    decorate separatingCandidate separatingValid ![![0, 0], ![0, 0]] ![1] ![![0, 0]],
    decorate separatingCandidate separatingValid ![![0, 0], ![0, 0]] ![0] ![![0, 1]],
    decorate chainCandidate chainValid ![![0, 0], ![0, 0], ![0, 0]] ![0] ![![0, 0], ![0, 0]],
    decorate separatingCandidate separatingValid ![![1, 0], ![0, 0]] ![0] ![![0, 0]],
    decorate separatingCandidate separatingValid ![![0, 0], ![0, 0]] ![0] ![![1, 0]],
    decorate loopCandidate loopValid ![![1, 0]] ![0] ![![0, 0]],
    decorate loopCandidate loopValid ![![0, 0]] ![0] ![![1, 0]],
    decorate loopCandidate loopValid ![![0, 0]] ![1] ![![0, 0]],
    decorate parallelCandidate parallelValid ![![0, 0], ![0, 0]] ![0] ![![0, 0], ![0, 0]],
    decorate loopBridgeMarkedEllipticCandidate loopBridgeMarkedEllipticValid ![![0, 0], ![0, 0]]
      ![0] ![![0, 0], ![0, 0]],
    decorate loopBridgeMarkedRationalCandidate loopBridgeMarkedRationalValid ![![0, 0], ![0, 0]]
      ![0] ![![0, 0], ![0, 0]],
    decorate twoLoopsCandidate twoLoopsValid ![![0, 0]] ![0] ![![0, 0], ![0, 0]]]

/-- All held columns have arithmetic genus two. -/
theorem graph_totalGenus (i : Fin 17) : (graph i).graph.totalGenus = 2 := by
  fin_cases i <;> decide +kernel

/-- Columns live in the existing decorated-graph isomorphism quotient. -/
def columns (i : Fin 17) : TautologicalStratum 2 (Fin 1) :=
  .mk (graph i) (graph_totalGenus i)

/-- Every column is homogeneous of codimension two. -/
theorem columns_codimension : ∀ i, (columns i).codimension = 2 := by
  simp only [columns, graph, decorate, DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The columns are distinct formal decorated strata, before relations. -/
theorem columns_injective : Function.Injective columns := by
  simp only [Function.Injective, columns, graph, decorate,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Decorated automorphism orders; a single loop-branch psi breaks its symmetry. -/
def automorphismOrders : Fin 17 → ℕ :=
  ![1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 8]

/-- The small order table is proved from the decorated graph isomorphism enumerator. -/
theorem automorphismOrders_correct : ∀ i, (graph i).automorphismCount = automorphismOrders i := by
  simp only [graph, decorate, DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The requested leading column is the actual square of external psi. -/
theorem psi_square_column : columns 3 =
    (TautologicalStratum.fundamental 2 (Fin 1) stableArity).addLegPsi (Pi.single 0 2) := by
  apply Quotient.sound
  apply (DecoratedStableGraph.isomorphic?_eq_true_iff _ _).mp
  simp only [graph, decorate, DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Original full-stable 3-spin rows followed by the pushed elliptic row. -/
def rows : Fin 7 → Coordinates 17 :=
  ![![0, -30, 30, 0, 42, 0, 0, 0, 42, 0, 3, 0, 0, 0, 0, 0, 0],
    ![362880, -78120, 61200, -138600, 37296, -7920, -42840, 1368, 18288,
      17640, 6120, -12600, -1800, 2232, 72, -792, -90],
    ![176256, -27864, -39312, 98280, 20304, 9072, -37800, -3672, 1296,
      22680, 2808, -7560, 1512, -2808, 216, -648, -54],
    ![0, 0, -30, 30, 0, 42, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0],
    ![64800, -7020, 9720, -41580, 9288, -3240, -18900, 756, 4968,
      11340, 972, -3780, -540, 1188, 108, -324, -27],
    ![12960, -900, -2520, 16380, 2520, 3528, -16380, -1764, -1800,
      13860, 180, -1260, 252, -1332, 180, -252, -9],
    ![0, 0, 0, 0, 0, 0, 0, 0, 102, -30, 0, 0, 0, 0, -3, 0, 0]]

/-- The held request, with coefficient one on psi_1 squared. -/
def requested : Coordinates 17 :=
  ![0, 0, 0, 1, 0, -155/351, -70/351, -23/390, 0, 328/1989, 0,
    -7/2808, -31/1404, -749/14040, -101/477360, -3/1040, -1/56160]

/-- The boundary side of the relation, retaining every signed coefficient. -/
def boundary : Coordinates 17 :=
  ![0, 0, 0, 0, 0, 155/351, 70/351, 23/390, 0, -328/1989, 0,
    7/2808, 31/1404, 749/14040, 101/477360, 3/1040, 1/56160]

/-- An exact witness in the seven original rows. -/
def certificate : Certificate 7 :=
  ⟨![7/505440, -19/19408896, 305/58226688, -53/3744,
    -1759/145566720, 161/9704448, 47/47736]⟩

/-- Lean's kernel verifies the complete rational combination. -/
theorem checked : check rows requested certificate = true := by decide +kernel

/-- The held coordinate relation isolates the external square. -/
theorem requested_eq : requested = Pi.single 3 1 - boundary := by decide +kernel

/-- The boundary side lowers every vertex genus and has at most one psi factor. -/
theorem boundary_reduces : ∀ i, boundary i ≠ 0 →
    0 < (graph i).graph.edgeCount ∧
    (∀ v, (graph i).graph.genus v < 2) ∧
    (graph i).kappaCodimension = 0 ∧
    (graph i).legPsiCodimension + (graph i).halfEdgePsiCodimension ≤ 1 := by
  simp only [graph, decorate, DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Formal interpretation is exactly psi-square minus the held boundary. -/
theorem interpret_request : interpret columns requested =
    StrataModule.basis (columns 3) - interpret columns boundary := by
  rw [requested_eq, map_sub, interpret, Fintype.linearCombination_apply_single, one_smul]

/-- The formal relation is nonzero before geometric vanishing is imposed. -/
theorem requested_ne_zero : interpret columns requested ≠ 0 := by
  intro h
  have hi := congrArg (fun r ↦ r (columns 3)) h
  rw [interpret_apply_column columns columns_injective] at hi
  exact (one_ne_zero : (1 : ℚ) ≠ 0) hi

/-- Incoming columns, normalization, original rows, and request are held fixed. -/
def AcceptsPresentation (p : Presentation 2 (Fin 1) 7 17) : Prop :=
  RelationCertificate.AcceptsPresentation columns rows requested p

/-- Checked arithmetic transfers only the supplied original row vanishings. -/
theorem evaluated_relation {V : Type*} [AddCommGroup V] [Module ℚ V]
    (p : Presentation 2 (Fin 1) 7 17) (hp : AcceptsPresentation p)
    (ev : StrataModule 2 (Fin 1) →ₗ[ℚ] V)
    (hrows : ∀ i, ev (interpret columns (rows i)) = 0) :
    ev (StrataModule.basis (columns 3)) = ev (interpret columns boundary) := by
  have he := evaluation_eq_zero columns rows requested p.certificate
    ((check_eq_true_iff _ _ _).mpr hp.2) ev hrows
  rw [interpret_request, map_sub, sub_eq_zero] at he
  exact he


/-- Source kappa pushforward coordinates of the same seven original rows. -/
def pushforwardRows : Fin 7 → Coordinates 17 :=
  ![![30, -30, 30, 0, 42, 0, 0, 0, 42, 0, 3, 0, 0, 0, 0, 0, 0],
    ![441000, -78120, 61200, -138600, 37296, -7920, -42840, 1368, 18288,
      17640, 6120, -12600, -1800, 2232, 72, -792, -90],
    ![204120, -27864, -39312, 98280, 20304, 9072, -37800, -3672, 1296,
      22680, 2808, -7560, 1512, -2808, 216, -648, -54],
    ![0, 0, -30, 30, 0, 42, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0],
    ![71820, -7020, 9720, -41580, 9288, -3240, -18900, 756, 4968,
      11340, 972, -3780, -540, 1188, 108, -324, -27],
    ![13860, -900, -2520, 16380, 2520, 3528, -16380, -1764, -1800,
      13860, 180, -1260, 252, -1332, 180, -252, -9],
    ![0, 0, 0, 0, 0, 0, 0, 0, 102, -30, 0, 0, 0, 0, -3, 0, 0]]

/-- Only the kappa_1-squared basis vector has a nontrivial conversion. -/
def pushforwardToMonomial (i : Fin 17) : Coordinates 17 :=
  Pi.single i 1 + if i = 1 then Pi.single 0 1 else 0

/-- The inverse subtracts kappa_2 in that same slot. -/
def monomialToPushforward (i : Fin 17) : Coordinates 17 :=
  Pi.single i 1 - if i = 1 then Pi.single 0 1 else 0

/-- Every row is bound to the original source coordinates. -/
theorem rows_conversion : ∀ i,
    combination pushforwardToMonomial ⟨pushforwardRows i⟩ = rows i := by
  decide +kernel

/-- The coordinate conversion is invertible on each basis vector. -/
theorem conversion_inverse_basis : ∀ i,
    combination monomialToPushforward ⟨pushforwardToMonomial i⟩ = Pi.single i 1 ∧
    combination pushforwardToMonomial ⟨monomialToPushforward i⟩ = Pi.single i 1 := by
  decide +kernel

/-- Linear extension of the source-to-monomial coordinate table. -/
def toMonomial : Coordinates 17 →ₗ[ℚ] Coordinates 17 :=
  Fintype.linearCombination ℚ pushforwardToMonomial

/-- Linear extension of its inverse. -/
def toPushforward : Coordinates 17 →ₗ[ℚ] Coordinates 17 :=
  Fintype.linearCombination ℚ monomialToPushforward

/-- The two coordinate maps are inverse on every rational vector. -/
theorem conversion_inverse :
    toPushforward.comp toMonomial = LinearMap.id ∧
    toMonomial.comp toPushforward = LinearMap.id := by
  constructor <;> apply LinearMap.pi_ext <;> intro i q
  · have hb : toPushforward (toMonomial (Pi.single i 1)) = Pi.single i 1 := by
      rw [toMonomial, Fintype.linearCombination_apply_single, one_smul,
        toPushforward, linearCombination_eq_combination]
      exact (conversion_inverse_basis i).1
    have hq : (Pi.single i q : Coordinates 17) = q • Pi.single i 1 := by
      simpa only [smul_eq_mul, mul_one] using
        Pi.single_smul (f := fun _ : Fin 17 ↦ ℚ) i q (1 : ℚ)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hq, map_smul, hb]
  · have hb : toMonomial (toPushforward (Pi.single i 1)) = Pi.single i 1 := by
      rw [toPushforward, Fintype.linearCombination_apply_single, one_smul,
        toMonomial, linearCombination_eq_combination]
      exact (conversion_inverse_basis i).2
    have hq : (Pi.single i q : Coordinates 17) = q • Pi.single i 1 := by
      simpa only [smul_eq_mul, mul_one] using
        Pi.single_smul (f := fun _ : Fin 17 ↦ ℚ) i q (1 : ℚ)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hq, map_smul, hb]

/-- Full incoming mathematical data; metadata hashes alone supply no proof. -/
structure Exchange where
  /-- Actual incoming graphs, raw normalization, rows, request and witness. -/
  presentation : Presentation 2 (Fin 1) 7 17
  /-- Original rows before monomial conversion. -/
  sourceRows : Fin 7 → Coordinates 17
  /-- Source-to-monomial conversion. -/
  sourceToMonomial : Fin 17 → Coordinates 17
  /-- Monomial-to-source conversion. -/
  monomialToSource : Fin 17 → Coordinates 17
  /-- Claimed boundary side, separately held. -/
  claimedBoundary : Coordinates 17
  /-- Decorated automorphism orders, never used to rescale the raw columns. -/
  automorphisms : Fin 17 → ℕ

/-- Every incoming field is compared with its caller-fixed mathematical meaning. -/
def AcceptsExchange (p : Exchange) : Prop :=
  AcceptsPresentation p.presentation ∧
  p.sourceRows = pushforwardRows ∧
  p.sourceToMonomial = pushforwardToMonomial ∧
  p.monomialToSource = monomialToPushforward ∧
  p.claimedBoundary = boundary ∧
  ∀ i, p.automorphisms i = (graph i).automorphismCount

/-- The marked elliptic factor, with one additional branch reserved for gluing. -/
theorem ellipticMarkedStable : StableArity 1 (Option (Fin 1)) := by
  norm_num [StableArity]

/-- Source columns acquire an elliptic factor; the original marking becomes a node. -/
noncomputable def ellipticGluingColumn (i : Fin 3) : TautologicalStratum 2 (Fin 1) :=
  (((GenusOnePsi.columns i).relabel (finSuccEquiv 0)).separating
    (TautologicalStratum.fundamental 1 (Option (Fin 1)) ellipticMarkedStable)).relabel
      (Equiv.emptySum (Fin 0) (Fin 1))

/-- The actual graph operation sends kappa, psi and the loop to these columns. -/
def ellipticDestinations : Fin 3 → Fin 17 := ![8, 9, 14]

/-- Node decorations and raw loop multiplicities survive the graph gluing. -/
theorem ellipticGluingColumn_eq : ∀ i,
    ellipticGluingColumn i = columns (ellipticDestinations i) := by
  simp only [ellipticGluingColumn, GenusOnePsi.columns, GenusOnePsi.graph,
    columns, graph, decorate, DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The seventh row has exactly the existing original elliptic row coefficients. -/
theorem elliptic_row_coordinates : rows 6 =
    combination (fun i ↦ Pi.single (ellipticDestinations i) 1)
      ⟨GenusOnePsi.rows 0⟩ := by decide +kernel

/-- Linear raw gluing of an elliptic input with the marked elliptic fundamental class. -/
noncomputable def glueElliptic : StrataModule 1 (Fin 1) →ₗ[ℚ] StrataModule 2 (Fin 1) :=
  (StrataModule.relabel (Equiv.emptySum (Fin 0) (Fin 1))).comp
    ((StrataModule.separating.flip (StrataModule.basis
      (TautologicalStratum.fundamental 1 (Option (Fin 1)) ellipticMarkedStable))).comp
        (StrataModule.relabel (finSuccEquiv 0)))

/-- The row used by the certificate is the formal pushforward of the existing row. -/
theorem elliptic_row_gluing :
    interpret columns (rows 6) =
      glueElliptic (interpret GenusOnePsi.columns (GenusOnePsi.rows 0)) := by
  rw [elliptic_row_coordinates, interpret_combination]
  simp only [interpret, Fintype.linearCombination_apply_single, one_smul]
  change _ = StrataModule.relabel (Equiv.emptySum (Fin 0) (Fin 1))
    (StrataModule.separating
      (StrataModule.relabel (finSuccEquiv 0)
        (interpret GenusOnePsi.columns (GenusOnePsi.rows 0)))
      (StrataModule.basis
        (TautologicalStratum.fundamental 1 (Option (Fin 1)) ellipticMarkedStable)))
  rw [relabel_interpret, separating_left_interpret, relabel_interpret]
  change _ = interpret ellipticGluingColumn (GenusOnePsi.rows 0)
  rw [show ellipticGluingColumn = fun i ↦ columns (ellipticDestinations i) from
    funext ellipticGluingColumn_eq, interpret_apply]

attribute [local instance] strataRealizationModule

/-- The accepted relation becomes an actual stable-curve psi-square identity. -/
theorem realized_psi_square {R : Type*} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R}
    (p : Presentation 2 (Fin 1) 7 17) (hp : AcceptsPresentation p)
    (A : StrataRealization C 2 (Fin 1)) (P : PsiClasses C)
    (hA : A.LegPsiCompatible P stableArity)
    (hfund : A.map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) stableArity)) = 1)
    (hrows : ∀ i, A.map (interpret columns (rows i)) = 0) :
    P.psi 2 (Fin 1) stableArity 0 ^ 2 = A.map (interpret columns boundary) := by
  have he := evaluated_relation p hp A.map hrows
  rw [psi_square_column, A.map_addLegPsi_single P _ hA, hfund, one_mul] at he
  exact he


/-- The left elliptic factor has only its node branch. -/
theorem ellipticSourceStable : StableArity 1 (Option (Fin 0)) := by
  norm_num [StableArity]

/-- Stability of the target before removing the empty external label summand. -/
theorem separatingStable : StableArity 2 (Fin 0 ⊕ Fin 1) := by
  norm_num [StableArity]

/-- The boundary row vanishes by primitive relabelling and separating laws,
using only the original genus-one row vanishing. -/
theorem elliptic_row_vanishes {R : Type*} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (E : StrataRealization C 1 (Fin 1)) (L : StrataRealization C 1 (Option (Fin 0)))
    (B : StrataRealization C 1 (Option (Fin 1)))
    (U : StrataRealization C 2 (Fin 0 ⊕ Fin 1)) (A : StrataRealization C 2 (Fin 1))
    (F : SeparatingPushforward C I)
    (hEL : E.RelabelCompatible L GenusOnePsi.stableArity ellipticSourceStable (finSuccEquiv 0))
    (hLB : L.SeparatingCompatible B U F ellipticSourceStable ellipticMarkedStable)
    (hUA : U.RelabelCompatible A separatingStable stableArity (Equiv.emptySum (Fin 0) (Fin 1)))
    (hsource : E.map (interpret GenusOnePsi.columns (GenusOnePsi.rows 0)) = 0) :
    A.map (interpret columns (rows 6)) = 0 := by
  rw [elliptic_row_gluing]
  change A.map (StrataModule.relabel (Equiv.emptySum (Fin 0) (Fin 1))
    (StrataModule.separating
      (StrataModule.relabel (finSuccEquiv 0)
        (interpret GenusOnePsi.columns (GenusOnePsi.rows 0)))
      (StrataModule.basis
        (TautologicalStratum.fundamental 1 (Option (Fin 1)) ellipticMarkedStable)))) = 0
  rw [U.map_relabel A separatingStable stableArity _ hUA,
    L.map_separating B U F ellipticSourceStable ellipticMarkedStable hLB,
    E.map_relabel L GenusOnePsi.stableArity ellipticSourceStable _ hEL,
    hsource, map_zero, TensorProduct.zero_tmul, map_zero, map_zero]

/-- The genus-two identity requires six original genus-two generator vanishings
and one original genus-one vanishing, with the intervening graph operations derived. -/
theorem realized_psi_square_from_generators {R : Type*} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (p : Exchange) (hp : AcceptsExchange p)
    (E : StrataRealization C 1 (Fin 1)) (L : StrataRealization C 1 (Option (Fin 0)))
    (B : StrataRealization C 1 (Option (Fin 1)))
    (U : StrataRealization C 2 (Fin 0 ⊕ Fin 1)) (A : StrataRealization C 2 (Fin 1))
    (F : SeparatingPushforward C I) (P : PsiClasses C)
    (hEL : E.RelabelCompatible L GenusOnePsi.stableArity ellipticSourceStable (finSuccEquiv 0))
    (hLB : L.SeparatingCompatible B U F ellipticSourceStable ellipticMarkedStable)
    (hUA : U.RelabelCompatible A separatingStable stableArity (Equiv.emptySum (Fin 0) (Fin 1)))
    (hA : A.LegPsiCompatible P stableArity)
    (hfund : A.map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) stableArity)) = 1)
    (hrows : ∀ i : Fin 6, A.map (interpret columns (rows i.castSucc)) = 0)
    (hsource : E.map (interpret GenusOnePsi.columns (GenusOnePsi.rows 0)) = 0) :
    P.psi 2 (Fin 1) stableArity 0 ^ 2 = A.map (interpret columns boundary) := by
  apply realized_psi_square p.presentation hp.1 A P hA hfund
  exact Fin.lastCases (elliptic_row_vanishes E L B U A F hEL hLB hUA hsource) hrows

/-- Multiplying the checked relation yields every higher one-marked power;
its remaining external and node powers are explicit decorated graph operations. -/
theorem realized_psi_power {R : Type*} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R}
    (p : Presentation 2 (Fin 1) 7 17) (hp : AcceptsPresentation p)
    (A : StrataRealization C 2 (Fin 1)) (P : PsiClasses C)
    (hA : A.LegPsiCompatible P stableArity)
    (hfund : A.map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) stableArity)) = 1)
    (hrows : ∀ i, A.map (interpret columns (rows i)) = 0) (k : ℕ) :
    P.psi 2 (Fin 1) stableArity 0 ^ (2 + k) =
      A.map (StrataModule.mulLegPsi (Pi.single 0 k) (interpret columns boundary)) := by
  rw [A.map_mulLegPsi P stableArity hA, P.monomial_single, pow_add,
    realized_psi_square p hp A P hA hfund hrows]


/-- Every class-valued CohFT receives the same one-marked ancestor reduction.
The right side still requires evaluation of decorated boundary pushforwards. -/
theorem ancestor_reduction {R V : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    {C : StableCurveCohomology R}
    (p : Exchange) (hp : AcceptsExchange p)
    (A : StrataRealization C 2 (Fin 1)) (P : PsiClasses C) (I : StableCurveIntegration C)
    (Omega : CohFT R V C) (a : Fin 1 → V)
    (hA : A.LegPsiCompatible P stableArity)
    (hfund : A.map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) stableArity)) = 1)
    (hrows : ∀ i, A.map (interpret columns (rows i)) = 0) (k : ℕ) :
    Omega.ancestor P I 2 (Fin 1) stableArity (Pi.single 0 (2 + k)) a =
      ∑ i, boundary i • A.integrateAgainst I stableArity (Omega.omega 2 (Fin 1) stableArity a)
        (StrataModule.basis ((columns i).addLegPsi (Pi.single 0 k))) := by
  rw [CohFT.ancestor_apply, P.monomial_single,
    realized_psi_power p.presentation hp.1 A P hA hfund hrows]
  change A.integrateAgainst I stableArity (Omega.omega 2 (Fin 1) stableArity a)
    (StrataModule.mulLegPsi (Pi.single 0 k) (interpret columns boundary)) = _
  rw [mulLegPsi_interpret, interpret_apply, map_sum]
  simp only [map_smul]

end AxiomaticGW.GenusTwoPsiSquare

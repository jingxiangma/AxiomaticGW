/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.StateSpaceCertificate
public import AxiomaticGW.Surfaces.TargetData

/-!
# Claim-bound full curve and invariant-edge conventions

These certificates connect the serialized lattice matrix and wall classes to
the existing surface coordinate monoids. They check the complete invariant
edge presentation, dual fan characters, orientation, and normal degrees.
The divisor intersection check is an identity in the exact coefficient field.
Geometric identification of the fan, and stable-map localization and graph
stabilization, remain separate obligations.
-/

@[expose] public section

namespace AxiomaticGW.GKM.CurveConventionCertificate

open EquivariantCoefficients Matrix

/-- Integer matrix presenting the existing full curve-coordinate map. -/
def latticeMatrix : (X : SurfaceTarget) →
    Matrix (Fin (X.blowups + 1)) (Fin (X.blowups + 1)) ℤ
  | .plane => !![1]
  | .hirzebruchOne => !![0, 1; 1, -1]
  | .blowupTwo => !![0, 0, 1; 1, 0, -1; 0, 1, -1]

/-- Matrix evaluation agrees with the established surface API on every class. -/
theorem latticeMatrix_mulVec (X : SurfaceTarget) (beta : X.Curve) :
    latticeMatrix X *ᵥ (fun i ↦ (beta i : ℤ)) = X.latticeCoordinates beta := by
  cases X
  · funext i
    fin_cases i
    change (∑ j : Fin 1, (!![1] : Matrix (Fin 1) (Fin 1) ℤ) 0 j * (beta j : ℤ)) = _
    rw [Fin.sum_univ_one]
    exact one_mul _
  · funext i
    change (∑ j : Fin 2, (!![0,1; 1,-1] : Matrix (Fin 2) (Fin 2) ℤ) i j *
      (beta j : ℤ)) = (![beta 1, (beta 0 : ℤ) - beta 1] : Fin 2 → ℤ) i
    rw [Fin.sum_univ_two]
    fin_cases i
    · change 0*(beta 0 : ℤ) + 1*(beta 1 : ℤ) = beta 1
      ring
    · change 1*(beta 0 : ℤ) + (-1)*(beta 1 : ℤ) = (beta 0 : ℤ) - beta 1
      ring
  · funext i
    change (∑ j : Fin 3, (!![0,0,1; 1,0,-1; 0,1,-1] : Matrix (Fin 3) (Fin 3) ℤ) i j *
      (beta j : ℤ)) = (![beta 2, (beta 0 : ℤ) - beta 2, (beta 1 : ℤ) - beta 2] : Fin 3 → ℤ) i
    rw [Fin.sum_univ_three]
    fin_cases i
    · change 0*(beta 0 : ℤ) + 0*(beta 1 : ℤ) + 1*(beta 2 : ℤ) = beta 2
      ring
    · change 1*(beta 0 : ℤ) + 0*(beta 1 : ℤ) + (-1)*(beta 2 : ℤ) = (beta 0 : ℤ) - beta 2
      ring
    · change 0*(beta 0 : ℤ) + 1*(beta 1 : ℤ) + (-1)*(beta 2 : ℤ) = (beta 1 : ℤ) - beta 2
      ring

/-- An additive torus character interpreted in the actual coefficient field. -/
noncomputable def character (w : Fin 2 → ℤ) : Coefficient :=
  (w 0 : Coefficient)*x + (w 1 : Coefficient)*y

/-- One oriented invariant curve, with its other incident normal branches. -/
structure Edge (X : SurfaceTarget) (n r : ℕ) where
  /-- Source fixed point. -/
  source : Fin n
  /-- Target fixed point. -/
  target : Fin n
  /-- Common ray of the two cones. -/
  wall : Fin r
  /-- Source tangent character along this curve. -/
  weight : Fin 2 → ℤ
  /-- Complete effective class, retaining every exceptional coordinate. -/
  curve : X.Curve
  /-- Other neighbor at the source. -/
  normalSource : Fin n
  /-- Other neighbor at the target. -/
  normalTarget : Fin n
  /-- Signed normal-bundle degree. -/
  normalDegree : ℤ

/-- Fixed semantic fan and state-space request, independent of candidate data. -/
structure Request (X : SurfaceTarget) (n r : ℕ) where
  /-- The already fixed classical state-space request. -/
  state : StateSpaceCertificate.Request n
  /-- State labels of the ordered ordinary divisors H,E₁,... . -/
  divisorState : Fin (X.blowups + 1) → Fin n
  /-- Fan rays in the declared torus basis. -/
  rays : Fin r → Fin 2 → ℤ
  /-- Sorted ray pairs labeling fixed points. -/
  points : Fin n → Fin 2 → Fin r
  /-- Tangent characters, in the dual order to those ray pairs. -/
  tangent : Fin n → Fin 2 → Fin 2 → ℤ
  /-- Expected full effective class of each invariant wall. -/
  wallClasses : Fin r → X.Curve
  /-- Walls realizing the chosen effective generators. -/
  generatorWalls : Fin (X.blowups + 1) → Fin r

/-- Candidate curve and edge data decoded from the version-one bundle. -/
structure Tables (X : SurfaceTarget) (n r : ℕ) where
  /-- Candidate fan rays. -/
  rays : Fin r → Fin 2 → ℤ
  /-- Candidate fixed-point ray pairs. -/
  points : Fin n → Fin 2 → Fin r
  /-- Candidate tangent pairs; their ordering may differ from dual-ray order. -/
  tangent : Fin n → Fin 2 → Fin 2 → ℤ
  /-- Candidate full lattice change of coordinates. -/
  curveMatrix : Matrix (Fin (X.blowups + 1)) (Fin (X.blowups + 1)) ℤ
  /-- Candidate anticanonical generator weights. -/
  weights : Fin (X.blowups + 1) → ℕ
  /-- Candidate full invariant-wall classes. -/
  wallClasses : Fin r → X.Curve
  /-- Candidate divisor intersections, ordered by divisor then wall. -/
  intersections : Fin (X.blowups + 1) → Fin r → ℤ
  /-- Complete edge list, one unoriented edge for every wall. -/
  edges : Fin r → Edge X n r

/-- A ray occurs in a fixed-point cone. -/
def Incident {X : SurfaceTarget} {n r : ℕ} (request : Request X n r)
    (p : Fin n) (rho : Fin r) : Prop :=
  request.points p 0 = rho ∨ request.points p 1 = rho

/-- Distinct fan fixed points share an invariant curve. -/
def Adjacent {X : SurfaceTarget} {n r : ℕ} (request : Request X n r)
    (p q : Fin n) : Prop := p ≠ q ∧ ∃ rho, Incident request p rho ∧ Incident request q rho

/-- Toric divisor restriction, computed from the fixed dual characters. -/
noncomputable def divisorRestriction {X : SurfaceTarget} {n r : ℕ} (request : Request X n r)
    (p : Fin n) (rho : Fin r) : Coefficient :=
  ∑ j : Fin 2, if request.points p j = rho then character (request.tangent p j) else 0

/-- Oriented edge weight read from the complete candidate presentation. -/
def edgeWeight {X : SurfaceTarget} {n r : ℕ} (tables : Tables X n r)
    (p q : Fin n) : Fin 2 → ℤ :=
  ∑ e, if (tables.edges e).source = p ∧ (tables.edges e).target = q then
    (tables.edges e).weight else
    if (tables.edges e).source = q ∧ (tables.edges e).target = p then
      -(tables.edges e).weight else 0

/-- Acceptance checks arithmetic and conventions; it assumes no GW recurrence. -/
structure Accepts {X : SurfaceTarget} {n r : ℕ}
    (request : Request X n r) (tables : Tables X n r) : Prop where
  /-- Fan rays match the held request in the declared torus basis. -/
  rays_eq : tables.rays = request.rays
  /-- Fixed-point labels match the held cone ordering. -/
  points_eq : tables.points = request.points
  /-- Each tangent pair agrees, allowing exchange of its two branches. -/
  tangent_eq : ∀ p,
    (tables.tangent p 0 = request.tangent p 0 ∧
      tables.tangent p 1 = request.tangent p 1) ∨
    (tables.tangent p 0 = request.tangent p 1 ∧
      tables.tangent p 1 = request.tangent p 0)
  /-- The full matrix is the established curve-coordinate map. -/
  matrix_eq : tables.curveMatrix = latticeMatrix X
  /-- Energy uses exactly the established positive generator weights. -/
  weights_eq : tables.weights = X.weights
  /-- All invariant-wall classes match the independently fixed request. -/
  walls_eq : tables.wallClasses = request.wallClasses
  /-- The declared generator walls really give the unit coordinate classes. -/
  generators_eq : ∀ i, tables.wallClasses (request.generatorWalls i) = Pi.single i 1
  /-- Fan tangent characters are dual to the corresponding ray pairs. -/
  tangent_dual : ∀ p i j,
    (∑ a : Fin 2, request.tangent p i a * request.rays (request.points p j) a) =
      if i = j then 1 else 0
  /-- The state-space Euler factors are those of the same two fan tangents. -/
  state_euler : ∀ p, request.state.euler p =
    character (request.tangent p 0) * character (request.tangent p 1)
  /-- The state-space Chern restriction uses those same tangent characters. -/
  state_tangentSum : ∀ p, request.state.tangentSum p =
    character (request.tangent p 0) + character (request.tangent p 1)
  /-- Integer intersections agree with the existing signed surface pairing. -/
  intersections_eq : ∀ i rho,
    tables.intersections i rho = X.divisorIntersections (tables.wallClasses rho) i
  /-- Each intersection is the full equivariant localization trace. -/
  intersections_trace : ∀ i rho, (tables.intersections i rho : Coefficient) =
    ∑ p, request.state.restrictions p (request.divisorState i) *
      divisorRestriction request p rho / request.state.euler p
  /-- Each wall occurs once, allowing either edge orientation. -/
  walls_bijective : Function.Bijective (fun e ↦ (tables.edges e).wall)
  /-- Each recorded edge has distinct endpoints containing its common wall. -/
  edge_endpoints : ∀ e, let edge := tables.edges e
    edge.source ≠ edge.target ∧ Incident request edge.source edge.wall ∧
      Incident request edge.target edge.wall
  /-- Every fan adjacency has a recorded edge in one of its two orientations. -/
  edges_complete : ∀ p q, Adjacent request p q → ∃ e,
    ((tables.edges e).source = p ∧ (tables.edges e).target = q) ∨
      ((tables.edges e).source = q ∧ (tables.edges e).target = p)
  /-- Curve degrees retain the complete wall class rather than energy alone. -/
  edge_classes : ∀ e, (tables.edges e).curve = tables.wallClasses (tables.edges e).wall
  /-- Source transverse characters give the oriented edge weight. -/
  source_weights : ∀ e j, request.points (tables.edges e).source j ≠ (tables.edges e).wall →
    (tables.edges e).weight = request.tangent (tables.edges e).source j
  /-- Target transverse characters give the reversed weight. -/
  target_weights : ∀ e j, request.points (tables.edges e).target j ≠ (tables.edges e).wall →
    -(tables.edges e).weight = request.tangent (tables.edges e).target j
  /-- Normal branches are the other actual adjacent invariant curves. -/
  normal_branches : ∀ e, let edge := tables.edges e
    Adjacent request edge.source edge.normalSource ∧
      Adjacent request edge.target edge.normalTarget ∧
      edge.normalSource ≠ edge.target ∧ edge.normalTarget ≠ edge.source
  /-- Normal degrees agree with the complete first-Chern degree. -/
  normal_energy : ∀ e, X.c1Degree (tables.edges e).curve = 2 + (tables.edges e).normalDegree
  /-- Normal characters have the declared integral transition degree. -/
  normal_characters : ∀ e, let edge := tables.edges e
    edgeWeight tables edge.source edge.normalSource -
      edgeWeight tables edge.target edge.normalTarget = edge.normalDegree • edge.weight

namespace Accepts

variable {X : SurfaceTarget} {n r : ℕ} {request : Request X n r} {tables : Tables X n r}

/-- The certified transport equals the established map for arbitrary classes. -/
theorem transport_correct (h : Accepts request tables) (beta : X.Curve) :
    tables.curveMatrix *ᵥ (fun i ↦ (beta i : ℤ)) = X.latticeCoordinates beta := by
  rw [h.matrix_eq, latticeMatrix_mulVec]

/-- Class transport cannot conflate two exceptional classes of equal energy. -/
theorem transport_injective (h : Accepts request tables) :
    Function.Injective (fun beta : X.Curve ↦
      tables.curveMatrix *ᵥ (fun i ↦ (beta i : ℤ))) := by
  intro a b hab
  change tables.curveMatrix *ᵥ (fun i ↦ (a i : ℤ)) =
    tables.curveMatrix *ᵥ (fun i ↦ (b i : ℤ)) at hab
  rw [h.transport_correct, h.transport_correct] at hab
  exact X.latticeCoordinates_injective hab

/-- Complete class addition is preserved, including all exceptional components. -/
theorem transport_add (h : Accepts request tables) (a b : X.Curve) :
    tables.curveMatrix *ᵥ (fun i ↦ ((a+b) i : ℤ)) =
      tables.curveMatrix *ᵥ (fun i ↦ (a i : ℤ)) +
        tables.curveMatrix *ᵥ (fun i ↦ (b i : ℤ)) := by
  rw [h.transport_correct, h.transport_correct, h.transport_correct, X.latticeCoordinates_add]

/-- Certified energy equals the existing effective-curve energy on every class. -/
theorem energy_correct (h : Accepts request tables) (beta : X.Curve) :
    WeightedCurveClass.energy tables.weights beta = X.effective.energy beta := by
  rw [h.weights_eq]
  rfl

/-- Edge classes and normal degrees recover the actual signed divisor pairing. -/
theorem edge_firstChern (h : Accepts request tables) (e : Fin r) :
    X.divisorPairing (SurfaceCohomology.firstChernDivisor X.blowups)
      (tables.edges e).curve = ((2 + (tables.edges e).normalDegree : ℤ) : ℚ) := by
  rw [SurfaceTarget.divisorPairing_firstChernDivisor, h.normal_energy]

/-- The intersection trace uses exactly the restrictions and Euler factors
of the accepted state-space tables. -/
theorem intersection_trace {state : StateSpaceCertificate.Tables n}
    (h : Accepts request tables) (hs : StateSpaceCertificate.Accepts request.state state)
    (i : Fin (X.blowups + 1)) (rho : Fin r) :
    (tables.intersections i rho : Coefficient) =
      ∑ p, state.restrictions p (request.divisorState i) *
        divisorRestriction request p rho / state.euler p := by
  rw [hs.restrictions_eq, hs.euler_eq]
  exact h.intersections_trace i rho

/-- The complete divisor trace is regular at the ordinary origin and has
the established integer intersection as its unique ordinary value. -/
theorem intersections_specialize (h : Accepts request tables)
    (i : Fin (X.blowups + 1)) (rho : Fin r) :
    Specializes (∑ p, request.state.restrictions p (request.divisorState i) *
      divisorRestriction request p rho / request.state.euler p)
        (tables.intersections i rho : ℚ) := by
  have heq : (∑ p, request.state.restrictions p (request.divisorState i) *
      divisorRestriction request p rho / request.state.euler p) =
      embed (MvPolynomial.C (tables.intersections i rho : ℚ)) := by
    rw [← h.intersections_trace, embed_C, Rat.cast_intCast]
  simpa only [atZero, MvPolynomial.eval₂Hom_C, RingHom.id_apply] using
    specializes_of_eq_polynomial (MvPolynomial.C (tables.intersections i rho : ℚ)) heq

end Accepts

end AxiomaticGW.GKM.CurveConventionCertificate

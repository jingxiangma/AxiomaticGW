/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.SingleCoveredEdge
public import AxiomaticGW.GKM.FixedGraphSupport
public import AxiomaticGW.GKM.HomogeneousSpecialization
public import AxiomaticGW.GKM.Fixtures.CurveReplay
public import AxiomaticGW.GKM.Fixtures.SurfaceReplay
public import AxiomaticGW.Surfaces.Queries

/-! # One point descendant on a plane line with both torus characters

The pinned point lift is supported at fixed point 1. A marked tangent direction there has
weight `u`, the other direction has weight `v`, and its one-flag contribution is
`(-u)^k / (v-u)`. Summing the two flags cancels their poles even at the smallest powers.
The edge and unstable vertex conventions follow Liu–Sheshmani, Theorem 4.7 and (4.7)–(4.8).
-/

@[expose] public noncomputable section
namespace AxiomaticGW.GKM.PlaneLineOneMarkedPoint
open EquivariantCoefficients CurveConventionCertificate

/-- The original unstable-arity request. The degree-one map has stable domain as a map. -/
def requests (k : ℕ) : SurfaceQuery .plane := ⟨0, ![1], [⟨.point, k⟩]⟩

/-- The pinned point restriction vanishes off point 1 and equals its tangent Euler class there. -/
theorem point_restriction (p : Fin 3) : SurfaceReplay.Plane.tables.restrictions p 2 =
    if p = 1 then CurveFrames.Plane.request.state.euler p else 0 := by
  rw [SurfaceReplay.Plane.accepted.restrictions_eq]
  fin_cases p
  · rfl
  · change y ^ 2 - x * y = (x - y) * -y
    ring
  · rfl

/-- The two tangent directions of the marked line at fixed point 1. -/
def direction (j : Fin 2) : Coefficient := character (CurveReplay.Plane.tables.tangent 1 j)

/-- The two signs refer to oriented tangent characters at the marked endpoint. -/
theorem directions : direction 0 = x - y ∧ direction 1 = -y := by
  constructor <;> norm_num [direction, character, CurveReplay.Plane.tables]
  ring

/-- The two equivariant flag contributions for the point lift, prior to ordinary specialization. -/
def equivariant (k : ℕ) : Coefficient :=
  (-direction 0) ^ k / (direction 1 - direction 0) +
    (-direction 1) ^ k / (direction 0 - direction 1)

/-- Degree-one plane localization factors for an edge oriented from the marked to the unmarked
endpoint. The normal bundle has degree one, so its factors are `v` and `v-u`. Both vertex
Euler factors, the marked insertion, and the two unstable source factors are retained. -/
def factors (u v eulerMarked eulerOther insertion : Coefficient) (k : ℕ) : Coefficient :=
  (-1 / u ^ 2 / (v * (v - u))) * (eulerMarked * eulerOther) * insertion *
    ((-u) ^ k / eulerMarked) * (-u / eulerOther)

/-- The literal factor product on each of three toric lines with either marked endpoint. -/
def flag (k : ℕ) (i : Fin 3) (reverse : Bool) : Coefficient :=
  let e := CurveReplay.Plane.tables.edges i
  let p := if reverse then e.target else e.source
  let q := if reverse then e.source else e.target
  let u := if reverse then -character e.weight else character e.weight
  let v := SurfaceFrames.Plane.request.tangentSum p - u
  factors u v (SurfaceFrames.Plane.request.euler p) (SurfaceFrames.Plane.request.euler q)
    (SurfaceFrames.Plane.request.restrictions p 2) k

/-- These are the three primitive degree-one lines with normal bundle of degree one. -/
theorem edge_frame : ∀ e : Fin 3, (CurveReplay.Plane.tables.edges e).curve = ![1] ∧
    (CurveReplay.Plane.tables.edges e).normalDegree = 1 := by decide +kernel

/-- Realizability of a target edge and a marked vertex image in a connected degree-one support. -/
def MarkedLine (i p : Fin 3) : Prop :=
  ∃ v e, ∃ G : FixedGraphSupport CurveReplay.Plane.tables v e, G.degree = ![1] ∧
    ∃ (a : Fin e) (m : Fin v), G.edgeIndex a = i ∧ G.image m = p

private theorem sheets {v e : ℕ} (G : FixedGraphSupport CurveReplay.Plane.tables v e)
    (hd : G.degree = ![1]) : (∑ j, (G.cover j : ℕ)) = 1 := by
  have h := congrFun hd 0
  change (∑ j, (G.cover j : ℕ) *
    (CurveReplay.Plane.tables.edges (G.edgeIndex j)).curve 0) = 1 at h
  simpa only [(edge_frame _).1, Matrix.cons_val_zero, mul_one] using h

/-- Every connected degree-one support has exactly two vertices and a single unramified edge. -/
theorem source_shape {v e : ℕ} (G : FixedGraphSupport CurveReplay.Plane.tables v e)
    (hd : G.degree = ![1]) : v = 2 ∧ e = 1 ∧ ∀ j, (G.cover j : ℕ) = 1 := by
  have nonloop : ∀ t : Fin 3, (CurveReplay.Plane.tables.edges t).source ≠
      (CurveReplay.Plane.tables.edges t).target := by decide +kernel
  obtain ⟨hv, he, h⟩ := G.shape_of_cover_sum_one (sheets G hd) fun j ↦ nonloop (G.edgeIndex j)
  exact ⟨hv, he, fun j ↦ (h j).1⟩

/-- Every realizable edge and marked fixed point determines exactly one orientation of one
of the three lines. Conversely every such mark is realized by an actual single cover. -/
theorem markedLine_iff (i p : Fin 3) : MarkedLine i p ↔ ∃! r : Bool,
    p = if r then (CurveReplay.Plane.tables.edges i).target else
      (CurveReplay.Plane.tables.edges i).source := by
  have hf : ∀ (t x : Fin 3),
      (x = (CurveReplay.Plane.tables.edges t).source ∨
        x = (CurveReplay.Plane.tables.edges t).target) ↔
      ∃! r : Bool, x = if r then (CurveReplay.Plane.tables.edges t).target else
        (CurveReplay.Plane.tables.edges t).source := by
    unfold ExistsUnique
    decide +kernel
  rw [← hf i p]
  constructor
  · rintro ⟨v, e, G, hd, a, m, rfl, rfl⟩
    obtain rfl := G.edgeCount_of_cover_sum_one (sheets G hd)
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rcases G.vertex_end_of_single m with rfl | rfl <;>
      rcases G.incident 0 with fwd | rev
    · exact Or.inl fwd.1
    · exact Or.inr rev.1
    · exact Or.inr fwd.2
    · exact Or.inl rev.2
  · intro h
    let G := FixedGraphSupport.singleCover CurveReplay.Plane.tables i 1 false
    have hd : G.degree = ![1] := by
      dsimp only [G]
      rw [FixedGraphSupport.degree_singleCover]
      change (1 : ℕ) • (CurveReplay.Plane.tables.edges i).curve = _
      rw [one_smul, (edge_frame i).1]
    rcases h with rfl | rfl
    · exact ⟨2, 1, G, hd, 0, 0, rfl, rfl⟩
    · exact ⟨2, 1, G, hd, 0, 1, rfl, rfl⟩

private theorem point_factors (u v e : Coefficient) (hu : u ≠ 0) (hv : v ≠ 0) (he : e ≠ 0)
    (hd : v - u ≠ 0) (k : ℕ) : factors u v (u * v) e (u * v) k = (-u) ^ k / (v - u) := by
  unfold factors
  field_simp

/-- Sum over all six marked ends using the pinned graph, state restrictions and edge signs.
Exactly two survive the point insertion. -/
theorem sum_flags (k : ℕ) : (∑ i : Fin 3, (flag k i false + flag k i true)) = equivariant k := by
  have hz {i : Fin 3} {r : Bool}
      (h : SurfaceFrames.Plane.request.restrictions
        (if r then (CurveReplay.Plane.tables.edges i).target else
          (CurveReplay.Plane.tables.edges i).source) 2 = 0) : flag k i r = 0 := by
    simp only [flag, factors, h, mul_zero, zero_mul]
  have h₀ : flag k 0 true = (-direction 1)^k / (direction 0 - direction 1) := by
    rw [directions.1, directions.2]
    have hu : character (CurveReplay.Plane.tables.edges 0).weight = y := by
      norm_num [character, CurveReplay.Plane.tables]
    simp only [flag, if_true, hu]
    change factors (-y) (x - 2*y - -y) ((x-y)*(-y)) (x*y) (y^2-x*y) k = _
    have hd : x-y - -y ≠ 0 := by simpa only [sub_neg_eq_add, sub_add_cancel] using x_ne_zero
    rw [show x - 2*y - -y = x-y by ring, show (x-y)*(-y) = -y*(x-y) by ring,
      show y^2-x*y = -y*(x-y) by ring]
    exact point_factors _ _ _ (neg_ne_zero.mpr y_ne_zero) x_sub_y_ne_zero
      (mul_ne_zero x_ne_zero y_ne_zero) hd k
  have h₂ : flag k 2 false = (-direction 0)^k / (direction 1 - direction 0) := by
    rw [directions.1, directions.2]
    have hu : character (CurveReplay.Plane.tables.edges 2).weight = x-y := directions.1
    simp only [flag, hu]
    change factors (x-y) (x - 2*y - (x-y)) ((x-y)*(-y)) ((-x)*(y-x)) (y^2-x*y) k = _
    have hd : -y - (x-y) ≠ 0 := by
      rw [show -y - (x-y) = -x by ring]
      exact neg_ne_zero.mpr x_ne_zero
    rw [show x - 2*y - (x-y) = -y by ring, show y^2-x*y = (x-y)*(-y) by ring]
    exact point_factors _ _ _ x_sub_y_ne_zero (neg_ne_zero.mpr y_ne_zero)
      (mul_ne_zero (neg_ne_zero.mpr x_ne_zero) y_sub_x_ne_zero) hd k
  rw [Fin.sum_univ_three, hz (i := 0) (r := false) rfl, h₀, hz (i := 1) (r := false) rfl,
    hz (i := 1) (r := true) rfl, h₂, hz (i := 2) (r := true) rfl, equivariant]
  abel

/-- Polynomial quotient of the difference of the two cotangent powers by the first character. -/
def polynomial : ℕ → Polynomial
  | 0 => 0
  | k + 1 => MvPolynomial.X 1 ^ k + (MvPolynomial.X 1 - MvPolynomial.X 0) * polynomial k

/-- With k+1 cotangent factors, the regular plane-line answer has exactly the
expected equivariant weight k. -/
theorem polynomial_homogeneous (k : ℕ) : (polynomial (k + 1)).IsHomogeneous k := by
  induction k with
  | zero =>
    simpa only [polynomial, pow_zero, mul_zero, add_zero] using
      (MvPolynomial.isHomogeneous_one (σ := Fin 2) (R := ℚ))
  | succ k ih =>
    rw [polynomial]
    apply (MvPolynomial.isHomogeneous_X_pow 1 (k + 1)).add
    simpa only [Nat.add_comm 1 k] using
      ((MvPolynomial.isHomogeneous_X ℚ (1 : Fin 2)).sub (MvPolynomial.isHomogeneous_X ℚ 0)).mul ih

private theorem clears_denominator (k : ℕ) :
    MvPolynomial.X 0 * polynomial k =
      (MvPolynomial.X 1 : Polynomial) ^ k - (MvPolynomial.X 1 - MvPolynomial.X 0) ^ k := by
  induction k with
  | zero => simp only [polynomial, mul_zero, pow_zero, sub_self]
  | succ k ih =>
    rw [polynomial, pow_succ, pow_succ, mul_add, mul_left_comm _ _ (polynomial k), ih]
    ring

/-- The cancellation is an identity in the actual two-variable fraction field for every power. -/
theorem equivariant_eq_polynomial (k : ℕ) : equivariant k = embed (polynomial k) := by
  have h := congrArg embed (clears_denominator k)
  simp only [map_mul, map_sub, map_pow, embed_X_zero, embed_X_one] at h
  rw [equivariant, directions.1, directions.2]
  have h₁ : -y - (x - y) = -x := by ring
  have h₂ : x - y - -y = x := by ring
  rw [h₁, h₂, neg_neg, neg_sub, div_neg, ← sub_eq_neg_add, ← sub_div, div_eq_iff x_ne_zero]
  rw [mul_comm, h]

/-- Every positive power gives a nonzero equivariant function, including those with zero
ordinary specialization. Evaluate the regular polynomial at (0,1) after cancellation. -/
theorem equivariant_ne_zero {k : ℕ} (hk : k ≠ 0) : equivariant k ≠ 0 := by
  have h : ∀ n : ℕ, MvPolynomial.eval₂Hom (RingHom.id ℚ) ![0, 1] (polynomial n) = (n : ℚ) := by
    intro n
    induction n with
    | zero => simp only [polynomial, map_zero, Nat.cast_zero]
    | succ n ih =>
      rw [polynomial, map_add, map_mul, map_sub, map_pow, ih, Nat.cast_succ]
      simp only [MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, one_pow, sub_zero, one_mul, add_comm]
  rw [equivariant_eq_polynomial]
  apply embed_ne_zero_of_eval _ ![0, 1]
  rw [h]
  exact_mod_cast hk

/-- The constant term of the polynomial is the ordinary one-point line descendant. -/
theorem atZero_polynomial (k : ℕ) : atZero (polynomial k) = if k = 1 then 1 else 0 := by
  cases k with
  | zero => simp only [polynomial, map_zero, Nat.zero_ne_one, if_false]
  | succ k =>
    rw [polynomial, map_add, map_mul, map_sub, map_pow]
    simp only [atZero, MvPolynomial.eval₂Hom_X', Pi.zero_apply, sub_self, zero_mul, add_zero]
    cases k <;> simp

/-- The complete two-flag sum has a unique ordinary value at every descendant power. -/
theorem specializes (k : ℕ) : Specializes (equivariant k) (if k = 1 then 1 else 0) := by
  rw [← atZero_polynomial]
  exact specializes_of_eq_polynomial _ (equivariant_eq_polynomial k)

end AxiomaticGW.GKM.PlaneLineOneMarkedPoint

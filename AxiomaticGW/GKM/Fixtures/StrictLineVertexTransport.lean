/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.StrictLineCoverTransport
public import AxiomaticGW.GKM.Fixtures.ExceptionalGenusTwoVertexTransport

/-! # Stable genus-two and unstable rational vertices over the strict-line edge

The marking powers and the degree of each individual flag are retained. The stable
formula compares Hodge coefficients before imposing numerical Hodge seeds. The
three unstable cases use the pinned producer's surface Euler denominator.
-/

@[expose] public section
namespace AxiomaticGW.GKM.StrictLineVertexTransport
open EquivariantCoefficients CurveConventionCertificate
open StrictLineCoverTransport GenusTwoVertexHodgeReduction GenusTwoLocalizationVertex
open ExceptionalGenusTwoVertexTransport (atEndpoint)
open ExceptionalCoverFactors (tangent)
open CurveReplay.OneBlowup renaming tables → f1
open CurveReplay.TwoBlowups renaming tables → bl2
open SurfaceFrames.OneBlowup renaming request → oneFrame
open SurfaceFrames.TwoBlowups renaming request → twoFrame
noncomputable section

/-- The direction of the outgoing flag is taken at this endpoint, with its own sheet number. -/
def flag {X : SurfaceTarget} {v e : ℕ} (t : Tables X v e) (k : Fin e) (last : Bool)
    (sheets : ℕ+) : Coefficient :=
  (if last then -character (t.edges k).weight else character (t.edges k).weight) / sheets.val

theorem flag_transport (last : Bool) (sheets : ℕ+) :
    field (flag f1 2 last sheets) = flag bl2 3 last sheets := by
  cases last <;> simp only [flag, Bool.false_eq_true, ↓reduceIte, map_div₀, map_natCast,
    map_neg, field_character, local_weights.1]

/-- The actual tangent Euler class at the chosen fixed point. -/
def euler {X : SurfaceTarget} {v e : ℕ} (t : Tables X v e) (k : Fin e) (last : Bool) :
    Coefficient :=
  ExceptionalCoverFactors.tangent t (if last then (t.edges k).target else (t.edges k).source) 1

theorem euler_transport (last : Bool) : field (euler f1 2 last) = euler bl2 3 last := by
  cases last
  · exact (endpoint_tangents 1).1
  · exact (endpoint_tangents 1).2

/-- Tangent branches in the pinned order at both strict-line endpoints. -/
theorem branches : let a := bl2.edges 3
    character (bl2.tangent a.source 0) = x ∧ character (bl2.tangent a.source 1) = y-x ∧
    character (bl2.tangent a.target 0) = y ∧ character (bl2.tangent a.target 1) = -x := by
  have h : let a := bl2.edges 3
      bl2.tangent a.source 0 = a.weight ∧
      bl2.tangent a.source 1 = edgeWeight bl2 a.source a.normalSource ∧
      bl2.tangent a.target 0 = edgeWeight bl2 a.target a.normalTarget ∧
      bl2.tangent a.target 1 = -a.weight := by decide +kernel
  have hn (w : Fin 2 → ℤ) : character (-w) = -character w := by
    simp only [character, Pi.neg_apply, Int.cast_neg]
    ring
  dsimp only
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2, hn, line_characters.1,
    line_characters.2.1, line_characters.2.2]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Numerical tangent normalization in the native source and target order. -/
theorem tangent_values (k : ℕ) :
    tangent bl2 (bl2.edges 3).source k = x^k*(y-x)^k ∧
    tangent bl2 (bl2.edges 3).target k = y^k*(-x)^k := by
  simp only [tangent, Fin.prod_univ_two, branches.1, branches.2.1, branches.2.2.1, branches.2.2.2,
    and_self]

/-- Neither unstable endpoint Euler denominator vanishes in the localization field. -/
theorem euler_ne_zero (last : Bool) : euler bl2 3 last ≠ 0 := by
  cases last
  · change ExceptionalCoverFactors.tangent bl2 (bl2.edges 3).source 1 ≠ 0
    rw [(tangent_values 1).1, pow_one, pow_one]
    exact mul_ne_zero x_ne_zero y_sub_x_ne_zero
  · change ExceptionalCoverFactors.tangent bl2 (bl2.edges 3).target 1 ≠ 0
    rw [(tangent_values 1).2, pow_one, pow_one]
    exact mul_ne_zero y_ne_zero (neg_ne_zero.mpr x_ne_zero)

/-- Both outgoing weights at a rational node have the same direction and positive sheet numbers. -/
theorem node_flag_sum_ne_zero (last : Bool) (a b : ℕ+) :
    flag bl2 3 last a + flag bl2 3 last b ≠ 0 := by
  let w : Coefficient := if last then -x else x
  have hw : w ≠ 0 := by cases last <;> first | exact x_ne_zero | exact neg_ne_zero.mpr x_ne_zero
  have ha : (a.val : Coefficient) ≠ 0 := Nat.cast_ne_zero.mpr a.ne_zero
  have hb : (b.val : Coefficient) ≠ 0 := Nat.cast_ne_zero.mpr b.ne_zero
  have hsum : (a.val : Coefficient) + (b.val : Coefficient) ≠ 0 := by
    rw [← Nat.cast_add]
    exact Nat.cast_ne_zero.mpr (by have := a.pos; omega)
  simp only [flag, line_characters.1]
  change w / a.val + w / b.val ≠ 0
  rw [div_add_div _ _ ha hb]
  apply div_ne_zero _ (mul_ne_zero ha hb)
  rw [mul_comm (a.val : Coefficient) w, ← mul_add, add_comm]
  exact mul_ne_zero hw hsum

/-- The complete stable source factor for an arbitrary ordered rational Hodge coefficient table. -/
def sourceAtEndpoint {X : SurfaceTarget} {v e f : ℕ} (t : Tables X v e) (k : Fin e)
    (last : Bool) (sheets : Fin f → ℕ+) (marks : List ℕ)
    (H : (a b : Fin 3) → a ≤ b → List ℕ → ℚ) : Coefficient :=
  let edge := t.edges k
  let p := if last then edge.target else edge.source
  source H marks (character (t.tangent p 0)) (character (t.tangent p 1))
    (fun j ↦ flag t k last (sheets j))

/-- The top-degree Hodge and flag terms transport for arbitrary valence, marks and sheet numbers. -/
theorem source_transport {f : ℕ} (last : Bool) (sheets : Fin f → ℕ+) (marks : List ℕ)
    (H : (a b : Fin 3) → a ≤ b → List ℕ → ℚ) :
    field (sourceAtEndpoint f1 2 last sheets marks H) =
      sourceAtEndpoint bl2 3 last sheets marks H := by
  have ht := local_weights.2.2.2.2.2
  change field.toRingHom _ = _
  cases last <;>
    simp only [sourceAtEndpoint, Bool.false_eq_true, ↓reduceIte, map_source,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, flag_transport, field_character,
      (ht 0).1, (ht 1).1, (ht 0).2, (ht 1).2]
  exact swap _ _ _ _ _

/-- In particular the two pinned surfaces give the same transported eight-seed stable vertex. -/
theorem stable {f : ℕ} (last : Bool) (sheets : Fin f → ℕ+) (marks : List ℕ) (seed : ↥seeds → ℚ) :
    field (atEndpoint f1 2 last sheets marks seed) = atEndpoint bl2 3 last sheets marks seed :=
  source_transport last sheets marks (evaluate seed)

/-- With the original Hodge recurrence and seed hypotheses the same vertex computes that source. -/
theorem stable_of_hodge {f : ℕ} (last : Bool) (sheets : Fin f → ℕ+) (marks : List ℕ)
    (seed : ↥seeds → ℚ) (H : (a b : Fin 3) → a ≤ b → List ℕ → ℚ)
    (laws : ∀ (a b : Fin 3) (h : a ≤ b), Recurrences a b (H a b h))
    (hseed : ∀ (a b : Fin 3) (h : a ≤ b), ∀ p (hk : (a.val, b.val, p) ∈ seeds),
      seed ⟨_, hk⟩ = H a b h p) :
    field (atEndpoint f1 2 last sheets marks seed) = sourceAtEndpoint bl2 3 last sheets marks H :=
  (stable last sheets marks seed).trans (reduced_eq_source seed H laws hseed _ _ _ _)

/-- Affine state lifts multiply the transported stable source at the same marked endpoint. -/
theorem marked_stable {n f : ℕ} (last : Bool) (sheets : Fin f → ℕ+) (states : Fin n → Fin 5)
    (powers : Fin n → ℕ) (seed : ↥seeds → ℚ) :
    let a := f1.edges 2; let b := bl2.edges 3
    let p := if last then a.target else a.source
    let q := if last then b.target else b.source
    (∏ j, twoFrame.restrictions q (states j)) *
      atEndpoint bl2 3 last sheets (List.ofFn powers) seed =
      (∏ j, lift (field ∘ oneFrame.restrictions p) (states j)) *
        field (atEndpoint f1 2 last sheets (List.ofFn powers) seed) := by
  dsimp only
  rw [stable]
  apply congrArg (· * atEndpoint bl2 3 last sheets (List.ofFn powers) seed)
  apply Finset.prod_congr rfl
  intro j _
  cases last
  · exact congrFun (insertion_transport 0) (states j)
  · exact congrFun (insertion_transport 1) (states j)

/-- The three unstable genus-zero cases in positive covered-edge localization. -/
inductive Unstable where
  | unmarkedEnd (sheets : ℕ+)
  | markedEnd (sheets : ℕ+) (power : ℕ)
  | unmarkedNode (first second : ℕ+)

/-- In the marked rational end the cotangent insertion uses the negative outgoing weight. -/
def unstable {X : SurfaceTarget} {v e : ℕ} (t : Tables X v e) (k : Fin e)
    (last : Bool) (u : Unstable) : Coefficient :=
  (match u with
   | .unmarkedEnd d => flag t k last d
   | .markedEnd d a => (-flag t k last d)^a
   | .unmarkedNode d₁ d₂ => (flag t k last d₁ + flag t k last d₂)⁻¹) / euler t k last

/-- Both univalent conventions and the rational node transport with their Euler factors. -/
theorem unstable_transport (last : Bool) (u : Unstable) :
    field (unstable f1 2 last u) = unstable bl2 3 last u := by
  cases u <;> simp only [unstable, map_div₀, map_pow, map_neg, map_inv₀, map_add,
    flag_transport, euler_transport]

end
end AxiomaticGW.GKM.StrictLineVertexTransport

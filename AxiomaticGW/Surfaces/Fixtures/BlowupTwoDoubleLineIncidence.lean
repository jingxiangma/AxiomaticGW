/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.Incidence
public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.GraphSupport
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineOneMarking

/-! # Point incidence for rational and elliptic vertices along the pure strict line

On 0, L and 2L the initial primary tables force a vertex carrying the point class to have degree
zero with only unit classes at the other markings. This constraint survives dual-node gluing
and the genus-zero and genus-one cotangent recursions, at every valence and all powers.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleLineIncidence
open BlowupTwoExceptionalIncidence (X Label Profile tag data profile profile_option profile_relabel
  profile_ordered profile_ofLabels profile_sum split_bound_of_le)
open BlowupTwoDoubleLine (curve)
open SurfaceLowGenusPointCache SurfacePointBenchmarkCache

/-- A point can occur only at zero line degree, accompanied by unit classes. -/
def Fits (b : X.Curve) (p : Profile) : Prop :=
  p 0 = 0 ∨ (b 2 = 0 ∧ p 0 = 1 ∧ p 1 = 0 ∧ p 2 = 0 ∧ p 3 = 0)

instance (b : X.Curve) (p : Profile) : Decidable (Fits b p) := by unfold Fits; infer_instance

private theorem fits_closed {b : X.Curve} {p q : Profile} (h : p ≤ q) (hq : Fits b q) :
    Fits b p := by
  have h₀ : p 0 ≤ q 0 := h 0
  have h₁ : p 1 ≤ q 1 := h 1
  have h₂ : p 2 ≤ q 2 := h 2
  have h₃ : p 3 ≤ q 3 := h 3
  unfold Fits at *
  omega

private theorem fits_join (c d : X.Curve) (p q : Profile) (b : Label)
    (h₁ : Fits c (p + tag b)) (h₂ : Fits d (q + tag b.dual)) :
    Fits (c + d) (p + q) := by
  have cases : ∀ a : Label, a = .unit ∨ a = .hyperplane ∨ a = .exceptional 0 ∨
      a = .exceptional 1 ∨ a = .point := by decide +kernel
  rcases cases b with rfl | rfl | rfl | rfl | rfl <;>
    simp [Fits, SurfaceBasisLabel.dual, tag, Pi.add_apply] at * <;> omega

private theorem zero_product {c d : X.Curve}
    (p q : Profile) (b : Label) {l r : ℚ}
    (hl : ¬Fits c (p + tag b) → l = 0) (hr : ¬Fits d (q + tag b.dual) → r = 0)
    (hz : ¬Fits (c+d) (p+q)) : l*r = 0 := by
  by_cases hx : Fits c (p + tag b)
  · rw [hr (fun hy ↦ hz (fits_join c d p q b hx hy)), mul_zero]
  · rw [hl hx, zero_mul]

/-- Arbitrary node and marking cotangent decorations preserve point incidence in a coordinate
box on which every vertex obeys the incidence vanishing condition. -/
private theorem decorated_graph_zero {bound : X.Curve} (v : SurfaceVertexValues X ℚ)
    (hv : ∀ g S [Fintype S] (h : StableArity g S) b k a, b ≤ bound →
       ¬Fits b (profile a) → v g S h b k a = 0)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (d : x.CotangentDecoration)
    (b : X.Curve) (k : S → ℕ) (a : S → Label) (hb : b ≤ bound) (hz : ¬Fits b (profile a)) :
    x.surfaceDecoratedEval X v d b k a = 0 := by
  induction x generalizing b with
  | fundamental g S h => exact hv g S h b (k + d) a hb hz
  | relabel e x ih => exact ih d b (k ∘ e) (a ∘ e) hb (profile_relabel e a ▸ hz)
  | separating x y ihx ihy =>
    unfold GluingExpression.surfaceDecoratedEval
    apply Finset.sum_eq_zero
    intro t ht
    have hs : t.1+t.2 = b := by
      rw [X.splittings_eq] at ht
      exact (X.effective.mem_splittings _ _ _).mp ht
    obtain ⟨h₁,h₂⟩ := split_bound_of_le hb hs
    apply Finset.sum_eq_zero
    intro u _
    apply mul_eq_zero_of_right
    apply zero_product (profile (a ∘ Sum.inl)) (profile (a ∘ Sum.inr)) u
    · intro hbad
      apply ihx d.1 t.1 _ _ h₁
      rwa [profile_option]
    · intro hbad
      apply ihy d.2 t.2 _ _ h₂
      rwa [profile_option]
    · rwa [hs, profile_sum]
  | nonseparating x ih =>
    unfold GluingExpression.surfaceDecoratedEval
    apply Finset.sum_eq_zero
    intro u _
    apply mul_eq_zero_of_right
    apply ih d b _ _ hb
    intro hx
    rw [profile_option, profile_option] at hx
    exact hz (fits_closed (fun j ↦ by simp only [Pi.add_apply]; omega) hx)

/-- Incidence on an undecorated graph follows by taking zero node decoration. -/
private theorem graph_zero_of_le {bound : X.Curve} (v : SurfaceVertexValues X ℚ)
    (hv : ∀ g S [Fintype S] (h : StableArity g S) b k a, b ≤ bound →
       ¬Fits b (profile a) → v g S h b k a = 0)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (b : X.Curve) (k : S → ℕ) (a : S → Label) (hb : b ≤ bound) (hz : ¬Fits b (profile a)) :
    x.surfaceEval X v b k a = 0 := by
  rw [← GluingExpression.surfaceDecoratedEval_zeroDecoration]
  exact decorated_graph_zero v hv x x.zeroDecoration b k a hb hz


private theorem classes (b : X.Curve) (hb : b ≤ curve) :
    b = 0 ∨ b = ![0, 0, 1] ∨ b = curve := by
  have hx : b 0 = 0 := Nat.eq_zero_of_le_zero (hb 0)
  have hy : b 1 = 0 := Nat.eq_zero_of_le_zero (hb 1)
  have hz : b 2 ≤ 2 := hb 2
  have h : b = ![0, 0, b 2] := by funext i; fin_cases i <;> first | rfl | assumption
  rw [h]
  interval_cases b 2 <;> decide +kernel

private theorem classical_good : ∀ a b c : Label, SurfacePrimary.classicalValue {a,b,c} ≠ 0 →
    Fits 0 (data {a,b,c}) := by decide +kernel

private theorem rational_primary_zero (q : SurfaceAncestorKey X) (hb : q.beta ≤ curve)
    (hz : ¬Fits q.beta (data q.primaryLabels)) :
    rationalPrimary X (genusZero X) q.beta q.primaryLabels = 0 := by
  rcases classes q.beta hb with h | h | h
  · rw [h] at hz ⊢
    change (if (0 : X.Curve) = 0 then _ else _) = 0
    rw [if_pos rfl]
    by_contra hu
    have hc : q.primaryLabels.card = 3 := by
      by_contra hn
      exact hu (if_neg hn)
    obtain ⟨a,b,c,hc⟩ := Multiset.card_eq_three.mp hc
    rw [hc] at hu hz
    exact hz (classical_good a b c hu)
  · rw [h] at hz ⊢
    have hp : q.primaryLabels.count .point ≠ 0 := fun h₀ ↦ hz (Or.inl h₀)
    simp only [rationalPrimary, show (![0,0,1] : X.Curve) ≠ 0 by decide +kernel, if_false,
      show X.effective.energy (![0,0,1] : X.Curve) - 1 = 0 by decide +kernel, hp]
  · rw [h] at hz ⊢
    simp [rationalPrimary, show curve ≠ 0 by decide +kernel,
      show genusZero X curve = 0 by decide +kernel]

private theorem elliptic_primary_zero (q : SurfaceAncestorKey X) (hb : q.beta ≤ curve)
    (hz : ¬Fits q.beta (data q.primaryLabels)) :
    ellipticPrimary X (genusOne X) q.beta q.primaryLabels = 0 := by
  rcases classes q.beta hb with h | h | h
  · rw [h] at hz ⊢
    by_contra hu
    have hc : q.primaryLabels.card = 1 := by
      by_contra hn
      exact hu (by simp only [ellipticPrimary, ite_true,
          SurfacePrimary.genusOneZeroValue, if_neg hn])
    obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hc
    rw [ha] at hz
    exact hz ((by decide +kernel : ∀ a : Label, Fits 0 (data {a})) a)
  · rw [h]
    simp [ellipticPrimary, show (![0,0,1] : X.Curve) ≠ 0 by decide +kernel,
      show genusOne X (![0,0,1] : X.Curve) = 0 by decide +kernel]
  · rw [h]
    simp [ellipticPrimary, show curve ≠ 0 by decide +kernel,
      show genusOne X curve = 0 by decide +kernel]

private theorem rational_zero (n : ℕ) (q : SurfaceAncestorKey X) (hb : q.beta ≤ curve)
    (hz : ¬Fits q.beta (data q.primaryLabels)) : rationalFuel X (genusZero X) n q = 0 := by
  induction n generalizing q with
  | zero => simp only [rationalFuel, rational_primary_zero q hb hz, ite_self]
  | succ n ih =>
    rw [rationalFuel]
    split_ifs with hg hprim
    · exact rational_primary_zero q hb hz
    · unfold SurfaceGenusZero.ancestorStep
      apply List.sum_eq_zero
      intro z h
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp h
      apply mul_eq_zero_of_right
      apply graph_zero_of_le
      · intro g S _ h b k a hbound hbad
        exact ih (SurfaceAncestorKey.ofLabels g S h b k a) hbound (by rwa [profile_ofLabels])
      · exact hb
      · rwa [profile_relabel, profile_ordered]
    · rfl

private theorem elliptic_zero (n : ℕ) (q : SurfaceAncestorKey X) (hb : q.beta ≤ curve)
    (hz : ¬Fits q.beta (data q.primaryLabels)) :
    ellipticFuel X (genusZero X) (genusOne X) n q = 0 := by
  induction n generalizing q with
  | zero => simp only [ellipticFuel, elliptic_primary_zero q hb hz, ite_self]
  | succ n ih =>
    rw [ellipticFuel]
    split_ifs with hg hprim
    · exact elliptic_primary_zero q hb hz
    · unfold ellipticStep
      apply List.sum_eq_zero
      intro z h
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp h
      apply mul_eq_zero_of_right
      apply graph_zero_of_le
      · intro g S _ h b k a hbound hbad
        dsimp only
        split_ifs
        · apply rational_zero _ _ hbound
          rwa [profile_ofLabels]
        · apply ih _ hbound
          rwa [profile_ofLabels]
      · exact hb
      · rwa [profile_relabel, profile_ordered]
    · rfl

/-- Arbitrary cotangent powers and marking multiplicities on rational and elliptic vertices
obey the same necessary incidence constraint as the primary tables. -/
theorem component_zero (q : SurfaceAncestorKey X) (hb : q.beta ≤ curve)
    (hz : ¬Fits q.beta (data q.primaryLabels)) :
    SurfaceLowGenusPointCache.componentValue X (genusZero X) (genusOne X) q = 0 := by
  unfold SurfaceLowGenusPointCache.componentValue
  split_ifs
  · exact rational_zero _ _ hb hz
  · exact elliptic_zero _ _ hb hz

open SurfaceGenusTwoPositiveSquare

/-- Short-circuit a certified lower-genus evaluator whenever strict-line point incidence
has already proved the full vertex zero. Other vertices retain their original evaluator. -/
def withPointSupport (c : CertifiedComponents X) : CertifiedComponents X where
  value q := if ¬Fits q.beta (data q.primaryLabels) ∧ (∀ i : Fin 3, q.beta i ≤ curve i)
    then 0 else c.value q
  sound q := by
    split
    next h =>
      rw [pointCoordinateComponent, coordinateComponent_eq]
      exact (component_zero q h.2 h.1).symm
    exact c.sound q

/-- Test class and cohomology support along the pure strict line at any cotangent degree. -/
def vertexZero (next : SurfaceAncestorKey X → ℚ) : SurfaceCotangentVertexValues X Bool :=
  fun g S _ h d _ beta a ↦
    let q := SurfaceAncestorKey.ofLabels g S h beta d a
    if q.DimensionCompatible then
      if g ≤ 1 then
        decide ((∀ i : Fin 3, beta i ≤ curve i) ∧ ¬Fits beta (data q.primaryLabels))
      else decide (beta 2 ≤ 1 ∧ q.totalPsi ≤ 1) && (next q == 0)
    else true

theorem vertexZero_sound (c : CertifiedComponents X) (next : SurfaceAncestorKey X → ℚ)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (d : S → ℕ) (l : DecidableEq S)
    (beta : X.Curve) (a : S → SurfaceBasisLabel X) :
    vertexZero next g S h d l beta a = true → c.vertex next g S h beta d a = 0 := by
  let q := SurfaceAncestorKey.ofLabels g S h beta d a
  unfold vertexZero CertifiedComponents.vertex
  by_cases hd : q.DimensionCompatible
  · by_cases hg : g ≤ 1
    · simp only [show (SurfaceAncestorKey.ofLabels g S h beta d a) = q from rfl, if_pos hd,
        if_pos hg, decide_eq_true_eq]
      intro hzero
      rw [c.sound, pointCoordinateComponent, coordinateComponent_eq]
      exact component_zero q hzero.1 hzero.2
    · simp only [show (SurfaceAncestorKey.ofLabels g S h beta d a) = q from rfl, if_pos hd,
        if_neg hg, Bool.and_eq_true]
      exact fun hz ↦ eq_of_beq hz.2
  · simp only [show (SurfaceAncestorKey.ofLabels g S h beta d a) = q from rfl,
      if_neg hd, implies_true]

end AxiomaticGW.BlowupTwoDoubleLineIncidence

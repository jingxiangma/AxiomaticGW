/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PointPullbackContraction
public import AxiomaticGW.Surfaces.AncestorMarkings
public import AxiomaticGW.Surfaces.DecoratedGluingEvaluation

/-! # Incidence of components on the two exceptional curves of the two-point blowup

A degree-zero component with divisors uses one divisor class, and a point pairs only with
units. Positive degree on either exceptional curve permits only that divisor and units.
The signed diagonal preserves this support at every separating and nonseparating node.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoExceptionalIncidence
/-- The two-point blowup whose two exceptional directions define this incidence test. -/
abbrev X := SurfaceTarget.blowupTwo
/-- The five homogeneous basis labels on the two-point blowup. -/
abbrev Label := SurfaceBasisLabel X
/-- Counts of the point, hyperplane and two exceptional basis labels. -/
abbrev Profile := Fin 4 → ℕ
/-- The four coordinates count points, hyperplanes and the two exceptional divisors. -/
def tag : Label → Profile
  | .unit => 0
  | .point => ![1,0,0,0]
  | .hyperplane => ![0,1,0,0]
  | .exceptional j => if j = 0 then ![0,0,1,0] else ![0,0,0,1]

/-- Record the incidence counts of a multiset of basis labels. -/
def data (m : Multiset Label) : Profile :=
  ![m.count .point, m.count .hyperplane, m.count (.exceptional 0), m.count (.exceptional 1)]

/-- Sum the incidence counts over all named markings. -/
def profile {S : Type} [Fintype S] (a : S → Label) : Profile := ∑ s, tag (a s)

/-- On the plane-degree-zero face, the nonunit labels and positive curve class must lie on
one support. The remaining possibility is a single point and otherwise units in class zero. -/
def Allowed (c : X.Curve) (p : Profile) : Prop :=
  (p 0 = 0 ∧ c 0 = 0 ∧ c 1 = 0 ∧ p 2 = 0 ∧ p 3 = 0) ∨
  (p 0 = 0 ∧ c 1 = 0 ∧ p 1 = 0 ∧ p 3 = 0) ∨
  (p 0 = 0 ∧ c 0 = 0 ∧ p 1 = 0 ∧ p 2 = 0) ∨
  (p 0 = 1 ∧ c 0 = 0 ∧ c 1 = 0 ∧ p 1 = 0 ∧ p 2 = 0 ∧ p 3 = 0)

theorem closed_of_le {c : X.Curve} {p q : Profile} (h : p ≤ q) (hq : Allowed c q) :
    Allowed c p := by
  have h₀ : p 0 ≤ q 0 := h 0
  have h₁ : p 1 ≤ q 1 := h 1
  have h₂ : p 2 ≤ q 2 := h 2
  have h₃ : p 3 ≤ q 3 := h 3
  rcases hq with ⟨ha,hb,hc,hd,he⟩ | ⟨ha,hb,hc,hd⟩ | ⟨ha,hb,hc,hd⟩ | ⟨ha,hb,hc,hd,he,hf⟩
  · exact Or.inl ⟨by omega,hb,hc,by omega,by omega⟩
  · exact Or.inr (Or.inl ⟨by omega,hb,by omega,by omega⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by omega,hb,by omega,by omega⟩))
  · by_cases hp : p 0 = 0
    · exact Or.inl ⟨hp,hb,hc,by omega,by omega⟩
    · exact Or.inr (Or.inr (Or.inr ⟨by omega,hb,hc,by omega,by omega,by omega⟩))

private theorem label_cases : ∀ b : Label, b = .unit ∨ b = .point ∨ b = .hyperplane ∨
    b = .exceptional 0 ∨ b = .exceptional 1 := by decide +kernel

/-- A contracted label and its dual can connect two allowed profiles only when their union
is allowed. In particular, every contraction across the two exceptional supports vanishes. -/
theorem join (c d : X.Curve) (p q : Profile) (b : Label)
    (h₁ : Allowed c (p + tag b)) (h₂ : Allowed d (q + tag b.dual)) :
    Allowed (c+d) (p+q) := by
  rcases label_cases b with rfl | rfl | rfl | rfl | rfl <;>
    simp [Allowed, SurfaceBasisLabel.dual, tag, Pi.add_apply] at * <;> omega

theorem profile_option {S : Type} [Fintype S] (a : S → Label) (b : Label) :
    profile (Option.elim · b a) = profile a + tag b := by
  simp only [profile, Fintype.sum_option, Option.elim_none, Option.elim_some, add_comm]

theorem profile_relabel {S T : Type} [Fintype S] [Fintype T]
    (e : S ≃ T) (a : T → Label) : profile (a ∘ e) = profile a :=
  e.sum_comp (fun t ↦ tag (a t))

theorem profile_sum {S T : Type} [Fintype S] [Fintype T] (a : S ⊕ T → Label) :
    profile (a ∘ Sum.inl) + profile (a ∘ Sum.inr) = profile a := by
  simp only [profile, Function.comp_def, Fintype.sum_sum_type]

theorem profile_multiset (m : Multiset Label) : (m.map tag).sum = data m := by
  induction m using Multiset.induction with
  | empty => funext i; fin_cases i <;> rfl
  | cons a m ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih]
    cases a with
    | unit | hyperplane | point =>
      funext i
      fin_cases i <;> simp [data, tag] <;> omega
    | exceptional j =>
      fin_cases j <;> funext i <;> fin_cases i <;> simp [data, tag] <;> omega

theorem profile_external {S : Type} [Fintype S] (a : S → Label) :
    data (Finset.univ.val.map a) = profile a := by
  rw [← profile_multiset, Multiset.map_map]
  rfl

theorem profile_ofLabels (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (c : X.Curve) (k : S → ℕ) (a : S → Label) :
    data (SurfaceAncestorKey.ofLabels g S h c k a).primaryLabels = profile a := by
  change data ((Finset.univ.val.map (fun t ↦ SurfaceInsertion.mk (a t) (k t))).map
    SurfaceInsertion.label) = _
  rw [Multiset.map_map]
  exact profile_external a

theorem profile_ordered (q : SurfaceAncestorKey X) :
    profile q.orderedLabels = data q.primaryLabels := by
  rw [← profile_ofLabels q.genus _ q.ordered_stable q.beta q.orderedPowers q.orderedLabels,
    q.of_ordered_eq]


instance (c : X.Curve) (u : Profile) : Decidable (Allowed c u) := by unfold Allowed; infer_instance
/-- The coordinate box of the mixed exceptional class. -/
def cap : X.Curve := ![1,1,0]

/-- Both effective summands of a class in a coordinate box lie in the same box. -/
theorem split_bound_of_le {bound beta : X.Curve} (hb : beta ≤ bound) {l r : X.Curve}
    (hs : l + r = beta) : l ≤ bound ∧ r ≤ bound := by
  have he (k : Fin 3) : l k + r k = beta k := congrFun hs k
  exact ⟨fun k ↦ (Nat.le_add_right (l k) (r k)).trans ((he k).le.trans (hb k)),
    fun k ↦ (Nat.le_add_left (r k) (l k)).trans ((he k).le.trans (hb k))⟩

theorem split_bound {beta : X.Curve} (hb : beta ≤ cap) {l r : X.Curve} (hs : l + r = beta) :
    l ≤ cap ∧ r ≤ cap := split_bound_of_le hb hs

private theorem zero_product {c d : X.Curve}
    (p q : Profile) (b : Label) {l r : ℚ}
    (hl : ¬Allowed c (p + tag b) → l = 0) (hr : ¬Allowed d (q + tag b.dual) → r = 0)
    (hz : ¬Allowed (c+d) (p+q)) : l*r = 0 := by
  by_cases hx : Allowed c (p + tag b)
  · rw [hr (fun hy ↦ hz (join c d p q b hx hy)), mul_zero]
  · rw [hl hx, zero_mul]

/-- Arbitrary node and marking cotangent decorations preserve incidence in any coordinate
box on which every vertex obeys the incidence vanishing condition. -/
theorem decorated_graph_zero {bound : X.Curve} (v : SurfaceVertexValues X ℚ)
    (hv : ∀ g S [Fintype S] (h : StableArity g S) b k a, b ≤ bound →
       ¬Allowed b (profile a) → v g S h b k a = 0)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (d : x.CotangentDecoration)
    (b : X.Curve) (k : S → ℕ) (a : S → Label) (hb : b ≤ bound) (hz : ¬Allowed b (profile a)) :
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
    exact hz (closed_of_le (fun j ↦ by simp only [Pi.add_apply]; omega) hx)

/-- Incidence on an undecorated graph follows by taking zero node decoration. -/
theorem graph_zero_of_le {bound : X.Curve} (v : SurfaceVertexValues X ℚ)
    (hv : ∀ g S [Fintype S] (h : StableArity g S) b k a, b ≤ bound →
       ¬Allowed b (profile a) → v g S h b k a = 0)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (b : X.Curve) (k : S → ℕ) (a : S → Label) (hb : b ≤ bound) (hz : ¬Allowed b (profile a)) :
    x.surfaceEval X v b k a = 0 := by
  rw [← GluingExpression.surfaceDecoratedEval_zeroDecoration]
  exact decorated_graph_zero v hv x x.zeroDecoration b k a hb hz

/-- Transfer incidence vanishing through any ordinary decorated surface evaluation. -/
theorem graph_zero (v : SurfaceVertexValues X ℚ)
    (hv : ∀ g S [Fintype S] (h : StableArity g S) b k a, b ≤ cap →
       ¬Allowed b (profile a) → v g S h b k a = 0)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (b : X.Curve) (k : S → ℕ) (a : S → Label) (hb : b ≤ cap) (hz : ¬Allowed b (profile a)) :
    x.surfaceEval X v b k a = 0 :=
  graph_zero_of_le v hv x b k a hb hz

end AxiomaticGW.BlowupTwoExceptionalIncidence

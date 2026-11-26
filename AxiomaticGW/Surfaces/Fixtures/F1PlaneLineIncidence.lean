/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PointPullbackContraction
public import AxiomaticGW.Surfaces.AncestorMarkings

/-! # Incidence support for degree at most one on the one-point blowup

The point, hyperplane, and exceptional multiplicities give a necessary condition on
a component of effective class at most 2E+F. The dual diagonal pairs propagate
that condition through separating edges, loops, and signed point pullback.
-/

@[expose] public section
namespace AxiomaticGW.F1PlaneLineIncidence
abbrev X := SurfaceTarget.hirzebruchOne
abbrev Label := SurfaceBasisLabel X
abbrev Profile := Fin 3 → ℕ
/-- Counts are ordered as points, hyperplanes, and exceptionals. Units impose no incidence. -/
def tag : Label → Profile
  | .unit => ![0,0,0]
  | .hyperplane => ![0,1,0]
  | .exceptional _ => ![0,0,1]
  | .point => ![1,0,0]
def data (m : Multiset Label) : Profile :=
  ![m.count .point, m.count .hyperplane, m.count (.exceptional 0)]
def profile {S : Type} [Fintype S] (a : S → Label) : Profile := ∑ s, tag (a s)
/-- In class zero, a point excludes every additional positive-codimension insertion, and
hyperplanes and exceptionals cannot meet. A nonzero exceptional class admits only exceptional
or unit insertions. Two points on a plane-degree-one curve require class H and exclude E. -/
def Allowed (c : X.Curve) (u : Profile) : Prop :=
  (c 1 = 0 ∧ c 0 = 0 ∧
    ((u 0 = 0 ∧ (u 1 = 0 ∨ u 2 = 0)) ∨ (u 0 = 1 ∧ u 1 = 0 ∧ u 2 = 0))) ∨
  (c 1 = 0 ∧ c 0 ≠ 0 ∧ u 0 = 0 ∧ u 1 = 0) ∨
  (0 < c 1 ∧ (u 0 ≤ 1 ∨ (c 0 = 1 ∧ u 0 = 2 ∧ u 2 = 0)))
theorem closed_of_le {c : X.Curve} {p q : Profile} (h : p ≤ q) (hq : Allowed c q) :
    Allowed c p := by
  have h₀ : p 0 ≤ q 0 := h 0
  have h₁ : p 1 ≤ q 1 := h 1
  have h₂ : p 2 ≤ q 2 := h 2
  rcases hq with ⟨hc,hd,hq⟩ | ⟨hc,hd,ha,hb⟩ | ⟨hc,hq⟩
  · refine Or.inl ⟨hc,hd,?_⟩
    rcases hq with ⟨h₃,h₄ | h₄⟩ | ⟨h₃,h₄,h₅⟩
    · exact Or.inl ⟨by omega, Or.inl (by omega)⟩
    · exact Or.inl ⟨by omega, Or.inr (by omega)⟩
    · by_cases hp : p 0 = 0
      · exact Or.inl ⟨hp, Or.inl (by omega)⟩
      · exact Or.inr ⟨by omega, by omega, by omega⟩
  · exact Or.inr (Or.inl ⟨hc,hd,by omega,by omega⟩)
  · refine Or.inr (Or.inr ⟨hc,?_⟩)
    rcases hq with hq | ⟨he,ha,hd⟩
    · exact Or.inl (by omega)
    · by_cases hp : p 0 ≤ 1
      · exact Or.inl hp
      · exact Or.inr ⟨he,by omega, by omega⟩

/-- Contraction against a dual node pair preserves these constraints. Each side may
carry a different full class and arbitrary cotangent powers. -/
theorem join (c d : X.Curve) (hc : c 1 + d 1 ≤ 1) (p q : Profile) (b : Label)
    (h₁ : Allowed c (p + tag b)) (h₂ : Allowed d (q + tag b.dual)) :
    Allowed (c+d) (p+q) := by
  rcases h₁ with ⟨_,_,⟨_,_ | _⟩ | ⟨_,_,_⟩⟩ | ⟨_,_,_,_⟩ | ⟨_,_ | ⟨_,_,_⟩⟩ <;>
    rcases h₂ with ⟨_,_,⟨_,_ | _⟩ | ⟨_,_,_⟩⟩ | ⟨_,_,_,_⟩ | ⟨_,_ | ⟨_,_,_⟩⟩ <;>
    cases b <;> simp [Allowed, SurfaceBasisLabel.dual, tag, Pi.add_apply] at * <;> omega

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
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      funext i
      fin_cases i <;> simp [data, tag]
      omega

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
/-- The full shifted source 2E+F bounds every effective component class in its splittings. -/
def cap : X.Curve := ![2,1]
theorem split_bound {beta : X.Curve} (hb : beta ≤ cap) {l r : X.Curve} (hs : l + r = beta) :
    l ≤ cap ∧ r ≤ cap ∧ l 1 + r 1 ≤ 1 := by
  have he (k : Fin 2) : l k + r k = beta k := congrFun hs k
  exact ⟨fun k ↦ (Nat.le_add_right (l k) (r k)).trans ((he k).le.trans (hb k)),
    fun k ↦ (Nat.le_add_left (r k) (l k)).trans ((he k).le.trans (hb k)),
    (he 1).trans_le (hb 1)⟩

private theorem zero_product {c d : X.Curve} (h : c 1 + d 1 ≤ 1)
    (p q : Profile) (b : Label) {l r : ℚ}
    (hl : ¬Allowed c (p + tag b) → l = 0) (hr : ¬Allowed d (q + tag b.dual) → r = 0)
    (hz : ¬Allowed (c+d) (p+q)) : l*r = 0 := by
  by_cases hx : Allowed c (p + tag b)
  · rw [hr (fun hy ↦ hz (join c d h p q b hx hy)), mul_zero]
  · rw [hl hx, zero_mul]

/-- Transfer incidence vanishing through any ordinary decorated surface evaluation. -/
theorem graph_zero (v : SurfaceVertexValues X ℚ)
    (hv : ∀ g S [Fintype S] (h : StableArity g S) b k a, b ≤ cap →
       ¬Allowed b (profile a) → v g S h b k a = 0)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (b : X.Curve) (k : S → ℕ) (a : S → Label) (hb : b ≤ cap) (hz : ¬Allowed b (profile a)) :
    x.surfaceEval X v b k a = 0 := by
  induction x generalizing b with
  | fundamental g S h => exact hv g S h b k a hb hz
  | relabel e x ih => exact ih b (k ∘ e) (a ∘ e) hb (profile_relabel e a ▸ hz)
  | separating x y ihx ihy =>
    unfold GluingExpression.surfaceEval
    apply Finset.sum_eq_zero
    intro t ht
    have hs : t.1+t.2 = b := by
      rw [X.splittings_eq] at ht
      exact (X.effective.mem_splittings _ _ _).mp ht
    obtain ⟨h₁,h₂,hd⟩ := split_bound hb hs
    apply Finset.sum_eq_zero
    intro u _
    apply mul_eq_zero_of_right
    apply zero_product hd (profile (a ∘ Sum.inl)) (profile (a ∘ Sum.inr)) u
    · intro hbad
      apply ihx t.1 _ _ h₁
      rwa [profile_option]
    · intro hbad
      apply ihy t.2 _ _ h₂
      rwa [profile_option]
    · rwa [hs, profile_sum]
  | nonseparating x ih =>
    unfold GluingExpression.surfaceEval
    apply Finset.sum_eq_zero
    intro u _
    apply mul_eq_zero_of_right
    apply ih b _ _ hb
    intro hx
    rw [profile_option, profile_option] at hx
    exact hz (closed_of_le (fun j ↦ by simp only [Pi.add_apply]; omega) hx)

/-- Every original binomial point placement obeys the same incidence constraint. -/
theorem point_graph_zero (v : ℕ → SurfaceCotangentVertexValues X ℚ)
    (n : ℕ) (hv : ∀ m, m ≤ n → ∀ g S [Fintype S] (h : StableArity g S) k l b a, b ≤ cap →
       ¬Allowed b (m • tag .point + profile a) → v m g S h k l b a = 0)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (d : x.CotangentDecoration) (l : x.DecidableLabels) (b : X.Curve) (a : S → Label)
    (hb : b ≤ cap) (hz : ¬Allowed b (n • tag .point + profile a)) :
    x.pointContraction X v d l b n a = 0 := by
  induction x generalizing b n with
  | fundamental g S h => exact hv n le_rfl g S h d l b a hb hz
  | relabel e x ih =>
    exact ih n hv d l b (a ∘ e) hb (by rwa [profile_relabel])
  | separating x y ihx ihy =>
    unfold GluingExpression.pointContraction
    apply Finset.sum_eq_zero
    intro t ht
    have hs : t.1+t.2 = b := by
      rw [X.splittings_eq] at ht
      exact (X.effective.mem_splittings _ _ _).mp ht
    obtain ⟨h₁,h₂,hd⟩ := split_bound hb hs
    apply Finset.sum_eq_zero
    intro u _
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro ij hij
    have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    apply mul_eq_zero_of_right
    apply zero_product hd (ij.1 • tag .point + profile (a ∘ Sum.inl))
      (ij.2 • tag .point + profile (a ∘ Sum.inr)) u
    · intro hz
      apply ihx ij.1 (fun m hm ↦ hv m (by omega)) d.1 l.1 t.1 _ h₁
      rwa [profile_option, ← add_assoc]
    · intro hz
      apply ihy ij.2 (fun m hm ↦ hv m (by omega)) d.2 l.2 t.2 _ h₂
      rwa [profile_option, ← add_assoc]
    · rw [add_add_add_comm, ← add_nsmul, he, profile_sum, hs]
      exact hz
  | nonseparating x ih =>
    unfold GluingExpression.pointContraction
    apply Finset.sum_eq_zero
    intro u _
    apply mul_eq_zero_of_right
    apply ih n hv d l b _ hb
    intro hx
    rw [profile_option, profile_option] at hx
    exact hz (closed_of_le (fun j ↦ by simp only [Pi.add_apply]; omega) hx)

/-- Signed universal-curve pullback preserves vanishing, including all new rational tails. -/
theorem pull_zero (v : SurfaceVertexValues X ℚ)
    (hv : ∀ g S [Fintype S] (h : StableArity g S) b k a, b ≤ cap →
       ¬Allowed b (profile a) → v g S h b k a = 0)
    (n : ℕ) (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (k : S → ℕ) (l : DecidableEq S) (b : X.Curve) (a : S → Label) (hb : b ≤ cap)
    (hz : ¬Allowed b (n • tag .point + profile a)) :
    SurfacePointPullback.vertex X v n g S h k l b a = 0 := by
  induction n using Nat.strong_induction_on generalizing g S b with
  | h n ih =>
    cases n with
    | zero =>
      rw [SurfacePointPullback.vertex]
      exact hv g S h b k a hb (by simpa only [zero_nsmul, zero_add] using hz)
    | succ n =>
      rw [SurfacePointPullback.vertex_succ]
      apply Multiset.sum_eq_zero
      intro w hw
      obtain ⟨t,_,rfl⟩ := Multiset.mem_map.mp hw
      apply mul_eq_zero_of_right
      apply point_graph_zero _ n (fun m hm ↦ by exact ih m (by omega)) _ _ _ b _ hb
      rw [profile_option]
      have he : (n+1) • tag .point + profile a = n • tag .point + (profile a + tag .point) := by
        rw [succ_nsmul]
        abel
      rwa [he] at hz

end AxiomaticGW.F1PlaneLineIncidence

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.DecoratedTermExpansion
public import AxiomaticGW.Surfaces.GenusOneAncestors

/-!
# Partial reconstruction of genus-two graph equations

Dimension-incompatible components vanish. Components of genus zero and one
use the existing finite-seed ancestor algorithms; higher-genus components
remain the existing ancestor variables. No genus-two value is supplied.

Every surviving monomial has bounded total component genus and an effective
remainder in the original full curve class. For a genus-two graph this proves
affine linearity in dimension-compatible genus-two ancestors. Removing *all*
variables at the original curve class leaves only smaller-energy variables.
It does not assert invertibility of the remaining coupled linear system.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo

/-- Execute only dimension vanishing and the already reconstructed genera. -/
def residualTerms {X : SurfaceTarget} (q : SurfaceAncestorKey X) :
    RationalTerms (SurfaceAncestorKey X) :=
  if q.DimensionCompatible then
    if q.genus ≤ 1 then
      RationalTerms.term
        (SurfaceGenusOne.componentValue X (SurfaceGenusOne.ancestorValue X) q) 0
    else RationalTerms.term 1 {q}
  else 0

/-- Terminal substitution for the existing decorated graph evaluator. -/
def vertexTerms (X : SurfaceTarget) :
    SurfaceVertexValues X (RationalTerms (SurfaceAncestorKey X)) :=
  fun g S _ h beta k a ↦ residualTerms (SurfaceAncestorKey.ofLabels g S h beta k a)

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {I : StableCurveIntegration C}

/-- The two lower-genus identifications are existing reconstruction theorems;
the residual variables denote actual ancestors without any additional equation. -/
theorem eval_residualTerms (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    (hzero : ∀ q : SurfaceAncestorKey X, q.genus = 0 →
      SurfaceGenusZero.ancestorValue X q = q.eval Omega P I)
    (hone : ∀ q : SurfaceAncestorKey X, q.genus = 1 →
      SurfaceGenusOne.ancestorValue X q = q.eval Omega P I)
    (q : SurfaceAncestorKey X) :
    RationalTerms.eval (SurfaceAncestorKey.eval Omega P I) (residualTerms q) =
      q.eval Omega P I := by
  unfold residualTerms
  split_ifs with hd hg
  · simp only [RationalTerms.eval_term, Multiset.map_zero, Multiset.prod_zero,
      Algebra.algebraMap_self_apply, mul_one, SurfaceGenusOne.componentValue]
    split_ifs with hz
    · exact hzero q hz
    · exact hone q (by omega)
  · simp only [RationalTerms.eval_term, Multiset.map_singleton, Multiset.prod_singleton,
      Algebra.algebraMap_self_apply, one_mul]
  · exact (q.eval_eq_zero_of_dimension_incompatible P T hd).symm

/-- Partial reconstruction preserves the entire geometric decorated contraction. -/
theorem eval_decoratedTerms (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    (hzero : ∀ q : SurfaceAncestorKey X, q.genus = 0 →
      SurfaceGenusZero.ancestorValue X q = q.eval Omega P I)
    (hone : ∀ q : SurfaceAncestorKey X, q.genus = 1 →
      SurfaceGenusOne.ancestorValue X q = q.eval Omega P I)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (d : x.CotangentDecoration) (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    RationalTerms.eval (SurfaceAncestorKey.eval Omega P I)
      (x.surfaceDecoratedTerms X (vertexTerms X) d beta k a) =
      x.gwDecoratedAncestorContraction Omega P I d beta k (fun s ↦ (a s).value) := by
  rw [GluingExpression.eval_surfaceDecoratedTerms]
  simp only [vertexTerms, eval_residualTerms P T hzero hone, SurfaceAncestorKey.eval_ofLabels]
  exact x.surfaceDecoratedEval_eq_gwDecoratedAncestorContraction Omega P I T.pairing_eq d beta k a

/-- Surviving variables, total component genus, and an effective full-class remainder. -/
def MonomialBound (g : ℕ) (beta : X.Curve) (m : Multiset (SurfaceAncestorKey X)) : Prop :=
  (∀ q ∈ m, 2 ≤ q.genus ∧ q.DimensionCompatible) ∧
    (m.map SurfaceAncestorKey.genus).sum ≤ g ∧
    ∃ delta : X.Curve, (m.map SurfaceAncestorKey.beta).sum + delta = beta

/-- Bounds apply before collection, so cancellation cannot hide a bad dependency. -/
def TermsBound (g : ℕ) (beta : X.Curve) (p : RationalTerms (SurfaceAncestorKey X)) : Prop :=
  ∀ t ∈ p, MonomialBound g beta t.2

theorem termsBound_zero (g : ℕ) (beta : X.Curve) : TermsBound g beta 0 := by
  intro t ht
  exact (Multiset.notMem_zero t ht).elim

private theorem termsBound_term (g : ℕ) (beta : X.Curve) (c : ℚ)
    (m : Multiset (SurfaceAncestorKey X)) (hm : MonomialBound g beta m) :
    TermsBound g beta (RationalTerms.term c m) := by
  unfold RationalTerms.term
  split_ifs
  · exact termsBound_zero g beta
  · intro t ht
    rw [Multiset.mem_singleton] at ht
    exact ht ▸ hm

theorem termsBound_residual (q : SurfaceAncestorKey X) :
    TermsBound q.genus q.beta (residualTerms q) := by
  unfold residualTerms
  split_ifs with hd hg
  · apply termsBound_term
    exact ⟨fun q hq ↦ (Multiset.notMem_zero q hq).elim, Nat.zero_le _, q.beta, zero_add _⟩
  · apply termsBound_term
    refine ⟨?_, ?_, 0, ?_⟩
    · intro r hr
      rw [Multiset.mem_singleton] at hr
      subst r
      exact ⟨by omega, hd⟩
    · exact le_rfl
    · exact add_zero _
  · exact termsBound_zero _ _

theorem TermsBound.mono {g h : ℕ} {beta : X.Curve}
    {p : RationalTerms (SurfaceAncestorKey X)} (hp : TermsBound g beta p) (hgh : g ≤ h) :
    TermsBound h beta p := by
  intro t ht
  obtain ⟨hm, hg, hbeta⟩ := hp t ht
  exact ⟨hm, hg.trans hgh, hbeta⟩

theorem termsBound_add {g : ℕ} {beta : X.Curve} {p q : RationalTerms (SurfaceAncestorKey X)}
    (hp : TermsBound g beta p) (hq : TermsBound g beta q) : TermsBound g beta (p + q) := by
  intro t ht
  exact (Multiset.mem_add.mp ht).elim (hp t) (hq t)

theorem termsBound_scale {g : ℕ} {beta : X.Curve} {p : RationalTerms (SurfaceAncestorKey X)}
    (hp : TermsBound g beta p) (c : ℚ) : TermsBound g beta (RationalTerms.scale c p) := by
  unfold RationalTerms.scale
  split_ifs
  · exact termsBound_zero g beta
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp ht
    exact hp s hs

private theorem monomialBound_add {g h : ℕ} {beta gamma : X.Curve}
    {m n : Multiset (SurfaceAncestorKey X)}
    (hm : MonomialBound g beta m) (hn : MonomialBound h gamma n) :
    MonomialBound (g + h) (beta + gamma) (m + n) := by
  obtain ⟨hm, hg, delta, hd⟩ := hm
  obtain ⟨hn, hh, epsilon, he⟩ := hn
  refine ⟨fun q hq ↦ (Multiset.mem_add.mp hq).elim (hm q) (hn q), ?_, delta + epsilon, ?_⟩
  · simpa only [Multiset.map_add, Multiset.sum_add] using Nat.add_le_add hg hh
  · rw [Multiset.map_add, Multiset.sum_add, add_add_add_comm, hd, he]

private theorem termsBound_mul {g h : ℕ} {beta gamma : X.Curve}
    {p q : RationalTerms (SurfaceAncestorKey X)} (hp : TermsBound g beta p)
    (hq : TermsBound h gamma q) : TermsBound (g + h) (beta + gamma) (RationalTerms.mul p q) := by
  intro t ht
  obtain ⟨s, hs, ht⟩ := Multiset.mem_bind.mp ht
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp ht
  exact monomialBound_add (hp s hs) (hq r hr)

theorem termsBound_sum {g : ℕ} {beta : X.Curve} {ι : Type*}
    (s : Finset ι) (f : ι → RationalTerms (SurfaceAncestorKey X))
    (hf : ∀ i ∈ s, TermsBound g beta (f i)) : TermsBound g beta (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact termsBound_zero g beta
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact termsBound_add (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))

theorem termsBound_bind {g : ℕ} {beta : X.Curve} {ι : Type*}
    (s : Multiset ι) (f : ι → RationalTerms (SurfaceAncestorKey X))
    (hf : ∀ i ∈ s, TermsBound g beta (f i)) : TermsBound g beta (s.bind f) := by
  intro t ht
  obtain ⟨i, hi, ht⟩ := Multiset.mem_bind.mp ht
  exact hf i hi t ht

/-- Gluing cannot create residual genus or curve class: separating vertices
split the class, and loops consume genus without creating new components. -/
theorem termsBound_decorated {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (d : x.CotangentDecoration) (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    TermsBound g beta (x.surfaceDecoratedTerms X (vertexTerms X) d beta k a) := by
  induction x generalizing beta with
  | fundamental g S h =>
    exact termsBound_residual (SurfaceAncestorKey.ofLabels g S h beta (k + d) a)
  | relabel e x ih => exact ih d beta (k ∘ e) (a ∘ e)
  | separating x y ihx ihy =>
    apply termsBound_sum
    intro pair hpair
    apply termsBound_sum
    intro b _
    apply termsBound_scale
    have hsum : pair.1 + pair.2 = beta := by
      rw [X.splittings_eq] at hpair
      exact (X.effective.mem_splittings _ _ _).mp hpair
    rw [← hsum]
    exact termsBound_mul (ihx d.1 pair.1 _ _) (ihy d.2 pair.2 _ _)
  | nonseparating x ih =>
    apply termsBound_sum
    intro b _
    apply termsBound_scale
    exact (ih d beta _ _).mono (Nat.le_succ _)

private theorem twice_card_le_genus (m : Multiset (SurfaceAncestorKey X))
    (hm : ∀ q ∈ m, 2 ≤ q.genus) : 2 * m.card ≤ (m.map SurfaceAncestorKey.genus).sum := by
  induction m using Multiset.induction_on with
  | empty => exact le_rfl
  | @cons q m ih =>
    have hq := hm q (Multiset.mem_cons_self q m)
    have hi := ih (fun r hr ↦ hm r (Multiset.mem_cons_of_mem hr))
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
    omega

/-- In genus two every nonconstant monomial is a single genus-two ancestor.
The conclusion retains its full class, powers and dimension equation. -/
theorem MonomialBound.affine {beta : X.Curve} {m : Multiset (SurfaceAncestorKey X)}
    (hm : MonomialBound 2 beta m) :
    m = 0 ∨ ∃ q, m = {q} ∧ q.genus = 2 ∧ q.DimensionCompatible ∧
      ∃ delta : X.Curve, q.beta + delta = beta := by
  have hc := twice_card_le_genus m (fun q hq ↦ (hm.1 q hq).1)
  have hg := hm.2.1
  have hcard : m.card ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with hz | ho
  · exact Or.inl (Multiset.card_eq_zero.mp hz)
  · obtain ⟨q, rfl⟩ := Multiset.card_eq_one.mp ho
    have hq := hm.1 q (Multiset.mem_singleton_self q)
    have hgen := hm.2.1
    simp only [Multiset.map_singleton, Multiset.sum_singleton] at hgen
    exact Or.inr ⟨q, rfl, by omega, hq.2, hm.2.2⟩

/-- Effective remainders give strict energy decrease unless the full class agrees. -/
theorem MonomialBound.dependency {beta : X.Curve} {m : Multiset (SurfaceAncestorKey X)}
    (hm : MonomialBound 2 beta m) (q : SurfaceAncestorKey X) (hq : q ∈ m) :
    q.genus = 2 ∧ q.DimensionCompatible ∧
      (q.beta = beta ∨ X.effective.energy q.beta < X.effective.energy beta) := by
  rcases hm.affine with rfl | ⟨r, rfl, hg, hd, delta, hdelta⟩
  · exact (Multiset.notMem_zero q hq).elim
  · rw [Multiset.mem_singleton] at hq
    subst r
    refine ⟨hg, hd, ?_⟩
    by_cases hz : delta = 0
    · exact Or.inl (by simpa only [hz, add_zero] using hdelta)
    · right
      have hpos : 0 < X.effective.energy delta :=
        Nat.pos_of_ne_zero (fun h ↦ hz ((X.effective.energy_eq_zero_iff delta).mp h))
      have he := congrArg X.effective.energy hdelta
      rw [map_add] at he
      omega

/-- The remainder after removing every unknown at the original full curve class. -/
def smallerClassTerms (beta : X.Curve) (p : RationalTerms (SurfaceAncestorKey X)) :
    RationalTerms (SurfaceAncestorKey X) := p.filter (fun t ↦ ∀ q ∈ t.2, q.beta ≠ beta)

/-- The complementary terms retain every unknown at the original full class. -/
def sameClassTerms (beta : X.Curve) (p : RationalTerms (SurfaceAncestorKey X)) :
    RationalTerms (SurfaceAncestorKey X) := p.filter (fun t ↦ ¬∀ q ∈ t.2, q.beta ≠ beta)

/-- Splitting off the entire coupled system preserves the original equation. -/
theorem eval_split_by_class {A : Type*} [CommRing A] [Algebra ℚ A]
    (v : SurfaceAncestorKey X → A) (beta : X.Curve) (p : RationalTerms (SurfaceAncestorKey X)) :
    RationalTerms.eval v p = RationalTerms.eval v (sameClassTerms beta p) +
      RationalTerms.eval v (smallerClassTerms beta p) := by
  rw [← RationalTerms.eval_add, sameClassTerms, smallerClassTerms, add_comm,
    Multiset.filter_add_not]

/-- The same-class part is a linear combination of genuine genus-two unknowns,
with no constant or smaller-class term. All insertion data remain in the key. -/
theorem sameClassTerms_dependencies {beta : X.Curve}
    {p : RationalTerms (SurfaceAncestorKey X)} (hp : TermsBound 2 beta p)
    (t : ℚ × Multiset (SurfaceAncestorKey X)) (ht : t ∈ sameClassTerms beta p) :
    ∃ q, t.2 = {q} ∧ q.genus = 2 ∧ q.DimensionCompatible ∧ q.beta = beta := by
  obtain ⟨ht, hsame⟩ := Multiset.mem_filter.mp ht
  rcases (hp t ht).affine with hz | ⟨q, hq, hg, hd, _⟩
  · exact (hsame (by simp only [hz, Multiset.notMem_zero, false_implies, implies_true])).elim
  · refine ⟨q, hq, hg, hd, ?_⟩
    by_contra hne
    apply hsame
    intro r hr
    rw [hq, Multiset.mem_singleton] at hr
    exact hr ▸ hne

/-- Every residual genus-two dependency in this remainder strictly decreases energy. -/
theorem smallerClassTerms_dependencies {beta : X.Curve}
    {p : RationalTerms (SurfaceAncestorKey X)} (hp : TermsBound 2 beta p)
    (t : ℚ × Multiset (SurfaceAncestorKey X)) (ht : t ∈ smallerClassTerms beta p)
    (q : SurfaceAncestorKey X) (hq : q ∈ t.2) :
    q.genus = 2 ∧ q.DimensionCompatible ∧
      X.effective.energy q.beta < X.effective.energy beta := by
  obtain ⟨ht, hne⟩ := Multiset.mem_filter.mp ht
  obtain ⟨hg, hd, he⟩ := (hp t ht).dependency q hq
  exact ⟨hg, hd, he.resolve_left (hne q hq)⟩

end AxiomaticGW.SurfaceGenusTwo

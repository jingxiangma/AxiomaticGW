/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.WDVV

/-!
# Curve-class support of primary genus-zero equations

Every surviving component is a positive-class point query of the required
dimension. Each monomial preserves the sum of the full curve classes.
Consequently the only possible term at the original energy is its singleton
point query; all variables in the remaining terms have strictly lower energy.
This controls recursive dependencies independently of any nonzero-pivot claim.
-/

@[expose] public section

namespace AxiomaticGW

namespace SurfaceBasisLabel

/-- Complex codimension counts divisors once and points twice, with units of degree zero. -/
theorem sum_codimension_add_units {X : SurfaceTarget} (m : Multiset (SurfaceBasisLabel X)) :
    (m.map codimension).sum + m.count .unit = m.card + m.count .point := by
  induction m using Multiset.induction_on with
  | empty => rfl
  | @cons a m ih =>
    cases a <;>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.count_cons,
        Multiset.card_cons, codimension, reduceCtorEq, ite_true, ite_false] at * <;> omega

end SurfaceBasisLabel

namespace SurfaceAncestorKey

/-- A surviving primary coefficient excludes unit insertions. -/
theorem unit_not_mem_of_primaryCoefficient_ne_zero {X : SurfaceTarget}
    (q : SurfaceAncestorKey X) (hc : q.primaryCoefficient ≠ 0) :
    SurfaceBasisLabel.unit ∉ q.primaryLabels := by
  intro hu
  apply hc
  exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨.unit, hu, rfl⟩)

/-- The dimension equation fixes the number of residual points in genus zero. -/
theorem point_count_of_genus_zero {X : SurfaceTarget} (q : SurfaceAncestorKey X)
    (hg : q.genus = 0) (hp : q.IsPrimary) (hd : q.DimensionCompatible)
    (hc : q.primaryCoefficient ≠ 0) :
    q.primaryLabels.count .point = X.effective.energy q.beta - 1 := by
  have hunits : q.primaryLabels.count .unit = 0 :=
    Multiset.count_eq_zero.mpr (q.unit_not_mem_of_primaryCoefficient_ne_zero hc)
  have hcodim : q.totalCodimension = (q.primaryLabels.map SurfaceBasisLabel.codimension).sum := by
    unfold totalCodimension primaryLabels
    rw [Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro s hs
    exact Nat.add_eq_left.mpr (hp s hs)
  have hcount := SurfaceBasisLabel.sum_codimension_add_units q.primaryLabels
  rw [hunits, add_zero, ← hcodim] at hcount
  have hcard : q.primaryLabels.card = q.insertions.card := Multiset.card_map _ _
  unfold DimensionCompatible at hd
  change (q.totalCodimension : ℤ) =
    (X.effective.energy q.beta : ℤ) + (q.genus : ℤ) - 1 + (q.insertions.card : ℤ) at hd
  rw [hg] at hd
  omega

end SurfaceAncestorKey

namespace SurfaceGenusZero

open SurfacePolynomialReduction

/-- The unique dimension-compatible primary point query at a positive class. -/
def pointVariable (X : SurfaceTarget) (beta : X.Curve) : Variable X :=
  .inr (SurfaceQuery.points X 0 beta (X.effective.energy beta - 1))

/-- Full class carried by either kind of residual variable. -/
def variableCurve {X : SurfaceTarget} : Variable X → X.Curve
  | .inl q => q.beta
  | .inr q => q.beta

/-- A monomial of positive-class genus-zero point queries with fixed total class. -/
def PointMonomial {X : SurfaceTarget} (beta : X.Curve) (m : Multiset (Variable X)) : Prop :=
  (∀ v ∈ m, ∃ gamma : X.Curve, gamma ≠ 0 ∧ v = pointVariable X gamma) ∧
    (m.map variableCurve).sum = beta

/-- Every uncollected term has the specified full curve class and point-query form. -/
def PointTerms {X : SurfaceTarget} (beta : X.Curve) (p : RationalTerms (Variable X)) : Prop :=
  ∀ t ∈ p, PointMonomial beta t.2

theorem pointTerms_zero {X : SurfaceTarget} (beta : X.Curve) :
    PointTerms beta 0 := by
  intro t ht
  exact (Multiset.notMem_zero t ht).elim

theorem pointTerms_term {X : SurfaceTarget} (beta : X.Curve) (c : ℚ)
    (m : Multiset (Variable X)) (hm : PointMonomial beta m) :
    PointTerms beta (RationalTerms.term c m) := by
  unfold RationalTerms.term
  split_ifs
  · exact pointTerms_zero beta
  · intro t ht
    rw [Multiset.mem_singleton] at ht
    exact ht ▸ hm

/-- Every genus-zero primary component has positive point support or is a constant at class zero. -/
theorem pointTerms_primary {X : SurfaceTarget} (q : SurfaceAncestorKey X)
    (hg : q.genus = 0) (hp : q.IsPrimary) : PointTerms q.beta (primaryTerms q) := by
  unfold primaryTerms reduceVariable
  split_ifs with hd hpos hc
  · exact pointTerms_zero q.beta
  · simp only [degreeZeroValue?]
    apply pointTerms_term
    have hq : q.pointQuery = SurfaceQuery.points X 0 q.beta
        (X.effective.energy q.beta - 1) := by
      rw [SurfaceAncestorKey.pointQuery, hg,
        q.point_count_of_genus_zero hg hp hd hc]
    constructor
    · intro v hv
      rw [Multiset.mem_singleton] at hv
      exact ⟨q.beta, hpos.2, hv.trans (congrArg Sum.inr hq)⟩
    · simp only [Multiset.map_singleton, Multiset.sum_singleton, variableCurve,
        SurfaceAncestorKey.pointQuery, SurfaceQuery.points]
  · have hz : q.beta = 0 := by
      by_contra hn
      exact hpos ⟨hp, hn⟩
    simp only [degreeZeroValue?, hz, hp, hg, and_self, ite_true]
    apply pointTerms_term
    constructor
    · intro v hv
      exact (Multiset.notMem_zero v hv).elim
    · rfl
  · exact pointTerms_zero q.beta

private theorem pointMonomial_add {X : SurfaceTarget} {beta gamma : X.Curve}
    {m n : Multiset (Variable X)} (hm : PointMonomial beta m) (hn : PointMonomial gamma n) :
    PointMonomial (beta + gamma) (m + n) := by
  constructor
  · intro v hv
    exact (Multiset.mem_add.mp hv).elim (hm.1 v) (hn.1 v)
  · rw [Multiset.map_add, Multiset.sum_add, hm.2, hn.2]

private theorem pointTerms_add {X : SurfaceTarget} {beta : X.Curve}
    {p q : RationalTerms (Variable X)} (hp : PointTerms beta p) (hq : PointTerms beta q) :
    PointTerms beta (p + q) := by
  intro t ht
  exact (Multiset.mem_add.mp ht).elim (hp t) (hq t)

private theorem pointTerms_scale {X : SurfaceTarget} {beta : X.Curve}
    {p : RationalTerms (Variable X)} (hp : PointTerms beta p) (c : ℚ) :
    PointTerms beta (RationalTerms.scale c p) := by
  unfold RationalTerms.scale
  split_ifs
  · exact pointTerms_zero beta
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp ht
    exact hp s hs

private theorem pointTerms_mul {X : SurfaceTarget} {beta gamma : X.Curve}
    {p q : RationalTerms (Variable X)} (hp : PointTerms beta p) (hq : PointTerms gamma q) :
    PointTerms (beta + gamma) (RationalTerms.mul p q) := by
  intro t ht
  obtain ⟨s, hs, ht⟩ := Multiset.mem_bind.mp ht
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp ht
  exact pointMonomial_add (hp s hs) (hq r hr)

private theorem pointTerms_sum {X : SurfaceTarget} {beta : X.Curve} {ι : Type*}
    (s : Finset ι) (f : ι → RationalTerms (Variable X))
    (hf : ∀ i ∈ s, PointTerms beta (f i)) : PointTerms beta (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact pointTerms_zero beta
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact pointTerms_add (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))

private theorem pointTerms_list_sum {X : SurfaceTarget} {beta : X.Curve}
    (ps : List (RationalTerms (Variable X))) (hp : ∀ p ∈ ps, PointTerms beta p) :
    PointTerms beta ps.sum := by
  induction ps with
  | nil => exact pointTerms_zero beta
  | cons p ps ih =>
    exact pointTerms_add (hp p List.mem_cons_self)
      (ih (fun q hq ↦ hp q (List.mem_cons_of_mem p hq)))

/-- The complete primary genus-zero evaluator preserves every curve coordinate.
No geometric laws, numerical values or bound on the number of markings are used. -/
theorem pointTerms_surface {X : SurfaceTarget} {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (hg : g = 0) (beta : X.Curve)
    (a : S → SurfaceBasisLabel X) :
    PointTerms beta (x.surfaceTerms X (primaryVertexTerms X) beta 0 a) := by
  induction x generalizing beta with
  | fundamental g Marks h =>
    apply pointTerms_primary _ hg
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hs
    rfl
  | relabel e x ih => exact ih hg beta (a ∘ e)
  | @separating g₁ g₂ S₁ S₂ _ _ x y ihx ihy =>
    unfold GluingExpression.surfaceTerms
    apply pointTerms_sum
    intro pair hpair
    apply pointTerms_sum
    intro b _
    apply pointTerms_scale
    have hsum : pair.1 + pair.2 = beta := by
      rw [X.splittings_eq] at hpair
      exact (X.effective.mem_splittings _ _ _).mp hpair
    rw [← hsum]
    have hleft : PsiClasses.separatingLeftPowers (0 : S₁ ⊕ S₂ → ℕ) = 0 := by
      funext s
      cases s <;> rfl
    have hright : PsiClasses.separatingRightPowers (0 : S₁ ⊕ S₂ → ℕ) = 0 := by
      funext s
      cases s <;> rfl
    rw [hleft, hright]
    exact pointTerms_mul (ihx (Nat.eq_zero_of_add_eq_zero_right hg) pair.1 _)
      (ihy (Nat.eq_zero_of_add_eq_zero_left hg) pair.2 _)
  | nonseparating x ih => omega

/-- All additional-marking placements of the original primary WDVV request
have homogeneous point support, retaining full classes rather than only energy. -/
theorem pointTerms_wdvv (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    PointTerms beta (WDVV.primaryTerms X n beta 0 a) := by
  apply pointTerms_sum
  intro i _
  apply pointTerms_scale
  apply pointTerms_list_sum
  intro p hp
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hp
  exact pointTerms_surface z rfl beta a

/-- A variable's energy cannot exceed the energy of the sum of all its monomial classes. -/
theorem variable_energy_le_sum {X : SurfaceTarget} (m : Multiset (Variable X))
    (v : Variable X) (hv : v ∈ m) :
    X.effective.energy (variableCurve v) ≤ X.effective.energy (m.map variableCurve).sum := by
  obtain ⟨rest, rfl⟩ := Multiset.exists_cons_of_mem hv
  rw [Multiset.map_cons, Multiset.sum_cons, map_add]
  exact Nat.le_add_right _ _

/-- Positivity excludes every nonempty point monomial of total curve class zero. -/
theorem PointMonomial.eq_zero {X : SurfaceTarget} {m : Multiset (Variable X)}
    (hm : PointMonomial (0 : X.Curve) m) : m = 0 := by
  apply Multiset.eq_zero_of_forall_notMem
  intro v hv
  obtain ⟨gamma, hgamma, rfl⟩ := hm.1 v hv
  have hle := variable_energy_le_sum m (pointVariable X gamma) hv
  rw [hm.2, map_zero] at hle
  exact hgamma ((X.effective.energy_eq_zero_iff gamma).mp (Nat.eq_zero_of_le_zero hle))

/-- A same-energy variable forces the entire monomial to be the original singleton.
In particular equal-energy but different full classes cannot survive here. -/
theorem PointMonomial.singleton_of_energy_eq {X : SurfaceTarget} {beta : X.Curve}
    {m : Multiset (Variable X)} (hm : PointMonomial beta m) (v : Variable X) (hv : v ∈ m)
    (he : X.effective.energy (variableCurve v) = X.effective.energy beta) :
    m = {pointVariable X beta} := by
  obtain ⟨gamma, hgamma, rfl⟩ := hm.1 v hv
  obtain ⟨rest, rfl⟩ := Multiset.exists_cons_of_mem hv
  have hsum : gamma + (rest.map variableCurve).sum = beta := by
    simpa only [Multiset.map_cons, Multiset.sum_cons, variableCurve, pointVariable,
      SurfaceQuery.points] using hm.2
  have henergy := congrArg X.effective.energy hsum
  rw [map_add] at henergy
  have hz : (rest.map variableCurve).sum = 0 :=
    (X.effective.energy_eq_zero_iff _).mp (by change X.effective.energy gamma = _ at he; omega)
  have hempty : rest = 0 := PointMonomial.eq_zero
    ⟨fun w hw ↦ hm.1 w (Multiset.mem_cons_of_mem hw), hz⟩
  rw [hempty, Multiset.map_zero, Multiset.sum_zero, add_zero] at hsum
  rw [hempty, hsum]
  rfl

/-- Apart from the original singleton, every dependency strictly decreases anticanonical energy. -/
theorem PointMonomial.energy_lt_of_ne_singleton {X : SurfaceTarget} {beta : X.Curve}
    {m : Multiset (Variable X)} (hm : PointMonomial beta m)
    (hne : m ≠ {pointVariable X beta}) (v : Variable X) (hv : v ∈ m) :
    X.effective.energy (variableCurve v) < X.effective.energy beta := by
  have hle := variable_energy_le_sum m v hv
  rw [hm.2] at hle
  have hne' : X.effective.energy (variableCurve v) ≠ X.effective.energy beta :=
    fun he ↦ hne (hm.singleton_of_energy_eq v hv he)
  omega

/-- Remove all singleton occurrences of the requested point query.
For `PointTerms` inputs, the following theorem proves strict decrease of the remainder. -/
def lowerTerms (X : SurfaceTarget) (beta : X.Curve) (p : RationalTerms (Variable X)) :
    RationalTerms (Variable X) := p.filter (fun t ↦ t.2 ≠ {pointVariable X beta})

/-- The lower part of any homogeneous point equation has only smaller positive point queries. -/
theorem lowerTerms_dependencies {X : SurfaceTarget} {beta : X.Curve}
    {p : RationalTerms (Variable X)} (hp : PointTerms beta p)
    (t : ℚ × Multiset (Variable X)) (ht : t ∈ lowerTerms X beta p)
    (v : Variable X) (hv : v ∈ t.2) :
    ∃ gamma : X.Curve, gamma ≠ 0 ∧ v = pointVariable X gamma ∧
      X.effective.energy gamma < X.effective.energy beta := by
  obtain ⟨htp, hne⟩ := Multiset.mem_filter.mp ht
  obtain ⟨gamma, hgamma, rfl⟩ := (hp t htp).1 v hv
  exact ⟨gamma, hgamma, rfl, (hp t htp).energy_lt_of_ne_singleton hne _ hv⟩

/-- Strict decrease holds uniformly for the actual primary WDVV graph equation. -/
theorem wdvv_lowerTerms_dependencies (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (t : ℚ × Multiset (Variable X))
    (ht : t ∈ lowerTerms X beta (WDVV.primaryTerms X n beta 0 a))
    (v : Variable X) (hv : v ∈ t.2) :
    ∃ gamma : X.Curve, gamma ≠ 0 ∧ v = pointVariable X gamma ∧
      X.effective.energy gamma < X.effective.energy beta :=
  lowerTerms_dependencies (pointTerms_wdvv X n beta a) t ht v hv

end SurfaceGenusZero

end AxiomaticGW

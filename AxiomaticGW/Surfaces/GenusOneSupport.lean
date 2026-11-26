/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroSupport

/-!
# Genus and full-class support of primary Getzler equations

A surviving primary term in genus at most one contains only positive-class
point queries. Their full classes sum to the original class, and the sum of
their genera is at most the graph genus. Removing the requested genus-one
singleton therefore leaves genus-zero queries or strictly smaller-energy
genus-one queries. Equal-energy genus-zero terms are retained.
-/

@[expose] public section

namespace AxiomaticGW

namespace SurfaceAncestorKey

/-- The signed dimension equation fixes the point count after primary reduction,
with genus retained. No vanishing theorem or geometric seed is assumed. -/
theorem point_count_of_primary {X : SurfaceTarget} (q : SurfaceAncestorKey X)
    (hp : q.IsPrimary) (hd : q.DimensionCompatible) (hc : q.primaryCoefficient ≠ 0) :
    q.primaryLabels.count .point = X.effective.energy q.beta + q.genus - 1 := by
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
  omega

end SurfaceAncestorKey

namespace SurfaceLowGenus

open SurfacePolynomialReduction
open SurfaceGenusZero (variableCurve)

/-- A point variable retaining genus and every curve coordinate. At genus and
class zero its point count uses the existing auxiliary natural-number truncation. -/
def pointVariable (X : SurfaceTarget) (g : ℕ) (beta : X.Curve) : Variable X :=
  .inr (SurfaceQuery.points X g beta (X.effective.energy beta + g - 1))

/-- Genus carried by either kind of residual variable. -/
def variableGenus {X : SurfaceTarget} : Variable X → ℕ
  | .inl q => q.genus
  | .inr q => q.genus

/-- Positive point support, homogeneous full class, and a bound on total component genus. -/
def PointMonomial {X : SurfaceTarget} (g : ℕ) (beta : X.Curve)
    (m : Multiset (Variable X)) : Prop :=
  (∀ v ∈ m, ∃ k gamma, gamma ≠ 0 ∧ v = pointVariable X k gamma) ∧
    (m.map variableCurve).sum = beta ∧ (m.map variableGenus).sum ≤ g

/-- The support conditions hold before collecting any equal monomials. -/
def PointTerms {X : SurfaceTarget} (g : ℕ) (beta : X.Curve)
    (p : RationalTerms (Variable X)) : Prop :=
  ∀ t ∈ p, PointMonomial g beta t.2

theorem pointTerms_zero {X : SurfaceTarget} (g : ℕ) (beta : X.Curve) :
    PointTerms g beta 0 := by
  intro t ht
  exact (Multiset.notMem_zero t ht).elim

theorem pointTerms_term {X : SurfaceTarget} (g : ℕ) (beta : X.Curve) (c : ℚ)
    (m : Multiset (Variable X)) (hm : PointMonomial g beta m) :
    PointTerms g beta (RationalTerms.term c m) := by
  unfold RationalTerms.term
  split_ifs
  · exact pointTerms_zero g beta
  · intro t ht
    rw [Multiset.mem_singleton] at ht
    exact ht ▸ hm

/-- Primary reduction in genera zero and one leaves positive point variables or
class-zero constants. The elliptic constants are already part of `primaryTerms`. -/
theorem pointTerms_primary {X : SurfaceTarget} (q : SurfaceAncestorKey X)
    (hg : q.genus ≤ 1) (hp : q.IsPrimary) : PointTerms q.genus q.beta (primaryTerms q) := by
  unfold primaryTerms reduceVariable
  split_ifs with hd hpos hc
  · exact pointTerms_zero q.genus q.beta
  · simp only [degreeZeroValue?]
    apply pointTerms_term
    have hq : q.pointQuery = SurfaceQuery.points X q.genus q.beta
        (X.effective.energy q.beta + q.genus - 1) := by
      rw [SurfaceAncestorKey.pointQuery, q.point_count_of_primary hp hd hc]
    constructor
    · intro v hv
      rw [Multiset.mem_singleton] at hv
      exact ⟨q.genus, q.beta, hpos.2, hv.trans (congrArg Sum.inr hq)⟩
    · simp only [Multiset.map_singleton, Multiset.sum_singleton, variableCurve,
        variableGenus, SurfaceAncestorKey.pointQuery, SurfaceQuery.points, le_refl, and_self]
  · have hz : q.beta = 0 := by
      by_contra hn
      exact hpos ⟨hp, hn⟩
    have hm : PointMonomial q.genus q.beta 0 := by
      constructor
      · intro v hv
        exact (Multiset.notMem_zero v hv).elim
      · simp only [Multiset.map_zero, Multiset.sum_zero, hz, Nat.zero_le, and_self]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hg with hg | hg
    · simp only [degreeZeroValue?, hz, hp, hg, and_self, ite_true]
      exact pointTerms_term _ _ _ _ (by simpa only [hg, hz] using hm)
    · simp only [degreeZeroValue?, hz, hp, hg, and_self, ite_true,
        Nat.one_ne_zero, ite_false]
      exact pointTerms_term _ _ _ _ (by simpa only [hg, hz] using hm)
  · exact pointTerms_zero q.genus q.beta

/-- Increasing the genus bound does not change the full curve or the variables. -/
theorem PointMonomial.mono {X : SurfaceTarget} {g h : ℕ} {beta : X.Curve}
    {m : Multiset (Variable X)} (hm : PointMonomial g beta m) (hgh : g ≤ h) :
    PointMonomial h beta m := ⟨hm.1, hm.2.1, hm.2.2.trans hgh⟩

theorem PointTerms.mono {X : SurfaceTarget} {g h : ℕ} {beta : X.Curve}
    {p : RationalTerms (Variable X)} (hp : PointTerms g beta p) (hgh : g ≤ h) :
    PointTerms h beta p := fun t ht ↦ (hp t ht).mono hgh

private theorem pointMonomial_add {X : SurfaceTarget} {g h : ℕ} {beta gamma : X.Curve}
    {m n : Multiset (Variable X)} (hm : PointMonomial g beta m) (hn : PointMonomial h gamma n) :
    PointMonomial (g + h) (beta + gamma) (m + n) := by
  constructor
  · intro v hv
    exact (Multiset.mem_add.mp hv).elim (hm.1 v) (hn.1 v)
  · simp only [Multiset.map_add, Multiset.sum_add, hm.2.1, hn.2.1, true_and]
    exact Nat.add_le_add hm.2.2 hn.2.2

private theorem pointTerms_add {X : SurfaceTarget} {g : ℕ} {beta : X.Curve}
    {p q : RationalTerms (Variable X)} (hp : PointTerms g beta p) (hq : PointTerms g beta q) :
    PointTerms g beta (p + q) := by
  intro t ht
  exact (Multiset.mem_add.mp ht).elim (hp t) (hq t)

private theorem pointTerms_scale {X : SurfaceTarget} {g : ℕ} {beta : X.Curve}
    {p : RationalTerms (Variable X)} (hp : PointTerms g beta p) (c : ℚ) :
    PointTerms g beta (RationalTerms.scale c p) := by
  unfold RationalTerms.scale
  split_ifs
  · exact pointTerms_zero g beta
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp ht
    exact hp s hs

private theorem pointTerms_mul {X : SurfaceTarget} {g h : ℕ} {beta gamma : X.Curve}
    {p q : RationalTerms (Variable X)} (hp : PointTerms g beta p) (hq : PointTerms h gamma q) :
    PointTerms (g + h) (beta + gamma) (RationalTerms.mul p q) := by
  intro t ht
  obtain ⟨s, hs, ht⟩ := Multiset.mem_bind.mp ht
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp ht
  exact pointMonomial_add (hp s hs) (hq r hr)

private theorem pointTerms_sum {X : SurfaceTarget} {g : ℕ} {beta : X.Curve} {ι : Type*}
    (s : Finset ι) (f : ι → RationalTerms (Variable X))
    (hf : ∀ i ∈ s, PointTerms g beta (f i)) : PointTerms g beta (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact pointTerms_zero g beta
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact pointTerms_add (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))

private theorem pointTerms_list_sum {X : SurfaceTarget} {g : ℕ} {beta : X.Curve}
    (ps : List (RationalTerms (Variable X))) (hp : ∀ p ∈ ps, PointTerms g beta p) :
    PointTerms g beta ps.sum := by
  induction ps with
  | nil => exact pointTerms_zero g beta
  | cons p ps ih =>
    exact pointTerms_add (hp p List.mem_cons_self)
      (ih (fun q hq ↦ hp q (List.mem_cons_of_mem p hq)))

/-- Full curve class is preserved by every gluing. Separating gluing adds
component genera; nonseparating gluing raises graph genus without adding one
to the genus of a surviving component variable. -/
theorem pointTerms_surface {X : SurfaceTarget} {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (hg : g ≤ 1) (beta : X.Curve)
    (a : S → SurfaceBasisLabel X) :
    PointTerms g beta (x.surfaceTerms X (primaryVertexTerms X) beta 0 a) := by
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
    exact pointTerms_mul (ihx (by omega) pair.1 _) (ihy (by omega) pair.2 _)
  | @nonseparating g S _ x ih =>
    unfold GluingExpression.surfaceTerms
    apply pointTerms_sum
    intro b _
    apply pointTerms_scale
    have hk : PsiClasses.nonseparatingPowers (0 : S → ℕ) = 0 := by
      funext s
      rcases s with _ | (_ | s) <;> rfl
    rw [hk]
    exact (ih (by omega) beta _).mono (by omega)

/-- The complete Getzler combination has homogeneous point support with total
component genus at most one, for every original additional-marking placement. -/
theorem pointTerms_getzler (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    PointTerms 1 beta (GetzlerGraphs.primaryTerms X n beta 0 a) := by
  unfold GetzlerGraphs.primaryTerms GetzlerGraphs.surfaceTerms
  apply pointTerms_sum
  intro i _
  apply pointTerms_scale
  apply pointTerms_list_sum
  intro p hp
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hp
  exact pointTerms_surface z (by omega) beta a

/-- A component's genus cannot exceed the sum of all component genera. -/
theorem PointMonomial.variable_genus_le {X : SurfaceTarget} {g : ℕ} {beta : X.Curve}
    {m : Multiset (Variable X)} (hm : PointMonomial g beta m)
    (v : Variable X) (hv : v ∈ m) : variableGenus v ≤ g := by
  obtain ⟨rest, rfl⟩ := Multiset.exists_cons_of_mem hv
  have h := hm.2.2
  rw [Multiset.map_cons, Multiset.sum_cons] at h
  omega

/-- Positivity excludes any nonempty monomial at total curve class zero. -/
theorem PointMonomial.eq_zero {X : SurfaceTarget} {g : ℕ} {m : Multiset (Variable X)}
    (hm : PointMonomial g (0 : X.Curve) m) : m = 0 := by
  apply Multiset.eq_zero_of_forall_notMem
  intro v hv
  obtain ⟨k, gamma, hgamma, rfl⟩ := hm.1 v hv
  have hle := SurfaceGenusZero.variable_energy_le_sum m (pointVariable X k gamma) hv
  rw [hm.2.1, map_zero] at hle
  exact hgamma ((X.effective.energy_eq_zero_iff gamma).mp (Nat.eq_zero_of_le_zero hle))

/-- A same-energy variable is the entire monomial and has the original full
curve class. This statement does not identify different genera. -/
theorem PointMonomial.singleton_of_energy_eq {X : SurfaceTarget} {g : ℕ} {beta : X.Curve}
    {m : Multiset (Variable X)} (hm : PointMonomial g beta m)
    (v : Variable X) (hv : v ∈ m)
    (he : X.effective.energy (variableCurve v) = X.effective.energy beta) :
    m = {v} ∧ variableCurve v = beta := by
  obtain ⟨rest, rfl⟩ := Multiset.exists_cons_of_mem hv
  have hsum : variableCurve v + (rest.map variableCurve).sum = beta := by
    simpa only [Multiset.map_cons, Multiset.sum_cons] using hm.2.1
  have henergy := congrArg X.effective.energy hsum
  rw [map_add] at henergy
  have hz : (rest.map variableCurve).sum = 0 :=
    (X.effective.energy_eq_zero_iff _).mp (by omega)
  have hgen := hm.2.2
  rw [Multiset.map_cons, Multiset.sum_cons] at hgen
  have hempty : rest = 0 := PointMonomial.eq_zero (g := g)
    ⟨fun w hw ↦ hm.1 w (Multiset.mem_cons_of_mem hw), hz, by omega⟩
  rw [hempty, Multiset.map_zero, Multiset.sum_zero, add_zero] at hsum
  exact ⟨by rw [hempty]; rfl, hsum⟩

/-- Remove precisely the singleton genus-one query to be solved for. -/
def lowerTerms (X : SurfaceTarget) (beta : X.Curve) (p : RationalTerms (Variable X)) :
    RationalTerms (Variable X) := p.filter (fun t ↦ t.2 ≠ {pointVariable X 1 beta})

/-- Every remaining dependency has lower genus, or the same genus and lower
energy. Genus-zero terms at the original energy are deliberately preserved. -/
theorem lowerTerms_dependencies {X : SurfaceTarget} {beta : X.Curve}
    {p : RationalTerms (Variable X)} (hp : PointTerms 1 beta p)
    (t : ℚ × Multiset (Variable X)) (ht : t ∈ lowerTerms X beta p)
    (v : Variable X) (hv : v ∈ t.2) :
    ∃ g gamma, gamma ≠ 0 ∧ v = pointVariable X g gamma ∧ g ≤ 1 ∧
      (g = 0 ∨ X.effective.energy gamma < X.effective.energy beta) := by
  obtain ⟨htp, hne⟩ := Multiset.mem_filter.mp ht
  have hm := hp t htp
  obtain ⟨g, gamma, hgamma, rfl⟩ := hm.1 v hv
  have hg : g ≤ 1 := hm.variable_genus_le _ hv
  refine ⟨g, gamma, hgamma, rfl, hg, ?_⟩
  by_cases hgzero : g = 0
  · exact Or.inl hgzero
  · right
    have hone : g = 1 := by omega
    have hle := SurfaceGenusZero.variable_energy_le_sum t.2 (pointVariable X g gamma) hv
    rw [hm.2.1] at hle
    change X.effective.energy gamma ≤ X.effective.energy beta at hle
    by_contra hn
    have he : X.effective.energy (variableCurve (pointVariable X g gamma)) =
        X.effective.energy beta := by change X.effective.energy gamma = _; omega
    obtain ⟨hsingle, hcurve⟩ := hm.singleton_of_energy_eq _ hv he
    change gamma = beta at hcurve
    exact hne (by rw [hsingle, hone, hcurve])

/-- The dependency theorem applies to every complete primary Getzler request,
without a marking bound or a guessed leading coefficient. -/
theorem getzler_lowerTerms_dependencies (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (t : ℚ × Multiset (Variable X))
    (ht : t ∈ lowerTerms X beta (GetzlerGraphs.primaryTerms X n beta 0 a))
    (v : Variable X) (hv : v ∈ t.2) :
    ∃ g gamma, gamma ≠ 0 ∧ v = pointVariable X g gamma ∧ g ≤ 1 ∧
      (g = 0 ∨ X.effective.energy gamma < X.effective.energy beta) :=
  lowerTerms_dependencies (pointTerms_getzler X n beta a) t ht v hv

end SurfaceLowGenus

end AxiomaticGW

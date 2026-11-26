/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.LowGenusAncestorDimension
public import AxiomaticGW.Surfaces.LowGenusPointCache

/-! # One-edge sewing for the first cotangent power

On positive rational components the two unit–point terms of the internal diagonal
vanish. The divisor terms contract to the intersection of the two curve classes.
The original rational and elliptic cotangent recursions with total power one involve
only such primary sewings and, in the elliptic case, the nonseparating primary trace.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceLowGenusPointCache
variable {X : SurfaceTarget}
private theorem positive_primary (v : X.Curve → ℚ) (d : X.Curve) (hd : d ≠ 0)
    (m : Multiset (SurfaceBasisLabel X)) :
    rationalPrimary X v d m = (m.map (SurfaceBasisLabel.primaryFactor d)).prod *
      (if m.count .point = X.effective.energy d - 1 then v d else 0) := by
  rw [rationalPrimary, if_neg hd]
  split_ifs with hp
  · dsimp only
    split_ifs with hc
    · rw [hc, zero_mul]
    · rfl
  · rw [mul_zero]

/-- A non-point node insertion on a positive rational vertex pulls out its divisor
intersection. The primary unit has factor zero. -/
theorem rationalPrimary_cons_of_nonpoint (v : X.Curve → ℚ) (d : X.Curve) (hd : d ≠ 0)
    (b : SurfaceBasisLabel X) (hb : b ≠ .point) (m : Multiset (SurfaceBasisLabel X)) :
    rationalPrimary X v d (b ::ₘ m) = b.primaryFactor d * rationalPrimary X v d m := by
  rw [positive_primary v d hd, positive_primary v d hd, Multiset.count_cons_of_ne (Ne.symm hb),
    Multiset.map_cons, Multiset.prod_cons, mul_assoc]

/-- The inverse intersection form on divisor coordinates, evaluated on two curve classes. -/
def curveIntersection (X : SurfaceTarget) (d e : X.Curve) : ℚ :=
  (SurfaceBasisLabel.hyperplane.primaryFactor d) * (SurfaceBasisLabel.hyperplane.primaryFactor e) -
    ∑ i : Fin X.blowups, (SurfaceBasisLabel.exceptional i).primaryFactor d *
      (SurfaceBasisLabel.exceptional i).primaryFactor e

/-- Sewing two positive rational primaries pairs their curve classes by the surface
intersection form, for arbitrary external markings and rational point function. -/
theorem rationalPrimary_node_sewing (v : X.Curve → ℚ) (d e : X.Curve) (hd : d ≠ 0) (he : e ≠ 0)
    (m n : Multiset (SurfaceBasisLabel X)) :
    (∑ b : SurfaceBasisLabel X, b.inverseWeight *
      (rationalPrimary X v d (b ::ₘ m) * rationalPrimary X v e (b.dual ::ₘ n))) =
    curveIntersection X d e * (rationalPrimary X v d m * rationalPrimary X v e n) := by
  have u (d : X.Curve) (hd : d ≠ 0) (m : Multiset (SurfaceBasisLabel X)) :
      rationalPrimary X v d (.unit ::ₘ m) = 0 := by
    rw [rationalPrimary_cons_of_nonpoint v d hd .unit
      (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])]
    exact zero_mul _
  have h (d : X.Curve) (hd : d ≠ 0) (m : Multiset (SurfaceBasisLabel X)) :=
    rationalPrimary_cons_of_nonpoint v d hd .hyperplane
      (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) m
  have exc (d : X.Curve) (hd : d ≠ 0) (m : Multiset (SurfaceBasisLabel X))
      (i : Fin X.blowups) := rationalPrimary_cons_of_nonpoint v d hd (.exceptional i)
        (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) m
  rw [SurfaceBasisLabel.sum_labels]
  simp only [SurfaceBasisLabel.dual, SurfaceBasisLabel.inverseWeight, u d hd, u e he,
    h d hd, h e he, exc d hd, exc e he, zero_mul, mul_zero, one_mul, zero_add, add_zero,
    neg_one_mul, curveIntersection, sub_mul, Finset.sum_mul, Finset.sum_neg_distrib]
  have eqsum :
      (∑ i : Fin X.blowups,
        ((SurfaceBasisLabel.exceptional i).primaryFactor d * rationalPrimary X v d m) *
        ((SurfaceBasisLabel.exceptional i).primaryFactor e * rationalPrimary X v e n)) =
      ∑ i : Fin X.blowups, ((SurfaceBasisLabel.exceptional i).primaryFactor d *
        (SurfaceBasisLabel.exceptional i).primaryFactor e) *
        (rationalPrimary X v d m * rationalPrimary X v e n) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [eqsum]
  ring

private def labelsBag {S : Type} [Fintype S] (a : S → SurfaceBasisLabel X) :
    Multiset (SurfaceBasisLabel X) := Finset.univ.val.map a

private theorem labelsBag_relabel {S T : Type} [Fintype S] [Fintype T] (e : S ≃ T)
    (a : T → SurfaceBasisLabel X) : labelsBag (a ∘ e) = labelsBag a := by
  have h := congrArg (fun m : Finset T ↦ m.val.map a) (Finset.map_univ_equiv e)
  simpa only [labelsBag, Finset.map_val, Multiset.map_map, Equiv.coe_toEmbedding] using h

private theorem labelsBag_option {S : Type} [Fintype S] (b : SurfaceBasisLabel X)
    (a : S → SurfaceBasisLabel X) : labelsBag (Option.elim · b a) = b ::ₘ labelsBag a := by
  unfold labelsBag
  change (none ::ₘ (Finset.univ.val.map (@Option.some S))).map _ = _
  rw [Multiset.map_cons, Multiset.map_map]
  rfl

private def bagVertex (f : ℕ → X.Curve → Multiset (SurfaceBasisLabel X) → ℚ) :
    SurfaceVertexValues X ℚ :=
  fun g _ _ _ beta _ a ↦ f g beta (labelsBag a)

private theorem graph_no_edge {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (f : ℕ → X.Curve → Multiset (SurfaceBasisLabel X) → ℚ) (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) (hg : x.graph.graph.edgeCount = 0) :
    x.surfaceEval X (bagVertex f) beta k a = f g beta (labelsBag a) := by
  induction x generalizing beta with
  | fundamental => rfl
  | relabel e x ih => exact (ih beta (k ∘ e) (a ∘ e) hg).trans (congrArg _ (labelsBag_relabel e a))
  | separating x y ihx ihy =>
    change _ + _ + 1 = 0 at hg
    omega
  | nonseparating x ih =>
    change _ + 1 = 0 at hg
    omega

private theorem graph_one_edge_zero {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (f : ℕ → X.Curve → Multiset (SurfaceBasisLabel X) → ℚ) (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) (he : x.graph.graph.edgeCount = 1)
    (hs : ∀ g₁ g₂, g₁ + g₂ = g → ∀ d e : X.Curve, d + e = beta → ∀ m n,
      (∑ b : SurfaceBasisLabel X, b.inverseWeight *
        (f g₁ d (b ::ₘ m) * f g₂ e (b.dual ::ₘ n))) = 0)
    (hl : ∀ g₀, g₀ + 1 = g → ∀ m, (∑ b : SurfaceBasisLabel X, b.inverseWeight *
      f g₀ beta (b ::ₘ b.dual ::ₘ m)) = 0) : x.surfaceEval X (bagVertex f) beta k a = 0 := by
  induction x with
  | fundamental =>
    change 0 = 1 at he
    omega
  | relabel e x ih => exact ih (k ∘ e) (a ∘ e) he hs hl
  | @separating g₁ g₂ S T _ _ x y ihx ihy =>
    change x.graph.graph.edgeCount + y.graph.graph.edgeCount + 1 = 1 at he
    have hx : x.graph.graph.edgeCount = 0 := by omega
    have hy : y.graph.graph.edgeCount = 0 := by omega
    unfold GluingExpression.surfaceEval
    apply Finset.sum_eq_zero
    intro p hp
    rw [X.splittings_eq] at hp
    have eq : p.1+p.2 = beta := (X.effective.mem_splittings _ _ _).mp hp
    simp only [graph_no_edge x f _ _ _ hx, graph_no_edge y f _ _ _ hy, labelsBag_option,
      Algebra.algebraMap_self_apply]
    exact hs g₁ g₂ rfl _ _ eq _ _
  | @nonseparating g S _ x ih =>
    change x.graph.graph.edgeCount + 1 = 1 at he
    have hx : x.graph.graph.edgeCount = 0 := by omega
    unfold GluingExpression.surfaceEval
    simp only [graph_no_edge x f _ _ _ hx, labelsBag_option, Algebra.algebraMap_self_apply]
    exact hl g rfl _


/-- The two primary vertex functions used by the rational and elliptic recursion. -/
def primaryAt (v₀ v₁ : X.Curve → ℚ) (g : ℕ) (d : X.Curve)
    (m : Multiset (SurfaceBasisLabel X)) : ℚ :=
  if g = 0 then rationalPrimary X v₀ d m else ellipticPrimary X v₁ d m

private theorem primaryLabels_ofLabels (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (d : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    (SurfaceAncestorKey.ofLabels g S h d k a).primaryLabels = labelsBag a := by
  unfold SurfaceAncestorKey.primaryLabels SurfaceAncestorKey.ofLabels
  exact (Multiset.map_map ..).trans rfl

/-- For a single cotangent power, every boundary term is one sewn primary graph. Vanishing
of the separating products and the nonseparating trace suffices at the actual input class. -/
theorem component_one_psi_zero_of_sewing (v₀ v₁ : X.Curve → ℚ) (q : SurfaceAncestorKey X)
    (hg : q.genus ≤ 1) (hk : q.totalPsi = 1)
    (hs : ∀ g₁ g₂, g₁ + g₂ = q.genus → ∀ d e : X.Curve, d + e = q.beta → ∀ m n,
      (∑ b : SurfaceBasisLabel X, b.inverseWeight *
        (primaryAt v₀ v₁ g₁ d (b ::ₘ m) * primaryAt v₀ v₁ g₂ e (b.dual ::ₘ n))) = 0)
    (hl : ∀ g₀, g₀ + 1 = q.genus → ∀ m, (∑ b : SurfaceBasisLabel X, b.inverseWeight *
      primaryAt v₀ v₁ g₀ q.beta (b ::ₘ b.dual ::ₘ m)) = 0) :
    componentValue X v₀ v₁ q = 0 := by
  have hp : ¬q.IsPrimary := fun h ↦ by
    have := q.totalPsi_eq_zero_iff.mpr h
    omega
  by_cases hz : q.genus = 0
  · rw [componentValue, if_pos hz, rationalValue, hk, rationalFuel, dif_pos hz, dif_neg hp]
    unfold SurfaceGenusZero.ancestorStep
    apply List.sum_eq_zero
    intro z hzmem
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hzmem
    apply mul_eq_zero_of_right
    calc
      _ = t.2.surfaceEval X (bagVertex (primaryAt v₀ v₁)) _ _ _ := by
        apply t.2.surfaceEval_congr_of_bounds
        intro g S _ h d k a hgen hpow
        have he := SurfaceGenusZero.sum_lowerAncestorPowers_add_one q hz hp
        have h0 : g = 0 := Nat.eq_zero_of_le_zero hgen
        let r := SurfaceAncestorKey.ofLabels g S h d k a
        have hr : r.totalPsi = 0 := by
          dsimp only [r]
          rw [SurfaceAncestorKey.totalPsi_ofLabels]
          omega
        have hrg : r.genus = 0 := h0
        change rationalFuel X v₀ 0 r = primaryAt _ _ g d _
        rw [rationalFuel, if_pos ⟨hrg, r.totalPsi_eq_zero_iff.mp hr⟩, primaryAt, if_pos h0]
        exact congrArg _ (primaryLabels_ofLabels ..)
      _ = 0 := graph_one_edge_zero _ _ _ _ _
        (PsiBoundaryExpansion.genusZeroTerms_edgeCount _ _ t ht)
        (fun _ _ eq ↦ hs _ _ (eq.trans hz.symm)) (fun _ eq ↦ hl _ (eq.trans hz.symm))
  · have ho : q.genus = 1 := by omega
    rw [componentValue, if_neg hz, ellipticValue, hk, ellipticFuel, dif_pos ho, dif_neg hp]
    unfold ellipticStep
    apply List.sum_eq_zero
    intro z hzmem
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hzmem
    apply mul_eq_zero_of_right
    calc
      _ = t.2.surfaceEval X (bagVertex (primaryAt v₀ v₁)) _ _ _ := by
        apply t.2.surfaceEval_congr_of_bounds
        intro g S _ h d k a hgen hpow
        have he := SurfaceGenusOne.sum_lowerAncestorPowers_add_one q ho hp
        let r := SurfaceAncestorKey.ofLabels g S h d k a
        have hr : r.totalPsi = 0 := by
          dsimp only [r]
          rw [SurfaceAncestorKey.totalPsi_ofLabels]
          omega
        have hp' := r.totalPsi_eq_zero_iff.mp hr
        change (if r.genus = 0 then rationalValue X v₀ r else ellipticFuel X v₀ v₁ 0 r) =
          primaryAt v₀ v₁ g d _
        by_cases h0 : g = 0
        · have hrg : r.genus = 0 := h0
          rw [if_pos hrg, rationalValue, hr, rationalFuel, if_pos ⟨hrg, hp'⟩,
            primaryAt, if_pos h0]
          exact congrArg _ (primaryLabels_ofLabels ..)
        · have hrg : r.genus ≠ 0 := h0
          have ho' : r.genus = 1 := by
            change g = 1
            omega
          rw [if_neg hrg, ellipticFuel, if_pos ⟨ho', hp'⟩, primaryAt, if_neg h0]
          exact congrArg _ (primaryLabels_ofLabels ..)
      _ = 0 := graph_one_edge_zero _ _ _ _ _ (PsiBoundaryExpansion.genusOneTerms_edgeCount _ t ht)
        (fun _ _ eq ↦ hs _ _ (eq.trans ho.symm)) (fun _ eq ↦ hl _ (eq.trans ho.symm))

end AxiomaticGW.SurfaceLowGenusPointCache

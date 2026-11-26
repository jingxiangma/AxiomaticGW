/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.LowGenusAncestorDimension
public import AxiomaticGW.Surfaces.LowGenusPointCache

/-! # Virtual-dimension vanishing in the reconstructed lower genera

Contracting dual basis labels adds two to the cohomological codimension. The two new
flags and the change of genus leave one unit of virtual codimension for each node.
The original one-node rational and elliptic cotangent equations therefore preserve virtual
dimension when one power is lowered. The primary inputs can be arbitrary point functions.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceLowGenusPointCache
variable {X : SurfaceTarget}

/-- External cotangent and state codimension minus the virtual dimension of a marked map. -/
def virtualDefect {S : Type} [Fintype S] (g : ℕ) (beta : X.Curve) (k : S → ℕ)
    (a : S → SurfaceBasisLabel X) : ℤ :=
  (∑ s, k s : ℕ) + ((∑ s, (a s).codimension : ℕ) : ℤ) -
    (X.c1Degree beta + (g : ℤ) - 1 + Fintype.card S)

/-- The executable query dimension test agrees with the labelled component grading. -/
theorem virtualDefect_ofLabels (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    (SurfaceAncestorKey.ofLabels g S h beta k a).DimensionCompatible ↔
      virtualDefect g beta k a = 0 := by
  unfold SurfaceAncestorKey.DimensionCompatible SurfaceAncestorKey.totalCodimension
    SurfaceAncestorKey.ofLabels virtualDefect
  simp only [Multiset.map_map, Function.comp_def, Multiset.card_map, Finset.card_val,
    Finset.card_univ]
  change ((∑ s, ((a s).codimension + k s) : ℕ) : ℤ) = _ ↔ _
  rw [Finset.sum_add_distrib, Nat.cast_add]
  omega

private theorem defect_separating {S T : Type} [Fintype S] [Fintype T]
    (g h : ℕ) (lhs rhs : X.Curve) (k : S ⊕ T → ℕ) (a : S ⊕ T → SurfaceBasisLabel X)
    (b : SurfaceBasisLabel X) :
    virtualDefect g lhs (PsiClasses.separatingLeftPowers k) (Option.elim · b (a ∘ Sum.inl)) +
    virtualDefect h rhs (PsiClasses.separatingRightPowers k) (Option.elim · b.dual (a ∘ Sum.inr)) =
      virtualDefect (g + h) (lhs + rhs) k a + 1 := by
  have hb : b.codimension + b.dual.codimension = 2 := by cases b <;> rfl
  have hk := PsiClasses.sum_separatingPowers k
  simp only [virtualDefect, Fintype.sum_option, Fintype.sum_sum_type, Fintype.card_option,
    Fintype.card_sum, Option.elim_none, Option.elim_some, Function.comp_apply, map_add,
    Nat.cast_add, Nat.cast_one]
  simp only [Fintype.sum_sum_type, Fintype.sum_option] at hk
  omega

private theorem defect_nonseparating {S : Type} [Fintype S] (g : ℕ) (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) (b : SurfaceBasisLabel X) :
    virtualDefect g beta (PsiClasses.nonseparatingPowers k)
      (Option.elim · b (fun t ↦ Option.elim t b.dual a)) =
      virtualDefect (g + 1) beta k a + 1 := by
  have hb : b.codimension + b.dual.codimension = 2 := by cases b <;> rfl
  have hk := PsiClasses.sum_nonseparatingPowers k
  simp only [Fintype.sum_option] at hk
  simp only [virtualDefect, Fintype.sum_option,
    Fintype.card_option, Option.elim_none, Option.elim_some, Nat.cast_add, Nat.cast_one]
  omega

/-- Each edge accounts for one additional codimension. If all terminal components respect
virtual dimension, the full graph does as well. -/
theorem graph_zero_of_virtual_dimension {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (v : SurfaceVertexValues X ℚ) (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X)
    (hv : ∀ g' T [Fintype T] (h : StableArity g' T) beta' k' a', g' ≤ g →
      virtualDefect g' beta' k' a' ≠ 0 → v g' T h beta' k' a' = 0)
    (hn : virtualDefect g beta k a + x.graph.graph.edgeCount ≠ 0) :
    x.surfaceEval X v beta k a = 0 := by
  induction x generalizing beta with
  | fundamental g S h =>
    apply hv _ _ _ _ _ _ le_rfl
    simpa only [show (GluingExpression.fundamental g S h).graph.graph.edgeCount = 0 from rfl,
      Nat.cast_zero, add_zero] using hn
  | @relabel g S T _ _ e x ih =>
    apply ih beta (k ∘ e) (a ∘ e) hv
    have he : virtualDefect g beta (k ∘ e) (a ∘ e) = virtualDefect g beta k a := by
      unfold virtualDefect
      have h₁ := e.sum_comp k
      have h₂ := e.sum_comp (fun t ↦ (a t).codimension)
      simp only [Function.comp_apply] at h₁ h₂ ⊢
      rw [h₁, h₂, Fintype.card_congr e]
    rw [he]
    exact hn
  | @separating g h S T _ _ x y ihx ihy =>
    simp only [GluingExpression.surfaceEval]
    apply Finset.sum_eq_zero
    intro p hp
    rw [X.splittings_eq] at hp
    have hsplit : p.1+p.2 = beta := (X.effective.mem_splittings _ _ _).mp hp
    apply Finset.sum_eq_zero
    intro b _
    have hb := defect_separating g h p.1 p.2 k a b
    rw [hsplit] at hb
    have he : (x.separating y).graph.graph.edgeCount =
        x.graph.graph.edgeCount + y.graph.graph.edgeCount + 1 := rfl
    rw [he, Nat.cast_add, Nat.cast_add, Nat.cast_one] at hn
    by_cases bad : virtualDefect g p.1 (PsiClasses.separatingLeftPowers k)
        (Option.elim · b (a ∘ Sum.inl)) + x.graph.graph.edgeCount = 0
    · rw [ihy p.2 _ _ (fun _ _ _ _ _ _ _ hl ↦ hv _ _ _ _ _ _ (by omega)) (by omega)]
      simp only [mul_zero]
    · rw [ihx p.1 _ _ (fun _ _ _ _ _ _ _ hl ↦ hv _ _ _ _ _ _ (by omega)) bad]
      simp only [zero_mul, mul_zero]
  | @nonseparating g S _ x ih =>
    simp only [GluingExpression.surfaceEval]
    apply Finset.sum_eq_zero
    intro b _
    rw [ih beta _ _ (fun _ _ _ _ _ _ _ hl ↦ hv _ _ _ _ _ _ (by omega)) (by
      rw [defect_nonseparating]
      change virtualDefect (g + 1) beta k a + ((x.graph.graph.edgeCount + 1 : ℕ) : ℤ) ≠ 0 at hn
      omega), mul_zero]
private theorem primary_defect_zero (q : SurfaceAncestorKey X) (hp : q.IsPrimary)
    (hn : ¬q.DimensionCompatible) (v₀ v₁ : X.Curve → ℚ) :
    (q.genus = 0 → rationalPrimary X v₀ q.beta q.primaryLabels = 0) ∧
    (q.genus = 1 → ellipticPrimary X v₁ q.beta q.primaryLabels = 0) := by
  have hc : q.totalCodimension = (q.primaryLabels.map SurfaceBasisLabel.codimension).sum := by
    unfold SurfaceAncestorKey.totalCodimension SurfaceAncestorKey.primaryLabels
    rw [Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro s hs
    exact Nat.add_eq_left.mpr (hp s hs)
  have hcard : q.primaryLabels.card = q.insertions.card := Multiset.card_map _ _
  unfold SurfaceAncestorKey.DimensionCompatible at hn
  rw [hc, ← hcard] at hn
  have pos (hb : q.beta ≠ 0) : 0 < X.effective.energy q.beta :=
    Nat.pos_of_ne_zero fun h ↦ hb ((X.effective.energy_eq_zero_iff _).mp h)
  have degrees (hf : (q.primaryLabels.map (SurfaceBasisLabel.primaryFactor q.beta)).prod ≠ 0) :
      (q.primaryLabels.map SurfaceBasisLabel.codimension).sum =
      q.primaryLabels.card + q.primaryLabels.count .point := by
    have h := SurfaceBasisLabel.sum_codimension_add_units q.primaryLabels
    rw [Multiset.count_eq_zero.mpr (q.unit_not_mem_of_primaryCoefficient_ne_zero hf), add_zero] at h
    exact h
  constructor
  · intro hg
    rw [rationalPrimary]
    split_ifs with hb hpoints
    · rw [SurfacePrimary.classicalValue]
      split_ifs with hm
      · rw [hg, hb, map_zero] at hn
        exact (SurfaceBasisLabel.prod_value_mem_degree q.primaryLabels).2.2 (by omega)
      · rfl
    · dsimp only
      split_ifs with hf
      · rfl
      · have hd := degrees hf
        have he := pos hb
        change ¬((_ : ℕ) : ℤ) = (X.effective.energy q.beta : ℤ) + q.genus - 1 +
          q.primaryLabels.card at hn
        omega
    · rfl
  · intro hg
    rw [ellipticPrimary]
    split_ifs with hb hpoints
    · rw [SurfacePrimary.genusOneZeroValue]
      split_ifs with hs
      · obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hs
        rw [ha, Multiset.map_singleton, Multiset.sum_singleton]
        rw [hg, hb, map_zero, ha, Multiset.map_singleton, Multiset.sum_singleton,
          Multiset.card_singleton] at hn
        cases a <;> first | rfl | exact False.elim (hn (by change (1 : ℤ) = _; decide))
      · rfl
    · dsimp only
      split_ifs with hf
      · rfl
      · have hd := degrees hf
        change ¬((_ : ℕ) : ℤ) = (X.effective.energy q.beta : ℤ) + q.genus - 1 +
          q.primaryLabels.card at hn
        omega
    · rfl

private theorem frame_defect {g : ℕ} {q : SurfaceAncestorKey X} {S : Type} [Fintype S]
    (e : S ≃ Fin q.orderedInsertions.length) (k : S → ℕ) (hg : q.genus = g)
    (hpower : (∑ s, k s) + 1 = q.totalPsi) (hn : ¬q.DimensionCompatible) :
    virtualDefect g q.beta k (q.orderedLabels ∘ e) + 1 ≠ 0 := by
  have hd := (virtualDefect_ofLabels q.genus _ q.ordered_stable q.beta
    q.orderedPowers q.orderedLabels).not.mp (by rw [q.of_ordered_eq]; exact hn)
  have hs := e.sum_comp (fun t ↦ (q.orderedLabels t).codimension)
  unfold virtualDefect at hd ⊢
  simp only [Function.comp_apply, hs, Fintype.card_congr e, q.sum_orderedPowers, hg] at hd ⊢
  omega

/-- The rational boundary recursion vanishes off virtual dimension at every fuel value. -/
theorem rationalFuel_zero_of_dimension (v₀ : X.Curve → ℚ) (fuel : ℕ) (q : SurfaceAncestorKey X)
    (hg : q.genus = 0) (hn : ¬q.DimensionCompatible) : rationalFuel X v₀ fuel q = 0 := by
  induction fuel generalizing q with
  | zero =>
    rw [rationalFuel]
    split_ifs with hp
    · exact (primary_defect_zero q hp.2 hn v₀ v₀).1 hg
    · rfl
  | succ fuel ih =>
    rw [rationalFuel, dif_pos hg]
    split_ifs with hp
    · exact (primary_defect_zero q hp hn v₀ v₀).1 hg
    · unfold SurfaceGenusZero.ancestorStep
      apply List.sum_eq_zero
      intro z hz
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
      apply mul_eq_zero_of_right
      apply graph_zero_of_virtual_dimension
      · intro g' S _ h beta k a hgen hn'
        exact ih _ (Nat.eq_zero_of_le_zero hgen) ((virtualDefect_ofLabels _ _ _ _ _ _).not.mpr hn')
      · rw [PsiBoundaryExpansion.genusZeroTerms_edgeCount 0 _ t ht]
        exact frame_defect _ _ hg (SurfaceGenusZero.sum_lowerAncestorPowers_add_one q hg hp) hn

/-- The elliptic boundary recursion has the same vanishing for both primary input functions. -/
theorem ellipticFuel_zero_of_dimension (v₀ v₁ : X.Curve → ℚ) (fuel : ℕ) (q : SurfaceAncestorKey X)
    (hg : q.genus = 1) (hn : ¬q.DimensionCompatible) : ellipticFuel X v₀ v₁ fuel q = 0 := by
  induction fuel generalizing q with
  | zero =>
    rw [ellipticFuel]
    split_ifs with hp
    · exact (primary_defect_zero q hp.2 hn v₀ v₁).2 hg
    · rfl
  | succ fuel ih =>
    rw [ellipticFuel, dif_pos hg]
    split_ifs with hp
    · exact (primary_defect_zero q hp hn v₀ v₁).2 hg
    · unfold ellipticStep
      apply List.sum_eq_zero
      intro z hz
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
      apply mul_eq_zero_of_right
      apply graph_zero_of_virtual_dimension
      · intro g' S _ h beta k a hgen hn'
        have hd := (virtualDefect_ofLabels _ _ h _ _ _).not.mpr hn'
        dsimp only
        split_ifs with hz
        · exact rationalFuel_zero_of_dimension _ _ _ hz hd
        · apply ih _ _ hd
          change g' = 1
          change g' ≠ 0 at hz
          omega
      · rw [PsiBoundaryExpansion.genusOneTerms_edgeCount _ t ht]
        exact frame_defect _ _ hg (SurfaceGenusOne.sum_lowerAncestorPowers_add_one q hg hp) hn

/-- Uniform off-dimension vanishing for every original rational or elliptic component. -/
theorem component_zero_of_dimension (v₀ v₁ : X.Curve → ℚ) (q : SurfaceAncestorKey X)
    (hg : q.genus ≤ 1) (hn : ¬q.DimensionCompatible) : componentValue X v₀ v₁ q = 0 := by
  unfold componentValue
  split_ifs with hr
  · exact rationalFuel_zero_of_dimension _ _ _ hr hn
  · exact ellipticFuel_zero_of_dimension _ _ _ _ (by omega) hn

end AxiomaticGW.SurfaceLowGenusPointCache

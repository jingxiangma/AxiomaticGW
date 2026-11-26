/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Coefficients.AffineCoefficient
public import AxiomaticGW.Surfaces.OnePsiSupport
public import AxiomaticGW.Surfaces.GenusTwoTerms

/-!
# Leading coefficients of normalized genus-two contractions

A residual genus-two variable in a separating contraction can only come from
one component. At the original full curve class, every other component has
class zero. This gives an exact coefficient evaluator using degree-zero
contractions and direct primary/first-descendant normalization. The result
includes zero input class and all node and external cotangent powers.

The evaluator computes the matrix of a coupled system. It does not assert
invertibility or discard the smaller-class terms from the complete equation.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction
open SurfaceGenusZero (variableCurve)
variable {X : SurfaceTarget}

/-- Reconstructed genera below two leave only constant monomials. -/
theorem TermsBound.monomial_eq_zero_of_genus_lt {g : ℕ} {beta : X.Curve}
    {p : RationalTerms (SurfaceAncestorKey X)} (hp : TermsBound g beta p) (hg : g < 2)
    (t : ℚ × Multiset (SurfaceAncestorKey X)) (ht : t ∈ p) : t.2 = 0 := by
  rcases ((hp.mono (by omega)) t ht).affine with hz | ⟨q, hq, hgen, _⟩
  · exact hz
  · have hbound := (hp t ht).2.1
    simp only [hq, Multiset.map_singleton, Multiset.sum_singleton, hgen] at hbound
    omega

/-- At total genus at most two, two residual monomials cannot both be nonconstant. -/
theorem TermsBound.constant_factor {g h : ℕ} {beta gamma : X.Curve}
    {p q : RationalTerms (SurfaceAncestorKey X)} (hp : TermsBound g beta p)
    (hq : TermsBound h gamma q) (hgen : g + h ≤ 2)
    (s : ℚ × Multiset (SurfaceAncestorKey X)) (hs : s ∈ p)
    (t : ℚ × Multiset (SurfaceAncestorKey X)) (ht : t ∈ q) : s.2 = 0 ∨ t.2 = 0 := by
  by_cases hg : g < 2
  · exact Or.inl (hp.monomial_eq_zero_of_genus_lt hg s hs)
  · exact Or.inr (hq.monomial_eq_zero_of_genus_lt (by omega) t ht)

/-- No residual singleton survives below genus two, under any substitution. -/
theorem TermsBound.substituted_coefficient_eq_zero_of_genus_lt {g : ℕ}
    {beta : X.Curve} {p : RationalTerms (SurfaceAncestorKey X)}
    (hp : TermsBound g beta p) (hg : g < 2)
    (f : SurfaceAncestorKey X → RationalTerms (Variable X)) (v : Variable X) :
    RationalTerms.coefficient (RationalTerms.affineSubstitute f p) {v} = 0 := by
  rw [RationalTerms.coefficient_affineSubstitute_singleton]
  apply Multiset.sum_eq_zero
  intro c hc
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hc
  rw [hp.monomial_eq_zero_of_genus_lt hg t ht, Multiset.map_zero,
    Multiset.sum_zero, mul_zero]

/-- Direct normalization cannot create a variable above the input energy. -/
theorem TermsBound.direct_coefficient_eq_zero_of_energy_lt {g : ℕ}
    {beta : X.Curve} {p : RationalTerms (SurfaceAncestorKey X)}
    (hp : TermsBound g beta p) (hg : g ≤ 2) (v : Variable X)
    (he : X.effective.energy beta < X.effective.energy (variableCurve v)) :
    RationalTerms.coefficient
      (RationalTerms.affineSubstitute directNormalizedTerms p) {v} = 0 := by
  rw [RationalTerms.coefficient_affineSubstitute_singleton]
  apply Multiset.sum_eq_zero
  intro c hc
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hc
  rcases ((hp.mono hg) t ht).affine with hz | ⟨q, hq, hgen, _, delta, hdelta⟩
  · rw [hz, Multiset.map_zero, Multiset.sum_zero, mul_zero]
  · rw [hq, Multiset.map_singleton, Multiset.sum_singleton,
      coefficient_directNormalizedTerms_eq_zero q (by omega) v, mul_zero]
    intro hv
    have hd := congrArg X.effective.energy hdelta
    rw [map_add, ← hv] at hd
    omega

/-- A coefficient before calibration tails, retaining the full decorated contraction. -/
def directCoefficient {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (d : x.CotangentDecoration) (beta : X.Curve) (k : S → ℕ)
    (a : S → SurfaceBasisLabel X) (v : Variable X) : ℚ :=
  RationalTerms.coefficient (RationalTerms.affineSubstitute directNormalizedTerms
    (x.surfaceDecoratedTerms X (vertexTerms X) d beta k a)) {v}

/-- Constant coefficient of the degree-zero decorated contraction. -/
def constantCoefficient {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (d : x.CotangentDecoration) (k : S → ℕ) (a : S → SurfaceBasisLabel X) : ℚ :=
  RationalTerms.coefficient (x.surfaceDecoratedTerms X (vertexTerms X) d 0 k a) 0

theorem directCoefficient_genus_lt {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (hg : g < 2) (d : x.CotangentDecoration)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) (v : Variable X) :
    directCoefficient x d beta k a v = 0 :=
  (termsBound_decorated x d beta k a).substituted_coefficient_eq_zero_of_genus_lt
    hg directNormalizedTerms v

theorem directCoefficient_energy_lt {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (hg : g ≤ 2) (d : x.CotangentDecoration)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) (v : Variable X)
    (he : X.effective.energy beta < X.effective.energy (variableCurve v)) :
    directCoefficient x d beta k a v = 0 :=
  (termsBound_decorated x d beta k a).direct_coefficient_eq_zero_of_energy_lt hg v he

/-- The vertex contribution needs no positive-class lower-genus value. -/
theorem directCoefficient_fundamental (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (hg : g ≤ 2) (d : S → ℕ) (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) (v : Variable X) :
    directCoefficient (.fundamental g S h) d beta k a v =
      if g = 2 then
        let q := SurfaceAncestorKey.ofLabels g S h beta (k + d) a
        if q.DimensionCompatible then
          RationalTerms.coefficient (directNormalizedTerms q) {v} else 0
      else 0 := by
  by_cases htwo : g = 2
  · subst g
    simp only [directCoefficient, GluingExpression.surfaceDecoratedTerms, vertexTerms,
      residualTerms, SurfaceAncestorKey.ofLabels, Nat.reduceLeDiff, if_false, if_true]
    split_ifs with hd
    · rw [RationalTerms.coefficient_affineSubstitute_term, Multiset.map_singleton,
        Multiset.sum_singleton, one_mul]
    · exact RationalTerms.coefficient_affineSubstitute_zero _ _
  · rw [if_neg htwo]
    exact directCoefficient_genus_lt (.fundamental g S h) (by omega) d beta k a v

private theorem sum_splittings_leading (beta : X.Curve) (c l c' l' : X.Curve → ℚ)
    (hl : ∀ gamma, X.effective.energy gamma < X.effective.energy beta → l gamma = 0)
    (hl' : ∀ gamma, X.effective.energy gamma < X.effective.energy beta → l' gamma = 0) :
    (X.splittings beta).sum (fun pair : X.Curve × X.Curve ↦
      c pair.1 * l' pair.2 + l pair.1 * c' pair.2) =
      c 0 * l' beta + l beta * c' 0 := by
  rw [Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_eq_single (0, beta)
    · intro pair hpair hne
      have hsum : pair.1 + pair.2 = beta := by
        rw [X.splittings_eq] at hpair
        exact (X.effective.mem_splittings _ _ _).mp hpair
      have hz : pair.1 ≠ 0 := by
        intro he
        apply hne
        exact Prod.ext he (by simpa only [he, zero_add] using hsum)
      have hpos : 0 < X.effective.energy pair.1 := Nat.pos_of_ne_zero
        (fun he ↦ hz ((X.effective.energy_eq_zero_iff _).mp he))
      have he := congrArg X.effective.energy hsum
      rw [map_add] at he
      rw [hl' pair.2 (by omega), mul_zero]
    · intro hn
      exact (hn (by rw [X.splittings_eq, X.effective.mem_splittings, zero_add])).elim
  · apply Finset.sum_eq_single (beta, 0)
    · intro pair hpair hne
      have hsum : pair.1 + pair.2 = beta := by
        rw [X.splittings_eq] at hpair
        exact (X.effective.mem_splittings _ _ _).mp hpair
      have hz : pair.2 ≠ 0 := by
        intro he
        apply hne
        exact Prod.ext (by simpa only [he, add_zero] using hsum) he
      have hpos : 0 < X.effective.energy pair.2 := Nat.pos_of_ne_zero
        (fun he ↦ hz ((X.effective.energy_eq_zero_iff _).mp he))
      have he := congrArg X.effective.energy hsum
      rw [map_add] at he
      rw [hl pair.1 (by omega), zero_mul]
    · intro hn
      exact (hn (by rw [X.splittings_eq, X.effective.mem_splittings, add_zero])).elim

/-- Only an input-class genus-two factor and a class-zero factor contribute.
The two summands remain valid when the input class itself is zero. -/
theorem directCoefficient_separating {g h : ℕ} {S T : Type} [Fintype S] [Fintype T]
    (x : GluingExpression g (Option S)) (y : GluingExpression h (Option T))
    (hgen : g + h ≤ 2) (dx : x.CotangentDecoration) (dy : y.CotangentDecoration)
    (beta : X.Curve) (k : S ⊕ T → ℕ) (a : S ⊕ T → SurfaceBasisLabel X)
    (v : Variable X) (hv : variableCurve v = beta) :
    directCoefficient (x.separating y) (dx, dy) beta k a v =
      ∑ b : SurfaceBasisLabel X, b.inverseWeight *
        (constantCoefficient x dx (PsiClasses.separatingLeftPowers k)
            (Option.elim · b (a ∘ Sum.inl)) *
          directCoefficient y dy beta (PsiClasses.separatingRightPowers k)
            (Option.elim · b.dual (a ∘ Sum.inr)) v +
        directCoefficient x dx beta (PsiClasses.separatingLeftPowers k)
            (Option.elim · b (a ∘ Sum.inl)) v *
          constantCoefficient y dy (PsiClasses.separatingRightPowers k)
            (Option.elim · b.dual (a ∘ Sum.inr))) := by
  let p (b : SurfaceBasisLabel X) (gamma : X.Curve) :=
    x.surfaceDecoratedTerms X (vertexTerms X) dx gamma (PsiClasses.separatingLeftPowers k)
      (Option.elim · b (a ∘ Sum.inl))
  let q (b : SurfaceBasisLabel X) (gamma : X.Curve) :=
    y.surfaceDecoratedTerms X (vertexTerms X) dy gamma (PsiClasses.separatingRightPowers k)
      (Option.elim · b.dual (a ∘ Sum.inr))
  have hp (b : SurfaceBasisLabel X) (gamma : X.Curve) : TermsBound g gamma (p b gamma) :=
    termsBound_decorated x dx gamma _ _
  have hq (b : SurfaceBasisLabel X) (gamma : X.Curve) : TermsBound h gamma (q b gamma) :=
    termsBound_decorated y dy gamma _ _
  change RationalTerms.coefficient
    (RationalTerms.affineSubstitute directNormalizedTerms
      (∑ pair ∈ X.splittings beta, ∑ b : SurfaceBasisLabel X,
        RationalTerms.scale b.inverseWeight (RationalTerms.mul (p b pair.1) (q b pair.2))))
      {v} = _
  simp only [RationalTerms.coefficient_affineSubstitute_sum,
    RationalTerms.coefficient_affineSubstitute_scale]
  have hprod (pair : X.Curve × X.Curve) (b : SurfaceBasisLabel X) :=
    RationalTerms.coefficient_affineSubstitute_mul directNormalizedTerms
      (p b pair.1) (q b pair.2) v ((hp b pair.1).constant_factor (hq b pair.2) hgen)
  simp only [hprod]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.mul_sum]
  congr 1
  apply sum_splittings_leading (X := X) beta
    (fun gamma ↦ RationalTerms.coefficient (p b gamma) 0)
    (fun gamma ↦ RationalTerms.coefficient
      (RationalTerms.affineSubstitute directNormalizedTerms (p b gamma)) {v})
    (fun gamma ↦ RationalTerms.coefficient (q b gamma) 0)
    (fun gamma ↦ RationalTerms.coefficient
      (RationalTerms.affineSubstitute directNormalizedTerms (q b gamma)) {v})
  · intro gamma he
    exact (hp b gamma).direct_coefficient_eq_zero_of_energy_lt (by omega) v
      (by simpa only [hv] using he)
  · intro gamma he
    exact (hq b gamma).direct_coefficient_eq_zero_of_energy_lt (by omega) v
      (by simpa only [hv] using he)

/-- A loop in total genus at most two leaves no genus-two residual component. -/
theorem directCoefficient_nonseparating {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g (Option (Option S))) (hg : g + 1 ≤ 2)
    (d : x.CotangentDecoration) (beta : X.Curve) (k : S → ℕ)
    (a : S → SurfaceBasisLabel X) (v : Variable X) :
    directCoefficient x.nonseparating d beta k a v = 0 := by
  simp only [directCoefficient, GluingExpression.surfaceDecoratedTerms,
    RationalTerms.coefficient_affineSubstitute_sum,
    RationalTerms.coefficient_affineSubstitute_scale]
  apply Finset.sum_eq_zero
  intro b _
  rw [(termsBound_decorated x d beta _ _).substituted_coefficient_eq_zero_of_genus_lt
    (by omega) directNormalizedTerms v, mul_zero]

/-- Compute a normalized leading coefficient without any positive-class
lower-genus reconstruction. Genus guards also avoid unused constant factors. -/
def leadingCoefficientEval (X : SurfaceTarget) (beta : X.Curve) (v : Variable X) :
    {g : ℕ} → {S : Type} → [Fintype S] →
      (x : GluingExpression g S) → g ≤ 2 → x.CotangentDecoration →
        (S → ℕ) → (S → SurfaceBasisLabel X) → ℚ
  | _, _, _, @GluingExpression.fundamental g S _ h, _, d, k, a =>
      if g = 2 then
        let q := SurfaceAncestorKey.ofLabels g S h beta (k + d) a
        if q.DimensionCompatible then
          RationalTerms.coefficient (directNormalizedTerms q) {v} else 0
      else 0
  | _, _, _, @GluingExpression.relabel _ _ _ _ _ e x, hg, d, k, a =>
      leadingCoefficientEval X beta v x hg d (k ∘ e) (a ∘ e)
  | _, _, _, @GluingExpression.separating g h _ _ _ _ x y, hg, d, k, a =>
      if g = 2 then
        ∑ b : SurfaceBasisLabel X, b.inverseWeight *
          (leadingCoefficientEval X beta v x (by omega) d.1
            (PsiClasses.separatingLeftPowers k) (Option.elim · b (a ∘ Sum.inl)) *
          constantCoefficient y d.2 (PsiClasses.separatingRightPowers k)
            (Option.elim · b.dual (a ∘ Sum.inr)))
      else if h = 2 then
        ∑ b : SurfaceBasisLabel X, b.inverseWeight *
          (constantCoefficient x d.1 (PsiClasses.separatingLeftPowers k)
            (Option.elim · b (a ∘ Sum.inl)) *
          leadingCoefficientEval X beta v y (by omega) d.2
            (PsiClasses.separatingRightPowers k) (Option.elim · b.dual (a ∘ Sum.inr)))
      else 0
  | _, _, _, @GluingExpression.nonseparating _ _ _ _, _, _, _, _ => 0

/-- Equality to the full direct coefficient, uniformly in classes and powers. -/
theorem leadingCoefficientEval_eq (beta : X.Curve) (v : Variable X)
    (hv : variableCurve v = beta) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (hg : g ≤ 2) (d : x.CotangentDecoration)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    leadingCoefficientEval X beta v x hg d k a = directCoefficient x d beta k a v := by
  induction x with
  | fundamental g S h => exact (directCoefficient_fundamental g S h hg d beta k a v).symm
  | relabel e x ih => exact ih hg d (k ∘ e) (a ∘ e)
  | @separating g h S T _ _ x y ihx ihy =>
    rw [directCoefficient_separating x y hg d.1 d.2 beta k a v hv]
    by_cases hx : g = 2
    · simp only [leadingCoefficientEval, if_pos hx, ihx,
        directCoefficient_genus_lt y (by omega), mul_zero, zero_add]
    · by_cases hy : h = 2
      · simp only [leadingCoefficientEval, if_neg hx, if_pos hy, ihy,
          directCoefficient_genus_lt x (by omega), zero_mul, add_zero]
      · simp only [leadingCoefficientEval, if_neg hx, if_neg hy,
          directCoefficient_genus_lt x (by omega), directCoefficient_genus_lt y (by omega),
          zero_mul, mul_zero, add_zero, Finset.sum_const_zero]
  | nonseparating x ih => exact (directCoefficient_nonseparating x hg d beta k a v).symm

end AxiomaticGW.SurfaceGenusTwo

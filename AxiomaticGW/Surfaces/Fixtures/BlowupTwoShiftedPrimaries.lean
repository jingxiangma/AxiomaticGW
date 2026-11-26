/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.LowGenusOnePsiSewing
public import AxiomaticGW.Surfaces.PointBenchmarkCache

/-! # Single-cotangent vanishing on the shifted strict-line and first ruling classes

On E₁+2L the only split with two nonvanishing positive rational point seeds is
(E₁+L, L), up to order. On 2E₁+L it is (E₁+L, E₁). In both cases the
intersection number is zero. Each elliptic split has a vanishing positive primary,
and the rational loop trace vanishes at the full class.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoShiftedPrimaries
open SurfaceLowGenusPointCache SurfacePointBenchmarkCache
abbrev X := SurfaceTarget.blowupTwo

/-- The two shifted source classes E₁+2L and 2E₁+L, respectively. -/
def source : Fin 2 → X.Curve := ![![1, 0, 2], ![2, 0, 1]]

private abbrev silent (g : ℕ) (d : X.Curve) : Prop :=
  d ≠ 0 ∧ (if g = 0 then genusZero X d else genusOne X d) = 0

private theorem primary_zero {g : ℕ} {d : X.Curve} (hv : silent g d)
    (m : Multiset (SurfaceBasisLabel X)) : primaryAt (genusZero X) (genusOne X) g d m = 0 := by
  obtain ⟨hd, hv⟩ := hv
  by_cases hz : g = 0
  · rw [if_pos hz] at hv
    rw [primaryAt, if_pos hz, rationalPrimary, if_neg hd]
    split_ifs <;> simp only [hv, mul_zero, ite_self]
  · rw [if_neg hz] at hv
    rw [primaryAt, if_neg hz, ellipticPrimary, if_neg hd]
    split_ifs <;> simp only [hv, mul_zero, ite_self]

private theorem support (i : Fin 2) (d e : X.Curve) (he : d + e = source i) :
    (silent 0 d ∨ silent 0 e ∨ (d ≠ 0 ∧ e ≠ 0 ∧ curveIntersection X d e = 0)) ∧
    (silent 0 d ∨ silent 1 e) ∧ (silent 1 d ∨ silent 0 e) := by
  have h : ∀ p ∈ X.splittings (source i),
      (silent 0 p.1 ∨ silent 0 p.2 ∨ (p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ curveIntersection X p.1 p.2 = 0)) ∧
      (silent 0 p.1 ∨ silent 1 p.2) ∧ (silent 1 p.1 ∨ silent 0 p.2) := by
    fin_cases i <;> decide +kernel
  apply h (d, e)
  rw [X.splittings_eq]
  exact (X.effective.mem_splittings _ _ _).mpr he

/-- Every stable genus-zero or genus-one vertex on either shifted class with precisely
one cotangent power vanishes in the original point-cached recursion. -/
theorem component_zero (i : Fin 2) (q : SurfaceAncestorKey X)
    (hb : q.beta = source i) (hg : q.genus ≤ 1) (hk : q.totalPsi = 1) :
    componentValue X (genusZero X) (genusOne X) q = 0 := by
  apply component_one_psi_zero_of_sewing _ _ q hg hk
  · intro g₁ g₂ hgen d e hde m n
    obtain ⟨h00, h01, h10⟩ := support i d e (hde.trans hb)
    have vanish (h : silent g₁ d ∨ silent g₂ e) :
        (∑ b : SurfaceBasisLabel X, b.inverseWeight *
          (primaryAt (genusZero X) (genusOne X) g₁ d (b ::ₘ m) *
           primaryAt (genusZero X) (genusOne X) g₂ e (b.dual ::ₘ n))) = 0 := by
      rcases h with hd|he
      · simp only [primary_zero hd, zero_mul, mul_zero, Finset.sum_const_zero]
      · simp only [primary_zero he, mul_zero, Finset.sum_const_zero]
    have gen : (g₁ = 0 ∧ g₂ = 0) ∨ (g₁ = 0 ∧ g₂ = 1) ∨ (g₁ = 1 ∧ g₂ = 0) := by omega
    rcases gen with ⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩
    · rcases h00 with hd | he | ⟨hd, he, ortho⟩
      · exact vanish (.inl hd)
      · exact vanish (.inr he)
      · change (∑ b : SurfaceBasisLabel X, b.inverseWeight *
          (rationalPrimary X (genusZero X) d (b ::ₘ m) *
            rationalPrimary X (genusZero X) e (b.dual ::ₘ n))) = 0
        rw [rationalPrimary_node_sewing _ _ _ hd he, ortho, zero_mul]
    · exact vanish h01
    · exact vanish h10
  · intro g₀ hgen m
    have hz : g₀ = 0 := by omega
    have hv : silent 0 (source i) := by fin_cases i <;> decide +kernel
    rw [hz, hb]
    simp only [primary_zero hv, mul_zero, Finset.sum_const_zero]

end AxiomaticGW.BlowupTwoShiftedPrimaries

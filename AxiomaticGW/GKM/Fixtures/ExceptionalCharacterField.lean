/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.ExceptionalAxisTransport
public import AxiomaticGW.GKM.Fixtures.ExceptionalBoundaryData
public import Mathlib.GroupTheory.OrderOfElement

/-! # Exceptional local characters in the exact two-variable coefficient field

The change from F₁ to the second exceptional edge of Bl₂ sends `(x,y)` to `(y−x,−x)`.
It preserves the origin and acts on complete rational functions, including removable poles.
-/

public section
namespace AxiomaticGW.GKM.ExceptionalCharacterField
open EquivariantCoefficients
open MvPolynomial (X C)
open ExceptionalAxisTransport
open CurveConventionCertificate (character edgeWeight)
noncomputable section

private abbrev px : Polynomial := X 0
private abbrev py : Polynomial := X 1

private def subst : Polynomial →+* Polynomial := MvPolynomial.eval₂Hom C ![py - px, -px]

private theorem subst_x : subst px = py - px := MvPolynomial.eval₂Hom_X' ..
private theorem subst_y : subst py = -px := MvPolynomial.eval₂Hom_X' ..
private theorem subst_c (r : ℚ) : subst (C r) = C r := MvPolynomial.eval₂Hom_C ..

private theorem subst_cube (p : Polynomial) : subst (subst (subst p)) = p := by
  apply DFunLike.congr_fun (f := (subst.comp subst).comp subst) (g := RingHom.id Polynomial) _ p
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, subst_c, RingHom.id_apply]
  · intro i
    fin_cases i
    · change subst (subst (subst px)) = px
      rw [subst_x, map_sub, subst_y, subst_x, map_sub, map_neg, subst_x, map_sub, subst_y, subst_x]
      ring
    · change subst (subst (subst py)) = py
      rw [subst_y, map_neg, subst_x, map_neg, map_sub, subst_y, subst_x]
      ring

/-- The polynomial automorphism. Its inverse is two successive forward substitutions. -/
def polynomial : Polynomial ≃+* Polynomial := RingEquiv.ofRingHom subst (subst.comp subst)
  (RingHom.ext subst_cube) (RingHom.ext subst_cube)

/-- The corresponding automorphism of the actual GKM fraction field. -/
def field : Coefficient ≃+* Coefficient := IsFractionRing.ringEquivOfRingEquiv polynomial

/-- Compatibility with the project's injective polynomial embedding. -/
theorem field_embed (p : Polynomial) : field (embed p) = embed (polynomial p) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _

/-- Transform both polynomials in any exact numerator/denominator presentation. -/
theorem field_fraction (n d : Polynomial) : field (embed n / embed d) =
    embed (polynomial n) / embed (polynomial d) := by rw [map_div₀, field_embed, field_embed]

/-- The declared pair of new characters is the image of the original field generators. -/
theorem field_generators : field x = y - x ∧ field y = -x := by
  constructor
  · rw [← embed_X_zero, field_embed, show polynomial (X 0) = _ from subst_x, map_sub]
    rfl
  · rw [← embed_X_one, field_embed, show polynomial (X 1) = _ from subst_y, map_neg]
    rfl

/-- The substitution fixes evaluation at the ordinary origin on every polynomial. -/
theorem polynomial_atZero (p : Polynomial) : atZero (polynomial p) = atZero p := by
  apply DFunLike.congr_fun (f := atZero.comp subst) (g := atZero) _ p
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply, subst_c]
  · intro i
    fin_cases i
    · change atZero (subst px) = atZero px
      rw [subst_x, map_sub]
      simp only [atZero, px, py, MvPolynomial.eval₂Hom_X', Pi.zero_apply, sub_zero]
    · change atZero (subst py) = atZero py
      rw [subst_y, map_neg]
      simp only [atZero, px, py, MvPolynomial.eval₂Hom_X', Pi.zero_apply, neg_zero]

/-- Both symbolic and ordinary denominator nonvanishing survive in both directions. -/
theorem denominator_iff (d : Polynomial) : (polynomial d ≠ 0 ↔ d ≠ 0) ∧
    (atZero (polynomial d) ≠ 0 ↔ atZero d ≠ 0) := by
  rw [polynomial_atZero, map_ne_zero_iff _ polynomial.injective]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- Three substitutions recover every rational function. -/
theorem cube (f : Coefficient) : field (field (field f)) = f := by
  obtain ⟨n, d, _, rfl⟩ := IsFractionRing.div_surjective Polynomial f
  rw [field_fraction, field_fraction, field_fraction]
  exact congrArg₂ (fun a b ↦ embed a / embed b) (subst_cube n) (subst_cube d)

/-- On any rational function the inverse is the square of the forward change. -/
theorem inverse_eq_square (f : Coefficient) : field.symm f = field (field f) := by
  apply field.injective
  rw [field.apply_symm_apply, cube]

/-- Explicit inverse character pair `(−y,x−y)`. -/
theorem inverse_variables : field.symm x = -y ∧ field.symm y = x - y := by
  rw [inverse_eq_square, inverse_eq_square, field_generators.1, field_generators.2,
    map_sub, map_neg,
    field_generators.1, field_generators.2]
  constructor <;> ring

/-- The change has order exactly three. -/
theorem order_three : orderOf field = 3 := by
  apply orderOf_eq_prime
  · ext f
    change field (field (field f)) = f
    exact cube f
  · intro hid
    have h := congrArg (fun a : Coefficient ≃+* Coefficient ↦ a y) hid
    rw [field_generators.2, RingAut.one_apply] at h
    have hn := embed_ne_zero_of_eval (px + py) (fun _ ↦ 1) (by
      rw [map_add, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
      norm_num)
    apply hn
    rw [map_add, embed_X_zero, embed_X_one, ← h, add_neg_cancel]

/-- Regular ordinary specialization at every value is preserved and reflected. -/
theorem specializes_iff (f : Coefficient) (q : ℚ) : Specializes (field f) q ↔ Specializes f q := by
  have forward (g : Coefficient) : Specializes g q → Specializes (field g) q := by
    rintro ⟨n, d, hd, rfl, hv⟩
    refine ⟨polynomial n, polynomial d, ?_, (field_fraction _ _).symm, ?_⟩
    · rwa [polynomial_atZero]
    · rwa [polynomial_atZero, polynomial_atZero]
  exact ⟨fun h ↦ cube f ▸ forward _ (forward _ h), forward f⟩

/-- The field transport uses the identity on E₁ and the order-three change on E₂. -/
@[expose] def sector (i : Fin 2) : Coefficient ≃+* Coefficient := ![RingEquiv.refl _, field] i

/-- The field substitution agrees with the character-lattice map on every integral weight. -/
theorem sector_character (i : Fin 2) (w : Fin 2 → ℤ) :
    sector i (character w) = character (characterChange i w) := by
  fin_cases i
  · rfl
  · change field (character w) = character (secondCharacterChange w)
    simp only [character, map_add, map_mul, map_intCast, field_generators.1, field_generators.2]
    change _ = ((-w 0 - w 1 : ℤ) : Coefficient) * x + (w 0 : Coefficient) * y
    push_cast
    ring

open CurveReplay.OneBlowup renaming tables → f1
open CurveReplay.TwoBlowups renaming tables → bl2

/-- The actual fraction-field map transports the edge weight, both normal weights,
and the two tangent characters at each fixed point, with the target-end branch exchange. -/
theorem local_field_weights (i : Fin 2) :
    let a := f1.edges 2; let b := bl2.edges (exceptionalEdge i)
    sector i (character a.weight) = character b.weight ∧
    sector i (character (edgeWeight f1 a.source a.normalSource)) =
      character (edgeWeight bl2 b.source b.normalSource) ∧
    sector i (character (edgeWeight f1 a.target a.normalTarget)) =
      character (edgeWeight bl2 b.target b.normalTarget) ∧
    ∀ j : Fin 2, sector i (character (f1.tangent a.source j)) =
      character (bl2.tangent b.source j) ∧ sector i (character (f1.tangent a.target j)) =
      character (bl2.tangent b.target j.rev) := by
  obtain ⟨h, _, _, h₁, h₂, ht⟩ := local_weights i
  simp only [sector_character, h, h₁, h₂, (ht _).1, (ht _).2, and_self, implies_true]

open SurfaceFrames.OneBlowup renaming request → oneFrame
open SurfaceFrames.TwoBlowups renaming request → twoFrame

/-- All five held insertion restrictions, with the hyperplane's character shift on E₁. -/
theorem insertion_transport (i p : Fin 2) :
    let a := f1.edges 2; let b := bl2.edges (exceptionalEdge i)
    let old j := sector i (oneFrame.restrictions (![a.source, a.target] p) j)
    twoFrame.restrictions (![b.source, b.target] p) =
      ![old 0, old 1 + (if i = 0 then x else 0), if i = 0 then old 2 else 0,
        if i = 1 then old 2 else 0, old 3] := by
  dsimp only
  rw [oneBlowup_restrictions p, twoBlowups_restrictions i p]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Matrix.head_cons, map_one, map_zero, zero_add, sector_character]

open ExceptionalBoundaryData (Factors factors)

/-- Apply a coefficient automorphism to all eleven entries of a pre-integration bridge packet. -/
def mapFactors (φ : Coefficient ≃+* Coefficient) (z : Factors) : Factors :=
  ⟨φ z.edge, φ z.tangent, φ z.insertions, φ z.eulerLeft, φ z.eulerRight, φ z.flagLeft,
    φ z.flagRight, φ z.automorphisms, φ z.boundary, φ z.psiLeft, φ z.psiRight⟩

/-- On the held degree-one bridge, every original producer factor agrees after transport. -/
theorem bridge_factors (i : Fin 2) : mapFactors (sector i) (factors .f1) =
    factors (![.first, .second] i) := by
  fin_cases i
  · rfl
  · change mapFactors field (factors .f1) = factors .second
    unfold mapFactors factors
    simp only [map_div₀, map_neg, map_one, map_add, map_sub, map_mul, map_pow, map_ofNat,
      field_generators.1, field_generators.2]
    congr 1 <;> ring_nf

/-- Edge propagation and tangent normalization transport before integration, for
every distribution of vertex genera and marked ends on the primitive exceptional edge. -/
theorem bridge_edge_tangent (i : Fin 2) :
    sector i ((factors .f1).edge * (factors .f1).tangent) =
      (factors (![.first, .second] i)).edge * (factors (![.first, .second] i)).tangent := by
  rw [map_mul]
  exact congrArg (fun a : Factors ↦ a.edge * a.tangent) (bridge_factors i)

end
end AxiomaticGW.GKM.ExceptionalCharacterField

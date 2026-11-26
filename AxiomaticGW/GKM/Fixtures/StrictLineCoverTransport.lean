/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.ExceptionalCoverFactors

/-! # Covers of the strict transform of the line through the two blowup centers

In the pinned effective basis L is (0,0,1). The unique target edge over this axis is
oriented from fixed point 2 to fixed point 3. The character substitution sends the
F₁ exceptional tangent and normal to the actual tangent and normal of L. The basis
restrictions below include the character shifts before performing localization sums.
-/

public section
namespace AxiomaticGW.GKM.StrictLineCoverTransport
open CurveConventionCertificate EquivariantCoefficients
open CurveReplay.OneBlowup renaming tables → f1
open CurveReplay.TwoBlowups renaming tables → bl2
open SurfaceFrames.OneBlowup renaming request → oneFrame
open SurfaceFrames.TwoBlowups renaming request → twoFrame

/-- Full Mori coordinate of the strict transform H−E₁−E₂. -/
@[expose] def line : SurfaceTarget.blowupTwo.Curve := ![0, 0, 1]

/-- Every sheet lies over the strict-line edge and all sheet numbers sum to d. -/
theorem class_iff (d : ℕ+) {v e : ℕ} (G : FixedGraphSupport bl2 v e) :
    G.degree = (d : ℕ) • line ↔ (∀ j, G.edgeIndex j = 3) ∧ ∑ j, (G.cover j : ℕ) = (d : ℕ) := by
  rw [show line = Pi.single (2 : Fin 3) 1 by decide +kernel]
  exact ExceptionalAxisTransport.degree_on_coordinate_iff bl2 3 2 (by decide +kernel)
    (by decide +kernel) d G

/-- A fixed graph of any positive pure strict-line degree has only these two vertex images. -/
theorem vertices (d : ℕ+) {v e : ℕ} (G : FixedGraphSupport bl2 v e)
    (hd : G.degree = (d : ℕ) • line) (w : Fin v) :
    G.image w = (bl2.edges 3).source ∨ G.image w = (bl2.edges 3).target :=
  ExceptionalAxisTransport.OverEdge.image_eq_endpoint (d := d) ⟨G, (class_iff d G).mp hd⟩ w

/-- Relabel the F₁ exceptional support on L, preserving the source graph and every cover degree. -/
def ofSizeEquiv (d : ℕ+) (v e : ℕ) :
    {G : FixedGraphSupport f1 v e //
      G.degree = (d : ℕ) • SurfaceTarget.hirzebruchOne.exceptionalCurve 0} ≃
    {G : FixedGraphSupport bl2 v e // G.degree = (d : ℕ) • line} :=
  let source := Equiv.subtypeEquivRight (ExceptionalAxisTransport.oneBlowup_class_iff d)
  let target := Equiv.subtypeEquivRight (class_iff d)
  (source.trans (ExceptionalAxisTransport.overEdgeEquiv f1 2 (by decide +kernel) bl2 3
    (by decide +kernel) d v e)).trans target.symm

/-- The original incidences and all individual covering multiplicities are preserved. -/
theorem graph_data (d : ℕ+) {v e : ℕ} (g : {G : FixedGraphSupport f1 v e //
    G.degree = (d : ℕ) • SurfaceTarget.hirzebruchOne.exceptionalCurve 0}) :
    (ofSizeEquiv d v e g).val.endpoint = g.val.endpoint ∧
    (ofSizeEquiv d v e g).val.cover = g.val.cover ∧
    ∀ w, (ofSizeEquiv d v e g).val.image w = if g.val.image w = (f1.edges 2).source
      then (bl2.edges 3).source else (bl2.edges 3).target :=
  ExceptionalAxisTransport.overEdgeEquiv_data f1 2 (by decide +kernel) bl2 3 (by decide +kernel) d
    ⟨g.val, (ExceptionalAxisTransport.oneBlowup_class_iff d g.val).mp g.property⟩

/-- Equivalence at the full curve class for all possible source sizes. -/
def supportEquiv (d : ℕ+) :
    FixedGraphSupport.AtDegree f1 ((d : ℕ) • SurfaceTarget.hirzebruchOne.exceptionalCurve 0) ≃
      FixedGraphSupport.AtDegree bl2 ((d : ℕ) • line) :=
  Equiv.sigmaCongrRight fun v ↦ Equiv.sigmaCongrRight fun e ↦ ofSizeEquiv d v e

/-- The integral change takes x to y and y to y−x, with inverse (x−y,x). -/
@[expose] def characterChange : (Fin 2 → ℤ) ≃+ (Fin 2 → ℤ) where
  toFun w := ![-w 1, w 0 + w 1]
  invFun w := ![w 0 + w 1, -w 0]
  left_inv w := by funext i; fin_cases i <;> dsimp <;> ring
  right_inv w := by funext i; fin_cases i <;> dsimp <;> ring
  map_add' a b := by funext i; fin_cases i <;> dsimp <;> ring

/-- The true tangent, adjacent transverse branches and both ordered tangent frames. -/
theorem local_weights : let a := f1.edges 2; let b := bl2.edges 3
    characterChange a.weight = b.weight ∧ a.normalDegree = -1 ∧ b.normalDegree = -1 ∧
    characterChange (edgeWeight f1 a.source a.normalSource) =
      edgeWeight bl2 b.source b.normalSource ∧
    characterChange (edgeWeight f1 a.target a.normalTarget) =
      edgeWeight bl2 b.target b.normalTarget ∧
    ∀ j : Fin 2, characterChange (f1.tangent a.source j) = bl2.tangent b.source j ∧
      characterChange (f1.tangent a.target j) = bl2.tangent b.target j.rev := by decide +kernel

noncomputable section
open MvPolynomial (X C)

private abbrev px : Polynomial := X 0
private abbrev py : Polynomial := X 1
private def sub (u v : Polynomial) : Polynomial →+* Polynomial := MvPolynomial.eval₂Hom C ![u,v]
private theorem sub_x (u v : Polynomial) : sub u v px = u := MvPolynomial.eval₂Hom_X' ..
private theorem sub_y (u v : Polynomial) : sub u v py = v := MvPolynomial.eval₂Hom_X' ..
private theorem sub_c (u v : Polynomial) (r : ℚ) : sub u v (C r) = C r := MvPolynomial.eval₂Hom_C ..

/-- Automorphism of the actual two-character polynomial ring. -/
def polynomial : Polynomial ≃+* Polynomial :=
  RingEquiv.ofRingHom (sub py (py-px)) (sub (px-py) px)
    (by
      apply MvPolynomial.ringHom_ext
      · intro r; simp only [RingHom.comp_apply, sub_c, RingHom.id_apply]
      · intro j
        fin_cases j
        · change sub py (py-px) (sub (px-py) px px) = px
          rw [sub_x, map_sub, sub_x, sub_y]
          ring
        · change sub py (py-px) (sub (px-py) px py) = py
          rw [sub_y, sub_x])
    (by
      apply MvPolynomial.ringHom_ext
      · intro r; simp only [RingHom.comp_apply, sub_c, RingHom.id_apply]
      · intro j
        fin_cases j
        · change sub (px-py) px (sub py (py-px) px) = px
          rw [sub_x, sub_y]
        · change sub (px-py) px (sub py (py-px) py) = py
          rw [sub_y, map_sub, sub_y, sub_x]
          ring)

/-- Extension of the character change to rational localization coefficients. -/
def field : Coefficient ≃+* Coefficient := IsFractionRing.ringEquivOfRingEquiv polynomial

theorem field_embed (p : Polynomial) : field (embed p) = embed (polynomial p) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _

private theorem at_origin (p : Polynomial) : atZero (polynomial p) = atZero p := by
  apply DFunLike.congr_fun (f := atZero.comp (sub py (py-px))) (g := atZero) _ p
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, sub_c]
  · intro j
    fin_cases j
    · change atZero (sub py (py-px) px) = atZero px
      simp only [sub_x, px, py, atZero, MvPolynomial.eval₂Hom_X', Pi.zero_apply]
    · change atZero (sub py (py-px) py) = atZero py
      simp only [sub_y, map_sub, px, py, atZero, MvPolynomial.eval₂Hom_X', Pi.zero_apply, sub_zero]

/-- Ordinary regularity and its value are preserved in both directions. -/
theorem specializes_iff (f : Coefficient) (q : ℚ) : Specializes (field f) q ↔ Specializes f q := by
  have undo (p : Polynomial) : atZero (polynomial.symm p) = atZero p := by
    simpa only [polynomial.apply_symm_apply] using (at_origin (polynomial.symm p)).symm
  constructor
  · rintro ⟨n, d, hd, hf, hq⟩
    refine ⟨polynomial.symm n, polynomial.symm d, ?_, ?_, ?_⟩
    · rwa [undo]
    · apply field.injective
      rwa [map_div₀, field_embed, field_embed, polynomial.apply_symm_apply,
        polynomial.apply_symm_apply]
    · rwa [undo, undo]
  · rintro ⟨n, d, hd, rfl, hq⟩
    refine ⟨polynomial n, polynomial d, ?_, ?_, ?_⟩
    · rwa [at_origin]
    · rw [map_div₀, field_embed, field_embed]
    · rwa [at_origin, at_origin]

theorem field_generators : field x = y ∧ field y = y-x := by
  constructor
  · rw [← embed_X_zero, field_embed, show polynomial px = py from sub_x _ _]
    rfl
  · rw [← embed_X_one, field_embed, show polynomial py = py-px from sub_y _ _, map_sub]
    rfl

/-- Every integral torus weight transforms by the same unimodular change. -/
theorem field_character (w : Fin 2 → ℤ) : field (character w) = character (characterChange w) := by
  change field ((w 0 : Coefficient)*x + (w 1 : Coefficient)*y) =
    ((-w 1 : ℤ) : Coefficient)*x + ((w 0 + w 1 : ℤ) : Coefficient)*y
  rw [map_add, map_mul, map_mul, map_intCast, map_intCast, field_generators.1, field_generators.2]
  push_cast
  ring

/-- The pinned source tangent of L is x. The transverse weights are y−x and y in endpoint order. -/
theorem line_characters : let b := bl2.edges 3
    character b.weight = x ∧ character (edgeWeight bl2 b.source b.normalSource) = y-x ∧
      character (edgeWeight bl2 b.target b.normalTarget) = y := by
  have h : let b := bl2.edges 3
      b.weight = ![1,0] ∧ edgeWeight bl2 b.source b.normalSource = ![-1,1] ∧
      edgeWeight bl2 b.target b.normalTarget = ![0,1] := by decide +kernel
  dsimp only
  rw [h.1, h.2.1, h.2.2]
  change ((1 : ℤ) : Coefficient) * x + ((0 : ℤ) : Coefficient) * y = x ∧
    ((-1 : ℤ) : Coefficient) * x + ((1 : ℤ) : Coefficient) * y = y-x ∧
    ((0 : ℤ) : Coefficient) * x + ((1 : ℤ) : Coefficient) * y = y
  push_cast
  constructor
  · ring
  · constructor <;> ring

/-- The tangent denominator of the degree-d edge deformation is nonzero in the native field. -/
theorem cover_tangent_ne_zero (d : ℕ+) : character (bl2.edges 3).weight / d.val ≠ 0 := by
  rw [line_characters.1]
  exact div_ne_zero x_ne_zero (Nat.cast_ne_zero.mpr d.ne_zero)

/-- The native vertex tangent normalizations transport for every number of incident flags. -/
theorem endpoint_tangents (k : ℕ) : let a := f1.edges 2; let b := bl2.edges 3
    field (ExceptionalCoverFactors.tangent f1 a.source k) =
      ExceptionalCoverFactors.tangent bl2 b.source k ∧
    field (ExceptionalCoverFactors.tangent f1 a.target k) =
      ExceptionalCoverFactors.tangent bl2 b.target k := by
  have h := local_weights.2.2.2.2.2
  simp only [ExceptionalCoverFactors.tangent, Fin.prod_univ_two, map_mul, map_pow, field_character,
    (h 0).1, (h 1).1, (h 0).2, (h 1).2]
  exact ⟨trivial, mul_comm _ _⟩

/-- The complete rational multiple-cover edge factor transports in every positive degree. -/
theorem cover_factor (d : ℕ+) : field (ExceptionalCoverFactors.atEdge f1 2 d) =
    ExceptionalCoverFactors.atEdge bl2 3 d := by
  rw [ExceptionalCoverFactors.atEdge, ExceptionalCoverFactors.atEdge,
    ExceptionalCoverFactors.map_factor, field_character, field_character, local_weights.1,
    local_weights.2.2.2.1]

/-- The product over all actual covers transports, including distinct degrees and parallel edges. -/
theorem graph_edge_product (d : ℕ+) {v e : ℕ} (g : {G : FixedGraphSupport f1 v e //
    G.degree = (d : ℕ) • SurfaceTarget.hirzebruchOne.exceptionalCurve 0}) :
    let h := (ofSizeEquiv d v e g).val
    field (∏ j, ExceptionalCoverFactors.atEdge f1 (g.val.edgeIndex j) (g.val.cover j)) =
      ∏ j, ExceptionalCoverFactors.atEdge bl2 (h.edgeIndex j) (h.cover j) := by
  let h := ofSizeEquiv d v e g
  have hs := ((ExceptionalAxisTransport.oneBlowup_class_iff d g.val).mp g.property).1
  have ht := ((class_iff d h.val).mp h.property).1
  dsimp only
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [hs j, ht j, (graph_data d g).2.1]
  exact cover_factor _

/-- Affine lift corrections in strict-line character coordinates, ordered as 1,H,E₁,E₂,pt. -/
@[expose] def lift (r : Fin 4 → Coefficient) : Fin 5 → Coefficient :=
  ![r 0, y*r 0-r 2, y*r 0-r 2, (y-x)*r 0-r 2, r 3]

/-- On both endpoints the three divisor lifts have coefficient −1 on the transported exceptional
restriction. Their unit shifts depend on the chosen native lifts. -/
theorem insertion_transport (p : Fin 2) : let a := f1.edges 2; let b := bl2.edges 3
    twoFrame.restrictions (![b.source, b.target] p) =
      lift (field ∘ oneFrame.restrictions (![a.source, a.target] p)) := by
  have source : oneFrame.restrictions (![(f1.edges 2).source, (f1.edges 2).target] p) =
      ![1, 0, ![y,x] p, 0] := by fin_cases p <;> funext j <;> fin_cases j <;> rfl
  have target : twoFrame.restrictions (![(bl2.edges 3).source, (bl2.edges 3).target] p) =
      ![![1,x,x,0,0], ![1,0,0,-x,0]] p := by fin_cases p <;> funext j <;> fin_cases j <;> rfl
  dsimp only
  rw [source, target]
  fin_cases p <;> funext j <;> fin_cases j <;> simp [lift, field_generators]

/-- The complete basis restriction transports at any marked vertex of any positive covered graph. -/
theorem vertex_restrictions (d : ℕ+) {v e : ℕ} (g : {G : FixedGraphSupport f1 v e //
    G.degree = (d : ℕ) • SurfaceTarget.hirzebruchOne.exceptionalCurve 0}) (w : Fin v) :
    twoFrame.restrictions ((ofSizeEquiv d v e g).val.image w) =
      lift (field ∘ oneFrame.restrictions (g.val.image w)) := by
  rw [(graph_data d g).2.2 w]
  rcases ExceptionalAxisTransport.oneBlowup_vertices d g.val g.property w with h | h
  · rw [if_pos h, h]
    exact insertion_transport 0
  · have hn : g.val.image w ≠ (f1.edges 2).source := h ▸ (by decide +kernel)
    rw [if_neg hn, h]
    exact insertion_transport 1

end
end AxiomaticGW.GKM.StrictLineCoverTransport

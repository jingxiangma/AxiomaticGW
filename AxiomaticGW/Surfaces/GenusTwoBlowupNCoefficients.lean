/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupNEEEPrimary
public import AxiomaticGW.Surfaces.GenusTwoBlowupNRelation

/-!
# Mixed BP coefficients of the shifted primary relation

The complete original EHH, EEH, EEE and HHH equations are combined at
`beta + E_i` with `energy(beta)` additional points and the exact coefficients
in `SurfaceGenusTwoBlowupNRelation.row`. Their primary coefficient at
`N_beta` is `6 * planeDegree(beta)`, uniformly on all full effective classes.
Signed exceptional multiplicities may be negative or zero, and class zero is
retained. Nonzero pivot use therefore requires positive plane degree.

The calculation retains all six marking assignments and the original complete
normalizer. EHH contributes `6 * alpha_i`; EEH and HHH contribute zero; EEE
contributes `12 - 18 * alpha_i`. The source-class nonprimary H, P and K terms
cancel in the four-row combination. Other classes and every primary tail remain
on the original polynomial. This file proves coefficients, not strict residual
support or a reconstruction recurrence.
-/

@[expose] public section
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwo GluingExpression
set_option maxRecDepth 20000
namespace AxiomaticGW.SurfaceGenusTwoBlowupNCoefficients
variable {X : SurfaceTarget}

/-- A classical rational triple with a zero product of its first two states vanishes. -/
theorem classical_orthogonal (b c : SurfaceBasisLabel X)
    (hbc : b.value * c.value = 0) (n : ℕ) (t : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) 0 n
      (![b, c, t] : Fin 3 → _) = 0 := by
  have hp : (∏ j : Fin 3, ((![b, c, t] : Fin 3 → SurfaceBasisLabel X) j).value) = 0 := by
    rw [Fin.prod_univ_three]
    change b.value * c.value * t.value = 0
    rw [hbc, zero_mul]
  simp only [SurfaceGenusZero.primaryScalar, ne_eq, not_true_eq_false, false_and,
    hp, mul_zero, map_zero, ite_true, ite_self]

/-- The original genus-two/rational join vanishes at zero remainder for an orthogonal rational
  pair. -/
theorem pair_orthogonal_zero (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ) (n : ℕ)
    (x : GluingExpression 2 (Fin 2)) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (a b c : SurfaceBasisLabel X)
    (hbc : b.value * c.value = 0) :
    let y := GetzlerGraphs.join (m := 1) (n := 2) 1 2 x
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
    remainderContraction X v main y (by exact (d, (0 : Fin 3 → ℕ)))
      (by exact (l, (inferInstance : DecidableEq (Fin 3)))) 0 n ![a, b, c] = 0 := by
  dsimp only
  rw [SurfaceGenusTwoBlowupPCoefficients.pair_join,
    (X.splittings_eq 0).trans X.effective.splittings_zero]
  simp only [Finset.sum_singleton]
  apply Finset.sum_eq_zero
  intro t _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [classical_orthogonal b c hbc]
  simp only [mul_zero]

/-- Either actual BP cotangent diagram vanishes for an orthogonal classical rational pair. -/
theorem paper_pair_orthogonal_zero (v : Variable X) (n : ℕ) (s : Fin 2)
    (a b c : SurfaceBasisLabel X)
    (hbc : b.value * c.value = 0) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) 0 n
        ![a, b, c] = 0 := by
  have h0 : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
  have h1 : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
  have hs : s = 0 ∨ s = 1 := by omega
  have he : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) 0 n
        ![a, b, c] =
      remainderContraction X v (remainderVertex X v (coefficientVertex X v))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          (fundamental 2 (Fin 2) (by norm_num [StableArity]))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        (by exact (Pi.single s 1, (0 : Fin 3 → ℕ)))
        (by exact ((inferInstance : DecidableEq (Fin 2)),
          (inferInstance : DecidableEq (Fin 3)))) 0 n ![a, b, c] := by
    rcases hs with rfl | rfl
    · rw [if_pos rfl, ← h0]
      rfl
    · rw [if_neg (by decide : (1 : Fin 2) ≠ 0), ← h1]
      rfl
  rw [he, pair_orthogonal_zero v _ n _ _ _ a b c hbc]


/-- All six EHH assignments retain twice the exceptional/point cotangent main at zero remainder. -/
theorem pair_markings_ehh (i : Fin X.blowups) (v : Variable X)
    (n : ℕ) (s : Fin 2) :
    (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm (if s = 0 then 2 else 3) e) 0 n
        ![.exceptional i, .hyperplane, .hyperplane]) =
      2 * remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
        (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0
        ![.exceptional i, .point] := by
  have hperm (e : Fin 6) :
      (![.exceptional i, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) ∘
        BelorousskiPandharipande.labelPermutation e =
      ![![.exceptional i, .hyperplane, .hyperplane],
        ![.exceptional i, .hyperplane, .hyperplane],
        ![.hyperplane, .exceptional i, .hyperplane],
        ![.hyperplane, .exceptional i, .hyperplane],
        ![.hyperplane, .hyperplane, .exceptional i],
        ![.hyperplane, .hyperplane, .exceptional i]] e := by
    funext t
    fin_cases e <;> fin_cases t <;> rfl
  simp only [SurfaceGenusTwoBlowupPCoefficients.remainder_orbit, hperm]
  rw [Fin.sum_univ_six]
  have hh : (.hyperplane : SurfaceBasisLabel X).value * (SurfaceBasisLabel.exceptional i :
    SurfaceBasisLabel X).value = 0 :=
    SurfaceCohomology.hyperplane_mul_exceptional X.blowups i
  have he : (.exceptional i : SurfaceBasisLabel X).value * (SurfaceBasisLabel.hyperplane :
    SurfaceBasisLabel X).value = 0 := by
    rw [mul_comm]
    exact hh
  have h0 := paper_pair_orthogonal_zero v n s .hyperplane (.exceptional i) .hyperplane he
  have h1 := paper_pair_orthogonal_zero v n s .hyperplane .hyperplane (.exceptional i) hh
  change remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) 0 n
        ![.exceptional i, .hyperplane, .hyperplane] +
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) 0 n
        ![.exceptional i, .hyperplane, .hyperplane] +
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) 0 n
        ![.hyperplane, .exceptional i, .hyperplane] +
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) 0 n
        ![.hyperplane, .exceptional i, .hyperplane] +
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) 0 n
        ![.hyperplane, .hyperplane, .exceptional i] +
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) 0 n
        ![.hyperplane, .hyperplane, .exceptional i] = _
  simp only [h0, h1, add_zero, SurfaceGenusTwoBlowupPCoefficients.paper_pair]
  ring

/-- All six EEH assignments retain minus twice the H/point cotangent main at zero remainder. -/
theorem pair_markings_eeh (i : Fin X.blowups) (v : Variable X)
    (n : ℕ) (s : Fin 2) :
    (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm (if s = 0 then 2 else 3) e) 0 n
        ![.exceptional i, .exceptional i, .hyperplane]) =
      -2 * remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
        (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0
        ![.hyperplane, .point] := by
  have hperm (e : Fin 6) :
      (![.exceptional i, .exceptional i, .hyperplane] : Fin 3 → SurfaceBasisLabel X) ∘
        BelorousskiPandharipande.labelPermutation e =
      ![![.exceptional i, .exceptional i, .hyperplane],
        ![.exceptional i, .hyperplane, .exceptional i],
        ![.exceptional i, .exceptional i, .hyperplane],
        ![.hyperplane, .exceptional i, .exceptional i],
        ![.exceptional i, .hyperplane, .exceptional i],
        ![.hyperplane, .exceptional i, .exceptional i]] e := by
    funext t
    fin_cases e <;> fin_cases t <;> rfl
  simp only [SurfaceGenusTwoBlowupPCoefficients.remainder_orbit, hperm]
  rw [Fin.sum_univ_six]
  have hh : (.hyperplane : SurfaceBasisLabel X).value * (SurfaceBasisLabel.exceptional i :
    SurfaceBasisLabel X).value = 0 :=
    SurfaceCohomology.hyperplane_mul_exceptional X.blowups i
  have he : (.exceptional i : SurfaceBasisLabel X).value * (SurfaceBasisLabel.hyperplane :
    SurfaceBasisLabel X).value = 0 := by
    rw [mul_comm]
    exact hh
  have h0 := paper_pair_orthogonal_zero v n s (.exceptional i) (.exceptional i) .hyperplane he
  have h1 := paper_pair_orthogonal_zero v n s (.exceptional i) .hyperplane (.exceptional i) hh
  change remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) 0 n
        ![.exceptional i, .exceptional i, .hyperplane] +
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) 0 n
        ![.exceptional i, .hyperplane, .exceptional i] +
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) 0 n
        ![.exceptional i, .exceptional i, .hyperplane] +
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) 0 n
        ![.hyperplane, .exceptional i, .exceptional i] +
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) 0 n
        ![.exceptional i, .hyperplane, .exceptional i] +
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) 0 n
        ![.hyperplane, .exceptional i, .exceptional i] = _
  simp only [h0, h1, zero_add, add_zero, SurfaceGenusTwoBlowupKCoefficients.paper_pair]
  ring

/-- The actual EHH coefficient retains exactly 6K_i minus 6alpha_i P at its requested nonprimary
  class. -/
theorem pointCoefficient_ehh_at_requested_class (i : Fin X.blowups) (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (n : ℕ) (he : X.effective.energy (SurfaceGenusZero.variableCurve v) = n + 1) :
    BelorousskiPandharipande.pointCoefficient X n (SurfaceGenusZero.variableCurve v)
      ![.exceptional i, .hyperplane, .hyperplane] v =
      6 * (if Sum.inr (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
        (.exceptional i) (n + 1)) = v then 1 else 0) -
      6 * ((X.signedMultiplicity (SurfaceGenusZero.variableCurve v) i : ℤ) : ℚ) *
        (if Sum.inr (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
          .point n) = v then 1 else 0) := by
  have hterm (j : Fin 20) (e : Fin 6) :
      SurfaceGenusTwo.pointCoefficient X v (BelorousskiPandharipande.orbitCotangentTerm j e)
        (SurfaceGenusZero.variableCurve v) n ![.exceptional i, .hyperplane, .hyperplane] =
      remainderPointCoefficient X v (coefficientVertex X v)
        (BelorousskiPandharipande.orbitCotangentTerm j e) 0 n
          ![.exceptional i, .hyperplane, .hyperplane] := by
    have h := remainderPointCoefficient_eq X v (coefficientVertex X v) rfl
      (BelorousskiPandharipande.orbitCotangentTerm j e) 0 n
      (![.exceptional i, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
    simpa only [add_zero] using h.symm
  have hz (e : Fin 6) : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 0 e) 0 n
      ![.exceptional i, .hyperplane, .hyperplane] = 0 := by
    rw [SurfaceGenusTwoBlowupPCoefficients.remainder_orbit,
      SurfaceGenusTwoBlowupPCoefficients.paper_zero v hv]
  have ho (e : Fin 6) : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 1 e) 0 n
      ![.exceptional i, .hyperplane, .hyperplane] = 0 := by
    rw [SurfaceGenusTwoBlowupPCoefficients.remainder_orbit,
      SurfaceGenusTwoBlowupPCoefficients.paper_one]
  simp only [BelorousskiPandharipande.pointCoefficient, hterm]
  rw [Fin.sum_univ_four]
  change -2 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 0 e) 0 n
        ![.exceptional i, .hyperplane, .hyperplane]) +
    2 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 1 e) 0 n
        ![.exceptional i, .hyperplane, .hyperplane]) +
    3 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 2 e) 0 n
        ![.exceptional i, .hyperplane, .hyperplane]) +
    -3 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 3 e) 0 n
        ![.exceptional i, .hyperplane, .hyperplane]) = _
  have h2 := pair_markings_ehh i v n (0 : Fin 2)
  have h3 := pair_markings_ehh i v n (1 : Fin 2)
  simp only [ite_true, if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h2 h3
  simp only [hz, ho, Finset.sum_const_zero, mul_zero, zero_add]
  rw [h2, h3, SurfaceGenusTwoBlowupKCoefficients.main_k i v hv n he,
    SurfaceGenusTwoBlowupKCoefficients.main_p i v hv n he]
  ring

/-- The actual EEH coefficient retains exactly minus 6H plus 6dP at its requested nonprimary
  class. -/
theorem pointCoefficient_eeh_at_requested_class (i : Fin X.blowups) (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (n : ℕ) (he : X.effective.energy (SurfaceGenusZero.variableCurve v) = n + 1) :
    BelorousskiPandharipande.pointCoefficient X n (SurfaceGenusZero.variableCurve v)
      ![.exceptional i, .exceptional i, .hyperplane] v =
      -6 * (if Sum.inr (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
        .hyperplane (n + 1)) = v then 1 else 0) +
      6 * (X.planeDegree (SurfaceGenusZero.variableCurve v) : ℚ) *
        (if Sum.inr (SurfaceFirstDescendant.query 2 (SurfaceGenusZero.variableCurve v)
          .point n) = v then 1 else 0) := by
  have hterm (j : Fin 20) (e : Fin 6) :
      SurfaceGenusTwo.pointCoefficient X v (BelorousskiPandharipande.orbitCotangentTerm j e)
        (SurfaceGenusZero.variableCurve v) n ![.exceptional i, .exceptional i, .hyperplane] =
      remainderPointCoefficient X v (coefficientVertex X v)
        (BelorousskiPandharipande.orbitCotangentTerm j e) 0 n
          ![.exceptional i, .exceptional i, .hyperplane] := by
    have h := remainderPointCoefficient_eq X v (coefficientVertex X v) rfl
      (BelorousskiPandharipande.orbitCotangentTerm j e) 0 n
      (![.exceptional i, .exceptional i, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
    simpa only [add_zero] using h.symm
  have hz (e : Fin 6) : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 0 e) 0 n
      ![.exceptional i, .exceptional i, .hyperplane] = 0 := by
    rw [SurfaceGenusTwoBlowupPCoefficients.remainder_orbit,
      SurfaceGenusTwoBlowupPCoefficients.paper_zero v hv]
  have ho (e : Fin 6) : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 1 e) 0 n
      ![.exceptional i, .exceptional i, .hyperplane] = 0 := by
    rw [SurfaceGenusTwoBlowupPCoefficients.remainder_orbit,
      SurfaceGenusTwoBlowupPCoefficients.paper_one]
  simp only [BelorousskiPandharipande.pointCoefficient, hterm]
  rw [Fin.sum_univ_four]
  change -2 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 0 e) 0 n
        ![.exceptional i, .exceptional i, .hyperplane]) +
    2 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 1 e) 0 n
        ![.exceptional i, .exceptional i, .hyperplane]) +
    3 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 2 e) 0 n
        ![.exceptional i, .exceptional i, .hyperplane]) +
    -3 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 3 e) 0 n
        ![.exceptional i, .exceptional i, .hyperplane]) = _
  have h2 := pair_markings_eeh i v n (0 : Fin 2)
  have h3 := pair_markings_eeh i v n (1 : Fin 2)
  simp only [ite_true, if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h2 h3
  simp only [hz, ho, Finset.sum_const_zero, mul_zero, zero_add]
  rw [h2, h3, SurfaceGenusTwoBlowupPCoefficients.main_h v hv n he,
    SurfaceGenusTwoBlowupPCoefficients.main_p v hv n he]
  ring

/-- An orthogonal rational triple carrying H vanishes at every full plane-zero class. -/
theorem primaryScalar_orthogonal_of_planeDegree_zero (b c : SurfaceBasisLabel X)
    (hbc : b.value * c.value = 0) (hH : b = .hyperplane ∨ c = .hyperplane)
    (delta : X.Curve) (hd : X.planeDegree delta = 0) (n : ℕ) (t : SurfaceBasisLabel X) :
    SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) delta n
      (![b, c, t] : Fin 3 → _) = 0 := by
  by_cases hz : delta = 0
  · rw [hz]
    exact classical_orthogonal b c hbc n t
  · rcases hH with hH | hH
    · exact SurfaceGenusZero.primaryScalar_eq_zero_of_hyperplane_zero _ delta hz
        ((X.planeDegree_eq_zero_iff_divisorIntersections_eq_zero delta).mp hd)
        (Fin 3) _ 0 hH n
    · exact SurfaceGenusZero.primaryScalar_eq_zero_of_hyperplane_zero _ delta hz
        ((X.planeDegree_eq_zero_iff_divisorIntersections_eq_zero delta).mp hd)
        (Fin 3) _ 1 hH n

/-- The original joined rational pair vanishes at every plane-zero remainder when its H pair is
  orthogonal. -/
theorem pair_orthogonal_of_planeDegree_zero (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ) (n : ℕ)
    (x : GluingExpression 2 (Fin 2)) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (delta : X.Curve) (hd : X.planeDegree delta = 0)
    (a b c : SurfaceBasisLabel X) (hbc : b.value * c.value = 0)
    (hH : b = .hyperplane ∨ c = .hyperplane) :
    let y := GetzlerGraphs.join (m := 1) (n := 2) 1 2 x
      (fundamental 0 (Fin 3) (by norm_num [StableArity]))
    remainderContraction X v main y (by exact (d, (0 : Fin 3 → ℕ)))
      (by exact (l, (inferInstance : DecidableEq (Fin 3)))) delta n ![a, b, c] = 0 := by
  dsimp only
  rw [SurfaceGenusTwoBlowupPCoefficients.pair_join]
  apply Finset.sum_eq_zero
  intro split hs
  have ha : split.1 + split.2 = delta := by
    rw [X.splittings_eq] at hs
    exact (X.effective.mem_splittings _ _ _).mp hs
  have hr : X.planeDegree split.2 = 0 := by
    have hh := congrArg X.planeDegree ha
    rw [map_add, hd] at hh
    omega
  apply Finset.sum_eq_zero
  intro t _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [primaryScalar_orthogonal_of_planeDegree_zero b c hbc hH split.2 hr ij.2 t.dual]
  simp only [mul_zero]

/-- Either BP cotangent diagram vanishes for an orthogonal rational H pair at every plane-zero
  remainder. -/
theorem paper_pair_orthogonal_of_planeDegree_zero (v : Variable X) (n : ℕ) (s : Fin 2)
    (delta : X.Curve) (hd : X.planeDegree delta = 0)
    (a b c : SurfaceBasisLabel X) (hbc : b.value * c.value = 0)
    (hH : b = .hyperplane ∨ c = .hyperplane) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![a, b, c] = 0 := by
  have h0 : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
  have h1 : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
  have hs : s = 0 ∨ s = 1 := by omega
  have he : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![a, b, c] =
      remainderContraction X v (remainderVertex X v (coefficientVertex X v))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          (fundamental 2 (Fin 2) (by norm_num [StableArity]))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        (by exact (Pi.single s 1, (0 : Fin 3 → ℕ)))
        (by exact ((inferInstance : DecidableEq (Fin 2)),
          (inferInstance : DecidableEq (Fin 3)))) delta n ![a, b, c] := by
    rcases hs with rfl | rfl
    · rw [if_pos rfl, ← h0]; rfl
    · rw [if_neg (by decide : (1 : Fin 2) ≠ 0), ← h1]; rfl
  rw [he, pair_orthogonal_of_planeDegree_zero v _ n _ _ _ delta hd a b c hbc hH]

/-- Either BP cotangent diagram with a rational HH pair inserts the point and keeps its full
  remainder. -/
theorem paper_pair_hh_of_planeDegree_zero (v : Variable X) (n : ℕ) (s : Fin 2)
    (delta : X.Curve) (hd : X.planeDegree delta = 0) (a : SurfaceBasisLabel X) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![a, .hyperplane, .hyperplane] =
      remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
        (by norm_num [StableArity]) (Pi.single s 1) inferInstance delta ![a, .point] := by
  have h0 : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
  have h1 : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
  have hs : s = 0 ∨ s = 1 := by omega
  have he : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![a, .hyperplane, .hyperplane] =
      remainderContraction X v (remainderVertex X v (coefficientVertex X v))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          (fundamental 2 (Fin 2) (by norm_num [StableArity]))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        (by exact (Pi.single s 1, (0 : Fin 3 → ℕ)))
        (by exact ((inferInstance : DecidableEq (Fin 2)),
          (inferInstance : DecidableEq (Fin 3)))) delta n ![a, .hyperplane, .hyperplane] := by
    rcases hs with rfl | rfl
    · rw [if_pos rfl, ← h0]; rfl
    · rw [if_neg (by decide : (1 : Fin 2) ≠ 0), ← h1]; rfl
  rw [he, SurfaceGenusTwoBlowupPPrimarySupport.pair_hh_of_planeDegree_zero v _ n _ _ _ delta hd a]
  rfl

/-- The six actual EHH assignments retain twice the exceptional/point main at any plane-zero
  remainder. -/
theorem pair_markings_ehh_of_planeDegree_zero (i : Fin X.blowups) (v : Variable X)
    (n : ℕ) (s : Fin 2) (delta : X.Curve) (hd : X.planeDegree delta = 0) :
    (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm (if s = 0 then 2 else 3) e) delta n
        ![.exceptional i, .hyperplane, .hyperplane]) =
      2 * remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
        (by norm_num [StableArity]) (Pi.single s 1) inferInstance delta
        ![.exceptional i, .point] := by
  have hperm (e : Fin 6) :
      (![.exceptional i, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) ∘
        BelorousskiPandharipande.labelPermutation e =
      ![![.exceptional i, .hyperplane, .hyperplane],
        ![.exceptional i, .hyperplane, .hyperplane],
        ![.hyperplane, .exceptional i, .hyperplane],
        ![.hyperplane, .exceptional i, .hyperplane],
        ![.hyperplane, .hyperplane, .exceptional i],
        ![.hyperplane, .hyperplane, .exceptional i]] e := by
    funext t
    fin_cases e <;> fin_cases t <;> rfl
  simp only [SurfaceGenusTwoBlowupPCoefficients.remainder_orbit, hperm]
  rw [Fin.sum_univ_six]
  have hh : (.hyperplane : SurfaceBasisLabel X).value * (SurfaceBasisLabel.exceptional i :
    SurfaceBasisLabel X).value = 0 :=
    SurfaceCohomology.hyperplane_mul_exceptional X.blowups i
  have he : (.exceptional i : SurfaceBasisLabel X).value * (SurfaceBasisLabel.hyperplane :
    SurfaceBasisLabel X).value = 0 := by
    rw [mul_comm]
    exact hh
  have h0 := paper_pair_orthogonal_of_planeDegree_zero v n s delta hd .hyperplane (.exceptional i)
    .hyperplane he (Or.inr rfl)
  have h1 := paper_pair_orthogonal_of_planeDegree_zero v n s delta hd .hyperplane .hyperplane
    (.exceptional i) hh (Or.inl rfl)
  change remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![.exceptional i, .hyperplane, .hyperplane] +
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![.exceptional i, .hyperplane, .hyperplane] +
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![.hyperplane, .exceptional i, .hyperplane] +
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![.hyperplane, .exceptional i, .hyperplane] +
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![.hyperplane, .hyperplane, .exceptional i] +
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3)) delta n
        ![.hyperplane, .hyperplane, .exceptional i] = _
  simp only [h0, h1, add_zero, paper_pair_hh_of_planeDegree_zero v n s delta hd]
  ring


/-- The original primary-main EHH graph vanishes at every plane-zero remainder. -/
theorem paper_zero_ehh (i : Fin X.blowups) (v : Variable X) (delta : X.Curve)
    (hd : X.planeDegree delta = 0) (n : ℕ) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 0) delta n
        ![.exceptional i, .hyperplane, .hyperplane] = 0 := by
  have h0 : (![0] : Fin 1 → ℕ) = 0 := by decide +kernel
  have hz : (![0, 0, 0] : Fin 3 → ℕ) = 0 := by decide +kernel
  have he : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 0) delta n
        ![.exceptional i, .hyperplane, .hyperplane] =
      remainderContraction X v (remainderVertex X v (coefficientVertex X v))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          SurfaceGenusTwoBlowupNEEEPrimary.primaryInner
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        ((![0], (0 : Fin 3 → ℕ)), (0 : Fin 3 → ℕ))
        (((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 3))),
          (inferInstance : DecidableEq (Fin 3))) delta n
        ![.exceptional i, .hyperplane, .hyperplane] := by
    rw [remainderPointCoefficient, if_pos (by decide +kernel)]
    change remainderContraction X v (remainderVertex X v (coefficientVertex X v))
      (GetzlerGraphs.join (m := 1) (n := 2) 1 2
        SurfaceGenusTwoBlowupNEEEPrimary.primaryInner
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      ((![0], ![0, 0, 0]), ![0, 0, 0]) _ delta n
        ![.exceptional i, .hyperplane, .hyperplane] = _
    rw [hz]; rfl
  exact he.trans ((SurfaceGenusTwoBlowupPPrimarySupport.pair_hh_of_planeDegree_zero v
    (remainderVertex X v (coefficientVertex X v)) n
    SurfaceGenusTwoBlowupNEEEPrimary.primaryInner
    (![0], (0 : Fin 3 → ℕ))
    ((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 3)))
    delta hd (.exceptional i)).trans (by
      rw [h0]
      exact SurfaceGenusTwoBlowupNEEEPrimary.primaryInner_exceptional_point_zero i v _ delta hd n))

/-- The original primary-main BP graph vanishes when its outer rational H pair is orthogonal. -/
theorem paper_zero_orthogonal_of_planeDegree_zero (v : Variable X) (delta : X.Curve)
    (hd : X.planeDegree delta = 0) (n : ℕ) (a b c : SurfaceBasisLabel X)
    (hbc : b.value * c.value = 0) (hH : b = .hyperplane ∨ c = .hyperplane) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 0) delta n ![a, b, c] = 0 := by
  have hz : (![0, 0, 0] : Fin 3 → ℕ) = 0 := by decide +kernel
  rw [remainderPointCoefficient, if_pos (by decide +kernel)]
  change remainderContraction X v (remainderVertex X v (coefficientVertex X v))
    (GetzlerGraphs.join (m := 1) (n := 2) 1 2
      (GetzlerGraphs.join (m := 0) (n := 2) 0 1
        (fundamental 2 (Fin 1) (by norm_num [StableArity]))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (fundamental 0 (Fin 3) (by norm_num [StableArity])))
    ((![0], ![0, 0, 0]), ![0, 0, 0])
    (((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 3))),
      (inferInstance : DecidableEq (Fin 3))) delta n ![a, b, c] = _
  rw [hz]
  exact pair_orthogonal_of_planeDegree_zero v _ n _ _ _ delta hd a b c hbc hH

/-- The original BP rational four-flag graph vanishes at plane-zero remainder if it carries H. -/
theorem paper_one_of_hyperplane_of_planeDegree_zero (v : Variable X) (delta : X.Curve)
    (hd : X.planeDegree delta = 0) (n : ℕ) (a : Fin 3 → SurfaceBasisLabel X)
    (s : Fin 3) (hs : a s = .hyperplane) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 1) delta n a = 0 := by
  have hx : (BelorousskiPandharipande.paperCotangentTerm 1).expression.maxComponentGenus = 2 :=
    by decide +kernel
  rw [remainderPointCoefficient, if_pos hx]
  change remainderContraction X v (remainderVertex X v (coefficientVertex X v))
    (GetzlerGraphs.join (m := 0) (n := 3) 0 3
      (fundamental 2 (Fin 1) (by norm_num [StableArity]))
      (fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (![1], (0 : Fin 4 → ℕ))
    ((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 4))) delta n a = _
  simp only [GetzlerGraphs.join, remainderContraction, ite_true, GluingExpression.pointContraction]
  apply Finset.sum_eq_zero
  intro split hsplit
  have ha : split.1 + split.2 = delta := by
    rw [X.splittings_eq] at hsplit
    exact (X.effective.mem_splittings _ _ _).mp hsplit
  have hd' : X.planeDegree split.2 = 0 := by
    have hh := congrArg X.planeDegree ha
    rw [map_add, hd] at hh
    omega
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  simp only [primaryPointVertex, and_self, ite_true]
  by_cases hz : split.2 = 0
  · rw [hz, SurfaceGenusTwoBlowupPCoefficients.classical_four]
    simp only [mul_zero]
  · rw [SurfaceGenusZero.primaryScalar_eq_zero_of_hyperplane_zero _ split.2 hz
      ((X.planeDegree_eq_zero_iff_divisorIntersections_eq_zero split.2).mp hd')
      (Fin 4) _ s.castSucc (by fin_cases s <;> exact hs) ij.2]
    simp only [mul_zero]

/-- The exact six covariant EHH labellings of the held BP orbit. -/
theorem ehh_permutation (i : Fin X.blowups) (e : Fin 6) :
    (![.exceptional i, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X) ∘
      BelorousskiPandharipande.labelPermutation e =
      ![![.exceptional i, .hyperplane, .hyperplane],
        ![.exceptional i, .hyperplane, .hyperplane],
        ![.hyperplane, .exceptional i, .hyperplane],
        ![.hyperplane, .exceptional i, .hyperplane],
        ![.hyperplane, .hyperplane, .exceptional i],
        ![.hyperplane, .hyperplane, .exceptional i]] e := by
  funext t; fin_cases e <;> fin_cases t <;> rfl

/-- At beta plus E_i, the full compressed EHH primary coefficient is six times the signed
  multiplicity of beta. -/
theorem pointCoefficient_ehh_primary_shifted (i : Fin X.blowups) (beta : X.Curve) :
    BelorousskiPandharipande.pointCoefficient X (X.effective.energy beta)
      (beta + X.exceptionalCurve i) ![.exceptional i, .hyperplane, .hyperplane]
      (.inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))) =
        6 * (X.signedMultiplicity beta i : ℚ) := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))
  have hterm (j : Fin 20) (e : Fin 6) :
      SurfaceGenusTwo.pointCoefficient X v (BelorousskiPandharipande.orbitCotangentTerm j e)
        (beta + X.exceptionalCurve i) (X.effective.energy beta)
        ![.exceptional i, .hyperplane, .hyperplane] =
      remainderPointCoefficient X v (coefficientVertex X v)
        (BelorousskiPandharipande.orbitCotangentTerm j e) (X.exceptionalCurve i)
        (X.effective.energy beta) ![.exceptional i, .hyperplane, .hyperplane] :=
    (remainderPointCoefficient_eq X v (coefficientVertex X v) rfl
      (BelorousskiPandharipande.orbitCotangentTerm j e) (X.exceptionalCurve i)
      (X.effective.energy beta) _).symm
  have hEH : (.exceptional i : SurfaceBasisLabel X).value *
      (SurfaceBasisLabel.hyperplane : SurfaceBasisLabel X).value = 0 := by
    rw [mul_comm]; exact SurfaceCohomology.hyperplane_mul_exceptional X.blowups i
  have hHE : (.hyperplane : SurfaceBasisLabel X).value *
      (SurfaceBasisLabel.exceptional i : SurfaceBasisLabel X).value = 0 :=
    SurfaceCohomology.hyperplane_mul_exceptional X.blowups i
  have hz (e : Fin 6) : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 0 e) (X.exceptionalCurve i)
      (X.effective.energy beta) ![.exceptional i, .hyperplane, .hyperplane] = 0 := by
    rw [SurfaceGenusTwoBlowupPCoefficients.remainder_orbit, ehh_permutation]
    fin_cases e
    · exact paper_zero_ehh i v _ (X.planeDegree_exceptionalCurve i) _
    · exact paper_zero_ehh i v _ (X.planeDegree_exceptionalCurve i) _
    · exact paper_zero_orthogonal_of_planeDegree_zero v _ (X.planeDegree_exceptionalCurve i)
        _ .hyperplane (.exceptional i) .hyperplane hEH (Or.inr rfl)
    · exact paper_zero_orthogonal_of_planeDegree_zero v _ (X.planeDegree_exceptionalCurve i)
        _ .hyperplane (.exceptional i) .hyperplane hEH (Or.inr rfl)
    · exact paper_zero_orthogonal_of_planeDegree_zero v _ (X.planeDegree_exceptionalCurve i)
        _ .hyperplane .hyperplane (.exceptional i) hHE (Or.inl rfl)
    · exact paper_zero_orthogonal_of_planeDegree_zero v _ (X.planeDegree_exceptionalCurve i)
        _ .hyperplane .hyperplane (.exceptional i) hHE (Or.inl rfl)
  have ho (e : Fin 6) : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 1 e) (X.exceptionalCurve i)
      (X.effective.energy beta) ![.exceptional i, .hyperplane, .hyperplane] = 0 := by
    rw [SurfaceGenusTwoBlowupPCoefficients.remainder_orbit]
    apply paper_one_of_hyperplane_of_planeDegree_zero v _ (X.planeDegree_exceptionalCurve i)
      _ _ ((BelorousskiPandharipande.labelPermutation e).symm 1)
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero]
  change BelorousskiPandharipande.pointCoefficient X _ _ _ v = _
  simp only [BelorousskiPandharipande.pointCoefficient, hterm]
  rw [Fin.sum_univ_four]
  change -2 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 0 e) (X.exceptionalCurve i)
      (X.effective.energy beta) ![.exceptional i, .hyperplane, .hyperplane]) +
    2 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 1 e) (X.exceptionalCurve i)
      (X.effective.energy beta) ![.exceptional i, .hyperplane, .hyperplane]) +
    3 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 2 e) (X.exceptionalCurve i)
      (X.effective.energy beta) ![.exceptional i, .hyperplane, .hyperplane]) +
    -3 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 3 e) (X.exceptionalCurve i)
      (X.effective.energy beta) ![.exceptional i, .hyperplane, .hyperplane]) = _
  have h2 := pair_markings_ehh_of_planeDegree_zero i v (X.effective.energy beta) (0 : Fin 2)
    (X.exceptionalCurve i) (X.planeDegree_exceptionalCurve i)
  have h3 := pair_markings_ehh_of_planeDegree_zero i v (X.effective.energy beta) (1 : Fin 2)
    (X.exceptionalCurve i) (X.planeDegree_exceptionalCurve i)
  simp only [ite_true, if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h2 h3
  simp only [hz, ho, Finset.sum_const_zero, mul_zero, zero_add]
  rw [h2, h3, SurfaceGenusTwoBlowupNEEEPrimary.main_exceptional_point_shifted i beta,
    SurfaceGenusTwoBlowupNEEEPrimary.main_point_exceptional_primary_zero i beta
      (X.effective.energy beta + 1)
      (X.exceptionalCurve i) (X.planeDegree_exceptionalCurve i) (X.effective.energy beta)]
  ring

/-- Either H/E_i cotangent main has zero primary coefficient at its own full class, for all point
  counts. -/
theorem main_hyperplane_exceptional_primary_zero (i : Fin X.blowups)
    (gamma : X.Curve) (m n : ℕ) (s : Fin 2) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 gamma m)
    remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0
      ![.hyperplane, .exceptional i] = 0 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 gamma m)
  have hs : (![.hyperplane, .exceptional i] : Fin 2 → SurfaceBasisLabel X) s ≠ .unit := by
    fin_cases s <;> intro h <;> cases h
  dsimp only
  rw [SurfaceGenusTwoBlowupPPrimary.remainderVertex_onePsi_zero_of_ne_unit v _ (Fin 2) _ s _ hs,
    SurfaceGenusTwoBlowupPPrimary.coefficient_residualTerms_eq_direct_at_class v _ rfl rfl]
  have hvb : SurfaceGenusZero.variableCurve v = gamma := rfl
  simp only [hvb]
  split_ifs with hd
  · rw [directNormalizedTerms_onePsi_ofLabels 2 le_rfl (Fin 2) _ s gamma _ n]
    have h0 : ((Finset.univ.erase (0 : Fin 2)).val.map
        (![.hyperplane, .exceptional i] : Fin 2 → SurfaceBasisLabel X)) = {.exceptional i} := rfl
    have h1 : ((Finset.univ.erase (1 : Fin 2)).val.map
        (![.hyperplane, .exceptional i] : Fin 2 → SurfaceBasisLabel X)) = {.hyperplane} := rfl
    rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
    · rw [h0, Matrix.cons_val_zero]
      apply SurfaceGenusTwoBlowupPPrimary.coefficient_terms_primary_zero
      · simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton,
          reduceCtorEq, and_false, or_self, not_false_eq_true]
      · intro h; cases h
      · simp only [SurfaceFirstDescendant.correctionCoefficient,
        SurfaceFirstDescendant.divisorSquare,
          Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton, reduceCtorEq,
          ite_false, zero_add, Nat.cast_zero, mul_zero, zero_mul]
    · rw [h1, Matrix.cons_val_one, Matrix.cons_val_zero]
      apply SurfaceGenusTwoBlowupPPrimary.coefficient_terms_primary_zero
      · simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton,
          reduceCtorEq, and_false, or_self, not_false_eq_true]
      · intro h; cases h
      · simp only [SurfaceFirstDescendant.correctionCoefficient,
        SurfaceFirstDescendant.divisorSquare,
          Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton, reduceCtorEq,
          ite_false, zero_add, Nat.cast_zero, mul_zero, zero_mul]
  · rfl

/-- A rational scalar vanishing condition kills the actual primary inner join, preserving its
  terminal callback. -/
theorem inner_hyperplane_node_zero (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ) (delta : X.Curve)
    (hd : X.planeDegree delta = 0) (n : ℕ) (k : Fin 1 → ℕ)
    (a : SurfaceBasisLabel X)
    (ha : ∀ gamma : X.Curve, X.planeDegree gamma = 0 → ∀ m b,
      SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X) gamma m
        (![.hyperplane, a, b] : Fin 3 → _) = 0) :
    remainderContraction X v main
      (GetzlerGraphs.join (m := 0) (n := 2) 0 1
        (fundamental 2 (Fin 1) (by norm_num [StableArity]))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (by exact (k, (0 : Fin 3 → ℕ)))
      (by exact ((inferInstance : DecidableEq (Fin 1)),
        (inferInstance : DecidableEq (Fin 3)))) delta n ![.hyperplane, a] = 0 := by
  simp only [GetzlerGraphs.join, remainderContraction, ite_true, GluingExpression.pointContraction]
  have hr (b : SurfaceBasisLabel X) :
      (Option.elim · b (((![.hyperplane, a] : Fin 2 → SurfaceBasisLabel X) ∘
        (finSumFinEquiv : Fin 0 ⊕ Fin 2 ≃ Fin 2)) ∘ Sum.inr)) ∘ finSuccEquiv' 1 =
      (![.hyperplane, a, b] : Fin 3 → SurfaceBasisLabel X) ∘ Equiv.swap 1 2 := by
    funext j; fin_cases j <;> rfl
  simp only [hr, primaryPointVertex, and_self, ite_true]
  apply Finset.sum_eq_zero
  intro split hs
  have hh : split.1 + split.2 = delta := by
    rw [X.splittings_eq] at hs
    exact (X.effective.mem_splittings _ _ _).mp hs
  have hright : X.planeDegree split.2 = 0 := by
    have he := congrArg X.planeDegree hh
    rw [map_add, hd] at he
    omega
  apply Finset.sum_eq_zero
  intro b _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ij _
  rw [SurfaceGenusZero.primaryScalar_relabel, ha split.2 hright ij.2 b.dual]
  simp only [mul_zero]

/-- The original primary-main HEE graph vanishes at the exceptional-generator remainder. -/
theorem paper_zero_hee_exceptional (i : Fin X.blowups) (v : Variable X) (n : ℕ) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 0) (X.exceptionalCurve i) n
        ![.hyperplane, .exceptional i, .exceptional i] = 0 := by
  have hz : (![0, 0, 0] : Fin 3 → ℕ) = 0 := by decide +kernel
  have he : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm 0) (X.exceptionalCurve i) n
        ![.hyperplane, .exceptional i, .exceptional i] =
      remainderContraction X v (remainderVertex X v (coefficientVertex X v))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          (GetzlerGraphs.join (m := 0) (n := 2) 0 1
            (fundamental 2 (Fin 1) (by norm_num [StableArity]))
            (fundamental 0 (Fin 3) (by norm_num [StableArity])))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        ((![0], (0 : Fin 3 → ℕ)), (0 : Fin 3 → ℕ))
        (((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 3))),
          (inferInstance : DecidableEq (Fin 3))) (X.exceptionalCurve i) n
          ![.hyperplane, .exceptional i, .exceptional i] := by
    rw [remainderPointCoefficient, if_pos (by decide +kernel)]
    change remainderContraction X v (remainderVertex X v (coefficientVertex X v))
      (GetzlerGraphs.join (m := 1) (n := 2) 1 2
        (GetzlerGraphs.join (m := 0) (n := 2) 0 1
          (fundamental 2 (Fin 1) (by norm_num [StableArity]))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        (fundamental 0 (Fin 3) (by norm_num [StableArity])))
      ((![0], ![0, 0, 0]), ![0, 0, 0]) _ (X.exceptionalCurve i) n
        ![.hyperplane, .exceptional i, .exceptional i] = _
    rw [hz]; rfl
  have hp := SurfaceGenusTwoBlowupNEEEPrimary.pair_ee_exceptional i v (remainderVertex X v
    (coefficientVertex X v)) n
    (GetzlerGraphs.join (m := 0) (n := 2) 0 1
      (fundamental 2 (Fin 1) (by norm_num [StableArity]))
      (fundamental 0 (Fin 3) (by norm_num [StableArity])))
    (![0], (0 : Fin 3 → ℕ))
    ((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 3))) .hyperplane
  have h0 := inner_hyperplane_node_zero v (remainderVertex X v (coefficientVertex X v))
    0 (map_zero _) n ![0] (.exceptional i)
    (fun gamma hd m b ↦ primaryScalar_orthogonal_of_planeDegree_zero .hyperplane (.exceptional i)
        (SurfaceCohomology.hyperplane_mul_exceptional X.blowups i) (Or.inl rfl) gamma hd m b)
  have h1 := inner_hyperplane_node_zero v (remainderVertex X v (coefficientVertex X v))
    (X.exceptionalCurve i) (X.planeDegree_exceptionalCurve i) n ![0] .point
    (fun gamma hd m b ↦ primaryScalar_orthogonal_of_planeDegree_zero .hyperplane .point
        (by rw [mul_comm]; exact SurfaceCohomology.point_mul_hyperplane X.blowups)
        (Or.inl rfl) gamma hd m b)
  exact he.trans (hp.trans (by rw [h0, h1, sub_self]))

/-- Either HEE cotangent graph has zero primary coefficient at its exceptional-generator
  remainder. -/
theorem paper_pair_hee_primary_exceptional (i : Fin X.blowups)
    (gamma : X.Curve) (m n : ℕ) (s : Fin 2) :
    let v : Variable X := .inr (SurfaceQuery.points X 2 gamma m)
    remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3))
      (X.exceptionalCurve i) n ![.hyperplane, .exceptional i, .exceptional i] = 0 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 gamma m)
  have h0 : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
  have h1 : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
  have he : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.paperCotangentTerm (if s = 0 then 2 else 3))
      (X.exceptionalCurve i) n ![.hyperplane, .exceptional i, .exceptional i] =
      remainderContraction X v (remainderVertex X v (coefficientVertex X v))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          (fundamental 2 (Fin 2) (by norm_num [StableArity]))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        (by exact (Pi.single s 1, (0 : Fin 3 → ℕ)))
        (by exact ((inferInstance : DecidableEq (Fin 2)),
          (inferInstance : DecidableEq (Fin 3)))) (X.exceptionalCurve i) n
            ![.hyperplane, .exceptional i, .exceptional i] := by
    rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
    · rw [if_pos rfl, ←h0]; rfl
    · rw [if_neg (by decide : (1 : Fin 2) ≠ 0), ←h1]; rfl
  dsimp only
  rw [he, SurfaceGenusTwoBlowupNEEEPrimary.pair_ee_exceptional i v _ n _ _ _ .hyperplane]
  change remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single s 1) inferInstance 0 ![.hyperplane, .exceptional i] -
    remainderVertex X v (coefficientVertex X v) n 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single s 1) inferInstance (X.exceptionalCurve i)
      ![.hyperplane, .point] = 0
  rw [main_hyperplane_exceptional_primary_zero i gamma m n s,
    SurfaceGenusTwoBlowupPPrimarySupport.pair_main_primary_zero_of_planeDegree_zero gamma m
      (X.exceptionalCurve i) (X.planeDegree_exceptionalCurve i) n s, sub_self]

/-- The exact six covariant EEH labellings of the held BP orbit. -/
theorem eeh_permutation (i : Fin X.blowups) (e : Fin 6) :
    (![.exceptional i, .exceptional i, .hyperplane] : Fin 3 → SurfaceBasisLabel X) ∘
      BelorousskiPandharipande.labelPermutation e =
      ![![.exceptional i, .exceptional i, .hyperplane],
        ![.exceptional i, .hyperplane, .exceptional i],
        ![.exceptional i, .exceptional i, .hyperplane],
        ![.hyperplane, .exceptional i, .exceptional i],
        ![.exceptional i, .hyperplane, .exceptional i],
        ![.hyperplane, .exceptional i, .exceptional i]] e := by
  funext t; fin_cases e <;> fin_cases t <;> rfl

/-- The complete compressed EEH equation has zero primary coefficient at an exceptional-generator
  remainder. -/
theorem pointCoefficient_eeh_primary_exceptional (i : Fin X.blowups)
    (gamma : X.Curve) (m n : ℕ) :
    BelorousskiPandharipande.pointCoefficient X n (gamma + X.exceptionalCurve i)
      ![.exceptional i, .exceptional i, .hyperplane]
      (.inr (SurfaceQuery.points X 2 gamma m)) = 0 := by
  let v : Variable X := .inr (SurfaceQuery.points X 2 gamma m)
  have hterm (j : Fin 20) (e : Fin 6) :
      SurfaceGenusTwo.pointCoefficient X v (BelorousskiPandharipande.orbitCotangentTerm j e)
        (gamma + X.exceptionalCurve i) n ![.exceptional i, .exceptional i, .hyperplane] =
      remainderPointCoefficient X v (coefficientVertex X v)
        (BelorousskiPandharipande.orbitCotangentTerm j e) (X.exceptionalCurve i) n
          ![.exceptional i, .exceptional i, .hyperplane] :=
    (remainderPointCoefficient_eq X v (coefficientVertex X v) rfl
      (BelorousskiPandharipande.orbitCotangentTerm j e) (X.exceptionalCurve i) n _).symm
  have hEH : (.exceptional i : SurfaceBasisLabel X).value *
      (SurfaceBasisLabel.hyperplane : SurfaceBasisLabel X).value = 0 := by
    rw [mul_comm]; exact SurfaceCohomology.hyperplane_mul_exceptional X.blowups i
  have hHE : (.hyperplane : SurfaceBasisLabel X).value *
      (SurfaceBasisLabel.exceptional i : SurfaceBasisLabel X).value = 0 :=
    SurfaceCohomology.hyperplane_mul_exceptional X.blowups i
  have hz (e : Fin 6) : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 0 e) (X.exceptionalCurve i) n
      ![.exceptional i, .exceptional i, .hyperplane] = 0 := by
    rw [SurfaceGenusTwoBlowupPCoefficients.remainder_orbit, eeh_permutation]
    fin_cases e
    · exact paper_zero_orthogonal_of_planeDegree_zero v _ (X.planeDegree_exceptionalCurve i)
        n (.exceptional i) (.exceptional i) .hyperplane hEH (Or.inr rfl)
    · exact paper_zero_orthogonal_of_planeDegree_zero v _ (X.planeDegree_exceptionalCurve i)
        n (.exceptional i) .hyperplane (.exceptional i) hHE (Or.inl rfl)
    · exact paper_zero_orthogonal_of_planeDegree_zero v _ (X.planeDegree_exceptionalCurve i)
        n (.exceptional i) (.exceptional i) .hyperplane hEH (Or.inr rfl)
    · exact paper_zero_hee_exceptional i v n
    · exact paper_zero_orthogonal_of_planeDegree_zero v _ (X.planeDegree_exceptionalCurve i)
        n (.exceptional i) .hyperplane (.exceptional i) hHE (Or.inl rfl)
    · exact paper_zero_hee_exceptional i v n
  have ho (e : Fin 6) : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 1 e) (X.exceptionalCurve i) n
      ![.exceptional i, .exceptional i, .hyperplane] = 0 := by
    rw [SurfaceGenusTwoBlowupPCoefficients.remainder_orbit]
    apply paper_one_of_hyperplane_of_planeDegree_zero v _ (X.planeDegree_exceptionalCurve i)
      n _ ((BelorousskiPandharipande.labelPermutation e).symm 2)
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Matrix.cons_val_two]
    rfl
  have hp (s : Fin 2) (e : Fin 6) : remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm (if s = 0 then 2 else 3) e)
      (X.exceptionalCurve i) n ![.exceptional i, .exceptional i, .hyperplane] = 0 := by
    rw [SurfaceGenusTwoBlowupPCoefficients.remainder_orbit, eeh_permutation]
    fin_cases e
    · exact paper_pair_orthogonal_of_planeDegree_zero v n s _ (X.planeDegree_exceptionalCurve i)
        (.exceptional i) (.exceptional i) .hyperplane hEH (Or.inr rfl)
    · exact paper_pair_orthogonal_of_planeDegree_zero v n s _ (X.planeDegree_exceptionalCurve i)
        (.exceptional i) .hyperplane (.exceptional i) hHE (Or.inl rfl)
    · exact paper_pair_orthogonal_of_planeDegree_zero v n s _ (X.planeDegree_exceptionalCurve i)
        (.exceptional i) (.exceptional i) .hyperplane hEH (Or.inr rfl)
    · exact paper_pair_hee_primary_exceptional i gamma m n s
    · exact paper_pair_orthogonal_of_planeDegree_zero v n s _ (X.planeDegree_exceptionalCurve i)
        (.exceptional i) .hyperplane (.exceptional i) hHE (Or.inl rfl)
    · exact paper_pair_hee_primary_exceptional i gamma m n s
  have h2 := hp (0 : Fin 2)
  have h3 := hp (1 : Fin 2)
  simp only [ite_true, if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h2 h3
  change BelorousskiPandharipande.pointCoefficient X n _ _ v = 0
  simp only [BelorousskiPandharipande.pointCoefficient, hterm]
  rw [Fin.sum_univ_four]
  change -2 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 0 e) (X.exceptionalCurve i) n
      ![.exceptional i, .exceptional i, .hyperplane]) +
    2 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 1 e) (X.exceptionalCurve i) n
      ![.exceptional i, .exceptional i, .hyperplane]) +
    3 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 2 e) (X.exceptionalCurve i) n
      ![.exceptional i, .exceptional i, .hyperplane]) +
    -3 * (∑ e : Fin 6, remainderPointCoefficient X v (coefficientVertex X v)
      (BelorousskiPandharipande.orbitCotangentTerm 3 e) (X.exceptionalCurve i) n
      ![.exceptional i, .exceptional i, .hyperplane]) = 0
  simp only [hz, ho, h2, h3, Finset.sum_const_zero, mul_zero, add_zero]

/-- The actual complete four-row relation has primary coefficient six times plane degree,
  including the zero boundary. -/
theorem row_primary_coefficient (i : Fin X.blowups) (beta : X.Curve) :
    RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row X i beta)
      {Sum.inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))} =
        6 * (X.planeDegree beta : ℚ) := by
  have hEH : RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.bpRow X
      (X.effective.energy beta) (beta + X.exceptionalCurve i)
      ![.exceptional i, .hyperplane, .hyperplane])
      {Sum.inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))} =
      6 * (X.signedMultiplicity beta i : ℚ) := by
    rw [SurfaceGenusTwoBlowupNRelation.bpRow, ← BelorousskiPandharipande.pointCoefficient_eq_full]
    exact pointCoefficient_ehh_primary_shifted i beta
  have hEEH : RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.bpRow X
      (X.effective.energy beta) (beta + X.exceptionalCurve i)
      ![.exceptional i, .exceptional i, .hyperplane])
      {Sum.inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))} = 0 := by
    rw [SurfaceGenusTwoBlowupNRelation.bpRow, ← BelorousskiPandharipande.pointCoefficient_eq_full]
    exact pointCoefficient_eeh_primary_exceptional i beta _ _
  have hEEE := SurfaceGenusTwoBlowupNEEEPrimary.normalizedCoefficient_primary_shifted i beta
  change RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.bpRow X
      (X.effective.energy beta) (beta + X.exceptionalCurve i)
      ![.exceptional i, .exceptional i, .exceptional i])
      {Sum.inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))} = _ at hEEE
  have hd : X.planeDegree beta = X.planeDegree (beta + X.exceptionalCurve i) := by
    rw [map_add, X.planeDegree_exceptionalCurve, add_zero]
  have hHHH := SurfaceGenusTwoBlowupPPrimarySupport.primary_coefficient_eq_zero_of_same_planeDegree
    (beta + X.exceptionalCurve i) beta hd (X.effective.energy beta + 1) (X.effective.energy beta)
  change RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.bpRow X
      (X.effective.energy beta) (beta + X.exceptionalCurve i)
      ![.hyperplane, .hyperplane, .hyperplane])
      {Sum.inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1))} = 0 at hHHH
  rw [SurfaceGenusTwoBlowupNRelation.row]
  simp only [RationalTerms.coefficient_add, RationalTerms.coefficient_scale, hEH, hEEH, hEEE, hHHH,
    mul_zero, add_zero]
  ring

/-- The actual complete four-row relation cancels every nonprimary coefficient at its shifted
  source class. -/
theorem row_source_nonprimary_coefficient_eq_zero (i : Fin X.blowups)
    (beta : X.Curve) (v : Variable X)
    (hv : ∀ gamma m, Sum.inr (SurfaceQuery.points X 2 gamma m) ≠ v)
    (hcurve : SurfaceGenusZero.variableCurve v = beta + X.exceptionalCurve i) :
    RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row X i beta) {v} = 0 := by
  have he : X.effective.energy (SurfaceGenusZero.variableCurve v) = X.effective.energy beta + 1 :=
    by
    rw [hcurve, X.energy_add_exceptionalCurve]
  have hd : X.planeDegree (SurfaceGenusZero.variableCurve v) = X.planeDegree beta := by
    rw [hcurve, map_add, X.planeDegree_exceptionalCurve, add_zero]
  have hEHH := pointCoefficient_ehh_at_requested_class i v hv (X.effective.energy beta) he
  have hEEH := pointCoefficient_eeh_at_requested_class i v hv (X.effective.energy beta) he
  have hEEE := SurfaceGenusTwoBlowupKCoefficients.pointCoefficient_at_requested_class i v hv
    (X.effective.energy beta) he
  have hHHH := SurfaceGenusTwoBlowupPCoefficients.pointCoefficient_at_requested_class v hv
    (X.effective.energy beta) he
  rw [hcurve] at hEHH hEEH hEEE hHHH
  rw [SurfaceGenusTwoBlowupNRelation.row]
  simp only [RationalTerms.coefficient_add, RationalTerms.coefficient_scale,
    SurfaceGenusTwoBlowupNRelation.bpRow, ←BelorousskiPandharipande.pointCoefficient_eq_full,
    hEHH, hEEH, hEEE, hHHH]
  have hd' : X.planeDegree (beta + X.exceptionalCurve i) = X.planeDegree beta := by
    rw [map_add, X.planeDegree_exceptionalCurve, add_zero]
  rw [hd']
  ring

end AxiomaticGW.SurfaceGenusTwoBlowupNCoefficients

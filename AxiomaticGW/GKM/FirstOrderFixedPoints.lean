/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.FixedPointAlgebra
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# First-order changes of a split fixed-point basis

The coefficient ring retains a separate square-zero coordinate for every curve
generator. A weighted pair of fixed points determines a rank-one cubic tensor
and its unique infinitesimal change of multiplicative coordinates. The metric
is the original reciprocal-Euler pairing on the flat fixed-point coordinates.
-/

@[expose] public section
namespace AxiomaticGW.GKM.FirstOrderFixedPoints

variable {K I D E : Type*} [Field K] [DecidableEq I] [Fintype E]
abbrev Scalars (K D : Type*) [Field K] := TrivSqZeroExt K (D → K)

/-- A positively oriented difference of two point restrictions. Reversing the
pair and its cubic weight simultaneously preserves the three-point tensor. -/
structure Pair (I : Type*) where
  left : I
  right : I

def Pair.diff (p : Pair I) (a : I → K) : K := a p.right - a p.left

variable (e : I → K) (p : E → Pair I) (w : D → E → K)

/-- Infinitesimal change from the original point restrictions to multiplicative coordinates. -/
def changeOfBasis (d : D) (a : I → K) (i : I) : K :=
  ∑ t, w d t * (p t).diff a *
    ((if i = (p t).left then e i else 0) + (if i = (p t).right then e i else 0))

abbrev flat (a : I → K) : I → Scalars K D := fun i ↦ TrivSqZeroExt.inl (a i)
abbrev constPart (a : I → Scalars K D) : I → K := fun i ↦ (a i).fst
abbrev coeff (a : I → Scalars K D) (d : D) : I → K := fun i ↦ (a i).snd d

/-- The invertible change of spectrum, simultaneously in every curve direction. -/
def spectrum (a : I → Scalars K D) (i : I) : Scalars K D :=
  ⟨(a i).fst, fun d ↦ (a i).snd d + changeOfBasis e p w d (constPart a) i⟩

def interpolate (a : I → Scalars K D) (i : I) : Scalars K D :=
  ⟨(a i).fst, fun d ↦ (a i).snd d - changeOfBasis e p w d (constPart a) i⟩

theorem spectrum_interpolate (a : I → Scalars K D) :
    spectrum e p w (interpolate e p w a) = a := by
  funext i
  apply TrivSqZeroExt.ext
  · rfl
  funext d
  exact sub_add_cancel _ _

theorem interpolate_spectrum (a : I → Scalars K D) :
    interpolate e p w (spectrum e p w a) = a := by
  funext i
  apply TrivSqZeroExt.ext
  · rfl
  funext d
  exact add_sub_cancel_right _ _

theorem spectrum_injective : Function.Injective (spectrum e p w) :=
  Function.LeftInverse.injective (interpolate_spectrum e p w)

/-- Pointwise multiplication in the corrected spectrum, pulled back to the fixed flat frame. -/
def product (a b : I → Scalars K D) : I → Scalars K D :=
  interpolate e p w (spectrum e p w a * spectrum e p w b)

theorem spectrum_product (a b : I → Scalars K D) :
    spectrum e p w (product e p w a b) = spectrum e p w a * spectrum e p w b :=
  spectrum_interpolate _ _ _ _

theorem product_assoc (a b c : I → Scalars K D) :
    product e p w (product e p w a b) c = product e p w a (product e p w b c) := by
  apply spectrum_injective e p w
  simp only [spectrum_product, mul_assoc]

theorem spectrum_one : spectrum e p w 1 = 1 := by
  funext i
  apply TrivSqZeroExt.ext
  · rfl
  funext d
  simp [spectrum, constPart, changeOfBasis, Pair.diff]

theorem product_one (a : I → Scalars K D) : product e p w 1 a = a := by
  apply spectrum_injective e p w
  rw [spectrum_product, spectrum_one, one_mul]

theorem spectrum_zero : spectrum e p w 0 = 0 := by
  funext i
  apply TrivSqZeroExt.ext
  · rfl
  funext d
  simp [spectrum, constPart, changeOfBasis, Pair.diff]

def projector (i : I) : I → Scalars K D := interpolate e p w (Pi.single i 1)

theorem projector_constant (i : I) : constPart (projector e p w i) = Pi.single i 1 := by
  funext j
  by_cases h : j = i <;> simp [constPart, projector, interpolate, h]

theorem projector_coefficient (i : I) (d : D) :
    coeff (projector e p w i) d = -changeOfBasis e p w d (Pi.single i 1) := by
  have h : constPart (Pi.single i 1 : I → Scalars K D) = Pi.single i 1 :=
    projector_constant e p w i
  funext j
  simp only [coeff, projector, interpolate, h, TrivSqZeroExt.snd_mk, Pi.neg_apply]
  by_cases hji : j = i <;> simp [hji]

theorem projector_mul (i j : I) :
    product e p w (projector e p w i) (projector e p w j) =
      if i = j then projector e p w i else 0 := by
  apply spectrum_injective e p w
  rw [spectrum_product]
  simp only [projector, spectrum_interpolate, apply_ite (spectrum e p w), spectrum_zero]
  funext k
  by_cases hi : k = i <;> by_cases hj : k = j <;> by_cases hij : i = j <;> simp_all

private theorem scalar_idempotent (a : Scalars K D) (ha : a * a = a) : a = 0 ∨ a = 1 := by
  have hc := congrArg TrivSqZeroExt.fst ha
  rw [TrivSqZeroExt.fst_mul] at hc
  have h : a.fst * (a.fst - 1) = 0 := by rw [mul_sub, hc, mul_one, sub_self]
  have hs (d : D) : a.fst * a.snd d + a.fst * a.snd d = a.snd d :=
    by simpa only [TrivSqZeroExt.snd_mul, op_smul_eq_smul, Pi.add_apply, Pi.smul_apply,
                   smul_eq_mul] using congrFun (congrArg TrivSqZeroExt.snd ha) d
  rcases mul_eq_zero.mp h with hz | h1
  · left
    apply TrivSqZeroExt.ext hz
    funext d
    change a.snd d = 0
    simpa only [hz, zero_mul, add_zero] using (hs d).symm
  · right
    have ho := sub_eq_zero.mp h1
    apply TrivSqZeroExt.ext ho
    funext d
    have hh := hs d
    rw [ho, one_mul] at hh
    change a.snd d = 0
    linear_combination hh

theorem projector_primitive (i : I) (a : I → Scalars K D) (ha : product e p w a a = a)
    (hi : product e p w a (projector e p w i) = a) : a = 0 ∨ a = projector e p w i := by
  have hs := congrArg (spectrum e p w) ha
  have hp := congrArg (spectrum e p w) hi
  rw [spectrum_product] at hs
  rw [spectrum_product, projector, spectrum_interpolate] at hp
  have hoff (j : I) (hj : j ≠ i) : spectrum e p w a j = 0 := by
    have h := congrFun hp j
    simpa only [Pi.mul_apply, Pi.single_eq_of_ne hj, mul_zero] using h.symm
  rcases scalar_idempotent _ (congrFun hs i) with hz | hu
  · left
    apply spectrum_injective e p w
    rw [spectrum_zero]
    funext j
    by_cases h : j = i
    · exact h ▸ hz
    · exact hoff j h
  · right
    apply spectrum_injective e p w
    rw [projector, spectrum_interpolate]
    funext j
    by_cases h : j = i
    · subst j
      simpa only [Pi.single_eq_same] using hu
    · simpa only [Pi.single_eq_of_ne h] using hoff j h

/-- Lowered linear coefficient from one pair of fixed points. -/
def cubic (d : D) (a b c : I → K) : K :=
  ∑ t, w d t * (p t).diff a * (p t).diff b * (p t).diff c

/-- Undeformed localized metric on fixed-point restrictions. -/
def pairing [Fintype I] (a b : I → K) : K := ∑ i, (e i)⁻¹ * a i * b i

theorem product_coefficient (d : D) (a b : I → K) (i : I) :
    coeff (product e p w (flat a) (flat b)) d i =
      changeOfBasis e p w d a i * b i + a i * changeOfBasis e p w d b i -
        changeOfBasis e p w d (a * b) i := by
  simp only [coeff, product, interpolate, spectrum, flat, Pi.mul_apply,
    TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mk, TrivSqZeroExt.fst_mk,
    TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inl, Pi.add_apply, Pi.zero_apply, op_smul_eq_smul,
    Pi.smul_apply, smul_eq_mul, zero_add]
  change a i * changeOfBasis e p w d b i + b i * changeOfBasis e p w d a i -
    changeOfBasis e p w d (a * b) i = _
  ring

theorem product_coefficient_pairs (d : D) (a b : I → K) (i : I) :
    coeff (product e p w (flat a) (flat b)) d i =
      ∑ t, w d t * (p t).diff a * (p t).diff b *
        ((if i = (p t).right then e i else 0) - (if i = (p t).left then e i else 0)) := by
  rw [product_coefficient]
  simp only [changeOfBasis, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Pair.diff, Pi.mul_apply]
  split_ifs <;> (try simp_all only) <;> ring

/-- The product obtained from the corrected spectrum lowers to the prescribed cubic
in the original, undeformed equivariant metric. -/
theorem product_pairing [Fintype I] (he : ∀ i, e i ≠ 0) (d : D) (a b c : I → K) :
    pairing e (coeff (product e p w (flat a) (flat b)) d) c = cubic p w d a b c := by
  simp only [pairing, product_coefficient_pairs, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  let z := w d t * (p t).diff a * (p t).diff b
  have hs (i : I) : (e i)⁻¹ * (z *
      ((if i = (p t).right then e i else 0) - (if i = (p t).left then e i else 0))) * c i =
      (if i = (p t).right then z * c i else 0) - (if i = (p t).left then z * c i else 0) := by
    split_ifs <;> field_simp [he i] <;> ring
  change (∑ i, (e i)⁻¹ * (z * _) * c i) = _
  simp_rw [hs]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact (mul_sub z _ _).symm

theorem spectrum_add (a b : I → Scalars K D) :
    spectrum e p w (a + b) = spectrum e p w a + spectrum e p w b := by
  funext i
  apply TrivSqZeroExt.ext
  · rfl
  funext d
  change (a i).snd d + (b i).snd d + changeOfBasis e p w d (constPart a + constPart b) i = _
  have hadd : changeOfBasis e p w d (constPart a + constPart b) i =
      changeOfBasis e p w d (constPart a) i + changeOfBasis e p w d (constPart b) i := by
    simp only [changeOfBasis, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    simp only [Pair.diff, Pi.add_apply]
    ring
  rw [hadd]
  change _ = ((a i).snd d + _) + ((b i).snd d + _)
  abel

theorem spectrum_smul (r : Scalars K D) (a : I → Scalars K D) :
    spectrum e p w (r • a) = r • spectrum e p w a := by
  funext i
  apply TrivSqZeroExt.ext
  · rfl
  funext d
  have hT : changeOfBasis e p w d (r.fst • constPart a) i =
      r.fst * changeOfBasis e p w d (constPart a) i := by
    simp only [changeOfBasis, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    simp only [Pair.diff, Pi.smul_apply, smul_eq_mul]
    ring
  change (r * a i).snd d + changeOfBasis e p w d (r.fst • constPart a) i =
    (r * spectrum e p w a i).snd d
  rw [hT]
  simp only [TrivSqZeroExt.snd_mul, op_smul_eq_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, spectrum, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk]
  ring

/-- The spectral transform is a linear equivalence over the full multivariate
square-zero coefficient ring. -/
def spectrumEquiv : (I → Scalars K D) ≃ₗ[Scalars K D] (I → Scalars K D) where
  toFun := spectrum e p w
  invFun := interpolate e p w
  left_inv := interpolate_spectrum e p w
  right_inv := spectrum_interpolate e p w
  map_add' := spectrum_add e p w
  map_smul' := spectrum_smul e p w

/-- The corrected projectors are an actual basis over the square-zero base. -/
noncomputable def primitiveBasis [Fintype I] : Module.Basis I (Scalars K D) (I → Scalars K D) :=
  (Pi.basisFun (Scalars K D) I).map (spectrumEquiv e p w).symm

theorem primitiveBasis_apply [Fintype I] (i : I) : primitiveBasis e p w i = projector e p w i := by
  rw [primitiveBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  rfl

/-- The primitive projectors form a complete decomposition of the original unit. -/
theorem projector_sum [Fintype I] : ∑ i : I, projector e p w i = 1 := by
  let f : (I → Scalars K D) →+ (I → Scalars K D) :=
    ⟨⟨spectrum e p w, spectrum_zero e p w⟩, spectrum_add e p w⟩
  apply spectrum_injective e p w
  rw [spectrum_one]
  change f (∑ i, projector e p w i) = _
  rw [map_sum]
  change ∑ i : I, spectrum e p w (interpolate e p w (Pi.single i 1)) = _
  simp only [spectrum_interpolate]
  funext j
  simp only [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Pi.one_apply]

variable [Fintype I]

/-- Scalar extension of the original equivariant metric to the square-zero base. -/
def metric (a b : I → Scalars K D) : Scalars K D :=
  ⟨pairing e (constPart a) (constPart b), fun d ↦
    pairing e (coeff a d) (constPart b) + pairing e (constPart a) (coeff b d)⟩

def trace (a : I → Scalars K D) : Scalars K D :=
  ⟨pairing e (constPart a) 1, fun d ↦ pairing e (coeff a d) 1⟩

/-- The metric is the trace pairing of the transported multiplication. -/
theorem trace_product (he : ∀ i, e i ≠ 0) (a b : I → Scalars K D) :
    trace e (product e p w a b) = metric e a b := by
  apply TrivSqZeroExt.ext
  · change (∑ i, (e i)⁻¹ * ((a i).fst * (b i).fst) * 1) = _
    simp only [metric, TrivSqZeroExt.fst_mk, pairing, constPart, mul_one, mul_assoc]
  funext d
  have h (i : I) : coeff (product e p w a b) d i =
      coeff (product e p w (flat (constPart a)) (flat (constPart b))) d i +
        coeff a d i * (b i).fst + (a i).fst * coeff b d i := by
    rw [product_coefficient]
    simp only [coeff, product, interpolate, spectrum, Pi.mul_apply, TrivSqZeroExt.snd_mul,
      TrivSqZeroExt.snd_mk, TrivSqZeroExt.fst_mk, op_smul_eq_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    change _ - changeOfBasis e p w d (constPart a * constPart b) i = _
    dsimp only [constPart]
    ring
  have hz := product_pairing e p w he d (constPart a) (constPart b) 1
  simp only [cubic, Pair.diff, Pi.one_apply, sub_self, mul_zero, Finset.sum_const_zero] at hz
  change pairing e (coeff (product e p w a b) d) 1 = _
  simp only [pairing, h, mul_add, Pi.one_apply, mul_one, Finset.sum_add_distrib] at hz ⊢
  rw [hz, zero_add]
  change _ = pairing e (coeff a d) (constPart b) + pairing e (constPart a) (coeff b d)
  simp only [pairing, mul_assoc, constPart]

theorem metric_orthogonal (he : ∀ i, e i ≠ 0) (i j : I) (hij : i ≠ j) :
    metric e (projector e p w i) (projector e p w j) = 0 := by
  rw [← trace_product e p w he, projector_mul, if_neg hij]
  apply TrivSqZeroExt.ext
  · simp [trace, pairing, constPart]
  funext d
  simp [trace, pairing, coeff]

private theorem pairing_single_right (a : I → K) (i : I) :
    pairing e a (Pi.single i 1) = (e i)⁻¹ * a i := by
  simp only [pairing, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

private theorem pairing_single_left (a : I → K) (i : I) :
    pairing e (Pi.single i 1) a = (e i)⁻¹ * a i := by
  simp only [pairing, Pi.single_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The reciprocal Euler norm and all its independent first-order corrections. -/
def norm (i : I) : Scalars K D :=
  ⟨(e i)⁻¹, fun d ↦ -2 * (e i)⁻¹ * changeOfBasis e p w d (Pi.single i 1) i⟩

theorem projector_norm (i : I) :
    metric e (projector e p w i) (projector e p w i) = norm e p w i := by
  apply TrivSqZeroExt.ext
  · simp only [metric, norm, TrivSqZeroExt.fst_mk, projector_constant, pairing_single_right,
      Pi.single_eq_same, mul_one]
  funext d
  simp only [metric, norm, TrivSqZeroExt.snd_mk, projector_constant, projector_coefficient,
    pairing_single_right, pairing_single_left, Pi.neg_apply]
  ring

/-- The inverse metric entry for contractions in the primitive frame, requiring no square roots. -/
def inverseNorm (i : I) : Scalars K D :=
  ⟨e i, fun d ↦ 2 * e i * changeOfBasis e p w d (Pi.single i 1) i⟩

omit [Fintype I] in
theorem norm_mul_inverseNorm (he : ∀ i, e i ≠ 0) (i : I) :
    norm e p w i * inverseNorm e p w i = 1 := by
  apply TrivSqZeroExt.ext
  · exact inv_mul_cancel₀ (he i)
  funext d
  simp only [norm, inverseNorm, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mk,
    TrivSqZeroExt.snd_mk, op_smul_eq_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    TrivSqZeroExt.snd_one, Pi.zero_apply]
  ring

/-- If a square root of the classical tangent Euler factor is chosen in the coefficient
field, the given first-order factor normalizes the primitive projector. -/
def normalizer (i : I) (s : K) : Scalars K D :=
  ⟨s, fun d ↦ s * changeOfBasis e p w d (Pi.single i 1) i⟩

omit [Fintype I] in
theorem normalizer_squared (i : I) (s : K) (hs : s ^ 2 = e i) :
    normalizer e p w i s ^ 2 = inverseNorm e p w i := by
  rw [sq]
  apply TrivSqZeroExt.ext
  · exact (sq s).symm.trans hs
  funext d
  simp only [normalizer, inverseNorm, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mk,
    TrivSqZeroExt.snd_mk, op_smul_eq_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← hs]
  ring

omit [Fintype I] in
theorem normalized_gram (he : ∀ i, e i ≠ 0) (i : I) (s : K) (hs : s ^ 2 = e i) :
    norm e p w i * normalizer e p w i s ^ 2 = 1 := by
  rw [normalizer_squared _ _ _ i s hs, norm_mul_inverseNorm _ _ _ he]

omit [Fintype I] in
/-- After extending coefficients to an algebraically closed field, a normalized
diagonal frame exists without imposing a square-root hypothesis on the source field. -/
theorem exists_normalized_gram [IsAlgClosed K] (he : ∀ i, e i ≠ 0) :
    ∃ s : I → K, ∀ i, (s i)^2 = e i ∧ norm e p w i * normalizer e p w i (s i)^2 = 1 := by
  choose s hs using fun i ↦ IsAlgClosed.exists_pow_nat_eq (e i) (n := 2) (by decide)
  exact ⟨s, fun i ↦ ⟨hs i, normalized_gram _ _ _ he i (s i) (hs i)⟩⟩

section BaseChange
variable {L : Type*} [Field L] (f : K →+* L)

/-- Apply a coefficient-field embedding to the constant and every full-curve coefficient. -/
def mapScalar (z : Scalars K D) : Scalars L D := ⟨f z.fst, fun d ↦ f (z.snd d)⟩

omit [Fintype I] in
theorem map_changeOfBasis (d : D) (a : I → K) (i : I) :
    f (changeOfBasis e p w d a i) =
      changeOfBasis (f ∘ e) p (fun g t ↦ f (w g t)) d (f ∘ a) i := by
  simp only [changeOfBasis, map_sum, map_mul, map_add, Pair.diff, map_sub, Function.comp_apply,
    apply_ite f, map_zero]

omit [Fintype I] in
theorem map_norm (i : I) : mapScalar f (norm e p w i) =
    norm (f ∘ e) p (fun g t ↦ f (w g t)) i := by
  have h : f ∘ (Pi.single i 1 : I → K) = Pi.single i 1 := by
    funext j
    by_cases h : j = i <;> simp [h]
  apply TrivSqZeroExt.ext
  · exact map_inv₀ f (e i)
  funext d
  simp only [mapScalar, norm, TrivSqZeroExt.snd_mk, map_mul, map_neg, map_ofNat, map_inv₀,
    map_changeOfBasis, h, Function.comp_apply]

end BaseChange

end AxiomaticGW.GKM.FirstOrderFixedPoints

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GW.BigQuantumProduct

/-!
# Stabilization boundary comparison and calibration

The weak `DescendantAncestorComparison` records only a difference. This file
adds optional geometric data that exhibits that difference as a finite sum of
factorized positive-degree rational-tail contributions.

The same package may supply the genus-zero two-point calibration. Its
coefficientwise symplectic identity is derived from a separately named
boundary relation, so neither boundary support nor symplecticity is hidden in
the definition of an operator.
-/

@[expose] public section

namespace AxiomaticGW

open Module

universe u

namespace EffectiveCurveMonoid

variable {B : Type*} [AddCancelCommMonoid B]

/-- Splittings whose rational-tail class, stored in the second component, is
positive. -/
noncomputable def positiveTailSplittings (D : EffectiveCurveMonoid B)
    (beta : B) : Finset (B × B) := by
  classical
  exact (D.splittings beta).filter fun split ↦ split.2 ≠ 0

@[simp]
theorem mem_positiveTailSplittings (D : EffectiveCurveMonoid B)
    (betaMain betaTail beta : B) :
    (betaMain, betaTail) ∈ D.positiveTailSplittings beta ↔
      betaMain + betaTail = beta ∧ betaTail ≠ 0 := by
  classical
  simp only [positiveTailSplittings, ne_eq, Finset.mem_filter,
    D.mem_splittings]

end EffectiveCurveMonoid

/-- A factorized finite rational-tail correction. `mainBoundary` already
contains the state-space operator contributed by the tail, while `tailWeight`
contains its remaining scalar multiplicity. -/
noncomputable def rationalTailCorrection
    {R V B : Type u} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCancelCommMonoid B] (D : EffectiveCurveMonoid B)
    {W : Type*} [AddCommGroup W] [Module R W]
    {S : Type} [Fintype S] (beta : B)
    (mainBoundary : S → B × B → MultilinearMap R (fun _ : S ↦ V) W)
    (tailWeight : S → B × B → R) :
    MultilinearMap R (fun _ : S ↦ V) W := by
  classical
  exact ∑ s, ∑ split ∈ D.positiveTailSplittings beta,
    tailWeight s split • mainBoundary s split

/-- A factorized rational-tail stabilization comparison: the weak residual is
exhibited as a finite sum of classes pushed forward from positive-degree
rational-tail strata, and every summand is factorized into main and tail
contributions. -/
structure StabilizationBoundaryComparison
    {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
    (P : PsiClasses C) (M : StableMapDescendants Omega) where
  /-- The underlying residual comparison, retained for compatibility. -/
  toDescendantAncestorComparison : DescendantAncestorComparison P M
  /-- Boundary pushforward contribution from the main component. Its type is
  deliberately explicit data because `StableCurveCohomology` has pullbacks
  but no Gysin interface. -/
  mainBoundary : ∀ (g : ℕ) (S : Type) [Fintype S]
      (_h : StableArity g S) (_beta : B) (_k : S → ℕ),
    S → B × B → Module.End R V →
      MultilinearMap R (fun _ : S ↦ V) (C.H g S)
  /-- Genus-zero two-point tail operator. These are also the nonconstant
  coefficients of the calibration below. -/
  twoPointTailCoefficient : ℕ → B → Module.End R V
  /-- The constant tail coefficient is the identity. -/
  twoPointTailCoefficient_zero :
    twoPointTailCoefficient 0 0 = LinearMap.id
  /-- Remaining scalar weight of a rational-tail stratum. -/
  tailWeight : ∀ (g : ℕ) (S : Type) [Fintype S]
      (_h : StableArity g S) (_beta : B) (_k : S → ℕ),
    S → B × B → R
  /-- The residual is precisely the finite factorized rational-tail sum. -/
  correction_eq_rational_tails : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (beta : B) (k : S → ℕ),
    toDescendantAncestorComparison.boundaryCorrection g S h beta k =
      rationalTailCorrection D beta
        (fun s split ↦ mainBoundary g S h beta k s split
          (twoPointTailCoefficient (k s) split.2))
        (tailWeight g S h beta k)
  /-- A zero cotangent power has no rational-tail correction at that marking. -/
  tailWeight_eq_zero : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity g S) (beta : B) (k : S → ℕ) (s : S)
      (split : B × B),
    k s = 0 → tailWeight g S h beta k s split = 0

namespace StabilizationBoundaryComparison

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
  {P : PsiClasses C} {M : StableMapDescendants Omega}

/-- The geometric comparison still supplies the original public weak API. -/
instance : Coe (StabilizationBoundaryComparison P M)
    (DescendantAncestorComparison P M) :=
  ⟨StabilizationBoundaryComparison.toDescendantAncestorComparison⟩

/-- No summand with a zero cotangent power contributes. -/
theorem rationalTailCorrection_zero_power_at
    (X : StabilizationBoundaryComparison P M)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (beta : B) (k : S → ℕ) (s : S) (hs : k s = 0) :
    ∀ split, X.tailWeight g S h beta k s split •
      X.mainBoundary g S h beta k s split
        (X.twoPointTailCoefficient (k s) split.2) = 0 := by
  intro split
  rw [X.tailWeight_eq_zero g S h beta k s split hs, zero_smul]

/-- The correction is a finite sum supported on splittings with a nonzero
rational-tail curve class. -/
theorem correction_eq_positive_tail_sum
    (X : StabilizationBoundaryComparison P M)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (beta : B) (k : S → ℕ) :
    X.toDescendantAncestorComparison.boundaryCorrection g S h beta k =
      ∑ s, ∑ split ∈ D.positiveTailSplittings beta,
        X.tailWeight g S h beta k s split •
          X.mainBoundary g S h beta k s split
            (X.twoPointTailCoefficient (k s) split.2) := by
  rw [X.correction_eq_rational_tails]
  rfl

end StabilizationBoundaryComparison

/-- Genus-zero two-point calibration data, coefficientwise in `z^-1` and the
effective curve class. This carrier stores only the operator coefficients and
their constant term; symplecticity requires `CalibrationBoundaryRelation`, and
no geometric fundamental solution is constructed here. -/
structure TwoPointCalibration
    {R V B : Type u} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCancelCommMonoid B] (D : EffectiveCurveMonoid B)
    (pairing : SymmetricPerfectPairing R V) where
  /-- Coefficient of `z^-power q^beta`. -/
  coefficient : ℕ → B → Module.End R V
  /-- Constant term of the calibration. -/
  coefficient_zero : coefficient 0 0 = LinearMap.id

namespace TwoPointCalibration

variable {R V B : Type u} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {pairing : SymmetricPerfectPairing R V}

/-- Coefficient of `S*(-z) S(z)` paired against two states. -/
noncomputable def symplecticCoefficient
    (S : TwoPointCalibration D pairing) (power : ℕ) (beta : B)
    (x y : V) : R := by
  classical
  exact ∑ powerSplit ∈ Finset.HasAntidiagonal.antidiagonal power,
    ∑ curveSplit ∈ D.splittings beta,
      ((-1 : R) ^ powerSplit.1) *
        pairing.form
          (S.coefficient powerSplit.1 curveSplit.1 x)
          (S.coefficient powerSplit.2 curveSplit.2 y)

/-- The Kronecker-delta coefficient of the identity calibration. -/
noncomputable def symplecticIdentityCoefficient
    (power : ℕ) (beta : B) (x y : V) : R := by
  classical
  exact if power = 0 ∧ beta = 0 then pairing.form x y else 0

end TwoPointCalibration

namespace StabilizationBoundaryComparison

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
  {P : PsiClasses C} {M : StableMapDescendants Omega}

/-- The two-point calibration built from the same tail operators that occur
in the rational-tail correction. -/
def calibration (X : StabilizationBoundaryComparison P M) :
    TwoPointCalibration D Omega.pairing where
  coefficient := X.twoPointTailCoefficient
  coefficient_zero := X.twoPointTailCoefficient_zero

@[simp]
theorem calibration_coefficient
    (X : StabilizationBoundaryComparison P M) (power : ℕ) (beta : B) :
    X.calibration.coefficient power beta =
      X.twoPointTailCoefficient power beta := rfl

end StabilizationBoundaryComparison

/-- Independent two-point boundary relation used to prove symplecticity of a
calibration. Naming it separately prevents a nominal `S`-operator from being
mistaken for a symplectic one. -/
structure CalibrationBoundaryRelation
    {R V B : Type u} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {pairing : SymmetricPerfectPairing R V}
    (S : TwoPointCalibration D pairing) where
  /-- The two ways of distributing a marked two-point boundary cancel. -/
  boundary_identity : ∀ (power : ℕ) (beta : B) (x y : V),
    S.symplecticCoefficient power beta x y =
      TwoPointCalibration.symplecticIdentityCoefficient
        (pairing := pairing) power beta x y

namespace CalibrationBoundaryRelation

variable {R V B : Type u} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {pairing : SymmetricPerfectPairing R V}
  {S : TwoPointCalibration D pairing}

/-- Coefficientwise symplecticity `S*(-z) S(z) = 1`. -/
theorem symplectic (H : CalibrationBoundaryRelation S)
    (power : ℕ) (beta : B) (x y : V) :
    S.symplecticCoefficient power beta x y =
      TwoPointCalibration.symplecticIdentityCoefficient
        (pairing := pairing) power beta x y :=
  H.boundary_identity power beta x y

end CalibrationBoundaryRelation

/-- A coefficientwise genus-indexed carrier for completed formal potentials.
Each coefficient is complete in the formal variables and Novikov degree. This
is not a construction of a topological Fock completion, and no unrestricted
exponential partition function is asserted. -/
structure CompletedFockPotential
    {B : Type*} [AddCancelCommMonoid B] (D : EffectiveCurveMonoid B)
    (Vars R : Type*) [CommRing R] where
  /-- Coefficient indexed by genus. -/
  coefficient : ℕ → FormalPotential D Vars R

namespace CompletedFockPotential

variable {B Vars R : Type*} [AddCancelCommMonoid B]
  {D : EffectiveCurveMonoid B} [CommRing R]

noncomputable instance : Add (CompletedFockPotential D Vars R) :=
  ⟨fun F G ↦ ⟨fun n ↦ F.coefficient n + G.coefficient n⟩⟩

instance : Zero (CompletedFockPotential D Vars R) :=
  ⟨⟨fun _ ↦ 0⟩⟩

noncomputable instance : SMul R (CompletedFockPotential D Vars R) :=
  ⟨fun r F ↦ ⟨fun n ↦ r • F.coefficient n⟩⟩

/-- Regard a connected genus potential as a coefficientwise completed Fock
family. This is an inclusion of data, not an unrestricted exponential. -/
def ofGenusPotential (F : GenusPotential (FormalPotential D Vars R)) :
    CompletedFockPotential D Vars R :=
  ⟨F⟩

@[simp]
theorem ofGenusPotential_coefficient
    (F : GenusPotential (FormalPotential D Vars R)) (g : ℕ) :
    (ofGenusPotential F).coefficient g = F g := rfl

@[ext]
theorem ext {F G : CompletedFockPotential D Vars R}
    (h : ∀ n, F.coefficient n = G.coefficient n) : F = G := by
  cases F with
  | mk f =>
      cases G with
      | mk g =>
          have hfg : f = g := funext h
          subst g
          rfl

end CompletedFockPotential

/-- A coefficientwise quantized action of a calibration. The action is kept
as optional data because constructing it requires target-specific
local-finiteness and polarization choices. -/
structure QuantizedCalibrationAction
    {R V B : Type u} {Vars : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCancelCommMonoid B]
    (D : EffectiveCurveMonoid B) (pairing : SymmetricPerfectPairing R V)
    (S : TwoPointCalibration D pairing) where
  /-- Supplied action representing the quantized inverse calibration on
  coefficientwise Fock data. -/
  act : CompletedFockPotential D Vars R → CompletedFockPotential D Vars R
  /-- Quantization preserves zero. -/
  map_zero : act 0 = 0
  /-- Quantization is additive. -/
  map_add : ∀ F G, act (F + G) = act F + act G

/-- Optional coefficientwise Givental comparison. The descendant--ancestor
identity is geometric input beyond the rational-tail class formula; packaging it here
makes the extra assumption visible and ties it to the calibration constructed
from those same tail operators. -/
structure GiventalComparison
    {R V B : Type u} {ι : Type} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
    {P : PsiClasses C} {M : StableMapDescendants Omega}
    (I : StableCurveIntegration C) (b : Basis ι R V)
    (X : StabilizationBoundaryComparison P M)
    (Q : QuantizedCalibrationAction D Omega.pairing X.calibration) where
  /-- Supplied scalar representing the exponential of the independent
  genus-one correction; no analytic exponential is assumed for arbitrary rings. -/
  genusOneFactor : R
  /-- Descendant coefficient data is the genus-one factor times the supplied
  quantized inverse calibration applied to ancestor coefficient data. -/
  partition_identity :
    CompletedFockPotential.ofGenusPotential
        (fun g ↦ Omega.descendantPotential M I b g) =
      genusOneFactor • Q.act
        (CompletedFockPotential.ofGenusPotential
          (fun g ↦ Omega.ancestorPotential P I b g))

namespace GiventalComparison

variable {R V B : Type u} {ι : Type} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
  {P : PsiClasses C} {M : StableMapDescendants Omega}
  {I : StableCurveIntegration C} {b : Basis ι R V}
  {X : StabilizationBoundaryComparison P M}
  {Q : QuantizedCalibrationAction D Omega.pairing X.calibration}

/-- Coefficientwise form of the quantized descendant--ancestor identity. -/
theorem coefficient_identity (G : GiventalComparison I b X Q) (g : ℕ) :
    Omega.descendantPotential M I b g =
      (G.genusOneFactor • Q.act
        (CompletedFockPotential.ofGenusPotential
          (fun h ↦ Omega.ancestorPotential P I b h))).coefficient g := by
  exact congrArg (fun F ↦ F.coefficient g) G.partition_identity

end GiventalComparison

end AxiomaticGW

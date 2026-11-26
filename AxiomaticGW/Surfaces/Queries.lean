/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.TargetData
public import AxiomaticGW.GW.Descendants.FullPotential
public import Mathlib.Tactic.DeriveFintype

/-!
# Queries and finite initial values for the fixed surfaces

Queries contain actual basis insertions, cotangent powers, genus, and the full
effective curve class. Evaluation uses the supplied numerical descendant
invariant. The finite seed specification records geometric input obligations;
it does not assert their existence or their sufficiency for reconstruction.
-/

@[expose] public section

namespace AxiomaticGW

/-- Labels of the unit, hyperplane, exceptional divisors, and point basis. -/
inductive SurfaceBasisLabel (X : SurfaceTarget)
  | unit
  | hyperplane
  | exceptional (i : Fin X.blowups)
  | point
  deriving DecidableEq, Repr, Fintype

namespace SurfaceBasisLabel

/-- Complex codimension, so divisor classes have degree one. -/
def codimension {X : SurfaceTarget} : SurfaceBasisLabel X → ℕ
  | unit => 0
  | hyperplane => 1
  | exceptional _ => 1
  | point => 2

/-- The actual state of the labelled basis vector. -/
def value {X : SurfaceTarget} : SurfaceBasisLabel X → SurfaceCohomology X.blowups
  | unit => 1
  | hyperplane => SurfaceCohomology.hyperplane X.blowups
  | exceptional i => SurfaceCohomology.exceptional X.blowups i
  | point => SurfaceCohomology.point X.blowups

theorem value_mem_degree {X : SurfaceTarget} (a : SurfaceBasisLabel X) :
    a.value ∈ SurfaceCohomology.degree X.blowups a.codimension := by
  cases a with
  | unit => exact SurfaceCohomology.one_mem_degree_zero _
  | hyperplane => exact SurfaceCohomology.hyperplane_mem_degree_one _
  | exceptional i => exact SurfaceCohomology.exceptional_mem_degree_one _ i
  | point => exact SurfaceCohomology.point_mem_degree_two _

end SurfaceBasisLabel

/-- One labelled descendant insertion. -/
structure SurfaceInsertion (X : SurfaceTarget) where
  /-- Canonical homogeneous basis class at this marking. -/
  label : SurfaceBasisLabel X
  /-- Nonnegative cotangent-line power at this marking. -/
  psi : ℕ
  deriving DecidableEq, Repr

/-- A finite descendant query in a fixed surface's complete curve monoid. -/
structure SurfaceQuery (X : SurfaceTarget) where
  /-- Genus of the connected source curve. -/
  genus : ℕ
  /-- Full effective curve class in the fixed target's coordinate monoid. -/
  beta : X.Curve
  /-- Ordered finite list of homogeneous descendant insertions. -/
  insertions : List (SurfaceInsertion X)

namespace SurfaceQuery

/-- Equality compares the actual genus, full class, and insertion data. -/
theorem eq_iff {X : SurfaceTarget} (p q : SurfaceQuery X) :
    p = q ↔ p.genus = q.genus ∧ p.beta = q.beta ∧ p.insertions = q.insertions := by
  cases p
  cases q
  simp only [SurfaceQuery.mk.injEq]

end SurfaceQuery

/-- Compare fields without transporting the decision through function equality.
This permits kernel replay for extensionally equal curve representatives. -/
instance instDecidableEqSurfaceQuery {X : SurfaceTarget} : DecidableEq (SurfaceQuery X) :=
  fun p q ↦ decidable_of_iff
    (p.genus = q.genus ∧ p.beta = q.beta ∧ p.insertions = q.insertions)
    (SurfaceQuery.eq_iff p q).symm

/-- Explicit compatibility of a supplied GW theory with the algebraic
surface model. This is not a proof of geometric cohomology identification,
classical three-point normalization, or existence of that GW theory. -/
structure SurfaceTheoryIdentification (X : SurfaceTarget)
    {C : StableCurveCohomology ℚ}
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C) :
    Prop where
  unit_eq : Omega.unit = 1
  pairing_eq : Omega.pairing = (SurfaceCohomology.frobenius X.blowups).pairing
  dimension_eq : Omega.graded.dimension = 2
  degree_eq : Omega.graded.degree = SurfaceCohomology.degree X.blowups
  c1Degree_eq : Omega.c1Degree = X.c1Degree

namespace SurfaceQuery

/-- Degree-zero curve-unstable arities are auxiliary conventions, outside
the geometric query domain. Positive-degree unstable arities are retained. -/
def GeometricDomain {X : SurfaceTarget} (q : SurfaceQuery X) : Prop :=
  q.beta ≠ 0 ∨ StableArity q.genus (Fin q.insertions.length)

instance {X : SurfaceTarget} (q : SurfaceQuery X) : Decidable q.GeometricDomain := by
  unfold GeometricDomain StableArity
  infer_instance

/-- Total complex codimension of states and cotangent powers. -/
def totalCodimension {X : SurfaceTarget} (q : SurfaceQuery X) : ℕ :=
  ∑ i : Fin q.insertions.length,
    ((q.insertions.get i).label.codimension + (q.insertions.get i).psi)

/-- The surface virtual dimension is `c₁(beta) + g - 1 + n`, in integers. -/
def DimensionCompatible {X : SurfaceTarget} (q : SurfaceQuery X) : Prop :=
  (q.totalCodimension : ℤ) =
    X.c1Degree q.beta + (q.genus : ℤ) - 1 + (q.insertions.length : ℤ)

instance {X : SurfaceTarget} (q : SurfaceQuery X) : Decidable q.DimensionCompatible :=
  inferInstanceAs (Decidable ((_ : ℤ) = _))

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- Evaluate through the existing full numerical invariant, including its
positive-degree unstable values. Outside `GeometricDomain`, this is the
auxiliary degree-zero unstable convention. Use `checkedEval` to reject those
requests. No independent value oracle is introduced. -/
noncomputable def eval (U : UnstableDescendantConventions M I) (q : SurfaceQuery X) : ℚ :=
  U.invariant q.genus (Fin q.insertions.length) q.beta
    (fun i ↦ (q.insertions.get i).psi)
    (fun i ↦ (q.insertions.get i).label.value)

/-- Reject degree-zero curve-unstable requests before returning a geometric
query result. The domain check itself is executable. -/
noncomputable def checkedEval (U : UnstableDescendantConventions M I)
    (q : SurfaceQuery X) : Option ℚ :=
  if q.GeometricDomain then some (q.eval U) else none

theorem checkedEval_of_geometricDomain (U : UnstableDescendantConventions M I)
    (q : SurfaceQuery X) (h : q.GeometricDomain) :
    q.checkedEval U = some (q.eval U) := if_pos h

theorem checkedEval_of_not_geometricDomain (U : UnstableDescendantConventions M I)
    (q : SurfaceQuery X) (h : ¬q.GeometricDomain) : q.checkedEval U = none := if_neg h

/-- The executable dimension predicate agrees with numerical degree
vanishing once the supplied theory's grading and Chern degree are identified. -/
theorem eval_eq_zero_of_dimension_incompatible
    (U : UnstableDescendantConventions M I) (T : SurfaceTheoryIdentification X Omega)
    (q : SurfaceQuery X) (h : ¬q.DimensionCompatible) : q.eval U = 0 := by
  apply U.invariant_eq_zero_of_degree_ne q.genus (Fin q.insertions.length) q.beta
    (fun i ↦ (q.insertions.get i).psi)
    (fun i ↦ (q.insertions.get i).label.codimension)
    (fun i ↦ (q.insertions.get i).label.value)
  · intro i
    rw [T.degree_eq]
    exact (q.insertions.get i).label.value_mem_degree
  · intro heq
    apply h
    unfold DimensionCompatible totalCodimension
    rw [Finset.sum_add_distrib, Nat.cast_add]
    rw [T.dimension_eq, T.c1Degree_eq, Fintype.card_fin] at heq
    rw [heq]
    unfold GWVirtualDimension
    ring

end SurfaceQuery

namespace SurfaceTarget

/-- A plane line is the sum of all chosen effective generators. -/
def lineCurve (X : SurfaceTarget) : X.Curve := fun _ ↦ 1

/-- The exceptional generators occur before the final fibre or line generator. -/
def exceptionalCurve (X : SurfaceTarget) (i : Fin X.blowups) : X.Curve :=
  Pi.single i.castSucc 1

theorem lineCurve_ne_zero (X : SurfaceTarget) : X.lineCurve ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  exact Nat.one_ne_zero h0

theorem exceptionalCurve_ne_zero (X : SurfaceTarget) (i : Fin X.blowups) :
    X.exceptionalCurve i ≠ 0 := by
  intro h
  have hi := congrFun h i.castSucc
  simp only [exceptionalCurve, Pi.single_eq_same, Pi.zero_apply] at hi
  exact Nat.one_ne_zero hi

theorem c1Degree_lineCurve (X : SurfaceTarget) : X.c1Degree X.lineCurve = 3 := by
  cases X <;> decide

theorem c1Degree_exceptionalCurve (X : SurfaceTarget) (i : Fin X.blowups) :
    X.c1Degree (X.exceptionalCurve i) = 1 := by
  cases X <;> fin_cases i <;> decide

end SurfaceTarget

/-- A closed finite list of initial-value obligations. The exceptional
constructors range only over divisors actually present in the fixed target. -/
inductive SurfaceSeed (X : SurfaceTarget)
  | line
  | exceptional (i : Fin X.blowups)
  | genusOneHyperplane
  | genusOneExceptional (i : Fin X.blowups)
  | genusTwoHyperplane
  | genusTwoExceptional (i : Fin X.blowups)
  | genusOneUnit
  deriving DecidableEq, Repr, Fintype

namespace SurfaceSeed

/-- The finite initial query, with no arbitrary lower-point seed family. -/
def query {X : SurfaceTarget} : SurfaceSeed X → SurfaceQuery X
  | line => ⟨0, X.lineCurve, [⟨.point, 0⟩, ⟨.point, 0⟩]⟩
  | exceptional i => ⟨0, X.exceptionalCurve i, []⟩
  | genusOneHyperplane => ⟨1, 0, [⟨.hyperplane, 0⟩]⟩
  | genusOneExceptional i => ⟨1, 0, [⟨.exceptional i, 0⟩]⟩
  | genusTwoHyperplane => ⟨2, 0, [⟨.hyperplane, 1⟩]⟩
  | genusTwoExceptional i => ⟨2, 0, [⟨.exceptional i, 1⟩]⟩
  | genusOneUnit => ⟨1, 0, [⟨.unit, 1⟩]⟩

/-- Source-specified geometric initial numbers, not asserted Lean axioms. The unit
entry is the positive Euler-characteristic-over-24 normalization. -/
def value {X : SurfaceTarget} : SurfaceSeed X → ℚ
  | line => 1
  | exceptional _ => 1
  | genusOneHyperplane => -1 / 8
  | genusOneExceptional _ => -1 / 24
  | genusTwoHyperplane => -1 / 960
  | genusTwoExceptional _ => -1 / 2880
  | genusOneUnit => X.genusOneDilaton

/-- Four common values and three values per exceptional divisor. -/
theorem card (X : SurfaceTarget) : Fintype.card (SurfaceSeed X) = 4 + 3 * X.blowups := by
  cases X <;> decide

theorem query_genus_le_two {X : SurfaceTarget} (s : SurfaceSeed X) :
    s.query.genus ≤ 2 := by
  cases s <;> simp only [query] <;> omega

theorem query_geometricDomain {X : SurfaceTarget} (s : SurfaceSeed X) :
    s.query.GeometricDomain := by
  cases s with
  | line => exact Or.inl X.lineCurve_ne_zero
  | exceptional i => exact Or.inl (X.exceptionalCurve_ne_zero i)
  | genusOneHyperplane => exact Or.inr (by norm_num [query, StableArity])
  | genusOneExceptional i => exact Or.inr (by norm_num [query, StableArity])
  | genusTwoHyperplane => exact Or.inr (by norm_num [query, StableArity])
  | genusTwoExceptional i => exact Or.inr (by norm_num [query, StableArity])
  | genusOneUnit => exact Or.inr (by norm_num [query, StableArity])

theorem query_dimensionCompatible {X : SurfaceTarget} (s : SurfaceSeed X) :
    s.query.DimensionCompatible := by
  cases s with
  | line =>
      change (4 : ℤ) = X.c1Degree X.lineCurve + 0 - 1 + 2
      rw [SurfaceTarget.c1Degree_lineCurve]
      norm_num
  | exceptional i =>
      change (0 : ℤ) = X.c1Degree (X.exceptionalCurve i) + 0 - 1 + 0
      rw [SurfaceTarget.c1Degree_exceptionalCurve]
      norm_num
  | genusOneHyperplane =>
      change (1 : ℤ) = X.c1Degree 0 + 1 - 1 + 1
      rw [map_zero]
      norm_num
  | genusOneExceptional i =>
      change (1 : ℤ) = X.c1Degree 0 + 1 - 1 + 1
      rw [map_zero]
      norm_num
  | genusTwoHyperplane =>
      change (2 : ℤ) = X.c1Degree 0 + 2 - 1 + 1
      rw [map_zero]
      norm_num
  | genusTwoExceptional i =>
      change (2 : ℤ) = X.c1Degree 0 + 2 - 1 + 1
      rw [map_zero]
      norm_num
  | genusOneUnit =>
      change (1 : ℤ) = X.c1Degree 0 + 1 - 1 + 1
      rw [map_zero]
      norm_num

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- Exactly the finite seed equalities for the supplied numerical theory.
This is a proposition to be established or named as geometric input, never
an arbitrary function furnishing values for unbounded families of queries. -/
def SeedValues (U : UnstableDescendantConventions M I) : Prop :=
  ∀ s : SurfaceSeed X, s.query.eval U = s.value

end SurfaceSeed

end AxiomaticGW

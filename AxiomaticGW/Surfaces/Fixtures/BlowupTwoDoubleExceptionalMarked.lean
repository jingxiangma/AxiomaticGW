/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalSingletons
public import AxiomaticGW.Surfaces.GenusTwoFewMarkingDimension

/-! # All string, dilaton and primary-divisor pairs on the double exceptional axes

The distinguished insertion is the string unit, the dilaton unit, H, E₁, or E₂.
The survivor ranges over the five surface basis labels. The original dimension
equation fixes its cotangent power in both marking orders.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleExceptionalMarked
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants
open BlowupTwoDoubleExceptionalDivisor (beta)
open BlowupTwoExceptionalOneMarking (labels)

private abbrev X := SurfaceTarget.blowupTwo

/-- Ordered pair; true puts the indicated unit or primary divisor in the last slot. -/
def request (i : Fin 2) (rule : Fin 5) (a : SurfaceBasisLabel .blowupTwo) (last : Bool) :
    SurfaceQuery .blowupTwo :=
  let s : SurfaceInsertion .blowupTwo := ⟨a, 4 - a.codimension⟩
  ![UnitEquation.string.pair last (beta i) s, UnitEquation.dilaton.pair last (beta i) s,
    divisorPair last (beta i) .hyperplane s, divisorPair last (beta i) (.exceptional 0) s,
    divisorPair last (beta i) (.exceptional 1) s] rule

/-- The ordered equation coefficients act on the complete class-specific singleton frame. -/
def values (i : Fin 2) (rule : Fin 5) (a : SurfaceBasisLabel .blowupTwo) : ℚ :=
  let v := BlowupTwoDoubleExceptionalSingletons.value i
  let s : SurfaceInsertion .blowupTwo := ⟨a, 4 - a.codimension⟩
  let divisorValue := fun (d : SurfaceBasisLabel .blowupTwo) ↦
    d.primaryFactor (beta i) * v a + cupCoefficient d s * v (cupInsertion d s).label
  ![v a, 3 * v a, divisorValue .hyperplane, divisorValue (.exceptional 0),
    divisorValue (.exceptional 1)] rule

private def singleton (i : Fin 2) : SurfaceQuery .blowupTwo → Option ℚ :=
  singletonTable? (fun j ↦ BlowupTwoDoubleExceptionalSingletons.request i (labels j))
    (fun j ↦ BlowupTwoDoubleExceptionalSingletons.value i (labels j))

private theorem singleton_sound (i : Fin 2) (q : SurfaceQuery .blowupTwo) (v : ℚ)
    (h : singleton i q = some v) : queryValue? 0 q = some v :=
  singletonTable?_sound (fun j ↦ BlowupTwoDoubleExceptionalSingletons.accepted i (labels j)) q v h

/-- Each row belongs to the fixed bounded benchmark. -/
theorem domain : ∀ (i : Fin 2) (r : Fin 5) (a : SurfaceBasisLabel .blowupTwo) (last : Bool),
    FewMarkingQuery (request i r a last) := by
  unfold FewMarkingQuery
  decide +kernel

/-- The original string, dilaton or two-term divisor reduction certifies every row. -/
theorem checked (i : Fin 2) (r : Fin 5) (a : SurfaceBasisLabel .blowupTwo) (last : Bool) :
    CheckedDescendant 0 (request i r a last) (values i r a) := by
  apply markedPairValueWith?_checked 0 (singleton_sound i)
  revert i r a last
  decide +kernel

/-- Recognition by either original ordered parser. -/
def recognized (q : SurfaceQuery .blowupTwo) : Bool :=
  (unitPairReduction? q).isSome || (divisorPairReduction? q).isSome

/-- Full query set for one axis, preserving both of the original marked slots. -/
def atAxis (i : Fin 2) : Finset (SurfaceQuery .blowupTwo) :=
  Finset.univ.image (fun t : Fin 5 × SurfaceBasisLabel .blowupTwo × Bool ↦
    request i t.1 t.2.1 t.2.2)

private def fromShapes (i : Fin 2) : Finset (SurfaceQuery .blowupTwo) :=
  ((dimensionShapes .blowupTwo 2).image (fun m ↦ (⟨2, beta i, m⟩ : SurfaceQuery .blowupTwo))).filter
    (fun q ↦ recognized q = true)

private theorem shape_eq (i : Fin 2) : atAxis i = fromShapes i := by
  fin_cases i <;> decide +kernel

/-- The frame is exactly the dimension-compatible two-mark requests accepted by either parser,
including both orderings and arbitrary natural cotangent powers. -/
theorem mem_atAxis_iff (i : Fin 2) (q : SurfaceQuery .blowupTwo) :
    q ∈ atAxis i ↔ q.genus = 2 ∧ q.beta = beta i ∧ q.insertions.length = 2 ∧
      q.DimensionCompatible ∧ recognized q = true := by
  have he : X.effective.energy (beta i) = 2 := by fin_cases i <;> decide +kernel
  constructor
  · intro h
    obtain ⟨⟨r, a, last⟩, _, rfl⟩ := Finset.mem_image.mp h
    have shape : ∀ (i : Fin 2) (r : Fin 5) (a : SurfaceBasisLabel .blowupTwo) (last : Bool),
        let q := request i r a last
        q.beta = beta i ∧ q.insertions.length = 2 ∧ recognized q = true := by decide +kernel
    obtain ⟨hb, hn, hr⟩ := shape i r a last
    have hd := domain i r a last
    exact ⟨hd.1, hb, hn, hd.2.2.2.2, hr⟩
  · rintro ⟨hg, hb, hn, hd, hr⟩
    rw [shape_eq, fromShapes, Finset.mem_filter]
    refine ⟨Finset.mem_image.mpr ⟨q.insertions, ?_, ?_⟩, hr⟩
    · rw [← he, mem_dimensionShapes_iff (beta i) (by rw [he]; decide)]
      refine ⟨by omega, ?_⟩
      rwa [show (⟨2, beta i, q.insertions⟩ : SurfaceQuery .blowupTwo) = q from
        (SurfaceQuery.eq_iff _ _).mpr ⟨hg.symm, hb.symm, rfl⟩]
    · exact (SurfaceQuery.eq_iff _ _).mpr ⟨hg.symm, hb.symm, rfl⟩

/-- The geometric value of every ordered row under the original geometric reconstruction inputs. -/
theorem accepted_from_geometry (i : Fin 2) (r : Fin 5) (a : SurfaceBasisLabel .blowupTwo)
    (last : Bool) :
    type_of% (@SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry
      (X := .blowupTwo) (i := 0) (q := request i r a last)
      (hg := (domain i r a last).1) (hv := checked i r a last)) :=
  @SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry
    (X := .blowupTwo) (i := 0) (q := request i r a last)
    (hg := (domain i r a last).1) (hv := checked i r a last)

end AxiomaticGW.BlowupTwoDoubleExceptionalMarked

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Geometry.EvaluationSupport
public import AxiomaticGW.Surfaces.GenusTwoCanonicalQueries

/-!
# Exceptional-image support for the fixed surfaces

Positive classes with zero hyperplane intersection have exceptional image.
The geometric input below asks that the point evaluation pullback vanish on
their stable-map spaces. Its geometric construction, by factoring evaluation
through the exceptional locus, is not implemented here. This is a class-level
condition for all genera and powers, independent of a reconstruction equation.

It implies every canonical positive exceptional genus-two value is zero,
because each such query contains a point. Class zero and descendants without
a point remain outside this vanishing rule. This supplies the exceptional
boundary needed by the surface route in Wennink, Lemma 8.3 and Section 8.3,
without assuming an infinite family of numerical genus-two seed values.
-/

@[expose] public section

namespace AxiomaticGW
variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  {U : UnstableDescendantConventions M I}

/-- The point class restricts to zero on positive exceptional-image stable maps.
Geometric applicability is required separately from the numerical GW laws. -/
def ExceptionalPointSupport (G : StableMapIntersection U) : Prop :=
  ∀ g S, [Fintype S] → ∀ beta, beta ≠ 0 → X.divisorIntersections beta 0 = 0 →
    ∀ s : S, G.evaluation g S beta s (SurfaceCohomology.point X.blowups) = 0

namespace SurfaceQuery

/-- An actual point marking vanishes by exceptional evaluation support, at any power. -/
theorem eval_eq_zero_of_exceptional_point (G : StableMapIntersection U)
    (hG : ExceptionalPointSupport G) (q : SurfaceQuery X)
    (hb : q.beta ≠ 0) (hd : X.divisorIntersections q.beta 0 = 0)
    (s : Fin q.insertions.length) (hs : (q.insertions.get s).label = .point) :
    q.eval U = 0 := by
  apply G.invariant_eq_zero_of_evaluation_eq_zero q.genus (Fin q.insertions.length)
    q.beta (fun i ↦ (q.insertions.get i).psi)
    (fun i ↦ (q.insertions.get i).label.value) s
  rw [hs]
  exact hG q.genus (Fin q.insertions.length) q.beta hb hd s

/-- The point may occur anywhere in the ordered query, with arbitrary other markings. -/
theorem eval_eq_zero_of_exceptional_point_mem (G : StableMapIntersection U)
    (hG : ExceptionalPointSupport G) (q : SurfaceQuery X)
    (hb : q.beta ≠ 0) (hd : X.divisorIntersections q.beta 0 = 0)
    (hp : SurfaceBasisLabel.point ∈ q.insertions.map SurfaceInsertion.label) :
    q.eval U = 0 := by
  obtain ⟨a, ha, hlabel⟩ := List.mem_map.mp hp
  obtain ⟨s, hs⟩ := List.mem_iff_get.mp ha
  apply eval_eq_zero_of_exceptional_point G hG q hb hd s
  rw [hs]
  exact hlabel

end SurfaceQuery

namespace SurfaceGenusTwo

/-- The positive exceptional primary family always retains at least one point. -/
theorem exceptional_primary_eval_eq_zero (G : StableMapIntersection U)
    (hG : ExceptionalPointSupport G) (beta : X.Curve)
    (hb : beta ≠ 0) (hd : X.divisorIntersections beta 0 = 0) :
    (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1)).eval U = 0 := by
  apply SurfaceQuery.eval_eq_zero_of_exceptional_point G hG _ hb hd
    ⟨0, by simp only [SurfaceQuery.points, List.length_replicate]; omega⟩
  simp only [SurfaceQuery.points, List.get_eq_getElem, List.getElem_replicate]

/-- Every divisor first-descendant family has a retained point at positive energy. -/
theorem exceptional_first_divisor_eval_eq_zero (G : StableMapIntersection U)
    (hG : ExceptionalPointSupport G) (beta : X.Curve)
    (hb : beta ≠ 0) (hd : X.divisorIntersections beta 0 = 0)
    (b : SurfaceBasisLabel X) :
    (SurfaceFirstDescendant.query 2 beta b (X.effective.energy beta)).eval U = 0 := by
  have he : 0 < X.effective.energy beta :=
    Nat.pos_of_ne_zero (fun h ↦ hb ((X.effective.energy_eq_zero_iff beta).mp h))
  apply SurfaceQuery.eval_eq_zero_of_exceptional_point G hG _ hb hd
    ⟨1, by simp only [SurfaceFirstDescendant.query, List.length_cons,
      List.length_replicate]; omega⟩
  simp only [SurfaceFirstDescendant.query, List.get_eq_getElem,
    List.getElem_cons_succ, List.getElem_replicate]

/-- The point descendant has its own point marking, including energy one. -/
theorem exceptional_first_point_eval_eq_zero (G : StableMapIntersection U)
    (hG : ExceptionalPointSupport G) (beta : X.Curve)
    (hb : beta ≠ 0) (hd : X.divisorIntersections beta 0 = 0) :
    (SurfaceFirstDescendant.query 2 beta .point (X.effective.energy beta - 1)).eval U = 0 := by
  apply SurfaceQuery.eval_eq_zero_of_exceptional_point G hG _ hb hd
    ⟨0, by simp only [SurfaceFirstDescendant.query, List.length_cons]; omega⟩
  simp only [SurfaceFirstDescendant.query, List.get_eq_getElem, List.getElem_cons_zero]

/-- Every member of the complete canonical list is zero in the positive exceptional sector. -/
theorem exceptional_canonical_eval_eq_zero (G : StableMapIntersection U)
    (hG : ExceptionalPointSupport G) (beta : X.Curve)
    (hb : beta ≠ 0) (hd : X.divisorIntersections beta 0 = 0)
    (q : SurfaceQuery X) (hq : q ∈ canonicalQueries X beta) : q.eval U = 0 := by
  rcases (mem_canonicalQueries beta q).mp hq with h | h | ⟨i, h⟩ | ⟨_, h⟩ <;> subst q
  · exact exceptional_primary_eval_eq_zero G hG beta hb hd
  · exact exceptional_first_divisor_eval_eq_zero G hG beta hb hd .hyperplane
  · exact exceptional_first_divisor_eval_eq_zero G hG beta hb hd (.exceptional i)
  · exact exceptional_first_point_eval_eq_zero G hG beta hb hd

/-- The exceptional boundary agrees with the geometric-domain query interface. -/
theorem exceptional_canonical_checkedEval_eq_zero (G : StableMapIntersection U)
    (hG : ExceptionalPointSupport G) (beta : X.Curve)
    (hb : beta ≠ 0) (hd : X.divisorIntersections beta 0 = 0)
    (q : SurfaceQuery X) (hq : q ∈ canonicalQueries X beta) : q.checkedEval U = some 0 := by
  rw [SurfaceQuery.checkedEval_of_geometricDomain U q
    (canonicalQueries_geometricDomain beta hq),
    exceptional_canonical_eval_eq_zero G hG beta hb hd q hq]

/-- Exact partial evaluation of point-supported exceptional requests.
Class zero and requests without a point require their own reconstruction. -/
def exceptionalPointQueryValue? (q : SurfaceQuery X) : Option ℚ :=
  if q.beta ≠ 0 ∧ X.divisorIntersections q.beta 0 = 0 ∧
      SurfaceBasisLabel.point ∈ q.insertions.map SurfaceInsertion.label then some 0 else none

/-- The returned zero is the actual geometric-domain query under the named support input. -/
theorem exceptionalPointQueryValue?_sound (G : StableMapIntersection U)
    (hG : ExceptionalPointSupport G) (q : SurfaceQuery X) (claimed : ℚ)
    (h : exceptionalPointQueryValue? q = some claimed) :
    q.checkedEval U = some claimed := by
  unfold exceptionalPointQueryValue? at h
  split_ifs at h with hq
  · have hc : claimed = 0 := (Option.some.inj h).symm
    rw [hc, SurfaceQuery.checkedEval_of_geometricDomain U q (Or.inl hq.1),
      SurfaceQuery.eval_eq_zero_of_exceptional_point_mem G hG q hq.1 hq.2.1 hq.2.2]

end SurfaceGenusTwo
end AxiomaticGW

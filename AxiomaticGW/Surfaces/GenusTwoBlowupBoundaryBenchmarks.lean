/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupBoundedCertificate

/-!
# Canonical genus-two benchmarks on positive plane-degree-zero classes

The energy-twelve window contains twelve exceptional classes on the first
blowup and ninety on the second. The sector map retains complete curve
coordinates and every exceptional divisor label. Reconstruction uses the
positive exceptional boundary of the original well-founded table.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwoBlowupBoundaryBenchmarks
open SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupBoundedCertificate

variable {X : SurfaceTarget}

/-- Positive effective classes of plane degree zero in the benchmark energy window. -/
def classes (X : SurfaceTarget) : Finset X.Curve :=
  (X.bounded 12).filter (fun beta ↦ beta ≠ 0 ∧ X.planeDegree beta = 0)

theorem mem_classes (beta : X.Curve) :
    beta ∈ classes X ↔ X.effective.energy beta ≤ 12 ∧ beta ≠ 0 ∧ X.planeDegree beta = 0 := by
  rw [classes, Finset.mem_filter, X.bounded_eq, X.effective.mem_bounded]

/-- The existing bounded-table sector list as a finite set. -/
def sectors (X : SurfaceTarget) : Finset (Family X) :=
  ⟨families X, by
    have inj : Function.Injective (@Family.exceptional X) := fun _ _ h ↦ Family.exceptional.inj h
    have h := (List.nodup_finRange X.blowups).map inj
    simp [families, h]⟩

/-- Distinct canonical requests, indexed by both the full curve class and sector. -/
def requests (X : SurfaceTarget) : Finset (SurfaceQuery X) :=
  ((classes X).product (sectors X)).map ⟨_, state_query_injective⟩

/-- The mathematical benchmark domain uses the independent canonical shape specification. -/
def InDomain (q : SurfaceQuery X) : Prop :=
  q.beta ≠ 0 ∧ X.planeDegree q.beta = 0 ∧ X.effective.energy q.beta ≤ 12 ∧
    q ∈ SurfaceGenusTwo.canonicalQueries X q.beta

private theorem query_beta (f : Family X) (beta : X.Curve) : (f.query beta).beta = beta := by
  cases f <;> rfl

private theorem mem_requests_state (q : SurfaceQuery X) :
    q ∈ requests X ↔ ∃ f : Family X, q.beta ∈ classes X ∧ f.query q.beta = q := by
  rw [requests, Finset.mem_map]
  constructor
  · rintro ⟨⟨beta, f⟩, h, rfl⟩
    exact ⟨f, by simpa only [Function.Embedding.coeFn_mk, query_beta] using
      (Finset.mem_product.mp h).1, by simp only [Function.Embedding.coeFn_mk, query_beta]⟩
  · rintro ⟨f, hb, hf⟩
    exact ⟨(q.beta, f), Finset.mem_product.mpr ⟨hb, mem_families X f⟩, hf⟩

/-- Enter the benchmark by its complete curve class and sector. -/
theorem query_mem (beta : X.Curve) (f : Family X) (h : beta ∈ classes X) :
    f.query beta ∈ requests X := by
  apply (mem_requests_state _).mpr
  rw [query_beta]
  exact ⟨f, h, rfl⟩

/-- Coverage is exact independently of the stored table value. -/
theorem mem_requests (q : SurfaceQuery X) : q ∈ requests X ↔ InDomain q := by
  rw [mem_requests_state]
  constructor
  · rintro ⟨f, hb, hf⟩
    obtain ⟨he, hpos, hd⟩ := (mem_classes _).mp hb
    refine ⟨hpos, hd, he, ?_⟩
    have hp := Nat.pos_of_ne_zero ((X.effective.energy_eq_zero_iff q.beta).not.mpr hpos)
    have hm := f.query_mem_canonicalQueries q.beta (fun _ ↦ hp)
    rwa [hf] at hm
  · rintro ⟨hn, hd, he, hq⟩
    obtain ⟨f, hf⟩ := family_of_mem_canonicalQueries hq
    exact ⟨f, (mem_classes _).mpr ⟨he, hn, hd⟩, hf⟩

/-- Each enumerated query decodes to its unique canonical state and the original
reconstruction assigns it zero, for any choice of the recursion pivot. -/
theorem reconstructed (i : Fin X.blowups) (q : SurfaceQuery X) (h : q ∈ requests X) :
    (state? q).map (SurfaceGenusTwoBlowupRecursion.values i) = some 0 := by
  obtain ⟨f, hb, hf⟩ := (mem_requests_state q).mp h
  obtain ⟨_, hpos, hd⟩ := (mem_classes _).mp hb
  rw [(state?_eq_some_iff q (q.beta, f)).mpr hf, Option.map_some,
    SurfaceGenusTwoBlowupRecursion.values_boundary i (q.beta, f) hd,
    SurfaceGenusTwoBlowupBoundary.value_of_ne_zero q.beta hpos f]

/-- Under ordinary exceptional point support every request has the reconstructed geometric value. -/
theorem checkedEval {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (V : StableMapIntersection U)
    (hV : ExceptionalPointSupport V) (q : SurfaceQuery X) (h : q ∈ requests X) :
    q.checkedEval U = some 0 := by
  obtain ⟨hn, hd, _, hq⟩ := (mem_requests q).mp h
  exact SurfaceGenusTwo.exceptional_canonical_checkedEval_eq_zero V hV _ hn
    ((X.planeDegree_eq_zero_iff_divisorIntersections_eq_zero q.beta).mp hd) q hq

/-- One distinct query for each sector at each complete curve class. -/
theorem card_requests (X : SurfaceTarget) :
    (requests X).card = (classes X).card * (X.blowups + 3) := by
  rw [requests, Finset.card_map]
  calc
    _ = (classes X).card * (sectors X).card := Finset.card_product _ _
    _ = _ := by
      change (classes X).card * (families X).length = _
      simp only [families, List.length_append, List.length_cons, List.length_nil, List.length_map,
        List.length_finRange]
      congr 1
      omega

/-- The full Mori coordinates give twelve positive exceptional classes on the first blowup
and ninety on the second. -/
theorem class_counts : (classes .hirzebruchOne).card = 12 ∧ (classes .blowupTwo).card = 90 := by
  decide +kernel

/-- The exact counts measure distinct complete queries in the energy-twelve boundary. -/
theorem counts :
    (requests .hirzebruchOne).card = 48 ∧ (requests .blowupTwo).card = 450 := by
  rw [card_requests, card_requests, class_counts.1, class_counts.2]
  decide

end AxiomaticGW.SurfaceGenusTwoBlowupBoundaryBenchmarks

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoAncestorCertificate
public import AxiomaticGW.Surfaces.PlaneGenusTwoQueryCertificate

/-!
# Reusing certified ancestors in plane descendant queries

A finite ancestor table is checked against the original square/product
equations and the same canonical terminal table. Substituting its accepted
values into the mixed comparison preserves every full descendant query.
Outside the cache, evaluation uses the original terminating algorithm.
The existing canonical-table theorem supplies its geometric interpretation.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open SurfaceGenusTwo

/-- Evaluate the unchanged mixed comparison using a finite ancestor cache. -/
def planeDescendantValueCached (canonical : ℕ → Fin 3 → ℚ)
    (queries : Finset (SurfaceAncestorKey .plane)) (values : SurfaceAncestorKey .plane → ℚ)
    (n : ℕ) (beta : SurfaceTarget.plane.Curve) (d : Fin n → ℕ)
    (a : Fin n → SurfaceBasisLabel .plane) : ℚ :=
  RationalTerms.eval (ancestorValueCached (planeLowPsiValueWith canonical) queries values)
    (SurfaceDescendant.mixedAncestorTerms 2 (Fin n)
      (by simp only [StableArity, Fintype.card_fin]; omega)
      (List.finRange n) beta d 0 a)

/-- An accepted cache changes no descendant value or supported insertion multiplicity. -/
theorem planeDescendantValueCached_eq (canonical : ℕ → Fin 3 → ℚ)
    (queries : Finset (SurfaceAncestorKey .plane)) (values : SurfaceAncestorKey .plane → ℚ)
    (hcheck : checkAncestorValues (planeLowPsiValueWith canonical) queries values = true)
    (n : ℕ) (beta : SurfaceTarget.plane.Curve) (d : Fin n → ℕ)
    (a : Fin n → SurfaceBasisLabel .plane) :
    planeDescendantValueCached canonical queries values n beta d a =
      planeDescendantValueWith canonical n beta d a := by
  rw [planeDescendantValueCached,
    ancestorValueCached_eq (planeLowPsiValueWith canonical) queries values hcheck]
  rfl

/-- Ordered full-query interface; unsupported genera are still rejected. -/
def planeQueryValueCached? (canonical : ℕ → Fin 3 → ℚ)
    (queries : Finset (SurfaceAncestorKey .plane)) (values : SurfaceAncestorKey .plane → ℚ)
    (q : SurfaceQuery .plane) : Option ℚ :=
  if q.genus = 2 then
    some (planeDescendantValueCached canonical queries values q.insertions.length q.beta
      (fun i ↦ (q.insertions.get i).psi) (fun i ↦ (q.insertions.get i).label))
  else none

/-- Acceptance preserves the existing query algorithm relative to its canonical table. -/
theorem planeQueryValueCached?_eq_with (canonical : ℕ → Fin 3 → ℚ)
    (queries : Finset (SurfaceAncestorKey .plane)) (values : SurfaceAncestorKey .plane → ℚ)
    (hcheck : checkAncestorValues (planeLowPsiValueWith canonical) queries values = true)
    (q : SurfaceQuery .plane) :
    planeQueryValueCached? canonical queries values q = planeQueryValueWith? canonical q := by
  rw [planeQueryValueCached?, planeQueryValueWith?]
  split_ifs
  · exact congrArg some (planeDescendantValueCached_eq canonical queries values hcheck
      _ q.beta _ _)
  · rfl

/-- Both accepted tables identify a cached answer with the original reconstruction. -/
theorem planeQueryValueCached?_eq (bound : ℕ) (canonical : ℕ → Fin 3 → ℚ)
    (hcanonical : planeCheckCanonicalTable bound canonical = true)
    (queries : Finset (SurfaceAncestorKey .plane)) (values : SurfaceAncestorKey .plane → ℚ)
    (hcheck : checkAncestorValues (planeLowPsiValueWith canonical) queries values = true)
    (q : SurfaceQuery .plane) (hb : q.beta 0 ≤ bound) :
    planeQueryValueCached? canonical queries values q = planeQueryValue? q := by
  rw [planeQueryValueCached?_eq_with canonical queries values hcheck,
    planeQueryValueWith?_eq bound canonical hcanonical q hb]

end AxiomaticGW.BelorousskiPandharipande

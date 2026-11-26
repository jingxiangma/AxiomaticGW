import AxiomaticGW.Surfaces.GenusTwoCachedAncestors
import AxiomaticGW.Surfaces.GenusTwoCachedComponents

open AxiomaticGW SurfaceGenusTwo

namespace GenusTwoComponentCacheTest

-- A genuine nonzero terminal, rather than an arbitrary supplied cache entry.
def pointKey : SurfaceAncestorKey .plane :=
  ⟨0, 0, ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.point, 0⟩] : List (SurfaceInsertion .plane)),
    by decide⟩

theorem pointValue : residualTerms pointKey = RationalTerms.term 1 0 := by cbv

def cache : ResidualCache .plane :=
  .ofEntries (fun _ : Fin 1 ↦ pointKey) (fun _ ↦ RationalTerms.term 1 0)
    (fun _ _ _ ↦ Subsingleton.elim _ _) (fun _ ↦ pointValue.symm)

-- The cache may contain only one lower-genus component. Every other component,
-- and either square or product marking selection, retains the original equation.
example (q : SurfaceAncestorKey .plane) (hk : 1 < q.totalPsi) :
    ancestorReductionTermsCached cache q hk = ancestorReductionTerms q hk :=
  ancestorReductionTermsCached_eq cache q hk

-- An incorrect value cannot supply the equality required by the constructor.
example : ¬(RationalTerms.term 2 0 = residualTerms pointKey) := by
  rw [pointValue]
  decide +kernel

-- Repeated full keys would double the lookup sum; the constructor rejects them.
example : ¬Function.Injective (fun _ : Fin 2 ↦ pointKey) := by
  intro h
  have he := h (a₁ := (0 : Fin 2)) (a₂ := 1) rfl
  exact (by decide : (0 : Fin 2) ≠ 1) he

-- No coverage premise is needed even for an empty cache, on any fixed target.
example (X : SurfaceTarget) (q : SurfaceAncestorKey X) (hk : 1 < q.totalPsi) :
    ancestorReductionTermsCached (ResidualCache.ofQueries X ∅) q hk =
      ancestorReductionTerms q hk := ancestorReductionTermsCached_eq _ q hk

-- Stored and missing nonzero scalar components both retain their actual value.
example : cachedLowerValue cache pointKey = 1 := by decide +kernel

def divisorKey : SurfaceAncestorKey .plane :=
  ⟨0, 0, ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩] :
    List (SurfaceInsertion .plane)), by decide⟩

example : divisorKey ∉ cache.queries ∧ cachedLowerValue cache divisorKey = 1 := by
  decide +kernel

-- Elliptic reconstruction works with a genuinely incomplete component cache.
def ellipticKey : SurfaceAncestorKey .plane :=
  ⟨1, 0, ([⟨.unit, 1⟩] : List (SurfaceInsertion .plane)), by decide⟩

example : ellipticStepCached cache ellipticKey (by decide) (by decide) = 1 / 8 := by
  decide +kernel

example (X : SurfaceTarget) (q : SurfaceAncestorKey X) (hg : q.genus = 1)
    (hp : ¬q.IsPrimary) :
    ellipticStepCached (ResidualCache.ofQueries X ∅) q hg hp =
      SurfaceGenusOne.ancestorValue X q := ellipticStepCached_eq _ q hg hp

end GenusTwoComponentCacheTest

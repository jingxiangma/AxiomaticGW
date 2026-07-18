/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.DecoratedStableGraph

/-!
# Basic tautological strata

This file constructs the one-vertex stable graph and its decorated strata.
These are the fundamental class and the ordinary kappa/psi monomials before
any boundary gluing.
-/

@[expose] public section

namespace AxiomaticGW

namespace StableGraphCode

variable {S : Type} [Fintype S]

/-- The stable graph with one genus-`g` vertex, all legs on that vertex, and
no internal edges. -/
def oneVertex (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) :
    StableGraphCode S where
  vertexCount := 1
  edgeCount := 0
  vertexCount_pos := by omega
  legVertex := fun _ ↦ 0
  endpoint := fun e _ ↦ Fin.elim0 e
  genus := fun _ ↦ g
  connected := by
    intro v w
    have hvw : v = w := Subsingleton.elim _ _
    subst w
    exact Relation.ReflTransGen.refl
  stable := by
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    have hflags : Fintype.card
        {p : Fin 0 × Fin 2 // (fun e _ ↦ Fin.elim0 e) p.1 p.2 =
          (0 : Fin 1)} = 0 := by
      rw [Fintype.card_eq_zero]
    simpa only [StableArity, mul_zero, Fintype.card_subtype_true,
      Fintype.card_fin, Nat.zero_add, hflags, Nat.add_zero] using h

@[simp]
theorem oneVertex_totalGenus (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) : (oneVertex g S h).totalGenus = g := by
  simp only [totalGenus, oneVertex, firstBetti, Finset.univ_unique,
    Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton, Nat.add_zero,
    Nat.reduceAdd, Nat.sub_self]

end StableGraphCode

namespace DecoratedStableGraph

variable {S : Type} [Fintype S]

/-- A decorated one-vertex stratum. Kappa classes live at the unique vertex,
and psi classes live at the labelled external legs. -/
def oneVertex (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (kappaPower : ℕ+ →₀ ℕ) (legPsiPower : S → ℕ) :
    DecoratedStableGraph S where
  graph := StableGraphCode.oneVertex g S h
  kappaPower := fun _ ↦ kappaPower
  legPsiPower := legPsiPower
  halfEdgePsiPower := fun e _ ↦ Fin.elim0 e

@[simp]
theorem oneVertex_totalGenus (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (kappaPower : ℕ+ →₀ ℕ)
    (legPsiPower : S → ℕ) :
    (oneVertex g S h kappaPower legPsiPower).graph.totalGenus = g :=
  StableGraphCode.oneVertex_totalGenus g S h

@[simp]
theorem oneVertex_codimension (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (kappaPower : ℕ+ →₀ ℕ)
    (legPsiPower : S → ℕ) :
    (oneVertex g S h kappaPower legPsiPower).codimension =
      kappaPower.sum (fun i power ↦ (i : ℕ) * power) +
        ∑ s, legPsiPower s := by
  simp only [codimension, kappaCodimension, legPsiCodimension,
    halfEdgePsiCodimension, oneVertex, StableGraphCode.oneVertex,
    Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Nat.zero_add, Nat.add_zero, Finset.univ_eq_empty,
    Finset.sum_empty]

end DecoratedStableGraph

namespace TautologicalStratum

variable {S : Type} [Fintype S]

/-- Isomorphism class of a decorated one-vertex stable graph. -/
noncomputable def oneVertex (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S)
    (kappaPower : ℕ+ →₀ ℕ) (legPsiPower : S → ℕ) :
    TautologicalStratum g S :=
  mk (DecoratedStableGraph.oneVertex g S h kappaPower legPsiPower)
    (DecoratedStableGraph.oneVertex_totalGenus g S h kappaPower
      legPsiPower)

/-- Fundamental-class stratum represented by the undecorated one-vertex
graph. -/
noncomputable def fundamental (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) :
    TautologicalStratum g S := oneVertex g S h 0 (fun _ ↦ 0)

@[simp]
theorem oneVertex_codimension (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (kappaPower : ℕ+ →₀ ℕ)
    (legPsiPower : S → ℕ) :
    (oneVertex g S h kappaPower legPsiPower).codimension =
      kappaPower.sum (fun i power ↦ (i : ℕ) * power) +
        ∑ s, legPsiPower s :=
  DecoratedStableGraph.oneVertex_codimension g S h kappaPower legPsiPower

@[simp]
theorem fundamental_codimension (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) : (fundamental g S h).codimension = 0 := by
  simp only [fundamental, oneVertex_codimension, Finsupp.sum_zero_index,
    Finset.sum_const_zero, Nat.add_zero]

end TautologicalStratum

end AxiomaticGW

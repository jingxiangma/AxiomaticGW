/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.CurveConventionCertificate
public import AxiomaticGW.Tautological.GraphBounds

/-! # Effective-degree support of connected localization graphs

The incidence graph can have parallel edges and unstable end vertices.
A vertex records its fixed-point image, and each edge covers an actual toric
edge a positive number of times. This is the support data prior to weighting
or stabilizing a fixed locus.
-/

@[expose] public section
namespace AxiomaticGW.GKM
open CurveConventionCertificate

/-- Incidence and covering data of one connected torus-fixed graph. -/
structure FixedGraphSupport {X : SurfaceTarget} {n r : ℕ} (tables : Tables X n r) (v e : ℕ) where
  /-- Both ends of each positive edge of the source graph. -/
  endpoint : Fin e → Fin 2 → Fin v
  /-- Fixed point carrying each possibly unstable vertex. -/
  image : Fin v → Fin n
  /-- Index of the undirected target edge in the original edge table. -/
  edgeIndex : Fin e → Fin r
  /-- Covering multiplicity of each edge. -/
  cover : Fin e → ℕ+
  /-- Both images are the endpoints of the same target curve, in either order. -/
  incident : ∀ a, let t := tables.edges (edgeIndex a)
    (image (endpoint a 0) = t.source ∧ image (endpoint a 1) = t.target) ∨
    (image (endpoint a 0) = t.target ∧ image (endpoint a 1) = t.source)
  /-- Paths relate every two source vertices. -/
  connected : (StableGraphCode.incidenceGraph endpoint).Connected

namespace FixedGraphSupport

variable {X : SurfaceTarget} {n r v e : ℕ} {tables : Tables X n r}
  (G : FixedGraphSupport tables v e)

/-- The full effective class, counting parallel edges and every sheet of a cover. -/
def degree : X.Curve := fun k ↦ ∑ a, (G.cover a : ℕ) * (tables.edges (G.edgeIndex a)).curve k

/-- A zero coordinate of the total forces every individual edge class into the same face. -/
theorem edge_coordinate_zero (k : Fin (X.blowups + 1)) (hk : G.degree k = 0) (a : Fin e) :
    (tables.edges (G.edgeIndex a)).curve k = 0 := by
  have hle : (G.cover a : ℕ) * (tables.edges (G.edgeIndex a)).curve k ≤ G.degree k :=
    Finset.single_le_sum (f := fun b ↦ (G.cover b : ℕ) * (tables.edges (G.edgeIndex b)).curve k)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
  rw [hk, Nat.le_zero] at hle
  exact (Nat.mul_eq_zero.mp hle).resolve_left (G.cover a).ne_zero

/-- On a zero coordinate face, vertex images have a common label whenever every permitted
target edge preserves that label. Labels can encode arbitrary connected components. -/
theorem constant_on_face {K : Type*} (k : Fin (X.blowups + 1)) (hk : G.degree k = 0)
    (label : Fin n → K)
    (hedge : ∀ t, (tables.edges t).curve k = 0 →
      label (tables.edges t).source = label (tables.edges t).target) (a b : Fin v) :
    label (G.image a) = label (G.image b) := by
  have ends (t : Fin e) : label (G.image (G.endpoint t 0)) = label (G.image (G.endpoint t 1)) := by
    have ht := hedge (G.edgeIndex t) (G.edge_coordinate_zero k hk t)
    rcases G.incident t with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
    · simpa only [h₀, h₁] using ht
    · simpa only [h₀, h₁] using ht.symm
  have path := (StableGraphCode.reachable_iff G.endpoint a b).mp (G.connected.preconnected a b)
  induction path with
  | refl => rfl
  | tail _ step ih =>
    apply ih.trans
    rcases step with ⟨t, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ends t
    · exact (ends t).symm

/-- One contracted vertex over a fixed point; its class is zero before genus or marking data. -/
def contractedPoint (tables : Tables X n r) (p : Fin n) : FixedGraphSupport tables 1 0 where
  endpoint := Fin.elim0
  image _ := p
  edgeIndex := Fin.elim0
  cover := Fin.elim0
  incident a := Fin.elim0 a
  connected := by decide +kernel

/-- A graph with one contracted vertex has zero effective class. -/
theorem degree_contractedPoint (tables : Tables X n r) (p : Fin n) :
    (contractedPoint tables p).degree = 0 := by
  funext k
  exact Finset.sum_empty

/-- A single positive cover of any recorded edge, with either ordering of its endpoints. -/
def singleCover (tables : Tables X n r) (t : Fin r) (d : ℕ+) (reverse : Bool) :
    FixedGraphSupport tables 2 1 where
  endpoint _ p := p
  image := if reverse then ![(tables.edges t).target, (tables.edges t).source]
    else ![(tables.edges t).source, (tables.edges t).target]
  edgeIndex _ := t
  cover _ := d
  incident _ := by cases reverse <;> first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩
  connected := by
    constructor
    intro i j
    apply (StableGraphCode.reachable_iff _ i j).2
    fin_cases i <;> fin_cases j
    · exact .refl
    · exact .single ⟨0, Or.inl ⟨rfl, rfl⟩⟩
    · exact .single ⟨0, Or.inr ⟨rfl, rfl⟩⟩
    · exact .refl

/-- A degree-`d` cover contributes `d` times the entire target edge class. -/
theorem degree_singleCover (tables : Tables X n r) (t : Fin r) (d : ℕ+) (reverse : Bool) :
    (singleCover tables t d reverse).degree = (d : ℕ) • (tables.edges t).curve := by
  funext k
  rw [degree, Fin.sum_univ_one]
  exact (nsmul_eq_mul _ _).symm

/-- Source graph support over all finite sizes at a specified full class. -/
abbrev AtDegree (tables : Tables X n r) (beta : X.Curve) :=
  Σ v, Σ e, {G : FixedGraphSupport tables v e // G.degree = beta}

end FixedGraphSupport
end AxiomaticGW.GKM

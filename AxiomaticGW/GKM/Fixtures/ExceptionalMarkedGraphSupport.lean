/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.ExceptionalAxisTransport

/-! # Vanishing of the native marked insertion factor on exceptional graph supports

`StableMapGKM._localization_factors` multiplies the basis restrictions at all marked
fixed points before using cotangent powers or genus factors. For positive plane-degree-zero
classes a point marking kills that product. On a pure exceptional axis of Bl₂ a marking
by the other exceptional divisor also kills it.
-/

public section
namespace AxiomaticGW.GKM.ExceptionalMarkedGraphSupport
open CurveConventionCertificate (Tables)
open EquivariantCoefficients (Coefficient)
open CurveReplay.OneBlowup renaming tables → f1
open CurveReplay.TwoBlowups renaming tables → bl2
open SurfaceFrames.OneBlowup renaming request → oneFrame
open SurfaceFrames.TwoBlowups renaming request → twoFrame

variable {X : SurfaceTarget} {n r : ℕ}

/-- Column in the GKM frame ordered by unit, hyperplane, exceptional divisors, point. -/
@[expose] def stateIndex : SurfaceBasisLabel X → Fin (X.blowups + 3)
  | .unit => ⟨0, by omega⟩
  | .hyperplane => ⟨1, by omega⟩
  | .exceptional i => ⟨i.val + 2, by omega⟩
  | .point => ⟨X.blowups + 2, by omega⟩

/-- Every F₁ column is the named state in the existing ordinary cohomology basis. -/
theorem oneBlowup_state (a : SurfaceBasisLabel .hirzebruchOne) :
    SurfaceFrames.OneBlowup.states (stateIndex a) = a.value := by
  cases a with
  | unit => exact SurfaceFrames.OneBlowup.states_unit
  | exceptional i => fin_cases i; rfl
  | _ => rfl

/-- Every Bl₂ column is the named state in the existing ordinary cohomology basis. -/
theorem twoBlowups_state (a : SurfaceBasisLabel .blowupTwo) :
    SurfaceFrames.TwoBlowups.states (stateIndex a) = a.value := by
  cases a with
  | unit => exact SurfaceFrames.TwoBlowups.states_unit
  | exceptional i => fin_cases i <;> rfl
  | _ => rfl

/-- A connected covered graph of the request's full class with an ordered marked-vertex map. -/
abbrev MarkedSupport (T : Tables X n r) (q : SurfaceQuery X) :=
  Σ g : FixedGraphSupport.AtDegree T q.beta, Fin q.insertions.length → Fin g.1

/-- The product of the native state restrictions at the ordered marked images. -/
@[expose] noncomputable def insertionFactor {T : Tables X n r} (q : SurfaceQuery X)
    (R : Fin n → Fin (X.blowups + 3) → Coefficient) (g : MarkedSupport T q) :
    Coefficient := ∏ j, R (g.1.2.2.val.image (g.2 j)) (stateIndex (q.insertions.get j).label)

/-- Every connected marked graph of this full request has zero insertion factor. -/
def Vanishes (T : Tables X n r) (R : Fin n → Fin (X.blowups + 3) → Coefficient)
    (q : SurfaceQuery X) : Prop := ∀ g : MarkedSupport T q, insertionFactor q R g = 0

/-- A vanishing insertion kills the whole finite sum in any module of class-valued weights. -/
theorem Vanishes.class_sum_zero {T : Tables X n r} {R} {q : SurfaceQuery X} (h : Vanishes T R q)
    {ι W : Type*} [Fintype ι] [AddCommMonoid W] [Module Coefficient W]
    (g : ι → MarkedSupport T q) (weight : ι → W) :
    ∑ i, insertionFactor q R (g i) • weight i = 0 := by
  apply Finset.sum_eq_zero
  exact fun i _ ↦ (h (g i)) ▸ zero_smul Coefficient (weight i)

private theorem zero_on_face {T : Tables X n r} {v e : ℕ} (G : FixedGraphSupport T v e)
    (k : Fin (X.blowups + 1)) (hk : G.degree k = 0) (hn : G.degree ≠ 0)
    (f : Fin n → Coefficient) (hf : ∀ t, (T.edges t).curve k = 0 →
      f (T.edges t).source = 0 ∧ f (T.edges t).target = 0) (w : Fin v) : f (G.image w) = 0 := by
  have he : Nonempty (Fin e) := by
    by_contra h
    apply hn
    funext c
    exact Finset.sum_eq_zero fun j _ ↦ (h ⟨j⟩).elim
  obtain ⟨j⟩ := he
  have same := G.constant_on_face k hk f fun t ht ↦ (hf t ht).1.trans (hf t ht).2.symm
  rw [same w (G.endpoint j 0)]
  have ends := hf _ (G.edge_coordinate_zero k hk j)
  rcases G.incident j with ⟨h, _⟩ | ⟨h, _⟩
  · exact (congrArg f h).trans ends.1
  · exact (congrArg f h).trans ends.2

private theorem of_label {T : Tables X n r} {R} {q : SurfaceQuery X} (a : SurfaceBasisLabel X)
    (hm : a ∈ q.insertions.map SurfaceInsertion.label)
    (hv : ∀ (g : FixedGraphSupport.AtDegree T q.beta) w,
      R (g.2.2.val.image w) (stateIndex a) = 0) : Vanishes T R q := by
  intro g
  obtain ⟨ins, hi, ha⟩ := List.mem_map.mp hm
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hi
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  change R _ (stateIndex (q.insertions.get j).label) = 0
  rw [hj, ha]
  exact hv g.1 (g.2 j)

/-- A point insertion kills every F₁ support of nonzero full class `(a,0)`. -/
theorem oneBlowup_point (q : SurfaceQuery .hirzebruchOne) (hn : q.beta ≠ 0)
    (hz : q.beta 1 = 0) (hm : .point ∈ q.insertions.map SurfaceInsertion.label) :
    Vanishes f1 oneFrame.restrictions q := by
  apply of_label .point hm
  rintro ⟨v, e, G, hd⟩ w
  apply zero_on_face G 1 (hd ▸ hz) (hd ▸ hn) (fun z ↦ oneFrame.restrictions z 3) _ w
  intro t
  fin_cases t <;> intro hf <;> first | exact ⟨rfl, rfl⟩ | cases hf

/-- A point insertion kills every Bl₂ support of nonzero full class `(a,b,0)`. -/
theorem twoBlowups_point (q : SurfaceQuery .blowupTwo) (hn : q.beta ≠ 0)
    (hz : q.beta 2 = 0) (hm : .point ∈ q.insertions.map SurfaceInsertion.label) :
    Vanishes bl2 twoFrame.restrictions q := by
  apply of_label .point hm
  rintro ⟨v, e, G, hd⟩ w
  apply zero_on_face G 2 (hd ▸ hz) (hd ▸ hn) (fun z ↦ twoFrame.restrictions z 4) _ w
  intro t
  fin_cases t <;> intro hf <;> first | exact ⟨rfl, rfl⟩ | cases hf

/-- On a positive pure Bl₂ axis, an insertion of the other exceptional divisor kills every graph. -/
theorem foreign_divisor (i j : Fin 2) (hij : i ≠ j) (d : ℕ+) (q : SurfaceQuery .blowupTwo)
    (hd : q.beta = (d : ℕ) • SurfaceTarget.blowupTwo.exceptionalCurve i)
    (hm : .exceptional j ∈ q.insertions.map SurfaceInsertion.label) :
    Vanishes bl2 twoFrame.restrictions q := by
  apply of_label (X := .blowupTwo) (.exceptional j) hm
  rintro ⟨v, e, G, hg⟩ w
  let z := (ExceptionalAxisTransport.ofSizeEquiv i d v e).symm ⟨G, hg.trans hd⟩
  have h := ExceptionalAxisTransport.vertex_image i d z w
  rw [show ExceptionalAxisTransport.ofSizeEquiv i d v e z = ⟨G, hg.trans hd⟩ from
    (ExceptionalAxisTransport.ofSizeEquiv i d v e).apply_symm_apply _] at h
  dsimp only at h ⊢
  rw [h]
  have hz (p : Fin 2) : let a := bl2.edges (ExceptionalAxisTransport.exceptionalEdge i)
      twoFrame.restrictions (![a.source, a.target] p)
        (stateIndex (X := .blowupTwo) (.exceptional j))
        = 0 := by
    dsimp only
    rw [ExceptionalAxisTransport.twoBlowups_restrictions i p]
    fin_cases i <;> fin_cases j <;> first | rfl | exact (hij rfl).elim
  split
  · exact hz 0
  · exact hz 1

end AxiomaticGW.GKM.ExceptionalMarkedGraphSupport

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoExceptionalGraphSupport

/-! # Connected fixed-graph support in the three surface edge tables

Positive covers of adjacent invariant curves realize every effective class on the plane
and the one-point blowup. On the two-point blowup only the open mixed exceptional face
is absent. These witnesses record incidence and full degree before weighting a fixed locus.
-/

@[expose] public section
namespace AxiomaticGW.GKM.SurfaceFixedGraphSupport
open CurveConventionCertificate
open FixedGraphSupport (AtDegree)

variable {X : SurfaceTarget} {n r m : ℕ}

/-- A directed walk in the pinned edge table, with an independent positive cover on each step. -/
def coveredPath (T : Tables X n r) (p : Fin (m + 1) → Fin n) (t : Fin m → Fin r)
    (d : Fin m → ℕ+) (h : ∀ j, p j.castSucc = (T.edges (t j)).source ∧
      p j.succ = (T.edges (t j)).target) : FixedGraphSupport T (m + 1) m where
  endpoint j := ![j.castSucc, j.succ]
  image := p
  edgeIndex := t
  cover := d
  incident j := Or.inl (h j)
  connected := by
    let ends (j : Fin m) := ![j.castSucc, j.succ]
    have reach (i : Fin (m + 1)) : (StableGraphCode.incidenceGraph ends).Reachable 0 i := by
      induction i using Fin.induction with
      | zero => exact .refl _
      | succ j ih =>
        apply ih.trans
        exact (StableGraphCode.reachable_iff ends _ _).mpr (.single ⟨j, Or.inl ⟨rfl, rfl⟩⟩)
    exact ⟨fun i j ↦ (reach i).symm.trans (reach j)⟩

private theorem pathSupport (T : Tables X n r) {β : X.Curve} (p : Fin (m + 1) → Fin n)
    (t : Fin m → Fin r) (d : Fin m → ℕ+) (h : ∀ j, p j.castSucc = (T.edges (t j)).source ∧
      p j.succ = (T.edges (t j)).target)
    (hd : ∀ k, ∑ j, (d j : ℕ) * (T.edges (t j)).curve k = β k) : Nonempty (AtDegree T β) :=
  ⟨_, _, coveredPath T p t d h, funext hd⟩

private def positive (a : ℕ) : ℕ+ := ⟨a + 1, Nat.succ_pos a⟩

/-- A cover of the line from 0 to 1 realizes any positive plane degree.
The origin uses the contracted vertex. -/
theorem plane (β : SurfaceTarget.plane.Curve) : Nonempty (AtDegree CurveReplay.Plane.tables β) := by
  have h : β = ![β 0] := by funext k; fin_cases k; rfl
  rw [h]
  cases β 0 with
  | zero =>
    refine ⟨1, 0, FixedGraphSupport.contractedPoint _ 0, ?_⟩
    rw [FixedGraphSupport.degree_contractedPoint]
    decide +kernel
  | succ a =>
    apply pathSupport CurveReplay.Plane.tables ![0, 1] ![0] ![positive a] (by decide +kernel)
    intro k
    fin_cases k
    rw [Fin.sum_univ_one]
    exact Nat.mul_one _

/-- A fiber (edge 0) meets the exceptional curve (edge 2) at fixed point 1.
Together with their individual covers this realizes the entire `(E,F)` cone. -/
theorem oneBlowup (β : SurfaceTarget.hirzebruchOne.Curve) :
    Nonempty (AtDegree CurveReplay.OneBlowup.tables β) := by
  have h : β = ![β 0, β 1] := by funext k; fin_cases k <;> rfl
  rw [h]
  cases β 0 with
  | zero =>
    cases β 1 with
    | zero =>
      refine ⟨1, 0, FixedGraphSupport.contractedPoint _ 0, ?_⟩
      rw [FixedGraphSupport.degree_contractedPoint]
      decide +kernel
    | succ b =>
      apply pathSupport CurveReplay.OneBlowup.tables ![0, 1] ![0] ![positive b] (by decide +kernel)
      intro k
      fin_cases k <;> simp [CurveReplay.OneBlowup.tables, positive]
  | succ a =>
    cases β 1 with
    | zero =>
      apply pathSupport CurveReplay.OneBlowup.tables ![1, 3] ![2] ![positive a] (by decide +kernel)
      intro k
      fin_cases k <;> simp [CurveReplay.OneBlowup.tables, positive]
    | succ b =>
      apply pathSupport CurveReplay.OneBlowup.tables ![0, 1, 3] ![0, 2]
        ![positive b, positive a] (by decide +kernel)
      intro k
      fin_cases k <;> simp [Fin.sum_univ_two, CurveReplay.OneBlowup.tables, positive]

/-- A positive cover of `L` joins the two exceptional branches. Zero multiplicity
on an exceptional branch omits that edge from the source path. -/
theorem throughLine (a b c : ℕ) : Nonempty (AtDegree CurveReplay.TwoBlowups.tables
    ![a, b, c + 1]) := by
  cases a with
  | zero =>
    cases b with
    | zero =>
      apply pathSupport CurveReplay.TwoBlowups.tables ![2, 3] ![3] ![positive c] (by decide +kernel)
      intro k
      fin_cases k <;> simp [CurveReplay.TwoBlowups.tables, positive]
    | succ b =>
      apply pathSupport CurveReplay.TwoBlowups.tables ![2, 3, 4] ![3, 4]
        ![positive c, positive b] (by decide +kernel)
      intro k
      fin_cases k <;> simp [Fin.sum_univ_two, CurveReplay.TwoBlowups.tables, positive]
  | succ a =>
    cases b with
    | zero =>
      apply pathSupport CurveReplay.TwoBlowups.tables ![1, 2, 3] ![2, 3]
        ![positive a, positive c] (by decide +kernel)
      intro k
      fin_cases k <;> simp [Fin.sum_univ_two, CurveReplay.TwoBlowups.tables, positive,
        Matrix.cons_val_two]
    | succ b =>
      apply pathSupport CurveReplay.TwoBlowups.tables ![1, 2, 3, 4] ![2, 3, 4]
        ![positive a, positive c, positive b] (by decide +kernel)
      intro k
      fin_cases k <;> simp [Fin.sum_univ_three, CurveReplay.TwoBlowups.tables, positive,
        Matrix.cons_val_two]

/-- The exact support in full `(E₁,E₂,L)` coordinates for arbitrary effective classes. -/
theorem twoBlowups_iff (β : SurfaceTarget.blowupTwo.Curve) :
    Nonempty (AtDegree CurveReplay.TwoBlowups.tables β) ↔ 0 < β 2 ∨ β 0 = 0 ∨ β 1 = 0 := by
  have h : β = ![β 0, β 1, β 2] := by funext k; fin_cases k <;> rfl
  conv_lhs => rw [h]
  cases β 2 with
  | zero =>
    simpa only [lt_self_iff_false, false_or] using
      BlowupTwoExceptionalGraphSupport.exceptional_face_support_iff (β 0) (β 1)
  | succ c => exact ⟨fun _ ↦ Or.inl (Nat.succ_pos _), fun _ ↦ throughLine (β 0) (β 1) c⟩

end AxiomaticGW.GKM.SurfaceFixedGraphSupport

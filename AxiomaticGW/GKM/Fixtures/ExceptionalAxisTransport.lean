/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.SurfaceFixedGraphSupport
public import AxiomaticGW.Surfaces.Queries

/-! # Transport of positive exceptional fixed-graph supports

The exceptional curve of F₁ and either exceptional curve of the two-point blowup have
the same covered incidence graphs after relabeling their two endpoints. Their local
tangent and normal characters agree under an integral change of character coordinates.
-/

public section
namespace AxiomaticGW.GKM.ExceptionalAxisTransport
open CurveConventionCertificate
open FixedGraphSupport (AtDegree)

variable {X Y : SurfaceTarget} {n r n' r' v e : ℕ}

/-- Connected supports with all sheets over one fixed target edge and total multiplicity d. -/
abbrev OverEdge (T : Tables X n r) (t : Fin r) (d : ℕ+) (v e : ℕ) :=
  {G : FixedGraphSupport T v e // (∀ j, G.edgeIndex j = t) ∧ ∑ j, (G.cover j : ℕ) = (d : ℕ)}

private theorem degree_pure {T : Tables X n r} (G : FixedGraphSupport T v e) (t : Fin r)
    (h : ∀ j, G.edgeIndex j = t) : G.degree = (∑ j, (G.cover j : ℕ)) • (T.edges t).curve := by
  funext k
  simp only [FixedGraphSupport.degree, h, Pi.smul_apply, nsmul_eq_mul, Nat.cast_id, Finset.sum_mul]

/-- A coordinate axis containing exactly one primitive target edge supports only its covers. -/
theorem degree_on_coordinate_iff (T : Tables X n r) (t : Fin r) (k₀ : Fin (X.blowups + 1))
    (hc : (T.edges t).curve = Pi.single k₀ 1)
    (unique : ∀ j, (∀ k, k ≠ k₀ → (T.edges j).curve k = 0) → j = t)
    (d : ℕ+) (G : FixedGraphSupport T v e) :
    G.degree = (d : ℕ) • Pi.single k₀ 1 ↔
      (∀ j, G.edgeIndex j = t) ∧ ∑ j, (G.cover j : ℕ) = (d : ℕ) := by
  constructor
  · intro hg
    have ht (j : Fin e) : G.edgeIndex j = t := by
      apply unique
      intro k hk
      apply G.edge_coordinate_zero k _ j
      simp only [hg, Pi.smul_apply, Pi.single_eq_of_ne hk, smul_zero]
    refine ⟨ht, ?_⟩
    have h := congrFun ((degree_pure G t ht).symm.trans hg) k₀
    simpa only [hc, Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, Nat.cast_id, Nat.mul_one]
      using h
  · rintro ⟨ht, hs⟩
    rw [degree_pure G t ht, hs, hc]

/-- Every vertex over a single covered edge lies at one of its two fixed endpoints. -/
theorem OverEdge.image_eq_endpoint {T : Tables X n r} {t : Fin r} {d : ℕ+} (g : OverEdge T t d v e)
    (x : Fin v) : g.val.image x = (T.edges t).source ∨ g.val.image x = (T.edges t).target := by
  have existsEdge : Nonempty (Fin e) := by
    by_contra hn
    have hs : ∑ j, (g.val.cover j : ℕ) = 0 := Finset.sum_eq_zero fun j _ ↦ (hn ⟨j⟩).elim
    exact d.ne_zero (g.property.2.symm.trans hs)
  obtain ⟨j⟩ := existsEdge
  have ends (a : Fin e) := g.val.incident a
  simp only [g.property.1] at ends
  have path := (StableGraphCode.reachable_iff _ _ _).mp
    (g.val.connected.preconnected (g.val.endpoint j 0) x)
  induction path with
  | refl => exact (ends j).elim (fun h ↦ Or.inl h.1) (fun h ↦ Or.inr h.1)
  | tail _ step _ =>
    rcases step with ⟨a, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩
    · exact (ends a).elim (fun h ↦ Or.inr h.2) (fun h ↦ Or.inl h.2)
    · exact (ends a).elim (fun h ↦ Or.inl h.1) (fun h ↦ Or.inr h.1)

private def relabel {T : Tables X n r} {t : Fin r} (hneq : (T.edges t).target ≠ (T.edges t).source)
    (U : Tables Y n' r') (u : Fin r') {d : ℕ+} (g : OverEdge T t d v e) : OverEdge U u d v e :=
  ⟨{ endpoint := g.val.endpoint
     image := fun x ↦ if g.val.image x = (T.edges t).source
       then (U.edges u).source else (U.edges u).target
     edgeIndex := fun _ ↦ u
     cover := g.val.cover
     connected := g.val.connected
     incident := by
       intro a
       have h := g.val.incident a
       rw [g.property.1 a] at h
       rcases h with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
       · exact Or.inl ⟨if_pos h₀, if_neg (h₁ ▸ hneq)⟩
       · exact Or.inr ⟨if_neg (h₀ ▸ hneq), if_pos h₁⟩ },
    fun _ ↦ rfl, g.property.2⟩

private theorem graph_ext {T : Tables X n r} {G H : FixedGraphSupport T v e}
    (hp : G.endpoint = H.endpoint) (hi : G.image = H.image) (he : G.edgeIndex = H.edgeIndex)
    (hc : G.cover = H.cover) : G = H := by
  cases G; cases H
  exact FixedGraphSupport.mk.injEq .. |>.mpr ⟨hp, hi, he, hc⟩

private theorem relabel_back {T : Tables X n r} {t : Fin r}
    (ht : (T.edges t).target ≠ (T.edges t).source)
    {U : Tables Y n' r'} {u : Fin r'} (hu : (U.edges u).target ≠ (U.edges u).source)
    {d : ℕ+} (g : OverEdge T t d v e) : relabel hu T t (relabel ht U u g) = g := by
  apply Subtype.ext
  have himage : (relabel hu T t (relabel ht U u g)).val.image = g.val.image := by
    funext x
    rcases OverEdge.image_eq_endpoint g x with hs | he
    · simp only [relabel, hs, if_pos]
    · simp only [relabel, he, if_neg ht, if_neg hu]
  have hedge : (relabel hu T t (relabel ht U u g)).val.edgeIndex = g.val.edgeIndex :=
    funext fun j ↦ (g.property.1 j).symm
  exact graph_ext rfl himage hedge rfl

/-- Relabel the two distinct fixed endpoints, preserving the entire source graph and its covers. -/
def overEdgeEquiv (T : Tables X n r) (t : Fin r) (ht : (T.edges t).target ≠ (T.edges t).source)
    (U : Tables Y n' r') (u : Fin r') (hu : (U.edges u).target ≠ (U.edges u).source)
    (d : ℕ+) (v e : ℕ) : OverEdge T t d v e ≃ OverEdge U u d v e where
  toFun := relabel ht U u
  invFun := relabel hu T t
  left_inv := relabel_back ht hu
  right_inv := relabel_back hu ht

/-- Relabeling preserves incidences and multiplicities and places each vertex at its
corresponding endpoint in the orientation of the two recorded edges. -/
theorem overEdgeEquiv_data (T : Tables X n r) (t : Fin r)
    (ht : (T.edges t).target ≠ (T.edges t).source)
    (U : Tables Y n' r') (u : Fin r') (hu : (U.edges u).target ≠ (U.edges u).source)
    (d : ℕ+) {v e : ℕ} (g : OverEdge T t d v e) :
    let h := (overEdgeEquiv T t ht U u hu d v e g).val
    h.endpoint = g.val.endpoint ∧ h.cover = g.val.cover ∧
    ∀ w, h.image w = if g.val.image w = (T.edges t).source then (U.edges u).source
      else (U.edges u).target := ⟨rfl, rfl, fun _ ↦ rfl⟩

open CurveReplay.OneBlowup renaming tables → f1
open CurveReplay.TwoBlowups renaming tables → bl2

/-- The two exceptional edge indices in the two-point blowup's pinned table. -/
@[expose] def exceptionalEdge : Fin 2 → Fin 5 := ![2, 4]

private theorem unique_f1 : ∀ j, (∀ k, k ≠ (0 : Fin 1).castSucc → (f1.edges j).curve k = 0) →
    j = 2 := by decide +kernel

private theorem unique_bl2 : ∀ (i : Fin 2) j, (∀ k, k ≠ i.castSucc → (bl2.edges j).curve k = 0) →
    j = exceptionalEdge i := by decide +kernel

/-- Positive degrees on the F₁ exceptional axis select the recorded exceptional edge. -/
theorem oneBlowup_class_iff (d : ℕ+) (G : FixedGraphSupport f1 v e) :
    G.degree = (d : ℕ) • SurfaceTarget.hirzebruchOne.exceptionalCurve 0 ↔
      (∀ j, G.edgeIndex j = 2) ∧ ∑ j, (G.cover j : ℕ) = (d : ℕ) :=
  degree_on_coordinate_iff f1 2 0 (by decide +kernel) unique_f1 d G

/-- The selected exceptional edge is the sole possible edge on its pure axis, and the sum
of its covering multiplicities is the full exceptional coefficient. -/
theorem twoBlowups_class_iff (i : Fin 2) (d : ℕ+) (G : FixedGraphSupport bl2 v e) :
    G.degree = (d : ℕ) • SurfaceTarget.blowupTwo.exceptionalCurve i ↔
      (∀ j, G.edgeIndex j = exceptionalEdge i) ∧ ∑ j, (G.cover j : ℕ) = (d : ℕ) :=
  degree_on_coordinate_iff bl2 _ i.castSucc (by fin_cases i <;> decide +kernel) (unique_bl2 i) d G

/-- A fixed-size equivalence of actual supports at the two specified full classes. -/
def ofSizeEquiv (i : Fin 2) (d : ℕ+) (v e : ℕ) :
    {G : FixedGraphSupport f1 v e //
      G.degree = (d : ℕ) • SurfaceTarget.hirzebruchOne.exceptionalCurve 0} ≃
    {G : FixedGraphSupport bl2 v e //
      G.degree = (d : ℕ) • SurfaceTarget.blowupTwo.exceptionalCurve i} :=
  let source := Equiv.subtypeEquivRight (oneBlowup_class_iff d)
  let target := Equiv.subtypeEquivRight (twoBlowups_class_iff i d)
  (source.trans (overEdgeEquiv f1 2 (by decide +kernel) bl2 (exceptionalEdge i)
    (by fin_cases i <;> decide +kernel) d v e)).trans target.symm

/-- Every vertex of a positive pure F₁ exceptional support maps to one of its two endpoints. -/
theorem oneBlowup_vertices (d : ℕ+) {v e : ℕ} (G : FixedGraphSupport f1 v e)
    (hd : G.degree = (d : ℕ) • SurfaceTarget.hirzebruchOne.exceptionalCurve 0) (w : Fin v) :
    G.image w = (f1.edges 2).source ∨ G.image w = (f1.edges 2).target :=
  OverEdge.image_eq_endpoint (d := d) ⟨G, (oneBlowup_class_iff d G).mp hd⟩ w

/-- The correspondence preserves every source incidence and every individual covering degree. -/
theorem preserves_covers (i : Fin 2) (d : ℕ+) {v e : ℕ} (g : {G : FixedGraphSupport f1 v e //
    G.degree = (d : ℕ) • SurfaceTarget.hirzebruchOne.exceptionalCurve 0}) :
    (ofSizeEquiv i d v e g).val.endpoint = g.val.endpoint ∧
    (ofSizeEquiv i d v e g).val.cover = g.val.cover ∧
    ∀ j, (ofSizeEquiv i d v e g).val.edgeIndex j = exceptionalEdge i := ⟨rfl, rfl, fun _ ↦ rfl⟩

/-- Vertex labels are transported in the orientation of the two pinned exceptional edges. -/
theorem vertex_image (i : Fin 2) (d : ℕ+) {v e : ℕ} (g : {G : FixedGraphSupport f1 v e //
    G.degree = (d : ℕ) • SurfaceTarget.hirzebruchOne.exceptionalCurve 0}) (w : Fin v) :
    (ofSizeEquiv i d v e g).val.image w = if g.val.image w = (f1.edges 2).source
      then (bl2.edges (exceptionalEdge i)).source else (bl2.edges (exceptionalEdge i)).target := by
  split <;> rename_i h
  · exact if_pos h
  · exact if_neg h

/-- Relabeling the two exceptional endpoints gives a bijection on connected supports for every
positive degree, including graphs with parallel edges or arbitrarily many components over E. -/
def supportEquiv (i : Fin 2) (d : ℕ+) :
    AtDegree f1 ((d : ℕ) • SurfaceTarget.hirzebruchOne.exceptionalCurve 0) ≃
    AtDegree bl2 ((d : ℕ) • SurfaceTarget.blowupTwo.exceptionalCurve i) :=
  Equiv.sigmaCongrRight fun v ↦ Equiv.sigmaCongrRight fun e ↦ ofSizeEquiv i d v e

/-- The integral character-coordinate change from the F₁ exceptional edge to Bl₂'s second one. -/
@[expose] def secondCharacterChange : (Fin 2 → ℤ) ≃+ (Fin 2 → ℤ) where
  toFun w := ![-w 0 - w 1, w 0]
  invFun w := ![w 1, -w 0 - w 1]
  left_inv w := by funext k; fin_cases k <;> dsimp; ring
  right_inv w := by funext k; fin_cases k <;> dsimp; ring
  map_add' a b := by funext k; fin_cases k <;> dsimp; ring

/-- The first exceptional edge retains the original characters. The second changes basis. -/
@[expose] def characterChange (i : Fin 2) : (Fin 2 → ℤ) ≃+ (Fin 2 → ℤ) :=
  ![AddEquiv.refl _, secondCharacterChange] i

/-- A comparison of the oriented tangent, the two adjacent normal characters, the signed
normal degree, and both ordered tangent frames. At the target endpoint the two branches swap. -/
theorem local_weights : ∀ i : Fin 2, let a := f1.edges 2; let b := bl2.edges (exceptionalEdge i)
    characterChange i a.weight = b.weight ∧ a.normalDegree = -1 ∧ b.normalDegree = -1 ∧
    characterChange i (edgeWeight f1 a.source a.normalSource) =
      edgeWeight bl2 b.source b.normalSource ∧
    characterChange i (edgeWeight f1 a.target a.normalTarget) =
      edgeWeight bl2 b.target b.normalTarget ∧
    ∀ j : Fin 2, characterChange i (f1.tangent a.source j) = bl2.tangent b.source j ∧
      characterChange i (f1.tangent a.target j) = bl2.tangent b.target j.rev := by decide +kernel

open EquivariantCoefficients (Coefficient x y)
open SurfaceFrames.OneBlowup renaming request → oneFrame
open SurfaceFrames.TwoBlowups renaming request → twoFrame

/-- F₁'s two normal characters in source, target order on its exceptional edge. -/
def normalFrame : Fin 2 → Fin 2 → ℤ := ![![0, 1], ![1, 0]]

/-- The normal frame comes from the actual adjacent edges at both endpoints. -/
theorem normalFrame_eq : let a := f1.edges 2
    normalFrame = ![edgeWeight f1 a.source a.normalSource,
      edgeWeight f1 a.target a.normalTarget] := by
  decide +kernel

private theorem one_normal (p : Fin 2) : character (normalFrame p) = ![y, x] p := by
  fin_cases p
  · change ((0 : ℤ) : Coefficient) * x + ((1 : ℤ) : Coefficient) * y = y
    norm_num
  · change ((1 : ℤ) : Coefficient) * x + ((0 : ℤ) : Coefficient) * y = x
    norm_num

private theorem two_normal (i p : Fin 2) : character (characterChange i (normalFrame p)) =
    ![![y, x], ![-x, y - x]] i p := by
  fin_cases i
  · exact one_normal p
  · fin_cases p
    · change ((-1 : ℤ) : Coefficient) * x + ((0 : ℤ) : Coefficient) * y = -x
      norm_num
    · change ((-1 : ℤ) : Coefficient) * x + ((1 : ℤ) : Coefficient) * y = y - x
      push_cast
      ring

/-- Restriction rows of the held F₁ basis along E, including its chosen hyperplane lift. -/
theorem oneBlowup_restrictions (p : Fin 2) : let a := f1.edges 2
    oneFrame.restrictions (![a.source, a.target] p) = ![1, 0, character (normalFrame p), 0] := by
  dsimp only
  rw [one_normal]
  fin_cases p <;> funext j <;> fin_cases j <;> rfl

/-- Restriction rows of the held Bl₂ basis along each exceptional edge. On E₁ the
hyperplane lift contributes the constant character x at both endpoints. -/
theorem twoBlowups_restrictions (i p : Fin 2) : let a := bl2.edges (exceptionalEdge i)
    let normal := character (characterChange i (normalFrame p))
    twoFrame.restrictions (![a.source, a.target] p) =
      ![1, if i = 0 then x else 0, if i = 0 then normal else 0,
        if i = 1 then normal else 0, 0] := by
  dsimp only
  rw [two_normal]
  fin_cases i <;> fin_cases p <;> funext j <;> fin_cases j <;> rfl

end AxiomaticGW.GKM.ExceptionalAxisTransport

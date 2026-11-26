/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.ExceptionalCharacterField
public import AxiomaticGW.GKM.Fixtures.ExceptionalMarkedGraphSupport

/-! # Transport of the complete marked insertion product over exceptional graph supports

On E₁ the Bl₂ hyperplane lift adds `x` times the unit. On either axis the other exceptional
divisor has zero restriction. Both statements apply at every marking, with no bound on the
cover degree, graph size, genus, or cotangent powers.
-/

public section
namespace AxiomaticGW.GKM.ExceptionalMarkedTransport
open EquivariantCoefficients (Coefficient x)
open ExceptionalAxisTransport ExceptionalCharacterField ExceptionalMarkedGraphSupport
open CurveConventionCertificate (Tables)
open CurveReplay.OneBlowup renaming tables → f1
open CurveReplay.TwoBlowups renaming tables → bl2
open SurfaceFrames.OneBlowup renaming request → oneFrame
open SurfaceFrames.TwoBlowups renaming request → twoFrame

/-- Fixed effective class and arity of a marked support, before basis labels are evaluated. -/
abbrev MarkedAt {X : SurfaceTarget} {v e : ℕ} (T : Tables X v e) (β : X.Curve) (n : ℕ) :=
  Σ G : FixedGraphSupport.AtDegree T β, Fin n → Fin G.1

/-- Transport every ordered marked-vertex assignment along the actual support bijection. -/
def markedEquiv (i : Fin 2) (d : ℕ+) (n : ℕ) :
    MarkedAt f1 ((d : ℕ) • SurfaceTarget.hirzebruchOne.exceptionalCurve 0) n ≃
    MarkedAt bl2 ((d : ℕ) • SurfaceTarget.blowupTwo.exceptionalCurve i) n where
  toFun | ⟨⟨v, e, G⟩, m⟩ => ⟨⟨v, e, ofSizeEquiv i d v e G⟩, m⟩
  invFun | ⟨⟨v, e, G⟩, m⟩ => ⟨⟨v, e, (ofSizeEquiv i d v e).symm G⟩, m⟩
  left_inv := by
    rintro ⟨⟨v, e, G⟩, m⟩
    dsimp only
    rw [(ofSizeEquiv i d v e).symm_apply_apply]
  right_inv := by
    rintro ⟨⟨v, e, G⟩, m⟩
    dsimp only
    rw [(ofSizeEquiv i d v e).apply_symm_apply]

/-- Write each target basis restriction in F₁ coordinates before the field change. -/
@[expose] noncomputable def pullRestriction (i : Fin 2)
    (r : SurfaceBasisLabel .hirzebruchOne → Coefficient) :
    SurfaceBasisLabel .blowupTwo → Coefficient
  | .unit => r .unit
  | .hyperplane => r .hyperplane + (if i = 0 then x else 0) * r .unit
  | .exceptional j => if i = j then r (.exceptional 0) else 0
  | .point => r .point

private theorem at_end (i p : Fin 2) (a : SurfaceBasisLabel .blowupTwo) :
    let f := f1.edges 2; let b := bl2.edges (exceptionalEdge i)
    twoFrame.restrictions (![b.source, b.target] p) (stateIndex a) =
      sector i (pullRestriction i (fun s ↦ oneFrame.restrictions (![f.source, f.target] p)
        (stateIndex s)) a) := by
  dsimp only
  rw [insertion_transport i p]
  have hu : oneFrame.restrictions (![(f1.edges 2).source, (f1.edges 2).target] p)
      (stateIndex (X := .hirzebruchOne) .unit) = 1 := by rw [oneBlowup_restrictions p]; rfl
  cases a with
  | unit | point => rfl
  | hyperplane =>
    fin_cases i
    · change _ + x = _ + x * _
      exact congrArg (_ + ·) ((mul_one x).symm.trans (congrArg (x * ·) hu.symm))
    · change sector 1 (oneFrame.restrictions _ 1) + 0 =
        sector 1 (oneFrame.restrictions _ 1 + 0 * oneFrame.restrictions _ 0)
      rw [zero_mul, add_zero, add_zero]
  | exceptional j =>
    fin_cases i <;> fin_cases j <;> first | rfl | exact (map_zero _).symm

/-- The transported native state restriction at any marked vertex of a positive covered graph. -/
theorem vertex_restriction (i : Fin 2) (d : ℕ+) {v e : ℕ} (g : {G : FixedGraphSupport f1 v e //
    G.degree = (d : ℕ) • SurfaceTarget.hirzebruchOne.exceptionalCurve 0}) (w : Fin v)
    (a : SurfaceBasisLabel .blowupTwo) :
    twoFrame.restrictions ((ofSizeEquiv i d v e g).val.image w) (stateIndex a) =
      sector i (pullRestriction i
        (fun s ↦ oneFrame.restrictions (g.val.image w) (stateIndex s)) a) := by
  rw [vertex_image]
  rcases oneBlowup_vertices d g.val g.property w with hs | ht
  · rw [if_pos hs, hs]
    exact at_end i 0 a
  · have hne : g.val.image w ≠ (f1.edges 2).source := ht ▸ (by decide +kernel)
    rw [if_neg hne, ht]
    exact at_end i 1 a

/-- Product of the corrected F₁ restrictions for all ordered Bl₂ markings on a source graph. -/
@[expose] noncomputable def sourceProduct (i : Fin 2) (d : ℕ+)
    (a : List (SurfaceInsertion .blowupTwo))
    (g : MarkedAt f1 ((d : ℕ) • SurfaceTarget.hirzebruchOne.exceptionalCurve 0) a.length) :
    Coefficient := ∏ j, pullRestriction i (fun s ↦ oneFrame.restrictions
      (g.1.2.2.val.image (g.2 j)) (stateIndex s)) (a.get j).label

/-- An original Bl₂ request in its specified positive full exceptional class. -/
@[expose] def targetQuery (i : Fin 2) (d : ℕ+) (genus : ℕ)
    (a : List (SurfaceInsertion .blowupTwo)) : SurfaceQuery .blowupTwo :=
  ⟨genus, (d : ℕ) • SurfaceTarget.blowupTwo.exceptionalCurve i, a⟩

/-- The complete native insertion product transports at every genus and positive cover degree. -/
theorem product_transport (i : Fin 2) (d : ℕ+) (genus : ℕ) (a : List (SurfaceInsertion .blowupTwo))
    (g : MarkedAt f1 ((d : ℕ) • SurfaceTarget.hirzebruchOne.exceptionalCurve 0) a.length) :
    insertionFactor (targetQuery i d genus a) twoFrame.restrictions (markedEquiv i d a.length g) =
      sector i (sourceProduct i d a g) := by
  obtain ⟨⟨v, e, G⟩, m⟩ := g
  rw [sourceProduct, map_prod]
  apply Finset.prod_congr rfl
  exact fun j _ ↦ vertex_restriction i d G (m j) (a.get j).label

/-- A reindexed finite class sum transports once the remaining, insertion-free graph weights
correspond under an explicit semilinear map. The marked factors are proved to correspond. -/
theorem class_sum_transport (i : Fin 2) (d : ℕ+) (genus : ℕ)
    (a : List (SurfaceInsertion .blowupTwo)) {ι κ M N : Type*} [Fintype ι] [Fintype κ]
    [AddCommMonoid M] [AddCommMonoid N] [Module Coefficient M] [Module Coefficient N]
    (F : M →ₛₗ[(sector i).toRingHom] N) (index : ι ≃ κ)
    (g : ι → MarkedAt f1 ((d : ℕ) • SurfaceTarget.hirzebruchOne.exceptionalCurve 0) a.length)
    (g' : κ → MarkedSupport bl2 (targetQuery i d genus a))
    (w : ι → M) (w' : κ → N) (hg : ∀ j, g' (index j) = markedEquiv i d a.length (g j))
    (hw : ∀ j, w' (index j) = F (w j)) :
    ∑ k, insertionFactor (targetQuery i d genus a) twoFrame.restrictions (g' k) • w' k =
      F (∑ j, sourceProduct i d a (g j) • w j) := by
  rw [← index.sum_comp, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hg, hw, product_transport, map_smulₛₗ]
  rfl

end AxiomaticGW.GKM.ExceptionalMarkedTransport

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.ExceptionalGenusTwoVertexTransport
public import AxiomaticGW.GKM.Fixtures.ExceptionalGenusTwoVertexValues

/-! # A genus-two double exceptional fixed locus with a bivalent vertex

Two unramified edges join the marked genus-two center to two indistinguishable
unmarked rational ends. The own exceptional divisor restricts to the transverse
character at the center. Both outgoing flags have its tangent character.
-/

@[expose] public section
namespace AxiomaticGW.GKM.ExceptionalDoubleCoverChain
open GenusTwoLocalizationVertex GenusTwoVertexHodgeReduction
open ExceptionalGenusTwoVertexValues (seed)
noncomputable section

/-- Each edge is oriented from its own rational leaf to the marked central vertex. -/
def ends : Fin 2 → Fin 2 → Fin 3 := ![![0, 1], ![2, 1]]

/-- The actual support has two one-sheeted covers of the same target edge. -/
def support {X : SurfaceTarget} {n r : ℕ} (t : CurveConventionCertificate.Tables X n r)
    (k : Fin r) : FixedGraphSupport t 3 2 where
  endpoint := ends
  image := ![(t.edges k).source, (t.edges k).target, (t.edges k).source]
  edgeIndex _ := k
  cover _ := 1
  incident j := by fin_cases j <;> exact Or.inl ⟨rfl, rfl⟩
  connected := by
    have h (p : Fin 3) : (StableGraphCode.incidenceGraph ends).Reachable 1 p := by
      apply (StableGraphCode.reachable_iff ends _ _).mpr
      fin_cases p
      · exact .single ⟨0, Or.inr ⟨rfl, rfl⟩⟩
      · exact .refl
      · exact .single ⟨1, Or.inr ⟨rfl, rfl⟩⟩
    exact ⟨fun i j ↦ (h i).symm.trans (h j)⟩

/-- Both source covers contribute to the full effective coordinates on each exceptional axis. -/
theorem classes :
    (support CurveReplay.OneBlowup.tables 2).degree = ![2, 0] ∧
    (support CurveReplay.TwoBlowups.tables 2).degree = ![2, 0, 0] ∧
    (support CurveReplay.TwoBlowups.tables 4).degree = ![0, 2, 0] := by decide +kernel

/-- Simultaneous vertex and edge permutations preserving every incidence and the marked center.
The target images and vertex genera distinguish the center from either rational leaf. -/
def symmetries : Finset ((Fin 3 → Fin 3) × (Fin 2 → Fin 2)) :=
  Finset.univ.filter fun p ↦ Function.Bijective p.1 ∧ Function.Bijective p.2 ∧ p.1 1 = 1 ∧
    ∀ e s, p.1 (ends e s) = ends (p.2 e) s

/-- Only the identity and the simultaneous exchange of the two leaves and edges survive. -/
theorem leaf_exchange : symmetries = {(id, id), (![2, 1, 0], ![1, 0])} ∧
    symmetries.card = 2 := by decide +kernel

/-- The signed Hodge integrals grouped by the transverse λ exponent. -/
def column (m : List ℕ) (j : Fin 3) : ℚ :=
  ∑ i : Fin 3, ∑ k ∈ profiles 2 m i j, (-1 : ℚ)^(i.val + j.val) *
    evaluate seed (min i j) (max i j) min_le_max (m ++ List.ofFn k)

/-- Values of the three columns from the explicit eight rational seeds. -/
theorem columns : (∀ j, column [3] j = ![11/720, -103/2880, 3/320] j) ∧
    (∀ j, column [1, 2] j = ![7/96, -7/32, 19/144] j) := by decide +kernel

variable {K : Type*} [Field K] [CharZero K]

/-- The marked genus-two center with two indistinguishable flag weights. -/
def center (m : List ℕ) (w t : K) : K := reduced seed m w t (fun _ : Fin 2 ↦ w)

/-- After summing over the two outgoing flag powers, only three transverse columns remain. -/
theorem collected (m : List ℕ) (w t : K) (hw : w ≠ 0) : center m w t =
    ∑ j : Fin 3, (column m j : K) * (t^((1 : ℤ)-j.val) *
      w^((m.sum : ℤ) + j.val - (6 + m.length))) := by
  unfold center reduced source
  apply Finset.sum_congr rfl
  intro j _
  simp only [column, Rat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  have hd := (mem_profiles m i j k).mp hk
  simp only [Fin.sum_univ_two] at hd
  have he : ((1 : ℤ)-i.val) + (-(k 0 : ℤ)-1) + (-(k 1 : ℤ)-1) =
      (m.sum : ℤ) + j.val - (6 + m.length) := by omega
  rw [Fin.prod_univ_two, mul_comm (w^((1 : ℤ)-i.val)) (t^_), mul_assoc, ← mul_assoc (w^_),
    ← zpow_add₀ hw, ← zpow_add₀ hw, he]

/-- Complete rational function of the bivalent genus-two vertex before tangent normalization. -/
theorem center_eq (w t : K) (hw : w ≠ 0) (ht : t ≠ 0) :
    center [3] w t = 11*t/(720*w^4) - 103/(2880*w^3) + 3/(320*t*w^2) ∧
    center [1, 2] w t = 7*t/(96*w^5) - 7/(32*w^4) + 19/(144*t*w^3) := by
  constructor <;> rw [collected _ w t hw, Fin.sum_univ_three] <;>
    simp only [columns.1, columns.2, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] <;>
    norm_num <;> field_simp <;> ring

/-- For this single fixed locus the two unmarked rational tails cancel their Euler factors.
Dividing by the exchange of the two identical leaves gives the factor one half. -/
theorem contribution (m : List ℕ) (w t : K) (hw : w ≠ 0) (ht : t + w ≠ 0) :
    (-1 / w^2)^2 * (((-w)*(t+w))^2 * (w*t)^2) * t^m.length *
      (((-w)/((-w)*(t+w)))^2 * center m w t) / symmetries.card =
      t^(2+m.length) * center m w t / 2 := by
  rw [leaf_exchange.2, Nat.cast_ofNat, pow_add]
  field_simp

end
end AxiomaticGW.GKM.ExceptionalDoubleCoverChain

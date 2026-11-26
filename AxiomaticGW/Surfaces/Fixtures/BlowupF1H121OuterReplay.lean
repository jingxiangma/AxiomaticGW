/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsReplay
public import AxiomaticGW.Surfaces.GenusTwoResidualLookup

/-!
# Complete finite kernel replay of the first F1 H-row term 121

All four ordered full curve splits, four node states, and two point distributions
are retained, including all thirty zero entries. Each scalar part is checked
against the original contraction with the already certified component cache.
Finite reindexing and cache preservation recover the unchanged weighted term.
This is one full original term, not acceptance of the entire 721-term H constant.
-/

@[expose] public section
set_option maxRecDepth 65536
set_option Elab.async false
set_option maxHeartbeats 0

namespace AxiomaticGW.BlowupF1H121OuterParts
open SurfaceGenusTwo BlowupF1H121Components
open BlowupF1CertifiedPoints (rational elliptic rational_eq elliptic_eq)
open scoped BigOperators

abbrev X := SurfaceTarget.hirzebruchOne

def vertex := SurfacePointPullback.vertex X
  (constantVertexWithPointLookup X cache rational elliptic)

/-- One separating-root summand after transporting the original external labels.
Only the fixed separating-root expression below is certified by this helper. -/
def rootSlice {g : ℕ} {S : Type} [Fintype S] :
    (x : GluingExpression g S) → x.CotangentDecoration → x.DecidableLabels →
      (X.Curve × X.Curve) → SurfaceBasisLabel X → (ℕ × ℕ) →
      (S → SurfaceBasisLabel X) → ℚ
  | @GluingExpression.fundamental g S _ _, _, _, _, _, _, _ => 0
  | @GluingExpression.relabel _ _ _ _ _ e x, d, l, split, b, ij, a => rootSlice x d l split b ij (a ∘ e)
  | @GluingExpression.separating _ _ _ _ _ _ x y, d, l, split, b, ij, a =>
      b.inverseWeight * (1 : ℕ).choose ij.1 *
        (let right := y.scalarPointContraction X vertex d.2 l.2 split.2 ij.2
          (Option.elim · b.dual (a ∘ Sum.inr))
         if right = 0 then 0 else
           x.scalarPointContraction X vertex d.1 l.1 split.1 ij.1
             (Option.elim · b (a ∘ Sum.inl)) * right)
  | @GluingExpression.nonseparating _ _ _ _, _, _, _, _, _, _ => 0

def sourceSplits : Fin 4 → X.Curve × X.Curve :=
  ![(![0, 0], ![1, 1]), (![0, 1], ![1, 0]),
    (![1, 0], ![0, 1]), (![1, 1], ![0, 0])]

def part (i : Fin 4) (b : SurfaceBasisLabel X) (k : Fin 2) : ℚ :=
  L24CorrectionsReplay.fullClaim 121 *
    rootSlice (L24Gluing.term121).expression (L24Gluing.term121).decoration
      (L24Gluing.term121).labels (sourceSplits i) b (k.val, 1 - k.val)
      ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0]

-- This equality exposes the complete existing outer summation before evaluating any part.
theorem original_eq_outer_sum :
    L24CorrectionsReplay.fullClaim 121 *
      guardedConstantPointContractionWithPointLookup X cache rational elliptic
        (L24Gluing.term 121) ![1, 1] 1
        ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] =
    ∑ split ∈ X.splittings ![1, 1], ∑ b : SurfaceBasisLabel X,
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal 1,
        L24CorrectionsReplay.fullClaim 121 * rootSlice
          (L24Gluing.term121).expression (L24Gluing.term121).decoration
          (L24Gluing.term121).labels split b ij
          ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] := by
  change L24CorrectionsReplay.fullClaim 121 *
    guardedConstantPointContractionWithPointLookup X cache rational elliptic
      L24Gluing.term121 ![1, 1] 1
      ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = _
  rw [guardedConstantPointContractionWithPointLookup,
    if_neg (by decide : ¬ 2 ≤ L24Gluing.term121.expression.maxComponentGenus)]
  simp only [L24Gluing.term121, L24Gluing.expression51, GetzlerGraphs.join,
    GluingExpression.scalarPointContraction, rootSlice, vertex, Finset.mul_sum, mul_assoc]

end AxiomaticGW.BlowupF1H121OuterParts

namespace AxiomaticGW.BlowupF1H121OuterParts

open SurfaceGenusTwo BlowupF1H121Components
open BlowupF1CertifiedPoints (rational elliptic rational_eq elliptic_eq)
open scoped BigOperators

/-- The four held full-coordinate splittings occur exactly once. -/
theorem sourceSplits_injective : Function.Injective sourceSplits := by
  decide +kernel

/-- The held four entries exhaust the original executable splitting finset. -/
theorem sourceSplits_complete :
    X.splittings ![1, 1] = Finset.univ.image sourceSplits := by
  decide +kernel

/-- Reindex any summand by the held full curve splits without evaluating it. -/
theorem sum_sourceSplits {M : Type*} [AddCommMonoid M]
    (f : X.Curve × X.Curve → M) :
    (∑ split ∈ X.splittings ![1, 1], f split) =
      ∑ i : Fin 4, f (sourceSplits i) := by
  rw [sourceSplits_complete]
  exact Finset.sum_image (fun _ _ _ _ h ↦ sourceSplits_injective h)

/-- Both ordered point distributions occur once, including each zero side. -/
theorem pointDistributions_injective :
    Function.Injective (fun k : Fin 2 ↦ (k.val, 1 - k.val)) := by
  intro k l h
  exact Fin.ext (congrArg Prod.fst h)

/-- The two held ordered distributions exhaust the original antidiagonal. -/
theorem pointDistributions_complete :
    Finset.HasAntidiagonal.antidiagonal (1 : ℕ) =
      Finset.univ.image (fun k : Fin 2 ↦ (k.val, 1 - k.val)) := by
  decide +kernel

/-- Reindex an arbitrary integrand without altering its binomial weight. -/
theorem sum_pointDistributions {M : Type*} [AddCommMonoid M]
    (f : ℕ × ℕ → M) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal 1, f ij) =
      ∑ k : Fin 2, f (k.val, 1 - k.val) := by
  rw [pointDistributions_complete]
  exact Finset.sum_image (fun _ _ _ _ h ↦ pointDistributions_injective h)

/-- Exactly reindex the original four splits, four states and two distributions.
The integrand is arbitrary, so all scalar, inverse-metric and binomial factors
remain part of the same summand. -/
theorem outer_sum_eq_indexed {M : Type*} [AddCommMonoid M]
    (f : (X.Curve × X.Curve) → SurfaceBasisLabel X → (ℕ × ℕ) → M) :
    (∑ split ∈ X.splittings ![1, 1], ∑ b : SurfaceBasisLabel X,
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal 1, f split b ij) =
    ∑ i : Fin 4, ∑ b : SurfaceBasisLabel X, ∑ k : Fin 2,
      f (sourceSplits i) b (k.val, 1 - k.val) := by
  rw [sum_sourceSplits]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  exact sum_pointDistributions (f (sourceSplits i) b)

/-- The fixed original cached term is exactly the sum of all 32 held parts. -/
theorem original_eq_sum_parts :
    L24CorrectionsReplay.fullClaim 121 *
      guardedConstantPointContractionWithPointLookup X cache rational elliptic
        (L24Gluing.term 121) ![1, 1] 1
        ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] =
    ∑ i : Fin 4, ∑ b : SurfaceBasisLabel X, ∑ k : Fin 2, part i b k := by
  rw [original_eq_outer_sum]
  exact outer_sum_eq_indexed (fun split b ij ↦
    L24CorrectionsReplay.fullClaim 121 * rootSlice
      (L24Gluing.term121).expression (L24Gluing.term121).decoration
      (L24Gluing.term121).labels split b ij
      ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0])

/-- The same finite certificate reconstructs the unchanged non-cache term. -/
theorem original_constant_eq_sum_parts :
    L24CorrectionsReplay.fullClaim 121 *
      guardedConstantPointContraction X (L24Gluing.term 121) ![1, 1] 1
        ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] =
    ∑ i : Fin 4, ∑ b : SurfaceBasisLabel X, ∑ k : Fin 2, part i b k := by
  rw [← guardedConstantPointContractionWithPointLookup_eq X cache rational elliptic
    rational_eq elliptic_eq]
  exact original_eq_sum_parts

end AxiomaticGW.BlowupF1H121OuterParts

namespace AxiomaticGWTest.BlowupF1H121OuterParts

open AxiomaticGW AxiomaticGW.BlowupF1H121OuterParts

/-- The certificate has 32 slots even if individual values vanish. -/
theorem slot_count :
    Fintype.card (Fin 4 × SurfaceBasisLabel X × Fin 2) = 32 := by
  decide +kernel

/-- The exceptional node state retains its negative inverse-metric weight. -/
theorem exceptional_weight :
    (SurfaceBasisLabel.exceptional (X := X) 0).inverseWeight = -1 := by
  decide +kernel

/-- Each finite point index retains the exact one-point distribution. -/
theorem point_count (k : Fin 2) : k.val + (1 - k.val) = 1 := by
  fin_cases k <;> decide

end AxiomaticGWTest.BlowupF1H121OuterParts

namespace AxiomaticGW.BlowupF1H121OuterParts
open SurfaceGenusTwo
open scoped BigOperators

theorem part_0_unit_0 : part 0 .unit 0 = 0 := by decide +kernel

theorem part_0_unit_1 : part 0 .unit 1 = 0 := by decide +kernel

theorem part_0_hyperplane_0 : part 0 .hyperplane 0 = (1 / 1440) := by decide +kernel

theorem part_0_hyperplane_1 : part 0 .hyperplane 1 = 0 := by decide +kernel

theorem part_0_exceptional_0_0 : part 0 (.exceptional 0) 0 = (-1 / 4320) := by decide +kernel

theorem part_0_exceptional_0_1 : part 0 (.exceptional 0) 1 = 0 := by decide +kernel

theorem part_0_point_0 : part 0 .point 0 = 0 := by decide +kernel

theorem part_0_point_1 : part 0 .point 1 = 0 := by decide +kernel

theorem part_1_unit_0 : part 1 .unit 0 = 0 := by decide +kernel

theorem part_1_unit_1 : part 1 .unit 1 = 0 := by decide +kernel

theorem part_1_hyperplane_0 : part 1 .hyperplane 0 = 0 := by decide +kernel

theorem part_1_hyperplane_1 : part 1 .hyperplane 1 = 0 := by decide +kernel

theorem part_1_exceptional_0_0 : part 1 (.exceptional 0) 0 = 0 := by decide +kernel

theorem part_1_exceptional_0_1 : part 1 (.exceptional 0) 1 = 0 := by decide +kernel

theorem part_1_point_0 : part 1 .point 0 = 0 := by decide +kernel

theorem part_1_point_1 : part 1 .point 1 = 0 := by decide +kernel

theorem part_2_unit_0 : part 2 .unit 0 = 0 := by decide +kernel

theorem part_2_unit_1 : part 2 .unit 1 = 0 := by decide +kernel

theorem part_2_hyperplane_0 : part 2 .hyperplane 0 = 0 := by decide +kernel

theorem part_2_hyperplane_1 : part 2 .hyperplane 1 = 0 := by decide +kernel

theorem part_2_exceptional_0_0 : part 2 (.exceptional 0) 0 = 0 := by decide +kernel

theorem part_2_exceptional_0_1 : part 2 (.exceptional 0) 1 = 0 := by decide +kernel

theorem part_2_point_0 : part 2 .point 0 = 0 := by decide +kernel

theorem part_2_point_1 : part 2 .point 1 = 0 := by decide +kernel

theorem part_3_unit_0 : part 3 .unit 0 = 0 := by decide +kernel

theorem part_3_unit_1 : part 3 .unit 1 = 0 := by decide +kernel

theorem part_3_hyperplane_0 : part 3 .hyperplane 0 = 0 := by decide +kernel

theorem part_3_hyperplane_1 : part 3 .hyperplane 1 = 0 := by decide +kernel

theorem part_3_exceptional_0_0 : part 3 (.exceptional 0) 0 = 0 := by decide +kernel

theorem part_3_exceptional_0_1 : part 3 (.exceptional 0) 1 = 0 := by decide +kernel

theorem part_3_point_0 : part 3 .point 0 = 0 := by decide +kernel

theorem part_3_point_1 : part 3 .point 1 = 0 := by decide +kernel

def claimed (i : Fin 4) (b : SurfaceBasisLabel X) (k : Fin 2) : ℚ :=
  if i = 0 ∧ k = 0 then
    match b with
    | .hyperplane => 1 / 1440
    | .exceptional _ => -1 / 4320
    | _ => 0
  else 0

theorem part_eq_claimed (i : Fin 4) (b : SurfaceBasisLabel X) (k : Fin 2) :
    part i b k = claimed i b k := by
  fin_cases i
  · cases b with
    | unit =>
      fin_cases k
      · exact part_0_unit_0
      · exact part_0_unit_1
    | hyperplane =>
      fin_cases k
      · exact part_0_hyperplane_0
      · exact part_0_hyperplane_1
    | exceptional e =>
      fin_cases e
      fin_cases k
      · exact part_0_exceptional_0_0
      · exact part_0_exceptional_0_1
    | point =>
      fin_cases k
      · exact part_0_point_0
      · exact part_0_point_1
  · cases b with
    | unit =>
      fin_cases k
      · exact part_1_unit_0
      · exact part_1_unit_1
    | hyperplane =>
      fin_cases k
      · exact part_1_hyperplane_0
      · exact part_1_hyperplane_1
    | exceptional e =>
      fin_cases e
      fin_cases k
      · exact part_1_exceptional_0_0
      · exact part_1_exceptional_0_1
    | point =>
      fin_cases k
      · exact part_1_point_0
      · exact part_1_point_1
  · cases b with
    | unit =>
      fin_cases k
      · exact part_2_unit_0
      · exact part_2_unit_1
    | hyperplane =>
      fin_cases k
      · exact part_2_hyperplane_0
      · exact part_2_hyperplane_1
    | exceptional e =>
      fin_cases e
      fin_cases k
      · exact part_2_exceptional_0_0
      · exact part_2_exceptional_0_1
    | point =>
      fin_cases k
      · exact part_2_point_0
      · exact part_2_point_1
  · cases b with
    | unit =>
      fin_cases k
      · exact part_3_unit_0
      · exact part_3_unit_1
    | hyperplane =>
      fin_cases k
      · exact part_3_hyperplane_0
      · exact part_3_hyperplane_1
    | exceptional e =>
      fin_cases e
      fin_cases k
      · exact part_3_exceptional_0_0
      · exact part_3_exceptional_0_1
    | point =>
      fin_cases k
      · exact part_3_point_0
      · exact part_3_point_1

theorem claimed_sum : (∑ i : Fin 4, ∑ b : SurfaceBasisLabel X, ∑ k : Fin 2,
    claimed i b k) = 1 / 2160 := by decide +kernel

/-- The unchanged original weighted term, including all zero slots and signed states. -/
theorem original_weighted121 :
    L24CorrectionsReplay.fullClaim 121 *
      guardedConstantPointContraction X (L24Gluing.term 121) ![1, 1] 1
        ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] = 1 / 2160 := by
  rw [original_constant_eq_sum_parts]
  simp only [part_eq_claimed]
  exact claimed_sum

end AxiomaticGW.BlowupF1H121OuterParts

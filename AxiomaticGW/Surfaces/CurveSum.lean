/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.CurveClasses
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Summing full effective coordinates as literal tuples

The three fixed surfaces have one, two or three generators. Nested range
sums enumerate their complete coordinate boxes without constructing
dependent function-valued finite sets. The equality theorem retains every
subclass; callers recover the complementary class by subtraction.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceTarget

/-- Sum once over every full coordinate tuple bounded componentwise by the request. -/
def sumSubcurves : (X : SurfaceTarget) → X.Curve → (X.Curve → ℚ) → ℚ
  | .plane, beta, f => ∑ a ∈ Finset.range (beta 0 + 1), f ![a]
  | .hirzebruchOne, beta, f =>
      ∑ a ∈ Finset.range (beta 0 + 1), ∑ b ∈ Finset.range (beta 1 + 1), f ![a, b]
  | .blowupTwo, beta, f =>
      ∑ a ∈ Finset.range (beta 0 + 1), ∑ b ∈ Finset.range (beta 1 + 1),
        ∑ c ∈ Finset.range (beta 2 + 1), f ![a, b, c]

/-- Direct tuple sums equal the original complete function-valued coordinate box. -/
theorem sumSubcurves_eq (X : SurfaceTarget) (beta : X.Curve) (f : X.Curve → ℚ) :
    sumSubcurves X beta f =
      ∑ first ∈ Fintype.piFinset (fun i ↦ Finset.range (beta i + 1)), f first := by
  cases X with
  | plane =>
    unfold sumSubcurves
    symm
    refine Finset.sum_bij (fun first _ ↦ first 0) ?_ ?_ ?_ ?_
    · intro first hf
      exact Fintype.mem_piFinset.mp hf 0
    · intro first _ second _ he
      funext i
      fin_cases i
      exact he
    · intro a ha
      refine ⟨![a], ?_, rfl⟩
      rw [Fintype.mem_piFinset]
      intro i
      fin_cases i
      exact ha
    · intro first _
      congr 1
      funext i
      fin_cases i
      rfl
  | hirzebruchOne =>
    simp only [sumSubcurves]
    rw [← Finset.sum_product']
    symm
    refine Finset.sum_bij (fun first _ ↦ (first 0, first 1)) ?_ ?_ ?_ ?_
    · intro first hf
      exact Finset.mem_product.mpr
        ⟨Fintype.mem_piFinset.mp hf 0, Fintype.mem_piFinset.mp hf 1⟩
    · intro first _ second _ he
      funext i
      fin_cases i
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he
    · intro ab hab
      refine ⟨![ab.1, ab.2], ?_, rfl⟩
      rw [Fintype.mem_piFinset]
      intro i
      fin_cases i
      · exact (Finset.mem_product.mp hab).1
      · exact (Finset.mem_product.mp hab).2
    · intro first _
      congr 1
      funext i
      fin_cases i <;> rfl
  | blowupTwo =>
    simp only [sumSubcurves]
    simp only [← Finset.sum_product']
    symm
    refine Finset.sum_bij (fun first _ ↦ (first 0, first 1, first 2)) ?_ ?_ ?_ ?_
    · intro first hf
      exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mp hf 0,
        Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mp hf 1, Fintype.mem_piFinset.mp hf 2⟩⟩
    · intro first _ second _ he
      funext i
      fin_cases i
      · exact congrArg Prod.fst he
      · exact congrArg (fun p ↦ p.2.1) he
      · exact congrArg (fun p ↦ p.2.2) he
    · intro abc habc
      refine ⟨![abc.1, abc.2.1, abc.2.2], ?_, rfl⟩
      rw [Fintype.mem_piFinset]
      intro i
      fin_cases i
      · exact (Finset.mem_product.mp habc).1
      · exact (Finset.mem_product.mp (Finset.mem_product.mp habc).2).1
      · exact (Finset.mem_product.mp (Finset.mem_product.mp habc).2).2
    · intro first _
      congr 1
      funext i
      fin_cases i <;> rfl

end AxiomaticGW.SurfaceTarget

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.DescendantStabilization

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.DescendantStabilization

open AxiomaticGW SurfaceCohomology SurfaceDescendant

/-- Stability deficits include every positive-degree genus-zero unstable arity. -/
example : stabilizationComplexity 0 Empty (fun s ↦ nomatch s) = 3 ∧
    stabilizationComplexity 0 (Fin 1) (fun _ ↦ 4) = 6 ∧
    stabilizationComplexity 0 (Fin 2) ![0,3] = 4 ∧
    stabilizationComplexity 1 Empty (fun s ↦ nomatch s) = 1 := by
  decide +kernel

/-- Stable genus-two arity has no marking deficit, including the empty request. -/
example : stabilizationComplexity 2 Empty (fun s ↦ nomatch s) = 0 ∧
    stabilizationComplexity 2 (Fin 2) ![2,3] = 5 := by
  decide +kernel

/-- The correction keeps the exceptional intersection sign. -/
example : (firstChernDivisor 2).val * exceptional 2 0 = point 2 ∧
    exceptional 2 0 * exceptional 2 0 = -point 2 ∧
    exceptional 2 0 * exceptional 2 1 = 0 := by
  refine ⟨firstChern_mul_exceptional 2 0, ?_, ?_⟩
  · rw [exceptional_mul_exceptional, if_pos rfl]
  · rw [exceptional_mul_exceptional, if_neg (by decide +kernel)]

/-- Arbitrarily large psi powers still decrease; zero powers are excluded. -/
example : stabilizationComplexity 0 (Fin 2) (lowerPower ![0,100] 1) = 100 ∧
    stabilizationComplexity 0 (Fin 2) ![0,100] = 101 ∧
    lowerPower (![0,100] : Fin 2 → ℕ) 0 = ![0,100] := by
  decide +kernel

/-- Synthetic callback for control-flow tests only; it is not a geometric GW model. -/
private def constantStable (X : SurfaceTarget) (g : ℕ) (c : ℚ)
    (S : Type) [Fintype S] [DecidableEq S] (_ : StableArity g S)
    (_ : S → ℕ) (_ : S → SurfaceCohomology X.blowups) : ℚ := c

/-- Three genus-zero marking additions retain the anticanonical coefficient. -/
example : stabilizedValue .plane 0 ![1] (constantStable .plane 0 1)
    Empty (fun s ↦ nomatch s) (fun s ↦ nomatch s) = 1 / 27 := by
  decide +kernel

/-- The one-marked psi correction is subtracted before dividing by energy. -/
example : stabilizedValue .plane 0 ![1] (constantStable .plane 0 1)
    (Fin 1) (fun _ ↦ 1) (fun _ ↦ (1 : SurfaceCohomology 0)) = 1 / 27 := by
  decide +kernel

/-- Energy-one exceptional classes do not create a zero denominator. -/
example : stabilizedValue .hirzebruchOne 0 ![1,0] (constantStable .hirzebruchOne 0 1)
    (Fin 1) (fun _ ↦ 1) (fun _ ↦ (1 : SurfaceCohomology 1)) = -1 := by
  decide +kernel

/-- Genus one needs exactly one primary marking at empty arity. -/
example : stabilizedValue .blowupTwo 1 ![0,0,2] (constantStable .blowupTwo 1 7)
    Empty (fun s ↦ nomatch s) (fun s ↦ nomatch s) = 7 / 2 := by
  decide +kernel

/-- Already stable requests pass through their callback, even at zero class. -/
example : stabilizedValue .plane 2 0 (constantStable .plane 2 7)
    Empty (fun s ↦ nomatch s) (fun s ↦ nomatch s) = 7 := by
  decide +kernel

/-- The numerical zero convention and the geometric query domain remain distinct. -/
example : stabilizedValue .plane 0 0 (constantStable .plane 0 7)
    (Fin 1) (fun _ ↦ 100) (fun _ ↦ (1 : SurfaceCohomology 0)) = 0 ∧
    stabilizedQuery? .plane ⟨0,0,[⟨.unit,100⟩]⟩ (constantStable .plane 0 7) = none := by
  decide +kernel

/-- Positive-degree empty requests are retained by the original query-domain rule. -/
example : stabilizedQuery? .plane ⟨0,![1],[]⟩ (constantStable .plane 0 27) = some 1 := by
  decide +kernel

section GeometricConsumers

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  (U : UnstableDescendantConventions M I) (T : SurfaceTheoryIdentification X Omega)
  (laws : DescendantStringDilatonLaws M I)
  {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
  (L : DescendantDivisorLaw M I A)

/-- No extra divisor-action hypothesis is needed for the negative exceptional square. -/
example (i : Fin X.blowups) :
    L.divisorAction (T.divisor (exceptionalDivisor X.blowups i))
      (exceptional X.blowups i) = -point X.blowups := by
  rw [T.divisorAction_eq_mul U laws L]
  change exceptional X.blowups i * exceptional X.blowups i = _
  rw [exceptional_mul_exceptional, if_pos rfl]

/-- The proved action applies to non-basis divisor combinations as well. -/
example : L.divisorAction (T.divisor (firstChernDivisor X.blowups))
    (hyperplane X.blowups) = (3 : ℚ) • point X.blowups := by
  rw [T.divisorAction_eq_mul U laws L]
  exact firstChern_mul_hyperplane X.blowups

/-- A three-point primary invariant accepts arbitrary linear combinations of states. -/
example (x y z : SurfaceCohomology X.blowups) :
    U.invariant 0 (Fin 3) 0 (fun _ ↦ 0) ![x,y,z] =
      counit X.blowups (x * y * z) := by
  rw [SurfacePrimary.invariant_zero_cubic U T laws (Fin 3) (by decide +kernel)]
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- Different abstract actions on the same family cannot change the correction. -/
example (L' : DescendantDivisorLaw M I A) : L.divisorAction = L'.divisorAction :=
  L.divisorAction_unique L' U laws

/-- Once stable descendants are supplied, the same original laws fix all unstable values. -/
example (U' : UnstableDescendantConventions M I)
    (H : FullDescendantDivisorLaw U L) (H' : FullDescendantDivisorLaw U' L)
    (hpair : T.DivisorPairingCompatible A)
    (g : ℕ) (S : Type) [Fintype S] (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceCohomology X.blowups) :
    U.invariant g S beta k a = U'.invariant g S beta k a :=
  numerical_extension_unique U U' T laws H H' hpair g S beta k a

/-- The adapter preserves the existing checked-query semantics at every finite request. -/
example (H : FullDescendantDivisorLaw U L) (hpair : T.DivisorPairingCompatible A)
    (q : SurfaceQuery X)
    (v : ∀ (S : Type) [Fintype S] [DecidableEq S],
      StableArity q.genus S → (S → ℕ) → (S → SurfaceCohomology X.blowups) → ℚ)
    (hv : ∀ (S : Type) [Fintype S] [DecidableEq S] (h : StableArity q.genus S)
      (k : S → ℕ) (a : S → SurfaceCohomology X.blowups),
      v S h k a = M.invariant I q.genus S h q.beta k a) :
    stabilizedQuery? X q v = q.checkedEval U :=
  stabilizedQuery?_eq_checkedEval U T laws H hpair q v hv

end GeometricConsumers
end AxiomaticGWTest.Surfaces.DescendantStabilization

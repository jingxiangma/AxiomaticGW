module

public import AxiomaticGW.Surfaces.GenusTwoBlowupPointCache

/-! Exact dispatch tests retain signed classes, shifted sources and exceptional labels. -/

@[expose] public section

namespace AxiomaticGWTest.Surfaces.GenusTwoBlowupPointCache

open AxiomaticGW SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupPointCache

/-- The complete signed Bl2 class is retained in every family and for either source shift. -/
theorem signed_full_class (i : Fin 2) (f : Family .blowupTwo)
    (v₀ v₁ : SurfaceTarget.blowupTwo.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue .blowupTwo)
    (h₁ : v₁ = SurfaceGenusOne.pointValue .blowupTwo) :
    constant (X := .blowupTwo) i (![2, 3, 1], f) v₀ v₁ =
      SurfaceGenusTwoBlowupScalar.constant (X := .blowupTwo) i (![2, 3, 1], f) :=
  constant_eq (X := .blowupTwo) i _ v₀ v₁ h₀ h₁

/-- Zero-class states retain the original scalar convention in every family. -/
theorem zero_class_all_families (f : Family .hirzebruchOne) :
    constant (X := .hirzebruchOne) 0 (0, f)
      (SurfaceGenusZero.pointValue .hirzebruchOne) (SurfaceGenusOne.pointValue .hirzebruchOne) =
      SurfaceGenusTwoBlowupScalar.constant (X := .hirzebruchOne) 0 (0, f) :=
  constant_eq (X := .hirzebruchOne) 0 _ _ _ rfl rfl

/-- The signed H source shifts the entire class and keeps the original five added points. -/
theorem signed_h_dispatch (v₀ v₁ : SurfaceTarget.blowupTwo.Curve → ℚ) :
    constant (X := .blowupTwo) 0 (![2, 3, 1], .hyperplane) v₀ v₁ =
      L24Relation.pointConstantWithPoints .blowupTwo v₀ v₁ 5 ![3, 3, 1]
        ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] := by
  have he : SurfaceTarget.blowupTwo.effective.energy ![2, 3, 1] = 6 := by decide +kernel
  have hs : (![2, 3, 1] : SurfaceTarget.blowupTwo.Curve) +
      SurfaceTarget.blowupTwo.exceptionalCurve 0 = ![3, 3, 1] := by
    funext k
    fin_cases k <;> rfl
  simp only [constant, he, hs, Nat.reduceSub]

/-- The K label remains independent of the exceptional index used to choose H/N sources. -/
theorem foreign_exceptional_dispatch (v₀ v₁ : SurfaceTarget.blowupTwo.Curve → ℚ) :
    constant (X := .blowupTwo) 0 (![2, 3, 1], .exceptional 1) v₀ v₁ =
      BelorousskiPandharipande.lowerPointConstantWithPrimary .blowupTwo v₀ v₁ 5 ![2, 3, 1]
        ![.exceptional 1, .exceptional 1, .exceptional 1] := by
  have he : SurfaceTarget.blowupTwo.effective.energy ![2, 3, 1] = 6 := by decide +kernel
  simp only [constant, he, Nat.reduceSub]

/-- The second exceptional shift preserves all four N weights and their original labels. -/
theorem primary_four_weights (v₀ v₁ : SurfaceTarget.blowupTwo.Curve → ℚ) :
    constant (X := .blowupTwo) 1 (![1, 0, 1], .primary) v₀ v₁ =
      (3 / 2) * BelorousskiPandharipande.lowerPointConstantWithPrimary .blowupTwo v₀ v₁
        2 ![1, 1, 1] ![.exceptional 1, .hyperplane, .hyperplane] +
      (-1) * BelorousskiPandharipande.lowerPointConstantWithPrimary .blowupTwo v₀ v₁
        2 ![1, 1, 1] ![.exceptional 1, .exceptional 1, .hyperplane] +
      (1 / 2) * BelorousskiPandharipande.lowerPointConstantWithPrimary .blowupTwo v₀ v₁
        2 ![1, 1, 1] ![.exceptional 1, .exceptional 1, .exceptional 1] +
      (-1 / 3) * BelorousskiPandharipande.lowerPointConstantWithPrimary .blowupTwo v₀ v₁
        2 ![1, 1, 1] ![.hyperplane, .hyperplane, .hyperplane] := by
  have he : SurfaceTarget.blowupTwo.effective.energy ![1, 0, 1] = 2 := by decide +kernel
  have hd : SurfaceTarget.blowupTwo.planeDegree ![1, 0, 1] = 1 := rfl
  have hs : (![1, 0, 1] : SurfaceTarget.blowupTwo.Curve) +
      SurfaceTarget.blowupTwo.exceptionalCurve 1 = ![1, 1, 1] := by
    funext k
    fin_cases k <;> rfl
  simp only [constant, he, hd, hs, Nat.cast_one, mul_one]

end AxiomaticGWTest.Surfaces.GenusTwoBlowupPointCache

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.ExceptionalMarkedGraphSupport
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoExceptionalFewMarkings

/-! # Native point-insertion support for the existing exceptional few-marking frames -/

public section
namespace AxiomaticGW.GKM.ExceptionalMarkedGraphBenchmark
open ExceptionalMarkedGraphSupport SurfaceGenusTwo

private theorem from_claim {X : SurfaceTarget} (q : SurfaceQuery X)
    (h : exceptionalPointQueryValue? q = some 0) : q.beta ≠ 0 ∧
    X.divisorIntersections q.beta 0 = 0 ∧ .point ∈ q.insertions.map SurfaceInsertion.label := by
  unfold exceptionalPointQueryValue? at h
  split at h
  · assumption
  · contradiction

/-- Every one of the original 106 ordered F₁ requests has vanishing native graph insertions. -/
theorem oneBlowup (i : Fin 106) : let q := GenusTwoExceptionalFewMarkings.OneBlowup.requests i
    FewMarkingQuery q ∧ Vanishes CurveReplay.OneBlowup.tables
      SurfaceFrames.OneBlowup.request.restrictions q := by
  obtain ⟨hf, h⟩ := GenusTwoExceptionalFewMarkings.OneBlowup.accepted i
  obtain ⟨hn, hd, hp⟩ := from_claim _ h
  refine ⟨hf, oneBlowup_point _ hn ?_ hp⟩
  change (((GenusTwoExceptionalFewMarkings.OneBlowup.requests i).beta 1 : ℕ) : ℤ) = 0 at hd
  exact_mod_cast hd

/-- Every one of the original 514 ordered Bl₂ requests has vanishing native graph insertions. -/
theorem twoBlowups (i : Fin 514) : let q := GenusTwoExceptionalFewMarkings.TwoBlowups.requests i
    FewMarkingQuery q ∧ Vanishes CurveReplay.TwoBlowups.tables
      SurfaceFrames.TwoBlowups.request.restrictions q := by
  obtain ⟨hf, h⟩ := GenusTwoExceptionalFewMarkings.TwoBlowups.accepted i
  obtain ⟨hn, hd, hp⟩ := from_claim _ h
  refine ⟨hf, twoBlowups_point _ hn ?_ hp⟩
  change (((GenusTwoExceptionalFewMarkings.TwoBlowups.requests i).beta 2 : ℕ) : ℤ) = 0 at hd
  exact_mod_cast hd

end AxiomaticGW.GKM.ExceptionalMarkedGraphBenchmark

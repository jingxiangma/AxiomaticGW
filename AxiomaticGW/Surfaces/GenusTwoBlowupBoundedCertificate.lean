/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupCertificate
public import AxiomaticGW.Surfaces.GenusTwoBlowupScalar
public import AxiomaticGW.Surfaces.GenusTwoBlowupDependencyEnergy
public import Mathlib.Data.List.Pi

/-!
# Executable bounded full-state certificates for genus-two blowup reconstruction

An executable coordinate list retains all full effective classes of bounded
energy and every H/P/N/K sector, including the internal nominal P0 state.
The existing complete-row support and coefficient-energy theorems prove that
this list covers every collected dependency of its positive-plane rows.

Scalar replay is therefore exactly the original full-row check without
constructing polynomial rows during numerical evaluation. The original finite
certificate soundness theorem supplies equality to the well-founded values.
This does not claim numerical suite completion or efficient runtime.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwoBlowupBoundedCertificate
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
variable {X : SurfaceTarget}

-- The original H dispatch includes all 815 source columns.
set_option maxRecDepth 20000

/-- An executable coordinate box, using List.pi rather than noncomputable Finset.toList. -/
def coordinateBox (X : SurfaceTarget) (B : ℕ) : List X.Curve :=
  (List.pi (List.finRange (X.blowups + 1)) (fun _ ↦ List.range (B + 1))).map
    (fun f k ↦ f k (List.mem_finRange k))

/-- Coordinate-box membership records every generator multiplicity. -/
theorem mem_coordinateBox (X : SurfaceTarget) (B : ℕ) (beta : X.Curve) :
    beta ∈ coordinateBox X B ↔ ∀ k, beta k ≤ B := by
  rw [coordinateBox, List.mem_map]
  constructor
  · rintro ⟨f, hf, hbeta⟩ k
    have hk := (List.mem_pi _ f).mp hf k (List.mem_finRange k)
    have he := congrFun hbeta k
    change f k (List.mem_finRange k) = beta k at he
    rw [he] at hk
    exact Nat.le_of_lt_succ (List.mem_range.mp hk)
  · intro h
    let f : ∀ k, k ∈ List.finRange (X.blowups + 1) → ℕ := fun k _ ↦ beta k
    refine ⟨f, (List.mem_pi _ f).mpr ?_, rfl⟩
    intro k _
    exact List.mem_range.mpr (Nat.lt_succ_of_le (h k))

/-- All full effective classes through the given anticanonical energy. -/
def classes (X : SurfaceTarget) (B : ℕ) : List X.Curve :=
  (coordinateBox X B).filter (fun beta ↦ decide (X.effective.energy beta ≤ B))

/-- Positive weights make the executable list complete for the requested energy. -/
theorem mem_classes (X : SurfaceTarget) (B : ℕ) (beta : X.Curve) :
    beta ∈ classes X B ↔ X.effective.energy beta ≤ B := by
  rw [classes, List.mem_filter, decide_eq_true_eq, mem_coordinateBox]
  constructor
  · exact And.right
  · intro hb
    refine ⟨fun k ↦ ?_, hb⟩
    exact (WeightedCurveClass.coordinate_le_energy X.weights X.weights_pos beta k).trans hb

/-- The executable class list agrees with the existing bounded Finset API. -/
theorem classes_toFinset (X : SurfaceTarget) (B : ℕ) :
    (classes X B).toFinset = X.bounded B := by
  ext beta
  rw [List.mem_toFinset, mem_classes, X.bounded_eq]
  exact (X.effective.mem_bounded B beta).symm

/-- Every exceptional label occurs independently; no Family typeclass is introduced. -/
def families (X : SurfaceTarget) : List (Family X) :=
  [.hyperplane, .point, .primary] ++ (List.finRange X.blowups).map Family.exceptional

/-- The finite list contains every reconstruction sector. -/
theorem mem_families (X : SurfaceTarget) (family : Family X) :
    family ∈ families X := by
  apply List.mem_append.mpr
  cases family with
  | hyperplane => exact Or.inl (List.mem_cons_self)
  | point => exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
  | primary =>
    exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  | exceptional i => exact Or.inr (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

/-- Executable complete states, preserving full class coordinates and exceptional labels.
The nominal P0 state is internal and is not asserted dimension compatible. -/
def states (X : SurfaceTarget) (B : ℕ) : List (State X) :=
  (classes X B).flatMap (fun beta ↦ (families X).map (fun family ↦ (beta, family)))

/-- State coverage is exactly the full-class energy bound, including all sectors at zero. -/
theorem mem_states (X : SurfaceTarget) (B : ℕ) (s : State X) :
    s ∈ states X B ↔ X.effective.energy s.1 ≤ B := by
  rw [states, List.mem_flatMap]
  constructor
  · rintro ⟨beta, hb, hs⟩
    obtain ⟨family, _, he⟩ := List.mem_map.mp hs
    have he' := congrArg Prod.fst he
    change beta = s.1 at he'
    rw [← he']
    exact (mem_classes X B beta).mp hb
  · intro hs
    refine ⟨s.1, (mem_classes X B s.1).mpr hs, ?_⟩
    exact List.mem_map.mpr ⟨s.2, mem_families X s.2, Prod.eta s⟩

private theorem energy_pos (s : State X) (hd : 0 < X.planeDegree s.1) :
    0 < X.effective.energy s.1 := by
  apply Nat.pos_of_ne_zero
  intro h
  have hz := (X.effective.energy_eq_zero_iff s.1).mp h
  rw [hz, map_zero] at hd
  omega

/-- The existing four solved-row support results dispatch to the same selected full row. -/
private theorem remainder_support (i : Fin X.blowups) (s : State X)
    (hd : 0 < X.planeDegree s.1) {t : ℚ × Multiset (Variable X)}
    (ht : t ∈ RationalTerms.collect (SurfaceGenusTwoBlowupRecursion.row i s))
    (hne : t.2 ≠ {Sum.inr (s.2.query s.1)}) :
    t.2 = 0 ∨ ∃ u : State X,
      t.2 = {Sum.inr (u.2.query u.1)} ∧ Earlier X u s := by
  obtain ⟨beta, family⟩ := s
  have hb := energy_pos (beta, family) hd
  cases family with
  | hyperplane =>
    rcases SurfaceGenusTwoBlowupHRow.remainder_support X i beta hb
      (Multiset.mem_filter.mpr ⟨ht, hne⟩) with hz | ⟨gamma, f, hm, he⟩
    · exact Or.inl hz
    · exact Or.inr ⟨(gamma, f), hm, he⟩
  | point =>
    rcases SurfaceGenusTwoBlowupPRow.remainder_support X beta hb
      (Multiset.mem_filter.mpr ⟨ht, hne⟩) with hz | ⟨gamma, f, hm, he⟩
    · exact Or.inl hz
    · exact Or.inr ⟨(gamma, f), hm, he⟩
  | primary =>
    rcases SurfaceGenusTwoBlowupNRow.remainder_support X i beta
      (Multiset.mem_filter.mpr ⟨ht, hne⟩) with hz | ⟨gamma, f, hm, he⟩
    · exact Or.inl hz
    · exact Or.inr ⟨(gamma, f), hm, he⟩
  | exceptional j =>
    rcases SurfaceGenusTwoBlowupKRow.remainder_support X j beta hb
      (Multiset.mem_filter.mpr ⟨ht, hne⟩) with hz | ⟨gamma, f, hm, he⟩
    · exact Or.inl hz
    · exact Or.inr ⟨(gamma, f), hm, he⟩

/-- Every actual collected variable is the exact own query or an earlier canonical state.
The latter retains its nonzero full coefficient for the energy theorem. -/
theorem rowVariables_support (i : Fin X.blowups) (s : State X)
    (hd : 0 < X.planeDegree s.1) (v : Variable X)
    (hv : v ∈ SurfaceGenusTwoBlowupCertificate.rowVariables i s) :
    v = .inr (s.2.query s.1) ∨ ∃ u : State X,
      Earlier X u s ∧ v = .inr (u.2.query u.1) ∧
        RationalTerms.coefficient (SurfaceGenusTwoBlowupRecursion.row i s)
          {.inr (u.2.query u.1)} ≠ 0 := by
  by_cases hself : v = .inr (s.2.query s.1)
  · exact Or.inl hself
  obtain ⟨t, ht, hvt⟩ := Multiset.mem_bind.mp (Multiset.mem_toFinset.mp hv)
  have hne : t.2 ≠ {Sum.inr (s.2.query s.1)} := by
    intro he
    rw [he, Multiset.mem_singleton] at hvt
    exact hself hvt
  rcases remainder_support i s hd ht hne with hz | ⟨u, hm, he⟩
  · exact (Multiset.notMem_zero v (hz ▸ hvt)).elim
  · rw [hm, Multiset.mem_singleton] at hvt
    have ha := RationalTerms.mem_collect.mp ht
    refine Or.inr ⟨u, he, hvt, ?_⟩
    rw [← hm, ← ha.2.1]
    exact ha.2.2

/-- A complete bounded grid statically covers every surviving earlier full-state dependency. -/
theorem checkClosure_states (i : Fin X.blowups) (B : ℕ) (s : State X)
    (hs : s ∈ states X B) (hd : 0 < X.planeDegree s.1) :
    SurfaceGenusTwoBlowupCertificate.checkClosure i (states X B) s = true := by
  rw [SurfaceGenusTwoBlowupCertificate.checkClosure, decide_eq_true_eq]
  intro v hv
  apply (SurfaceGenusTwoBlowupCertificate.checkDependency_eq_true_iff _ s v).mpr
  rcases rowVariables_support i s hd v hv with hself | ⟨u, he, hq, hc⟩
  · exact Or.inl hself
  · refine Or.inr ⟨u, (mem_states X B u).mpr ?_, he, hq⟩
    exact (SurfaceGenusTwoBlowupDependencyEnergy.dependency_energy_le_of_positive_planeDegree
      i s u hd hc).trans ((mem_states X B s).mp hs)

/-- Full-grid scalar columns cover the actual collected row, after all real cancellations. -/
theorem columns_cover (i : Fin X.blowups) (B : ℕ) (s : State X)
    (hs : s ∈ states X B) (hd : 0 < X.planeDegree s.1) :
    ∀ v ∈ (RationalTerms.collect (SurfaceGenusTwoBlowupRecursion.row i s)).bind Prod.snd,
      v ∈ SurfaceGenusTwoBlowupScalar.columns (states X B) := by
  intro v hv
  have hc := checkClosure_states i B s hs hd
  rw [SurfaceGenusTwoBlowupCertificate.checkClosure, decide_eq_true_eq] at hc
  have hv' : v ∈ SurfaceGenusTwoBlowupCertificate.rowVariables i s :=
    Multiset.mem_toFinset.mpr hv
  apply (SurfaceGenusTwoBlowupScalar.mem_columns _ v).mpr
  rcases (SurfaceGenusTwoBlowupCertificate.checkDependency_eq_true_iff _ s v).mp
    (hc v hv') with hself | ⟨u, hu, _, hq⟩
  · exact ⟨s, hs, hself⟩
  · exact ⟨u, hu, hq⟩

/-- Scalar replay on the complete grid equals evaluation of the unchanged original row. -/
theorem replay_eq_row (i : Fin X.blowups) (B : ℕ) (s : State X)
    (values : Variable X → ℚ) (hs : s ∈ states X B) (hd : 0 < X.planeDegree s.1) :
    SurfaceGenusTwoBlowupScalar.replay i s values (states X B) =
      RationalTerms.eval values (SurfaceGenusTwoBlowupRecursion.row i s) :=
  SurfaceGenusTwoBlowupScalar.replay_eq_row i s values _ (columns_cover i B s hs hd)

/-- Check the same boundary and full row through scalar coefficients, with closure proved. -/
def checkRow (i : Fin X.blowups) (B : ℕ) (candidate : State X → ℚ) (s : State X) : Bool :=
  if X.planeDegree s.1 = 0 then
    decide (candidate s = SurfaceGenusTwoBlowupBoundary.value s.1 s.2)
  else decide (SurfaceGenusTwoBlowupScalar.replay i s (canonicalValuation candidate)
    (states X B) = 0)

/-- Scalar row checks are exactly the sound full-row checks on the complete bounded grid. -/
theorem checkRow_eq (i : Fin X.blowups) (B : ℕ) (candidate : State X → ℚ)
    (s : State X) (hs : s ∈ states X B) :
    checkRow i B candidate s =
      SurfaceGenusTwoBlowupCertificate.checkCanonicalRow i (states X B) candidate s := by
  by_cases hd : X.planeDegree s.1 = 0
  · rw [checkRow, SurfaceGenusTwoBlowupCertificate.checkCanonicalRow, if_pos hd, if_pos hd]
  · have hp := Nat.pos_of_ne_zero hd
    rw [checkRow, SurfaceGenusTwoBlowupCertificate.checkCanonicalRow, if_neg hd, if_neg hd,
      checkClosure_states i B s hs hp, Bool.true_and, replay_eq_row i B s _ hs hp]

/-- Verify every bounded canonical value by scalar replay, including zero-valued rows. -/
def checkTable (i : Fin X.blowups) (B : ℕ) (candidate : State X → ℚ) : Bool :=
  (states X B).all (checkRow i B candidate)

/-- An accepted scalar grid supplies the existing complete-row certificate. -/
theorem checkTable_eq (i : Fin X.blowups) (B : ℕ) (candidate : State X → ℚ) :
    checkTable i B candidate =
      SurfaceGenusTwoBlowupCertificate.checkCanonicalTable i (states X B) candidate := by
  apply Bool.eq_iff_iff.mpr
  simp only [checkTable, SurfaceGenusTwoBlowupCertificate.checkCanonicalTable, List.all_eq_true]
  constructor <;> intro h s hs
  · rw [← checkRow_eq i B candidate s hs]
    exact h s hs
  · rw [checkRow_eq i B candidate s hs]
    exact h s hs

/-- Every accepted bounded scalar value equals the original well-founded reconstruction. -/
theorem checkTable_sound (i : Fin X.blowups) (B : ℕ) (candidate : State X → ℚ)
    (hcheck : checkTable i B candidate = true) (s : State X)
    (hs : X.effective.energy s.1 ≤ B) :
    candidate s = SurfaceGenusTwoBlowupRecursion.values i s := by
  rw [checkTable_eq] at hcheck
  exact SurfaceGenusTwoBlowupCertificate.checkCanonicalTable_sound
    i (states X B) candidate hcheck s ((mem_states X B s).mpr hs)

end AxiomaticGW.SurfaceGenusTwoBlowupBoundedCertificate

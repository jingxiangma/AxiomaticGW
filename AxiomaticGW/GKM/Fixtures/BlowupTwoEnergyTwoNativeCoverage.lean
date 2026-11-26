/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoDoubleExceptionalComparison
public import AxiomaticGW.GKM.Fixtures.BlowupTwoMixedExceptional
public import AxiomaticGW.GKM.Fixtures.BlowupTwoPositivePlaneEnergyTwoSingletons
public import AxiomaticGW.GKM.Fixtures.BlowupTwoPositivePlaneEnergyTwoPairs

/-! # Exact native references at anticanonical energy two on the two-point blowup

The four native reports give one row for every dimension-compatible genus-two request with at
most two ordered markings in the six classes of energy two. Looking up a row retains its source
report and both torus characters. Identifying its value with a surface reconstruction requires
a separate target-side comparison.
-/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoEnergyTwoNativeCoverage

open SurfaceGenusTwo EquivariantCoefficients

/-- Row in one of the four original packets, retaining its packet-local index. -/
abbrev Row := Fin 210 ⊕ Fin 105 ⊕ Fin 15 ⊕ Fin 300

/-- The total row count, with doubled exceptional, mixed exceptional, positive-plane singleton,
and positive-plane pair packets in that order. -/
def rowIndex : Row ≃ Fin 630 :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans
    finSumFinEquiv)).trans finSumFinEquiv

/-- The original full class, genus and ordered insertions bound to each row. -/
def requests : Row → SurfaceQuery .blowupTwo :=
  Sum.elim BlowupTwoDoubleExceptionalFewMarkings.requests <|
    Sum.elim BlowupTwoMixedExceptional.requests <|
      Sum.elim BlowupTwoPositivePlaneEnergyTwoSingletons.requests
        BlowupTwoPositivePlaneEnergyTwoPairs.requests

/-- The reported ordinary value. -/
def values : Row → ℚ :=
  Sum.elim BlowupTwoDoubleExceptionalFewMarkings.values <|
    Sum.elim BlowupTwoMixedExceptional.values <|
      Sum.elim BlowupTwoPositivePlaneEnergyTwoSingletons.values
        BlowupTwoPositivePlaneEnergyTwoPairs.values

/-- The reported rational function of the two torus characters. -/
noncomputable def equivariant : Row → Coefficient :=
  Sum.elim BlowupTwoDoubleExceptionalFewMarkings.equivariant <|
    Sum.elim BlowupTwoMixedExceptional.equivariant <|
      Sum.elim BlowupTwoPositivePlaneEnergyTwoSingletons.equivariant
        BlowupTwoPositivePlaneEnergyTwoPairs.equivariant

/-- At the virtual dimension the actual fraction equals the embedded rational number. -/
theorem equivariant_eq_ordinary (r : Row) : equivariant r = (values r : Coefficient) := by
  rcases r with i | i | i | i
  · exact BlowupTwoDoubleExceptionalFewMarkings.equivariant_eq_ordinary i
  · exact BlowupTwoMixedExceptional.equivariant_eq_ordinary i
  · exact BlowupTwoPositivePlaneEnergyTwoSingletons.equivariant_eq_ordinary i
  · exact BlowupTwoPositivePlaneEnergyTwoPairs.equivariant_eq_ordinary i

/-- Regularity and specialization use the representative from the corresponding packet. -/
theorem specializes (r : Row) : Specializes (equivariant r) (values r) := by
  rcases r with i | i | i | i
  · exact BlowupTwoDoubleExceptionalFewMarkings.specializes i
  · exact BlowupTwoMixedExceptional.specializes i
  · exact BlowupTwoPositivePlaneEnergyTwoSingletons.specializes i
  · exact BlowupTwoPositivePlaneEnergyTwoPairs.specializes i

/-- The component of the original doubled-exceptional row number modulo 105 ranks
the marking list independently of the curve class. Each positive-plane class has five
singletons and one hundred ordered pairs in separate reports. -/
def number (q : SurfaceQuery .blowupTwo) : ℕ :=
  let d := BlowupTwoDoubleExceptionalFewMarkings.rowNumber q
  if q.beta 2 = 0 then
    if q.beta 0 = 1 then 210 + d % 105 else d
  else
    let c := if q.beta 2 = 2 then 0 else if q.beta 1 = 1 then 1 else 2
    if q.insertions.length = 1 then 315 + 5 * c + d % 105
    else 330 + 100 * c + (d % 105 - 5)

private theorem number_requests (r : Row) : number (requests r) = (rowIndex r).val := by
  rcases r with i | i | i | i
  · have h : ∀ j, (BlowupTwoDoubleExceptionalFewMarkings.requests j).beta 2 = 0 ∧
        (BlowupTwoDoubleExceptionalFewMarkings.requests j).beta 0 ≠ 1 := by decide +kernel
    change number (BlowupTwoDoubleExceptionalFewMarkings.requests i) = i.val
    simp only [number, (h i).1, (h i).2, if_true, if_false,
      BlowupTwoDoubleExceptionalFewMarkings.rowNumber_requests]
  · exact (by decide +kernel : ∀ j, number (BlowupTwoMixedExceptional.requests j) = 210 + j.val) i
  · exact (by decide +kernel : ∀ j,
      number (BlowupTwoPositivePlaneEnergyTwoSingletons.requests j) = 210 + (105 + j.val)) i
  · exact (by decide +kernel : ∀ j,
      number (BlowupTwoPositivePlaneEnergyTwoPairs.requests j) = 210 + (105 + (15 + j.val))) i

/-- Two packet indices cannot bind the same full ordered request. -/
theorem requests_injective : Function.Injective requests := by
  intro r s h
  apply rowIndex.injective
  exact Fin.ext ((number_requests r).symm.trans ((congrArg number h).trans (number_requests s)))

set_option maxRecDepth 8192 in
private theorem frame (r : Row) : FewMarkingQuery (requests r) ∧
    SurfaceTarget.blowupTwo.effective.energy (requests r).beta = 2 := by
  rcases r with i | i | i | i
  all_goals revert i; unfold FewMarkingQuery; decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
-- Elaborating the image of the four concrete packets expands their finite row types.
/-- The literal native inputs exhaust the independently specified mathematical frame. -/
theorem complete : Finset.univ.image requests = fewMarkingsAtEnergy .blowupTwo 2 := by
  apply Finset.eq_of_subset_of_card_le
  · intro q h
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp h
    exact (mem_fewMarkingsAtEnergy_iff _ _).mpr (frame r)
  · rw [Finset.card_image_of_injective _ requests_injective, Finset.card_univ,
      Fintype.card_congr rowIndex, Fintype.card_fin,
      card_fewMarkingsAtEnergy _ _ (by decide), card_dimensionShapes]
    decide +kernel

/-- A direct lookup checks the entire candidate request, including genus and both powers.
It also rejects requests outside the frame that happen to have the same row number. -/
def lookup (q : SurfaceQuery .blowupTwo) : Option Row :=
  if h : number q < 630 then
    let r := rowIndex.symm ⟨number q, h⟩
    if requests r = q then some r else none
  else none

/-- Lookup recovers every original packet row. -/
theorem lookup_requests (r : Row) : lookup (requests r) = some r := by
  simp only [lookup, number_requests, dif_pos (rowIndex r).isLt, Fin.eta,
    Equiv.symm_apply_apply, if_true]

/-- A successful lookup binds the complete request actually supplied by the user. -/
theorem lookup_eq_some_iff (q : SurfaceQuery .blowupTwo) (r : Row) :
    lookup q = some r ↔ requests r = q := by
  constructor
  · intro h
    unfold lookup at h
    split at h
    · dsimp only at h
      split at h
      · cases h
        assumption
      · cases h
    · cases h
  · rintro rfl
    exact lookup_requests r

/-- Each energy-two request has a unique native row, an exact two-character field value
and its unique ordinary specialization. -/
theorem unique_reference {q : SurfaceQuery .blowupTwo}
    (hq : q ∈ fewMarkingsAtEnergy .blowupTwo 2) :
    ∃! r : Row, lookup q = some r ∧ equivariant r = (values r : Coefficient) ∧
      ∀ a : ℚ, Specializes (equivariant r) a ↔ a = values r := by
  rw [← complete] at hq
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hq
  refine ⟨r, ⟨lookup_requests r, equivariant_eq_ordinary r, fun a ↦ ⟨?_, ?_⟩⟩, ?_⟩
  · exact fun ha ↦ ha.unique (specializes r)
  · rintro rfl
    exact specializes r
  · intro s hs
    exact requests_injective ((lookup_eq_some_iff _ s).mp hs.1)

end AxiomaticGW.GKM.BlowupTwoEnergyTwoNativeCoverage

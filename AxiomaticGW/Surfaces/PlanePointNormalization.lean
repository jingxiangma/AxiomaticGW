/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoZeroRemainder

/-!
# Plane normalization with counted primary points

An explicitly identified first-power insertion determines the canonical
normalization independently of the sorted occurrence selected internally.
Added primary points retain their multiplicity in the resulting descendant
query. These identities apply to the full normalizer, using its proved plane
calibration cancellation.
-/

@[expose] public section

namespace AxiomaticGW.SurfacePolynomialReduction

/-- The unique first-power occurrence is independent of insertion sorting. -/
theorem normalizedTerms_plane_of_onePsi (q : SurfaceAncestorKey .plane)
    (hg : 2 ≤ q.genus) (b : SurfaceBasisLabel .plane)
    (m : Multiset (SurfaceBasisLabel .plane))
    (hi : q.insertions = ⟨b, 1⟩ ::ₘ m.map (fun c ↦ ⟨c, 0⟩)) :
    normalizedTerms q = RationalTerms.rename Sum.inr
      (SurfaceFirstDescendant.terms q.genus q.beta b m) := by
  have hp : q.totalPsi = 1 := by
    simp only [SurfaceAncestorKey.totalPsi, hi, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_map, Function.comp_def, Multiset.map_const', Multiset.sum_replicate,
      nsmul_zero, add_zero]
  have hb : q.onePsiInsertion hp = ⟨b, 1⟩ := by
    have ht := q.onePsiInsertion_mem hp
    rw [hi, Multiset.mem_cons] at ht
    rcases ht with ht | ht
    · exact ht
    · obtain ⟨c, hc, he⟩ := Multiset.mem_map.mp ht
      have hz := q.onePsiInsertion_power hp
      rw [← he] at hz
      cases hz
  rw [normalizedTerms_plane_eq_direct, directNormalizedTerms, dif_pos ⟨hg, hp⟩]
  simp only [SurfaceAncestorKey.onePsiPrimaries, hb, hi, Multiset.erase_cons_head,
    Multiset.map_map, Function.comp_def, Multiset.map_id']

/-- Counted points do not change which occurrence carries the single psi. -/
theorem normalizedTerms_plane_onePsi_addPoints (q : SurfaceAncestorKey .plane)
    (hg : 2 ≤ q.genus) (b : SurfaceBasisLabel .plane)
    (m : Multiset (SurfaceBasisLabel .plane))
    (hi : q.insertions = ⟨b, 1⟩ ::ₘ m.map (fun c ↦ ⟨c, 0⟩)) (n : ℕ) :
    normalizedTerms (q.addPoints n) = RationalTerms.rename Sum.inr
      (SurfaceFirstDescendant.terms q.genus q.beta b (Multiset.replicate n .point + m)) := by
  apply normalizedTerms_plane_of_onePsi (q.addPoints n) hg b _
  simp only [SurfaceAncestorKey.addPoints, hi, Multiset.map_add, Multiset.map_replicate,
    Multiset.add_cons]

/-- A specified marking, with every other label and its multiplicity retained,
gives the canonical first-descendant terms without inspecting the internal sort. -/
theorem normalizedTerms_plane_onePsi_ofLabels (g : ℕ) (hg : 2 ≤ g)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity g S) (s : S)
    (beta : SurfaceTarget.plane.Curve) (a : S → SurfaceBasisLabel .plane) (n : ℕ) :
    normalizedTerms ((SurfaceAncestorKey.ofLabels g S h beta (Pi.single s 1) a).addPoints n) =
      RationalTerms.rename Sum.inr (SurfaceFirstDescendant.terms g beta (a s)
        (Multiset.replicate n .point + (Finset.univ.erase s).val.map a)) := by
  apply normalizedTerms_plane_onePsi_addPoints _ hg (a s) _
  have he : (Finset.univ : Finset S).val = s ::ₘ (Finset.univ.erase s).val := by
    rw [Finset.erase_val, Multiset.cons_erase (Finset.mem_univ s)]
  change (Finset.univ.val.map fun t ↦
    (⟨a t, (Pi.single s 1 : S → ℕ) t⟩ : SurfaceInsertion .plane)) = _
  rw [he, Multiset.map_cons, Pi.single_eq_same, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro t ht
  have hts : t ≠ s := (Finset.mem_erase.mp ht).1
  simp only [Pi.single_eq_of_ne hts, Function.comp_apply]

end AxiomaticGW.SurfacePolynomialReduction

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction

/-- The terminal first-power coefficient is the canonical descendant
expression with its original dimension check, for any requested variable. -/
theorem coefficient_residualTerms_plane_onePsi (v : Variable .plane)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (beta : SurfaceTarget.plane.Curve) (a : S → SurfaceBasisLabel .plane) (n : ℕ) :
    let q := (SurfaceAncestorKey.ofLabels 2 S h beta (Pi.single s 1) a).addPoints n
    RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
      (residualTerms q)) {v} =
      if q.DimensionCompatible then
        RationalTerms.coefficient (RationalTerms.rename Sum.inr
          (SurfaceFirstDescendant.terms 2 beta (a s)
            (Multiset.replicate n .point + (Finset.univ.erase s).val.map a))) {v}
      else 0 := by
  dsimp only
  rw [residualTerms]
  simp only [if_neg (show ¬((SurfaceAncestorKey.ofLabels 2 S h beta
    (Pi.single s 1) a).addPoints n).genus ≤ 1 from Nat.not_succ_le_self 1)]
  split_ifs with hd
  · simp only [RationalTerms.coefficient_affineSubstitute_term, Multiset.map_singleton,
      Multiset.sum_singleton, one_mul]
    rw [normalizedTerms_plane_onePsi_ofLabels 2 le_rfl S h s beta a n]
  · exact RationalTerms.coefficient_affineSubstitute_zero _ _

/-- Closed zero-remainder coefficients now expose the canonical descendant
queries and the separate classical unit correction used by the shifted system. -/
theorem remainderVertex_onePsi_plane_zero_normalized (v : Variable .plane) (n : ℕ)
    (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (a : S → SurfaceBasisLabel .plane) :
    let main := remainderVertex .plane v (planeCoefficientVertex v)
    let beta := SurfaceGenusZero.variableCurve v
    let q := (SurfaceAncestorKey.ofLabels 2 S h beta (Pi.single s 1) a).addPoints n
    main n 2 S h (Pi.single s 1) inferInstance 0 a =
      (if q.DimensionCompatible then
        RationalTerms.coefficient (RationalTerms.rename Sum.inr
          (SurfaceFirstDescendant.terms 2 beta (a s)
            (Multiset.replicate n .point + (Finset.univ.erase s).val.map a))) {v}
      else 0) -
      if a s = .unit then
        (n : ℚ) * main (n - 1) 2 S h 0 inferInstance 0 (Function.update a s .point)
      else 0 := by
  dsimp only
  rw [remainderVertex_onePsi_plane_zero, coefficient_residualTerms_plane_onePsi]

end AxiomaticGW.SurfaceGenusTwo

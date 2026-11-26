import AxiomaticGW.Surfaces.GenusTwoPsiReduction
import AxiomaticGW.Surfaces.PlaneGenusTwoLowPsi
import AxiomaticGW.Tautological.Fixtures.GenusTwoPsiPullbacksReplay

open AxiomaticGW SurfaceGenusTwo GluingExpression BelorousskiPandharipande

-- Added markings have power zero; each old occurrence retains its original power.
example : markedPowers (![2, 1] : Fin 2 → ℕ) 2 (some (some 0)) = 2 ∧
    markedPowers (![2, 1] : Fin 2 → ℕ) 2 (some (some 1)) = 1 ∧
    markedPowers (![2, 1] : Fin 2 → ℕ) 2 (some none) = 0 ∧
    markedPowers (![2, 1] : Fin 2 → ℕ) 2 none = 0 := by decide +kernel

-- Pulling back a square creates one negative tail, not a tail multiplied by its power.
example : (fundamentalCorrections GenusTwoPsiSquare.stableArity
    (fun _ : Fin 1 ↦ 2) 1).card = 1 ∧
    ((fundamentalCorrections GenusTwoPsiSquare.stableArity
      (fun _ : Fin 1 ↦ 2) 1).map Prod.fst).sum = -1 := by decide +kernel

-- The product has a separate correction at each of its two old labels.
example : (fundamentalCorrections GenusTwoPsiProduct.stableArity
    (fun _ : Fin 2 ↦ 1) 1).card = 2 ∧
    ((fundamentalCorrections GenusTwoPsiProduct.stableArity
      (fun _ : Fin 2 ↦ 1) 1).map Prod.fst).sum = -2 := by decide +kernel

-- The original genus-two tail is retained with its original negative relation coefficient.
example : (-3, GenusTwoPsiProduct.boundaryCotangentTerm 0) ∈
    GenusTwoPsiProduct.boundaryRemainder 0 := by
  apply Multiset.mem_add.mpr
  right
  apply (CotangentCombination.mem_pullback _ 0 _).mpr
  refine ⟨(-3, GenusTwoPsiProduct.boundaryCotangentTerm 0), ?_,
    (1, GenusTwoPsiProduct.boundaryCotangentTerm 0), Multiset.mem_singleton_self _, ?_⟩
  · apply Multiset.mem_map.mpr
    refine ⟨0, Finset.mem_val.mpr (Finset.mem_univ _), ?_⟩
    rw [GenusTwoPsiProduct.genusTwo_tail_coefficient]
  · norm_num

-- The isolated square reconstructs the exact independently held Sage pullback expression.
example : (CotangentCombination.relabel (ExtraMarkings.finEquiv 1 1)
    ({(1, markedFundamental GenusTwoPsiSquare.stableArity (fun _ : Fin 1 ↦ 2) 1)} +
      GenusTwoPsiSquare.boundaryRemainder 1)).strata =
    GenusTwoPsiPullbacks.squareTwo.strata := by
  rw [← GenusTwoPsiSquare.pullback_eq_leading_add_boundary]
  rfl

-- Descent holds at every marking count and every full curve class on each target.
example (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 1) → ℕ) (a : ExtraMarkings n (Fin 1) → SurfaceBasisLabel X)
    (t : ℚ × Multiset (SurfaceAncestorKey X))
    (ht : t ∈ boundaryReductionTerms X (GenusTwoPsiSquare.boundaryRemainder n) beta k a)
    (q : SurfaceAncestorKey X) (hq : q ∈ t.2) :
    q.totalPsi < 2 + ∑ s, k s :=
  (boundaryReductionTerms_dependency X _ (GenusTwoPsiSquare.boundaryRemainder_bounds n)
    beta k a ht q hq).2.2.1

example (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 2) → ℕ) (a : ExtraMarkings n (Fin 2) → SurfaceBasisLabel X)
    (t : ℚ × Multiset (SurfaceAncestorKey X))
    (ht : t ∈ boundaryReductionTerms X (GenusTwoPsiProduct.boundaryRemainder n) beta k a)
    (q : SurfaceAncestorKey X) (hq : q ∈ t.2) :
    q.genus = 2 ∧ q.totalPsi < 2 + ∑ s, k s ∧
      (q.beta = beta ∨ X.effective.energy q.beta < X.effective.energy beta) := by
  have h := boundaryReductionTerms_dependency X _ (GenusTwoPsiProduct.boundaryRemainder_bounds n)
    beta k a ht q hq
  exact ⟨h.1, h.2.2⟩

-- These exact boundary evaluations use the already certified degree-zero triple.
-- Geometric interpretation is supplied by the source-generator reduction theorems.
set_option maxRecDepth 20000 in
example : RationalTerms.eval (planeLowPsiValueWith (fun _ ↦ ![0, -1 / 960, 0]))
    (boundaryReductionTerms .plane (GenusTwoPsiProduct.boundaryRemainder 0)
      ![0] (fun _ ↦ 0) (![SurfaceBasisLabel.hyperplane, .unit])) = -1 / 320 := by
  decide +kernel

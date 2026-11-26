/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PolynomialReduction
public import AxiomaticGW.Tautological.PsiBoundaryExpansion
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Nat.Pairing

/-!
# Computable marking frames for symmetric ancestor queries

Canonical sorting gives a list representative of the existing insertion
multiset, without choosing an arbitrary representative of a quotient.
The sorted list retains multiplicities and pairs each state with its power.
Its finite marking frame can send the retained base label of a cotangent
expansion to any selected marking. The ordering is explicit local data,
not a new global order instance on mathematical insertions.
-/

@[expose] public section

namespace AxiomaticGW
namespace SurfaceBasisLabel

/-- Fixed basis numbering for executable insertion sorting. -/
def sortCode {X : SurfaceTarget} : SurfaceBasisLabel X → ℕ
  | .unit => 0
  | .hyperplane => 1
  | .exceptional i => i.val + 2
  | .point => X.blowups + 2

theorem sortCode_injective (X : SurfaceTarget) :
    Function.Injective (sortCode (X := X)) := by
  cases X <;> decide +kernel

end SurfaceBasisLabel

namespace SurfaceInsertion

/-- Pair the basis index and power injectively; neither coordinate is discarded. -/
def sortCode {X : SurfaceTarget} (s : SurfaceInsertion X) : ℕ :=
  Nat.pair s.label.sortCode s.psi

theorem sortCode_injective (X : SurfaceTarget) :
    Function.Injective (sortCode (X := X)) := by
  rintro ⟨a, m⟩ ⟨b, n⟩ h
  obtain ⟨hab, hmn⟩ := Nat.pair_eq_pair.mp h
  have hab' := SurfaceBasisLabel.sortCode_injective X hab
  cases hab'
  cases hmn
  rfl

/-- An explicit computational order, used only where a marking list is required. -/
abbrev sortOrder (X : SurfaceTarget) : LinearOrder (SurfaceInsertion X) :=
  LinearOrder.lift' sortCode (sortCode_injective X)

/-- Exposed structural implementation for kernel replay. Mathlib's insertion
sort bodies are not exposed across module boundaries; the following lemmas
identify this implementation with that existing public sorting API. -/
def insertForReplay {X : SurfaceTarget} (a : SurfaceInsertion X) :
    List (SurfaceInsertion X) → List (SurfaceInsertion X)
  | [] => [a]
  | b :: l => if a.sortCode ≤ b.sortCode then a :: b :: l else b :: insertForReplay a l

theorem insertForReplay_eq {X : SurfaceTarget} (a : SurfaceInsertion X)
    (l : List (SurfaceInsertion X)) :
    insertForReplay a l = List.orderedInsert (fun a b ↦ a.sortCode ≤ b.sortCode) a l := by
  induction l with
  | nil => rw [insertForReplay, List.orderedInsert_nil]
  | cons b l ih => rw [insertForReplay, List.orderedInsert_cons, ih]

/-- Insertion sort with a body available to downstream proof kernels. -/
def sortForReplay {X : SurfaceTarget} (l : List (SurfaceInsertion X)) :
    List (SurfaceInsertion X) := l.foldr insertForReplay []

theorem sortForReplay_eq {X : SurfaceTarget} (l : List (SurfaceInsertion X)) :
    sortForReplay l = List.insertionSort (fun a b ↦ a.sortCode ≤ b.sortCode) l := by
  induction l with
  | nil => rw [sortForReplay, List.foldr_nil, List.insertionSort_nil]
  | cons a l ih =>
      change insertForReplay a (sortForReplay l) = _
      rw [insertForReplay_eq, ih, List.insertionSort_cons]

end SurfaceInsertion

namespace SurfaceAncestorKey
variable {X : SurfaceTarget}

/-- A computable representative of the existing symmetric insertion multiset. -/
def orderedInsertions (q : SurfaceAncestorKey X) : List (SurfaceInsertion X) :=
  letI := SurfaceInsertion.sortOrder X
  Quot.liftOn q.insertions SurfaceInsertion.sortForReplay fun l m h ↦ by
    simp only [SurfaceInsertion.sortForReplay_eq]
    exact ((List.perm_insertionSort (· ≤ ·) l).trans
      (h.trans (List.perm_insertionSort (· ≤ ·) m).symm)).eq_of_pairwise'
        (List.pairwise_insertionSort _ _) (List.pairwise_insertionSort _ _)

/-- Structural insertion sorting agrees with the canonical multiset sort.
Its recursion also reduces in the proof kernel, unlike opaque accessibility
proofs used by the general merge implementation. -/
theorem orderedInsertions_eq_sort (q : SurfaceAncestorKey X) :
    letI := SurfaceInsertion.sortOrder X
    q.orderedInsertions = q.insertions.sort (· ≤ ·) := by
  letI := SurfaceInsertion.sortOrder X
  unfold orderedInsertions Multiset.sort
  exact Quot.inductionOn q.insertions fun l ↦
    (SurfaceInsertion.sortForReplay_eq l).trans
      (List.mergeSort_eq_insertionSort (fun a b : SurfaceInsertion X ↦ a ≤ b) l).symm

theorem orderedInsertions_coe (q : SurfaceAncestorKey X) :
    (q.orderedInsertions : Multiset (SurfaceInsertion X)) = q.insertions := by
  rw [q.orderedInsertions_eq_sort]
  exact Multiset.sort_eq _ _

theorem orderedInsertions_length (q : SurfaceAncestorKey X) :
    q.orderedInsertions.length = q.insertions.card := by
  rw [q.orderedInsertions_eq_sort]
  exact Multiset.length_sort _

theorem ordered_stable (q : SurfaceAncestorKey X) :
    StableArity q.genus (Fin q.orderedInsertions.length) := by
  simpa only [StableArity, Fintype.card_fin, q.orderedInsertions_length] using q.stable

/-- States and powers in the same ordered occurrence frame. -/
def orderedLabels (q : SurfaceAncestorKey X) : Fin q.orderedInsertions.length →
    SurfaceBasisLabel X := fun i ↦ (q.orderedInsertions.get i).label

/-- Cotangent powers in the same sorted occurrence frame as `orderedLabels`. -/
def orderedPowers (q : SurfaceAncestorKey X) : Fin q.orderedInsertions.length → ℕ :=
  fun i ↦ (q.orderedInsertions.get i).psi

/-- Sorting does not alter the original symmetric query. -/
theorem of_ordered_eq (q : SurfaceAncestorKey X) :
    ofLabels q.genus (Fin q.orderedInsertions.length) q.ordered_stable q.beta
      q.orderedPowers q.orderedLabels = q := by
  apply (eq_iff _ _).mpr
  refine ⟨rfl, rfl, ?_⟩
  change (Finset.univ : Finset (Fin q.orderedInsertions.length)).val.map
      q.orderedInsertions.get = q.insertions
  rw [Fin.univ_val_map, List.ofFn_get, q.orderedInsertions_coe]

/-- Every original insertion occurs at some numbered marking, with multiplicity retained. -/
theorem ordered_get_mem (q : SurfaceAncestorKey X) (i : Fin q.orderedInsertions.length) :
    q.orderedInsertions.get i ∈ q.insertions := by
  rw [← q.orderedInsertions_coe]
  exact List.get_mem _ _

theorem isPrimary_iff_orderedPowers (q : SurfaceAncestorKey X) :
    q.IsPrimary ↔ ∀ i, q.orderedPowers i = 0 := by
  constructor
  · intro h i
    exact h _ (q.ordered_get_mem i)
  · intro h s hs
    have he := congrArg SurfaceAncestorKey.insertions q.of_ordered_eq
    rw [← he] at hs
    change s ∈ (Finset.univ : Finset (Fin q.orderedInsertions.length)).val.map
      (fun i ↦ ⟨q.orderedLabels i, q.orderedPowers i⟩) at hs
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hs
    exact h i

/-- A nonprimary query has an explicitly enumerable positive-power marking. -/
theorem positiveMarkings_nonempty (q : SurfaceAncestorKey X) (h : ¬q.IsPrimary) :
    ((Finset.univ : Finset (Fin q.orderedInsertions.length)).filter
      (fun i ↦ 0 < q.orderedPowers i)).Nonempty := by
  by_contra hn
  apply h
  rw [isPrimary_iff_orderedPowers]
  intro i
  by_contra hi
  exact hn ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, Nat.pos_of_ne_zero hi⟩⟩

/-- The least numbered positive-power marking in the explicit sorted frame. -/
def positiveMark (q : SurfaceAncestorKey X) (h : ¬q.IsPrimary) :
    Fin q.orderedInsertions.length :=
  ((Finset.univ : Finset (Fin q.orderedInsertions.length)).filter
    (fun i ↦ 0 < q.orderedPowers i)).min' (q.positiveMarkings_nonempty h)

theorem positiveMark_pos (q : SurfaceAncestorKey X) (h : ¬q.IsPrimary) :
    0 < q.orderedPowers (q.positiveMark h) :=
  (Finset.mem_filter.mp (Finset.min'_mem _ (q.positiveMarkings_nonempty h))).2

/-- Total remaining cotangent degree is the reconstruction measure. -/
def totalPsi (q : SurfaceAncestorKey X) : ℕ := (q.insertions.map SurfaceInsertion.psi).sum

theorem totalPsi_ofLabels (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    (ofLabels g S h beta k a).totalPsi = ∑ s, k s := by
  simp only [totalPsi, ofLabels, Multiset.map_map, Function.comp_def]
  rfl

theorem sum_orderedPowers (q : SurfaceAncestorKey X) :
    ∑ i, q.orderedPowers i = q.totalPsi := by
  rw [← totalPsi_ofLabels q.genus _ q.ordered_stable q.beta
    q.orderedPowers q.orderedLabels, q.of_ordered_eq]

theorem totalPsi_eq_zero_iff (q : SurfaceAncestorKey X) :
    q.totalPsi = 0 ↔ q.IsPrimary := by
  rw [← q.sum_orderedPowers, q.isPrimary_iff_orderedPowers]
  simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left]

/-- The actual ancestor invariant is unchanged by canonical insertion sorting. -/
theorem eval_eq_ordered {C : StableCurveCohomology ℚ}
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C) (I : StableCurveIntegration C) (q : SurfaceAncestorKey X) :
    q.eval Omega P I = Omega.surfaceVertexValues P I q.genus
      (Fin q.orderedInsertions.length) q.ordered_stable q.beta
        q.orderedPowers q.orderedLabels :=
  (congrArg (SurfaceAncestorKey.eval Omega P I) q.of_ordered_eq).symm.trans
    (eval_ofLabels Omega P I _ _ _ _ _ _)

end SurfaceAncestorKey

namespace ExtraMarkings

/-- Send any retained base label to a specified numbered marking, preserving
the existing old-first ordering before the final transposition. -/
def markingFrame (base count : ℕ) (h : base ≤ count) (s : Fin base) (t : Fin count) :
    ExtraMarkings (count-base) (Fin base) ≃ Fin count :=
  let e := (ExtraMarkings.finEquiv (count-base) base).trans
    (finCongr (Nat.add_sub_of_le h))
  e.trans (Equiv.swap (e (ExtraMarkings.oldLabel (count-base) s)) t)

theorem markingFrame_oldLabel (base count : ℕ) (h : base ≤ count)
    (s : Fin base) (t : Fin count) :
    markingFrame base count h s t (ExtraMarkings.oldLabel (count-base) s) = t := by
  exact Equiv.swap_apply_left _ _

end ExtraMarkings
end AxiomaticGW

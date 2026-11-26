/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.BasicStrata
public import AxiomaticGW.Tautological.GraphIsomorphisms
public import AxiomaticGW.Tautological.StrataModule
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# External psi multiplication on decorated strata

Adding powers to labelled external legs defines an operation on graph
presentations, their isomorphism classes, and the free rational strata module.
It preserves graph incidence and automorphism factors and raises codimension
by the sum of the added powers. No common-refinement product is assumed.
Compatibility with a geometric realization is a separate requirement.
-/

@[expose] public section

namespace AxiomaticGW

open scoped BigOperators

namespace DecoratedStableGraph

variable {S : Type} [Fintype S]

/-- Add a psi monomial at the fixed external labels, retaining every other
graph and decoration field. This operation is executable on presentations. -/
def addLegPsi (G : DecoratedStableGraph S) (k : S → ℕ) : DecoratedStableGraph S :=
  { G with legPsiPower := fun s ↦ G.legPsiPower s + k s }

/-- A zero external monomial leaves the presentation unchanged. -/
theorem addLegPsi_zero (G : DecoratedStableGraph S) : G.addLegPsi 0 = G := by
  cases G
  simp only [addLegPsi, Pi.zero_apply, Nat.add_zero]

/-- Successive external monomials add their powers. -/
theorem addLegPsi_add (G : DecoratedStableGraph S) (k l : S → ℕ) :
    G.addLegPsi (k + l) = (G.addLegPsi k).addLegPsi l := by
  cases G
  simp only [addLegPsi, Pi.add_apply, Nat.add_assoc]

/-- External multiplication changes codimension by exactly the added powers. -/
theorem addLegPsi_codimension (G : DecoratedStableGraph S) (k : S → ℕ) :
    (G.addLegPsi k).codimension = G.codimension + ∑ s, k s := by
  change G.graph.edgeCount + G.kappaCodimension +
    (∑ s, (G.legPsiPower s + k s)) + G.halfEdgePsiCodimension = _
  rw [Finset.sum_add_distrib]
  unfold codimension legPsiCodimension
  omega

/-- Label-preserving isomorphisms transport external psi multiplication. -/
def Iso.addLegPsi {G H : DecoratedStableGraph S} (e : Iso G H) (k : S → ℕ) :
    Iso (G.addLegPsi k) (H.addLegPsi k) where
  graphIso := e.graphIso
  kappaPower_comm := e.kappaPower_comm
  legPsiPower_comm := fun s ↦ congrArg (fun n ↦ n + k s) (e.legPsiPower_comm s)
  halfEdgePsiPower_comm := e.halfEdgePsiPower_comm

/-- Cancelling identical external powers recovers the original isomorphism. -/
def Iso.removeLegPsi {G H : DecoratedStableGraph S} {k : S → ℕ}
    (e : Iso (G.addLegPsi k) (H.addLegPsi k)) : Iso G H where
  graphIso := e.graphIso
  kappaPower_comm := e.kappaPower_comm
  legPsiPower_comm := fun s ↦ Nat.add_right_cancel (e.legPsiPower_comm s)
  halfEdgePsiPower_comm := e.halfEdgePsiPower_comm

/-- Adding fixed external powers preserves all isomorphisms bijectively. -/
def addLegPsiIsoEquiv (G H : DecoratedStableGraph S) (k : S → ℕ) :
    Iso G H ≃ Iso (G.addLegPsi k) (H.addLegPsi k) where
  toFun e := e.addLegPsi k
  invFun := Iso.removeLegPsi
  left_inv _ := Iso.ext rfl
  right_inv _ := Iso.ext rfl

/-- External labels are fixed by graph automorphisms, so their added powers
do not change the automorphism normalization. -/
theorem addLegPsi_automorphismCount (G : DecoratedStableGraph S) (k : S → ℕ) :
    (G.addLegPsi k).automorphismCount = G.automorphismCount := by
  letI := isoFintype G G
  letI := isoFintype (G.addLegPsi k) (G.addLegPsi k)
  rw [automorphismCount_eq_card, automorphismCount_eq_card]
  exact (Fintype.card_congr (addLegPsiIsoEquiv G G k)).symm

end DecoratedStableGraph

namespace TautologicalStratum

variable {g : ℕ} {S : Type} [Fintype S]

/-- External psi multiplication on isomorphism classes of presentations. -/
def addLegPsi (x : TautologicalStratum g S) (k : S → ℕ) : TautologicalStratum g S :=
  Quotient.map (fun G ↦ ⟨G.1.addLegPsi k, G.2⟩) (fun _ _ h ↦ by
    obtain ⟨e⟩ := h
    exact ⟨e.addLegPsi k⟩) x

/-- Quotient multiplication computes on any chosen presentation. -/
theorem addLegPsi_mk (G : DecoratedStableGraph S) (hG : G.graph.totalGenus = g)
    (k : S → ℕ) :
    (mk G hG).addLegPsi k = mk (G.addLegPsi k) hG := rfl

/-- A zero monomial acts as the identity on strata. -/
theorem addLegPsi_zero (x : TautologicalStratum g S) : x.addLegPsi 0 = x := by
  refine Quotient.inductionOn x ?_
  intro G
  change Quotient.mk _ ⟨G.1.addLegPsi 0, G.2⟩ = Quotient.mk _ G
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  exact G.1.addLegPsi_zero

/-- The quotient action composes by addition of powers. -/
theorem addLegPsi_add (x : TautologicalStratum g S) (k l : S → ℕ) :
    x.addLegPsi (k + l) = (x.addLegPsi k).addLegPsi l := by
  refine Quotient.inductionOn x ?_
  intro G
  change Quotient.mk (decoratedStratumSetoid g S) ⟨G.1.addLegPsi (k + l), G.2⟩ =
    Quotient.mk (decoratedStratumSetoid g S) ⟨(G.1.addLegPsi k).addLegPsi l, G.2⟩
  apply congrArg (Quotient.mk (decoratedStratumSetoid g S))
  apply Subtype.ext
  exact G.1.addLegPsi_add k l

/-- Multiplication raises the presentation-independent codimension. -/
theorem addLegPsi_codimension (x : TautologicalStratum g S) (k : S → ℕ) :
    (x.addLegPsi k).codimension = x.codimension + ∑ s, k s := by
  refine Quotient.inductionOn x ?_
  intro G
  exact G.1.addLegPsi_codimension k

/-- Adding identical powers cannot identify distinct labelled strata. -/
theorem addLegPsi_injective (k : S → ℕ) :
    Function.Injective (fun x : TautologicalStratum g S ↦ x.addLegPsi k) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro G H heq
  change mk (G.1.addLegPsi k) G.2 = mk (H.1.addLegPsi k) H.2 at heq
  obtain ⟨e⟩ := Quotient.exact heq
  exact mk_eq_mk G.2 H.2 ⟨e.removeLegPsi⟩

/-- Multiplication of a one-vertex monomial agrees with ordinary exponent
addition, including its already present kappa decorations. -/
theorem addLegPsi_oneVertex (h : StableArity g S) (a : ℕ+ →₀ ℕ) (b k : S → ℕ) :
    (oneVertex g S h a b).addLegPsi k = oneVertex g S h a (b + k) := rfl

end TautologicalStratum

namespace StrataModule

variable {g : ℕ} {S : Type} [Fintype S]

/-- The rational linear action of an external psi monomial. It keeps each
raw gluing-pushforward coefficient unchanged. -/
noncomputable def mulLegPsi (k : S → ℕ) : StrataModule g S →ₗ[ℚ] StrataModule g S :=
  Finsupp.linearCombination ℚ (fun x ↦ basis (x.addLegPsi k))

/-- A basis coefficient is sent to the same coefficient of the shifted graph. -/
theorem mulLegPsi_single (k : S → ℕ) (x : TautologicalStratum g S) (q : ℚ) :
    mulLegPsi k (Finsupp.single x q) = q • basis (x.addLegPsi k) :=
  Finsupp.linearCombination_single _ _ _

/-- The module action agrees with the graph action on every basis stratum. -/
theorem mulLegPsi_basis (k : S → ℕ) (x : TautologicalStratum g S) :
    mulLegPsi k (basis x) = basis (x.addLegPsi k) := by
  rw [basis, mulLegPsi_single, one_smul]

/-- The zero monomial is the identity linear map. -/
theorem mulLegPsi_zero : (mulLegPsi (0 : S → ℕ) : StrataModule g S →ₗ[ℚ] _) =
    LinearMap.id := by
  apply Finsupp.lhom_ext
  intro x q
  rw [mulLegPsi_single, TautologicalStratum.addLegPsi_zero]
  simp only [basis, Finsupp.smul_single, smul_eq_mul, mul_one, LinearMap.id_apply]

/-- Composing module operations agrees with multiplying their monomials. -/
theorem mulLegPsi_add (k l : S → ℕ) :
    (mulLegPsi (k + l) : StrataModule g S →ₗ[ℚ] _) =
      (mulLegPsi l).comp (mulLegPsi k) := by
  apply Finsupp.lhom_ext
  intro x q
  simp only [mulLegPsi_single, TautologicalStratum.addLegPsi_add,
    LinearMap.comp_apply, map_smul, mulLegPsi_basis]

/-- A homogeneous combination is shifted by precisely the monomial degree. -/
theorem mulLegPsi_mem_degree (k : S → ℕ) {d : ℕ} {r : StrataModule g S}
    (hr : r ∈ degree d) : mulLegPsi k r ∈ degree (d + ∑ s, k s) := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨x, hx, rfl⟩ := hr
    rw [mulLegPsi_basis, ← hx, ← TautologicalStratum.addLegPsi_codimension]
    exact basis_mem_degree _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul q a _ ha => rw [map_smul]; exact Submodule.smul_mem _ q ha

/-- Above-dimension strata remain above dimension after external
multiplication. No geometric relation system is presumed complete. -/
theorem mulLegPsi_mem_dimensionRelations (k : S → ℕ) {r : StrataModule g S}
    (hr : r ∈ dimensionRelations) : mulLegPsi k r ∈ dimensionRelations := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨x, hx, rfl⟩ := hr
    rw [mulLegPsi_basis]
    apply basis_mem_dimensionRelations
    rw [TautologicalStratum.addLegPsi_codimension]
    omega
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul q a _ ha => rw [map_smul]; exact Submodule.smul_mem _ q ha

end StrataModule

end AxiomaticGW

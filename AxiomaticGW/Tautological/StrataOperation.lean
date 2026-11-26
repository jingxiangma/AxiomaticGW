/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.RelabelRealization
public import AxiomaticGW.Tautological.SeparatingRealization

/-!
# Contexts for transporting relations through decorated trees

A context has one variable input. It records label transport, external psi
multiplication and separating attachment of fixed decorated graphs. These
are the operations used by the genus-two power and rational-component
corrections in L24. Its finite graph action and rational linear map agree.
Kernel preservation is derived from the existing primitive realization
laws at the operations actually used, not assumed for the resulting row.
-/

@[expose] public section

namespace AxiomaticGW

/-- A typed unary context with an actual finite graph at each fixed attachment. -/
inductive StrataOperation (g₀ : ℕ) (S₀ : Type) [Fintype S₀] :
    (g : ℕ) → (S : Type) → [Fintype S] → Type 1 where
  | input : StrataOperation g₀ S₀ g₀ S₀
  | relabel {g : ℕ} {S T : Type} [Fintype S] [Fintype T]
      (e : S ≃ T) (x : StrataOperation g₀ S₀ g S) : StrataOperation g₀ S₀ g T
  | attach {g₁ g₂ : ℕ} {S T : Type} [Fintype S] [Fintype T]
      (x : StrataOperation g₀ S₀ g₁ (Option S))
      (fixed : DecoratedStableGraph (Option T)) (hf : fixed.graph.totalGenus = g₂)
      (h : StableArity g₂ (Option T)) : StrataOperation g₀ S₀ (g₁ + g₂) (S ⊕ T)
  | mulPsi {g : ℕ} {S : Type} [Fintype S]
      (k : S → ℕ) (x : StrataOperation g₀ S₀ g S) : StrataOperation g₀ S₀ g S

namespace StrataOperation

variable {g₀ g : ℕ} {S₀ S : Type} [Fintype S₀] [Fintype S]

/-- Stability is propagated from the input and the fixed attached components. -/
theorem stable (h₀ : StableArity g₀ S₀) {g : ℕ} {S : Type} [Fintype S] :
    (x : StrataOperation g₀ S₀ g S) → StableArity g S
  | @input _ _ _ => h₀
  | @relabel _ _ _ _ _ _ _ _ e x => (StableArity.equiv e).mp (x.stable h₀)
  | @attach _ _ _ _ _ _ _ _ _ x _ _ h => StableArity.separating (x.stable h₀) h
  | @mulPsi _ _ _ _ _ _ _ x => x.stable h₀

/-- The computable graph action retains all node powers at the attachments. -/
def graph {g : ℕ} {S : Type} [Fintype S] :
    StrataOperation g₀ S₀ g S → DecoratedStableGraph S₀ → DecoratedStableGraph S
  | @input _ _ _, G => G
  | @relabel _ _ _ _ _ _ _ _ e x, G => (x.graph G).relabel e
  | @attach _ _ _ _ _ _ _ _ _ x fixed _ _, G => (x.graph G).separating fixed
  | @mulPsi _ _ _ _ _ _ k x, G => (x.graph G).addLegPsi k

/-- Attach two chosen finite labels; surviving labels are left first, then right. -/
def join {g₁ g₂ m n : ℕ} (x : StrataOperation g₀ S₀ g₁ (Fin (m + 1)))
    (fixed : DecoratedStableGraph (Fin (n + 1))) (hf : fixed.graph.totalGenus = g₂)
    (h : StableArity g₂ (Fin (n + 1))) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    StrataOperation g₀ S₀ (g₁ + g₂) (Fin (m + n)) :=
  ((x.relabel (finSuccEquiv' i)).attach (fixed.relabel (finSuccEquiv' j)) hf
    ((StableArity.equiv (finSuccEquiv' j)).mp h)).relabel finSumFinEquiv

/-- The graph action has the genus indicated by the typed construction. -/
theorem graph_totalGenus (x : StrataOperation g₀ S₀ g S)
    (G : DecoratedStableGraph S₀) (hG : G.graph.totalGenus = g₀) :
    (x.graph G).graph.totalGenus = g := by
  induction x with
  | input => exact hG
  | relabel e x ih => exact ih
  | attach x fixed hf h ih =>
    exact (StableGraphCode.separating_totalGenus _ _).trans (congrArg₂ (· + ·) ih hf)
  | mulPsi k x ih => exact ih

/-- The rational map is the composition of the established primitive operations. -/
noncomputable def map {g : ℕ} {S : Type} [Fintype S] : StrataOperation g₀ S₀ g S →
    StrataModule g₀ S₀ →ₗ[ℚ] StrataModule g S
  | @input _ _ _ => LinearMap.id
  | @relabel _ _ _ _ _ _ _ _ e x => (StrataModule.relabel e).comp x.map
  | @attach _ _ _ _ _ _ _ _ _ x fixed hf _ =>
      (StrataModule.separating.flip (StrataModule.basis (.mk fixed hf))).comp x.map
  | @mulPsi _ _ _ _ _ _ k x => (StrataModule.mulLegPsi k).comp x.map

/-- A finite input presentation is carried to precisely the computed graph. -/
theorem map_basis (x : StrataOperation g₀ S₀ g S)
    (G : DecoratedStableGraph S₀) (hG : G.graph.totalGenus = g₀) :
    x.map (StrataModule.basis (.mk G hG)) =
      StrataModule.basis (.mk (x.graph G) (x.graph_totalGenus G hG)) := by
  induction x with
  | input => rfl
  | relabel e x ih =>
    change StrataModule.relabel e (x.map _) = _
    rw [ih, StrataModule.relabel_basis]
    rfl
  | attach x fixed hf h ih =>
    change StrataModule.separating (x.map _) (StrataModule.basis (.mk fixed hf)) = _
    rw [ih, StrataModule.separating_basis_basis]
    rfl
  | mulPsi k x ih =>
    change StrataModule.mulLegPsi k (x.map _) = _
    rw [ih, StrataModule.mulLegPsi_basis]
    rfl

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- Only the primitive compatibilities along this particular context are required. -/
def Compatible (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (P : PsiClasses C) (h₀ : StableArity g₀ S₀)
    {g : ℕ} {S : Type} [Fintype S] :
    StrataOperation g₀ S₀ g S → Prop
  | @input _ _ _ => True
  | @relabel _ _ _ g S T _ _ e x =>
      x.Compatible A F P h₀ ∧
        (A g S).RelabelCompatible (A g T) (x.stable h₀) ((x.relabel e).stable h₀) e
  | @attach _ _ _ g₁ g₂ S T _ _ x fixed hf h =>
      x.Compatible A F P h₀ ∧
        (A g₁ (Option S)).SeparatingCompatible (A g₂ (Option T)) (A (g₁ + g₂) (S ⊕ T))
          F (x.stable h₀) h
  | @mulPsi _ _ _ g S _ _ x =>
      x.Compatible A F P h₀ ∧ (A g S).LegPsiCompatible P (x.stable h₀)

/-- A source class relation vanishes after this actual decorated graph operation. -/
theorem map_vanishes (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (P : PsiClasses C) (h₀ : StableArity g₀ S₀)
    (x : StrataOperation g₀ S₀ g S) (hc : x.Compatible A F P h₀)
    (r : StrataModule g₀ S₀) (hr : (A g₀ S₀).map r = 0) :
    (A g S).map (x.map r) = 0 := by
  induction x with
  | input => exact hr
  | @relabel g S T _ _ e x ih =>
    change (A g T).map (StrataModule.relabel e (x.map r)) = 0
    rw [StrataRealization.map_relabel _ _ _ _ _ hc.2, ih hc.1, map_zero]
  | @attach g₁ g₂ S T _ _ x fixed hf h ih =>
    change (A (g₁ + g₂) (S ⊕ T)).map
      (StrataModule.separating (x.map r) (StrataModule.basis (.mk fixed hf))) = 0
    rw [StrataRealization.map_separating _ _ _ _ _ _ hc.2, ih hc.1,
      TensorProduct.zero_tmul, map_zero]
  | mulPsi k x ih =>
    change (A _ _).map (StrataModule.mulLegPsi k (x.map r)) = 0
    rw [StrataRealization.map_mulLegPsi _ _ _ hc.2, ih hc.1, zero_mul]

end StrataOperation
end AxiomaticGW

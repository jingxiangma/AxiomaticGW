module

public import AxiomaticGW.Surfaces.ScalarPointRootParts
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace AxiomaticGWTest.ScalarPointRootParts

open AxiomaticGW

abbrev X := SurfaceTarget.hirzebruchOne

def unitVertex : ℕ → SurfaceCotangentVertexValues X ℚ :=
  fun _ _ _ _ _ _ _ _ _ ↦ 1

def leaf : GluingExpression 1 (Option (Fin 0)) :=
  .fundamental 1 (Option (Fin 0)) (by
    norm_num only [StableArity, Fintype.card_option, Fintype.card_fin])

def pair : GluingExpression 2 (Fin 0 ⊕ Fin 0) := .separating leaf leaf

/-- Point count two retains its nontrivial binomial factor and exceptional sign. -/
theorem signed_binomial_slot :
    pair.scalarPointRootSeparating X unitVertex (fun _ ↦ 0, fun _ ↦ 0)
      ((inferInstance : DecidableEq (Option (Fin 0))),
        (inferInstance : DecidableEq (Option (Fin 0)))) 2 (![0, 0], ![0, 0]) (.exceptional 0) (1, 1)
      (Sum.elim Fin.elim0 Fin.elim0) = -2 := by
  decide +kernel

def loopSource : GluingExpression 1 (Option (Option (Fin 1))) :=
  .fundamental 1 (Option (Option (Fin 1))) (by
    norm_num only [StableArity, Fintype.card_option, Fintype.card_fin])

def loop : GluingExpression 2 (Fin 1) := .nonseparating loopSource

/-- Self-gluing retains the signed state on the same complete curve. -/
theorem signed_nonseparating_slot :
    loop.scalarPointRootNonseparating X unitVertex (fun _ ↦ 0)
      (inferInstance : DecidableEq (Option (Option (Fin 1))))
      ![1, 1] 3 (.exceptional 0) (fun _ ↦ .hyperplane) = -1 := by
  decide +kernel

/-- A nonseparating root contributes no separating slot. -/
theorem nonseparating_has_no_separating_slot :
    loop.scalarPointRootSeparating X unitVertex (fun _ ↦ 0)
      (inferInstance : DecidableEq (Option (Option (Fin 1))))
      3 (![0, 0], ![1, 1]) .hyperplane (1, 2) (fun _ ↦ .point) = 0 := rfl

/-- External relabelling keeps the existing insertion pullback direction. -/
theorem relabel_preserves_slots {g : ℕ} {S T : Type} [Fintype S] [Fintype T]
    (e : S ≃ T) (x : GluingExpression g S)
    (d : x.CotangentDecoration) (l : x.DecidableLabels) (n : ℕ)
    (split : X.Curve × X.Curve) (b : SurfaceBasisLabel X) (ij : ℕ × ℕ)
    (a : T → SurfaceBasisLabel X) :
    (x.relabel e).scalarPointRootSeparating X unitVertex d l n split b ij a =
      x.scalarPointRootSeparating X unitVertex d l n split b ij (a ∘ e) := rfl

end AxiomaticGWTest.ScalarPointRootParts

/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.FixedGraphSupport
public import AxiomaticGW.GKM.RationalLocalizationVertex
public import AxiomaticGW.GKM.EllipticLocalizationVertex
public import AxiomaticGW.GKM.GenusTwoLocalizationVertex
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.FinRange

/-! # Source-curve factors on an imported GKM graph

Incident flags retain their edge indices, ends, orientations and sheet numbers.
Original marking numbers determine the order of external descendants. The rational
unstable conventions are evaluated only for their three positive-edge shapes.
-/

@[expose] public section
namespace AxiomaticGW.GKM.SurfaceLocalizationVertex
open CurveConventionCertificate EquivariantCoefficients GenusTwoVertexHodgeReduction

variable {X : SurfaceTarget} {n r v e a : ℕ} {tables : Tables X n r}

/-- All incident half-edges in source-edge order. Parallel covers remain distinct. -/
def flagsAt (G : FixedGraphSupport tables v e) (p : Fin v) : List (Fin e × Fin 2) :=
  ((List.finRange e).product (List.finRange 2)).filter fun z ↦ G.endpoint z.1 z.2 = p

/-- Each half-edge occurs at its own vertex. -/
theorem mem_flagsAt (G : FixedGraphSupport tables v e) (p : Fin v) (z : Fin e × Fin 2) :
    z ∈ flagsAt G p ↔ G.endpoint z.1 z.2 = p := by
  obtain ⟨i, j⟩ := z
  have h : (i, j) ∈ (List.finRange e).product (List.finRange 2) :=
    List.mem_product.mpr ⟨List.mem_finRange i, List.mem_finRange j⟩
  simp only [flagsAt, List.mem_filter, h, true_and, decide_eq_true_eq]

/-- No indexed half-edge contributes twice to the same local factor. -/
theorem flagsAt_nodup (G : FixedGraphSupport tables v e) (p : Fin v) :
    (flagsAt G p).Nodup :=
  ((List.nodup_finRange e).product (List.nodup_finRange 2)).filter _

/-- Cotangent powers in the order of the original external marking numbers. -/
def powersAt (mark : Fin a → Fin v) (power : Fin a → ℕ) (p : Fin v) : List ℕ :=
  ((List.finRange a).filter fun j ↦ mark j = p).map power

/-- The outgoing flag character is divided by the actual covering multiplicity.
Orientation is read from the source fixed-point image and the imported target edge. -/
noncomputable def outgoing (G : FixedGraphSupport tables v e) (z : Fin e × Fin 2) : Coefficient :=
  let edge := tables.edges (G.edgeIndex z.1)
  let w := character edge.weight
  (if G.image (G.endpoint z.1 z.2) = edge.source then w else -w) / (G.cover z.1).val

/-- The two ends of any covered edge in an accepted fan have opposite outgoing characters.
This holds for either orientation and every positive multiplicity. -/
theorem outgoing_opposite {request : Request X n r} (h : Accepts request tables)
    (G : FixedGraphSupport tables v e) (i : Fin e) :
    outgoing G (i,1) = -outgoing G (i,0) := by
  have distinct := (h.edge_endpoints (G.edgeIndex i)).1.symm
  rcases G.incident i with ⟨h₀,h₁⟩ | ⟨h₀,h₁⟩
  · simp only [outgoing, h₀, h₁, distinct, if_false, if_true, neg_div]
  · simp only [outgoing, h₀, h₁, distinct, if_false, if_true, neg_div, neg_neg]

/-- Genus-zero through genus-two native source factor. A zero tangent or flag character,
a vanishing unstable smoothing denominator, an unstable contracted input, or a genus outside
the reconstructed range returns none. -/
noncomputable def factor? {L : Type*} [Field L] [DecidableEq L] (seed : ↥seeds → ℚ) (g : ℕ)
    (m : List ℕ) (u v : L) (flags : List L) : Option L :=
  if u = 0 ∨ v = 0 ∨ 0 ∈ flags then none else
  match g, m, flags with
  | 0, [], [w] => some (w / (u * v))
  | 0, [d], [w] => some ((-w)^d / (u * v))
  | 0, [], [w, t] => if w + t = 0 then none else some ((w + t)⁻¹ / (u * v))
  | 0, p, ws =>
    if 3 ≤ p.length + ws.length then some (RationalLocalizationVertex.closed p.get u v ws.get)
    else none
  | 1, [], [] => none
  | 1, p, ws => some (EllipticHodge.source p u v ws.get EllipticHodge.nativeMoment)
  | 2, p, ws => some (GenusTwoLocalizationVertex.reduced seed p u v ws.get)
  | _, _, _ => none

/-- The numerical source on one indexed fixed vertex. The two tangent directions
come from its own packet entry, including when its flags cover different invariant curves. -/
noncomputable def atVertex? (G : FixedGraphSupport tables v e) (genus : Fin v → ℕ)
    (mark : Fin a → Fin v) (power : Fin a → ℕ) (p : Fin v) (seed : ↥seeds → ℚ) :
    Option Coefficient := by
  classical
  exact factor? seed (genus p) (powersAt mark power p)
    (character (tables.tangent (G.image p) 0)) (character (tables.tangent (G.image p) 1))
    ((flagsAt G p).map (outgoing G))

end AxiomaticGW.GKM.SurfaceLocalizationVertex

/- Computed genus-two vertex integrals for X2 in class [1, 0, 0].
Ordered insertions: [['E1', 3]].
Report SHA256: b4f9fd9de26dd7a6b0ba783023060e26964bc872b94b6e6cfb307076a53223a4.
The eight seed values come from admcycles. The geometric interpretation uses the
explicit forgetful and dimension equations. The enclosing graph sum is outside this certificate. -/
module

public import AxiomaticGW.GKM.GenusTwoVertexHodgeReduction

@[expose] public section
namespace AxiomaticGW.GKM.ExceptionalGenusTwoVertexValues
open GenusTwoVertexHodgeReduction

/-- The eight literal seed integrals in the native admcycles ledger. -/
def seed (k : ↥seeds) : ℚ :=
  match k.val with
  | (0, 0, [4]) => (1 / 1152)
  | (0, 0, [2, 3]) => (29 / 5760)
  | (0, 0, [2, 2, 2]) => (7 / 240)
  | (0, 1, [3]) => (1 / 480)
  | (0, 1, [2, 2]) => (5 / 576)
  | (0, 2, [2]) => (7 / 5760)
  | (1, 1, [2]) => (7 / 2880)
  | (1, 2, []) => (1 / 5760)
  | _ => 0

/-- The supplied seed keys span the complete reduced vertex domain. -/
theorem seed_support : seeds = ([(0, 0, [4]),
    (0, 0, [2, 3]),
    (0, 0, [2, 2, 2]),
    (0, 1, [3]),
    (0, 1, [2, 2]),
    (0, 2, [2]),
    (1, 1, [2]),
    (1, 2, [])] : List (ℕ × ℕ × List ℕ)).toFinset := by decide +kernel

/-- Every distinct marked Hodge integral consumed during the held graph sum. -/
def vertices : List (Fin 3 × Fin 3 × List ℕ × ℚ) :=
  [(0, 0, [2, 3], (29 / 5760)),
    (0, 0, [4], (1 / 1152)),
    (0, 1, [1, 3], (1 / 160)),
    (0, 1, [3], (1 / 480)),
    (0, 2, [0, 3], (7 / 5760)),
    (0, 2, [2], (7 / 5760)),
    (1, 1, [0, 3], (7 / 2880)),
    (1, 1, [2], (7 / 2880)),
    (1, 2, [1], (1 / 2880)),
    (2, 2, [0], 0)]

/-- Compare one actual input and value with the checked vertex recurrence. -/
def agrees (r : Fin 3 × Fin 3 × List ℕ × ℚ) : Bool :=
  if h : r.1 ≤ r.2.1 then decide (evaluate seed r.1 r.2.1 h r.2.2.1 = r.2.2.2) else false

theorem checked : vertices.all agrees = true := by decide +kernel

theorem vertex_sound (i j : Fin 3) (hij : i ≤ j) (p : List ℕ) (v : ℚ)
    (hr : (i, j, p, v) ∈ vertices) (V : List ℕ → ℚ) (h : Recurrences i j V)
    (hs : ∀ ps (hk : ((i : ℕ), (j : ℕ), ps) ∈ seeds), seed ⟨_, hk⟩ = V ps) :
    V p = v := by
  have hv := List.all_eq_true.mp checked _ hr
  simpa only [agrees, dif_pos hij, decide_eq_true_eq, evaluate_sound seed i j hij V h hs] using hv

end AxiomaticGW.GKM.ExceptionalGenusTwoVertexValues

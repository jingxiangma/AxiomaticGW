# Implementation progress

This file is the durable implementation record for AxiomaticGW. The [roadmap](AxiomaticGWRoadmap.md) remains the source of truth for milestone status and ordering; this record captures how a completed implementation was delivered and verified.

Each entry records the accepted scope, implementation commit, a link to the canonical mathematics-to-Lean map, principal API, verification evidence, deliberately deferred work, and the next gate. Git history remains the authoritative source for the exact diff.

## 2026-07-17: M3 and M4 completed

**Status:** Complete. M5 is ready to start.

**Implementation commit:** [`0095d91`](https://github.com/jingxiangma/AxiomaticGW/commit/0095d91f3434b42332670725307c5d36e06d330a), `Complete M3 and M4 CohFT foundations`.

### Accepted scope

- Finish the primitive stable-curve interface selected by design decision D9, including degree preservation and the immediate forget/glue coherence laws.
- Extract the genus-zero Frobenius algebra from a full CohFT and prove its commutativity, unit laws, metric invariance, WDVV, and associativity.
- Construct the scalar topological part under coherent connected degree-zero data.
- Prove that every scalar-valued topological CohFT agrees in every stable genus and arity with the canonical theory of its extracted Frobenius algebra.
- Validate the construction through the constant degree-zero model and its public API regression tests.

### Delivered API

- `StableCurveCohomology` now requires degree-preserving primitive maps and the immediate repeated-forget, forget/nonseparating, and forget/separating compatibilities.
- `ConnectedDegreeZero.scalar` coherently projects a CohFT class to a scalar.
- `GenusZeroCohFT` packages the derived genus-zero restriction without replacing the all-genus `CohFT` as the primary object.
- `GenusZeroCohFT.product` and its derived theorems provide Frobenius extraction, WDVV, and associativity.
- `CohFT.topologicalPart` constructs the general degree-zero topological theory.
- `TopologicalCohFT.classification` proves the full stable-arity Frobenius round trip.

### Mathematics-to-Lean map

The canonical mathematics-to-Lean map records the [M3](../MathematicsToLean.md#m3-stable-curves-and-gluing) and [M4](../MathematicsToLean.md#m4-full-unital-cohft) note sections, source modules, principal declarations, implemented boundaries, and deliberate deferrals for this milestone.

### Verification

The implementation passed the following local gates before it was committed:

```bash
lake build
lake test
lake lint
git diff --check
rg -n '\b(sorry|admit)\b' AxiomaticGW AxiomaticGWTest
```

The source scan returned no placeholders. The pushed commit also passed:

- [GitHub Actions CI run 10](https://github.com/jingxiangma/AxiomaticGW/actions/runs/29560104676), which built, tested, and linted the project.
- [API documentation run 7](https://github.com/jingxiangma/AxiomaticGW/actions/runs/29560104656), which built the project and deployed the generated Lean API documentation.

### Deferred by design

- Stable graphs, arbitrary iterated gluing, and independence of contraction order remain in the later stable-graph or modular-operad layer specified by D9. They are not unfinished M3 acceptance items.
- M5 structures were not scaffolded speculatively. Tautological classes, pushforwards, and integration will be introduced only with the first theorem that consumes them.

### Next gate

Begin M5 with the smallest useful stable-curve tautological extension: marked `psi`-classes and their relabelling and pullback behavior. Add integration, pushforward, boundary, kappa, and Hodge data only as ancestor constructions begin to require them.

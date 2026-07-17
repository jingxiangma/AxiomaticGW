# Implementation progress

This file is the durable implementation record for AxiomaticGW. The [roadmap](AxiomaticGWRoadmap.md) remains the source of truth for milestone status and ordering; this record captures how a completed implementation was delivered and verified.

Each entry records the accepted scope, implementation commit, a link to the canonical mathematics-to-Lean map, principal API, verification evidence, deliberately deferred work, and the next gate. Git history remains the authoritative source for the exact diff.

## 2026-07-17: Core theorem integration and point-target stable-curve block

**Status:** Implemented and locally verified.

**Implementation commit:** This entry is delivered in the same commit as the implementation.

### Accepted scope

- Keep cohomology-valued GW classes coefficientwise under D14 and derive completed numerical and finite-free state operations without adding unused completed-tensor structures.
- Remove the abstract `QuantumProductFamily`; derive small WDVV and associativity directly from `CurveClassGW` gluing.
- Construct descendant and ancestor potentials from invariants with canonical occurrence labels and reciprocal multiplicity-factorial weights.
- Construct the formal big product from genus-zero primary invariants and prove its zero-background specialization; defer nonzero-background associativity until the higher-point boundary relation is formalized.
- Isolate the point target as stable-curve intersection theory and state the full labelled DVV recursion as an explicit higher tautological hypothesis.

### Delivered API

- `CurveClassGW.smallProductCoefficient_wdvv`, `smallProductCoefficient_assoc`, and the coefficientwise unit and commutativity theorems.
- `MvPowerSeries.pderiv_commute`, `iteratedPDeriv`, `stablePart`, and `insertionDerivative`.
- `CurveClassGW.descendantPotential`, `ancestorPotential`, `potentials`, and `DescendantAncestorComparison.descendantPotential_eq_ancestor_add_boundary`.
- `CurveClassGW.formalBigProduct`, its metric characterization, and `formalBigProduct_zero`.
- `PsiClasses.monomial_degree` and the `PointTarget` primary, ancestor, intersection, WDVV, initial-value, and `DVVRecursion` declarations.

### Verification

The implementation passed:

```bash
lake build
lake test
lake lint
git diff --check
rg -n '\b(sorry|admit)\b' AxiomaticGW AxiomaticGWTest
```

Public regression examples exercise derived small associativity, the formal-big-to-small specialization, point-target normalization and dimension vanishing, and the DVV double-factorial coefficient.

The placeholder scan returned no matches. The Markdown audit also found no unbalanced standalone display-math delimiters or display delimiters attached to prose, preserving Typora-compatible math blocks.

### Deferred by design

- Big WDVV and formal big-product associativity require the genus-zero boundary relation with arbitrary background markings.
- Global string and dilaton PDEs require an explicit choice of unstable zero-, one-, and two-point conventions; the implemented equations remain honest stable-sector laws.
- A concrete cohomology model of `Mbar`, a proof of `PointTarget.DVVRecursion`, and actual stable-map moduli and virtual classes remain geometric realization work.

### Next gate

Formalize the higher-point genus-zero boundary relation needed for big WDVV, or construct a concrete stable-curve cohomology realization that proves the point initial values and DVV. Either direction now extends a theorem boundary rather than adding a speculative carrier structure.

## 2026-07-17: M5--M9 axiomatic interfaces and M10 realization boundary

**Status:** Implemented and locally verified. The core axiomatic data types are present through total free energies; the remaining work is theorem integration and concrete realization rather than another speculative structure layer.

**Implementation commit:** This entry is delivered in the same commit as the implementation.

### Accepted scope

- Add exactly the stable-curve tautological operations consumed by ancestors: psi classes, integration, forgetful pushforward, projection, rational-tail correction, and kappa classes.
- Add positive locally finite effective curve classes and a coefficientwise primary GW theory with grading, normalization, gluing, negative-degree vanishing, and optional divisor data.
- Implement the beta-preserving completed Novikov ring and the first fixed-beta quantum-product interface.
- Keep stable-map descendants distinct from stable-curve ancestors and expose the stabilization boundary correction explicitly.
- Use mathlib multivariable power series and Laurent series for formal variables, genus potentials, and the total free energy.
- Stop the geometric layer at an algebraic output package; do not invent unused stack, obstruction-theory, or virtual-cycle carriers.

### Delivered API

- `PsiClasses`, `StableCurveIntegration`, `ForgetfulPushforward`, `PsiForgetFormula`, `CohFT.ancestor`, and the constant tautological model.
- `EffectiveCurveMonoid`, `GradedStateSpace`, `CurveClassGW`, `GWDivisorAxiom`, and `constantCurveClassGW.theory`.
- `NovikovSeries`, its convolution ring, monomials, `ofMonoidAlgebra`, and `CurveClassGW.smallProductCoefficient`.
- `StableMapDescendants`, `DescendantAncestorComparison`, and the integrated descendant--ancestor theorem.
- `MvPowerSeries.pderiv`, `GWPotentials`, `totalFreeEnergy`, exact genus-coefficient theorems, and `DescendantEquationLaws`.
- `VirtualGWPackage` and its projections to the realized primary, descendant, and comparison layers.

### Mathematics-to-Lean map

The canonical map now records source modules and principal declarations for [M5 through M10](../MathematicsToLean.md#m5-tautological-classes-and-ancestors), including the exact boundary between implemented interfaces and future theorems or geometry.

### Verification

The implementation passed:

```bash
lake build
lake test
lake lint
git diff --check
rg -n '\b(sorry|admit)\b' AxiomaticGW AxiomaticGWTest
```

The placeholder scan returned no matches. Public regression examples cover ancestors, finite curve-class splittings, the beta-zero primary model, Novikov monomial multiplication, Laurent genus coefficients, and commutation of distinct formal partial derivatives.

### Deferred by design

- The construction of an ordinary Novikov-valued CohFT by scalar extension from `CurveClassGW` remains outside the coefficientwise scope, and big associativity still requires the higher-point boundary theorem.
- Hodge classes, general decorated stable graphs, and arbitrary tautological relations remain theorem-driven extensions.
- Differential forms of every correlator equation and the exponential total potential require additional formal-series theorems or a stronger mixed completion.
- Actual moduli stacks, virtual fundamental classes, and concrete projective-target packages remain outside the current mathematical foundations.

### Next gate

Derive GW WDVV coefficientwise, construct concrete potentials without imposing a false algebraic scalar extension on arbitrary cohomology targets, and use the point target as the preferred stable-curve regression instance.

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

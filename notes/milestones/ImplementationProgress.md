# Implementation progress

This file is the durable implementation record for AxiomaticGW. The [roadmap](AxiomaticGWRoadmap.md) remains the source of truth for milestone status and ordering; this record captures how a completed implementation was delivered and verified.

Each entry records the accepted scope, implementation commit, a link to the canonical mathematics-to-Lean map, principal API, verification evidence, deliberately deferred work, and the next gate. Git history remains the authoritative source for the exact diff.

Older entries preserve their then-current scope and next gate; explicit follow-up paragraphs record work completed by later revisions.

## 2026-07-18: Simplifier stability and mathematical-comment audit

**Status:** Implemented and locally verified.

### Review evidence

The proof audit covered every `simp`, `simpa`, `simp_all`, and simplifier-enabled Aesop call in all 42 production Lean modules and the public API regression tests. The terminology audit separately inspected every module docstring, public declaration docstring, and explanatory inline comment. Mathematical vocabulary was cross-checked against the project-local arXiv TeX sources for two-dimensional TFTs, CohFT/Gromov--Witten theory and quantum products, point-target psi-class intersections and DVV, and Givental's descendant--ancestor formalism.

### Findings and revisions

- **Medium:** 227 unrestricted simplifier calls depended on the evolving package and mathlib simp sets. Every production and test call now uses an explicit `simp only`, `simpa only`, or `simp_all only` set; the single explicit `simp_rw` already names its rewrite rules.
- **Medium:** Novikov multiplication associativity delegated the finite splitting bijection to Aesop with a broad simp set. The proof now states the forward and inverse membership calculations explicitly and uses associativity of curve-class addition transparently.
- **Low:** Comments used several vague or nonstandard phrases, including “flat identity,” “curve ancestors,” “Frobenius correlator theories,” “curve-class theory,” and “coefficient product,” while some stabilization/Fock comments overstated supplied carrier data. They now use flat unit, stable-curve ancestors, Frobenius-algebra correlators, fixed-class small-quantum-product contributions, and explicit supplied-data qualifications.
- No critical or high-severity issue was found. No declaration name, theorem statement, assumption, simp attribute, instance, coercion, or import changed.

### Mathematical effect

The represented definitions, theorem propositions, hypotheses, normalizations, and public APIs are unchanged. The Novikov proof exposes the same reassociation bijection previously discharged by automation. Comment changes make the formal limitations of optional geometric and Fock-space carriers more precise without strengthening them.

### Verification

Direct elaboration passed for every changed Lean module, followed by:

```bash
lake build
lake test
lake lint
git diff --check
git diff --cached --check
rg --pcre2 -n '\b(?:simp|simpa|simp_all)(?! only)(?:\s|\[|$)' AxiomaticGW AxiomaticGWTest -g '*.lean'
rg -n '\b(sorry|admit)\b|^\s*(axiom|unsafe|opaque)\b|sorryAx|admitAx' AxiomaticGW AxiomaticGWTest
```

The full build completed 2,570 jobs. `lake test` passed with only the pre-existing private-module warning for `AxiomaticGWTest/Basic.lean`; library lint passed. Both source scans returned no matches. There are 369 explicit simplifier calls. `#print axioms` for Novikov associativity, TFT product reconstruction, and small and big quantum associativity reported only `propext`, `Classical.choice`, and `Quot.sound`.

### Remaining risk and next gate

Explicit simp lemma names may change in a future mathlib upgrade, but such changes now fail locally instead of silently changing proof normalization. The one `simp_rw` call is controlled by its two named rewrite rules. Terminology can vary between sources, but retained carrier names and their non-geometric limits are centralized in the [mathematical terminology audit](TerminologyAudit.md). The next mathematically substantive priority remains a concrete stable-curve or stable-map realization rather than further vocabulary-only work.

## 2026-07-18: Mathematical terminology and module-path audit

**Status:** Implemented and locally verified.

### Review evidence

The audit covered the public entry point and all 42 production Lean modules, including public structures, definitions, theorem families, module names, and downstream uses. Terminology was checked against searchable arXiv TeX sources for two-dimensional TFTs, Gromov--Witten classes and quantum cohomology, point-target descendants and DVV, and Givental's calibrated descendant--ancestor formalism. The decisions and the exact limits of retained carrier names are recorded in the [mathematical terminology audit](TerminologyAudit.md), and source metadata is recorded in the [online reference ledger](../references/online/README.md).

### Findings and revisions

- **Medium:** The small and big quantum-product APIs were divided among ambiguously named and overlapping modules. `GW/SmallQuantumProduct.lean` now owns the small product, while `GW/BigQuantumProduct.lean` owns the big product, arbitrary-background genus-zero WDVV, associativity, and the primary potential.
- **Low:** `TopologicalCorrelatorTheory`, `CurveClassGW`, `threePointFunctional`, the small/big product families, and `GenusZeroHigherBoundary` did not use the standard or most discoverable literature terms. They are now `TwoDimensionalTFT`, `GromovWittenTheory`, `threePointFunction`, the `smallQuantumProduct`/`bigQuantumProduct` families, and `GenusZeroWDVV`.
- **Low:** The `AxiomaticGW.Point.Descendants` path named a mathematical object rather than the target. It is now `AxiomaticGW.PointTarget.Descendants`, matching the existing namespace and the phrase “GW theory of a point.”
- No mathematical-correctness defect was found in the reviewed declarations. Potentially stronger names such as `CompletedFockPotential`, `TwoPointCalibration`, `GiventalComparison`, and `VirtualGWPackage` were retained only with explicit Lean docstrings and a central limitations ledger stating what the carriers do not construct or prove.

### Mathematical effect

This is an intentionally breaking public-name and import-path migration with no compatibility aliases. The represented data, theorem propositions, hypotheses, normalizations, and proofs are unchanged; only names, module ownership, imports, documentation, and regression examples changed.

### Verification

Direct elaboration passed for `AxiomaticGW/GW/Basic.lean`, `AxiomaticGW/GW/Descendants/Stabilization.lean`, and `AxiomaticGWTest/Basic.lean`. The final revision also passed:

```bash
lake build
lake test
lake lint
git diff --check
git diff --cached --check
rg -n '\b(sorry|admit)\b|^\s*(axiom|unsafe|opaque)\b|sorryAx|admitAx' AxiomaticGW AxiomaticGWTest
```

The full build completed 2,570 jobs. `lake test` passed with only the pre-existing private-module warning for `AxiomaticGWTest/Basic.lean`; library lint passed. The placeholder/axiom scan and production stale-name scan returned no matches. Project-local Markdown link, anchor, Typora display-math, and soft-wrap audits passed. `#print axioms` for TFT product reconstruction, small and big quantum associativity, and genus-zero CohFT associativity reported only `propext`, `Classical.choice`, and `Quot.sound`.

### Remaining risk and next gate

External users must migrate to the new public names and module paths because no deprecated aliases were retained. The terminology audit does not upgrade optional algebraic carriers into geometric constructions; the next mathematically substantive priority remains a concrete stable-curve or stable-map realization that proves one of those optional packages rather than another vocabulary-only revision.

## 2026-07-18: Optional stabilization, stable-graph, and full-potential extensions

**Status:** Implemented and locally verified.

**Implementation commit:** `9a3d625`, `Complete axiomatic stabilization revision`.

### Delivered API

- `StableGraph` with loop-aware valence, arithmetic genus, complete edge orders, `StableGraphPullbacks.orderedPullback_eq`, and the canonical constant-target graph pullback.
- `GenusZeroWDVV`, the stable primary potential, and derived coefficientwise associativity of the big quantum product.
- `StabilizationBoundaryComparison`, positive-tail splittings, the tail-derived `TwoPointCalibration`, separately justified coefficientwise symplecticity, and explicit completed-Fock/quantized comparison carriers.
- `UnstableDescendantConventions`, stable/unstable agreement theorems, `global_string`, `global_dilaton`, and `fullDescendantPotential`.

### Logical boundary

All new geometry is optional hypothesis data. The weak residual does not imply boundary support, a calibration does not imply symplecticity without its boundary relation, and a quantized partition identity is not inferred from an arbitrary additive action. Concrete virtual stable-map geometry remains outside the repository foundations.

### Verification

The revision passed direct elaboration of every new Lean module and the public entry point, followed by:

```bash
lake build
lake test
lake lint
git diff --check
git diff --cached --check
rg -n '\b(sorry|admit)\b|^\s*(axiom|unsafe|opaque)\b|sorryAx|admitAx' AxiomaticGW AxiomaticGWTest
```

Public regression examples cover graph loops and edge orders, arbitrary-background genus-zero WDVV associativity, global string, and positive-tail support. `#print axioms` on the main derived theorem in each new layer reported only `propext`, `Classical.choice`, and `Quot.sound`.

### Next gate

Prove the primary-potential third-derivative characterization and construct a nontrivial geometric instance of one optional package; the concrete virtual geometry foundation remains the larger external dependency.

## 2026-07-18: Dependency-order mathematical audit and conservative repairs

**Status:** Implemented and locally verified.

### Review evidence

The review followed the dependency order from contractions through the M10 carrier. Formula and convention checks used the arXiv TeX sources for Kontsevich--Manin's CohFT/GW axioms, Mulase--Safnuk's DVV normalization, and Givental's calibrated ancestor--descendant transformation, recorded in the [online reference ledger](../references/online/README.md).

### Findings and revisions

- Corrected missing label transports in forget/nonseparating and forget/separating coherence, and added contraction relabelling lemmas.
- Enforced stable-curve vanishing above `3g - 3 + |S|`; added forgetful pushforward relabelling and degree-zero laws and derived kappa naturality and degree.
- Corrected stable-map descendant grading so psi powers participate in the virtual-dimension equation before nonnegativity is tested. The former natural-primary-degree theorem remains as a derived compatibility result.
- Split string/dilaton laws from divisor-dependent data and made divisor action linear in the divisor state.
- Added the multivariable power-series Leibniz rule and proved commutativity of the big quantum product from relabelling and integration naturality.
- Isolated a foundational limitation: `DescendantAncestorComparison` is an unconstrained residual decomposition, and `VirtualGWPackage` is only an algebraic carrier. Documentation and milestone status now avoid claiming boundary support or geometric realization.
- Derived ancestor and stable-map-invariant relabelling, ancestor total homogeneity, and the residual subtraction, relabelling, and degree theorems. These make the weak layer coherent without pretending to supply geometric boundary support.
- Clarified the stable-sector potential convention, the absence of an external classical-cup identification, the point-target DVV hypothesis, current universe restrictions, and deferred truncation/base-change APIs.

### Verification

The final patch passed direct elaboration of every changed Lean file and:

```bash
lake build
lake test
lake lint
git diff --check
rg -n '\b(sorry|admit)\b' AxiomaticGW AxiomaticGWTest
rg -n '^\s*(axiom|unsafe|opaque)\b|sorryAx|admitAx' AxiomaticGW AxiomaticGWTest
```

Both scans returned no matches. `#print axioms` on the new top-degree, kappa, descendant-degree, Leibniz, and formal-product commutativity theorems reported only `propext`, `Classical.choice`, and `Quot.sound`.

### Next gate at the time

Replace the unconstrained descendant--ancestor residual with a stabilization comparison carrying boundary support and factorization. This is the most important remaining correctness boundary before treating M8 or M10 as a geometric interface.

**Follow-up:** The optional axiomatic comparison was implemented in `9a3d625`; constructing it from concrete stable-map geometry remains open.

## 2026-07-17: Core theorem integration and point-target stable-curve block

**Status:** Implemented and locally verified.

**Implementation commit:** This entry is delivered in the same commit as the implementation.

### Accepted scope

- Keep cohomology-valued GW classes coefficientwise under D14 and derive completed numerical and finite-free state operations without adding unused completed-tensor structures.
- Remove the abstract `QuantumProductFamily`; derive small WDVV and associativity directly from `GromovWittenTheory` gluing.
- Construct descendant and ancestor potentials from invariants with canonical occurrence labels and reciprocal multiplicity-factorial weights.
- Construct the big quantum product from genus-zero primary invariants and prove its zero-background specialization; defer nonzero-background associativity until the higher-point boundary relation is formalized.
- Isolate the point target as stable-curve intersection theory and state the full labelled DVV recursion as an explicit higher tautological hypothesis.

### Delivered API

- `GromovWittenTheory.smallQuantumProductCoefficient_wdvv`, `smallQuantumProductCoefficient_assoc`, and the coefficientwise unit and commutativity theorems.
- `MvPowerSeries.pderiv_commute`, `iteratedPDeriv`, `stablePart`, and `insertionDerivative`.
- `GromovWittenTheory.descendantPotential`, `ancestorPotential`, `potentials`, and the residual identity `DescendantAncestorComparison.descendantPotential_eq_ancestor_add_boundary`.
- `GromovWittenTheory.bigQuantumProduct`, its metric characterization, and `bigQuantumProduct_zero`.
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

- Big WDVV and big-quantum-product associativity require the genus-zero boundary relation with arbitrary background markings.
- Global string and dilaton PDEs require an explicit choice of unstable zero-, one-, and two-point conventions; the implemented equations remain honest stable-sector laws.
- A concrete cohomology model of `Mbar`, a proof of `PointTarget.DVVRecursion`, and actual stable-map moduli and virtual classes remain geometric realization work.

**Follow-up:** Higher-background associativity and explicit unstable string/dilaton extensions were implemented in `9a3d625`. The vector-field PDE presentation and concrete geometric models remain open.

### Next gate at the time

Formalize the higher-point genus-zero boundary relation needed for big WDVV, or construct a concrete stable-curve cohomology realization that proves the point initial values and DVV. Either direction now extends a theorem boundary rather than adding a speculative carrier structure.

## 2026-07-17: M5--M9 axiomatic interfaces and M10 algebraic carrier

**Status:** Implemented and locally verified. The core axiomatic data types are present through total free energies; the remaining work is theorem integration and concrete realization rather than another speculative structure layer.

**Implementation commit:** This entry is delivered in the same commit as the implementation.

### Accepted scope

- Add exactly the stable-curve tautological operations consumed by ancestors: psi classes, integration, forgetful pushforward, projection, rational-tail correction, and kappa classes.
- Add positive locally finite effective curve classes and a coefficientwise primary GW theory with grading, normalization, gluing, negative-degree vanishing, and optional divisor data.
- Implement the beta-preserving completed Novikov ring and the first fixed-beta quantum-product interface.
- Keep stable-map descendants distinct from stable-curve ancestors and expose their residual difference explicitly. The 2026-07-18 audit clarified that this field does not encode geometric boundary support.
- Use mathlib multivariable power series and Laurent series for formal variables, genus potentials, and the total free energy.
- Stop the geometric layer at an algebraic output package; do not invent unused stack, obstruction-theory, or virtual-cycle carriers.

### Delivered API

- `PsiClasses`, `StableCurveIntegration`, `ForgetfulPushforward`, `PsiForgetFormula`, `CohFT.ancestor`, and the constant tautological model.
- `EffectiveCurveMonoid`, `GradedStateSpace`, `GromovWittenTheory`, `GWDivisorAxiom`, and `constantGromovWittenTheory.theory`.
- `NovikovSeries`, its convolution ring, monomials, `ofMonoidAlgebra`, and `GromovWittenTheory.smallQuantumProductCoefficient`.
- `StableMapDescendants`, `DescendantAncestorComparison`, and the integrated descendant--ancestor residual identity.
- `MvPowerSeries.pderiv`, `GWPotentials`, `totalFreeEnergy`, exact genus-coefficient theorems, and `DescendantEquationLaws`.
- `VirtualGWPackage` and its projections to the stored primary, descendant, and residual layers; this carrier is not a realization theorem.

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

- The construction of an ordinary Novikov-valued CohFT by scalar extension from `GromovWittenTheory` remains outside the coefficientwise scope, and big associativity still requires the higher-point boundary theorem.
- Hodge classes, general decorated stable graphs, and arbitrary tautological relations remain theorem-driven extensions.
- Differential forms of every correlator equation and the exponential total potential require additional formal-series theorems or a stronger mixed completion.
- Actual moduli stacks, virtual fundamental classes, and concrete projective-target packages remain outside the current mathematical foundations.

**Follow-up:** The separate stable-graph carrier, arbitrary-background genus-zero WDVV, rational-tail comparison data, and full-potential extension were implemented in `9a3d625`; the other geometric and mixed-completion limitations above still apply.

### Next gate at the time

Derive GW WDVV coefficientwise, construct concrete potentials without imposing a false algebraic scalar extension on arbitrary cohomology targets, and use the point target as the preferred stable-curve regression instance.

## 2026-07-17: M3 and M4 completed

**Status at the time:** Complete; the next planned milestone was M5.

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

**Follow-up:** M5 and the separate optional stable-graph layer were completed in later entries. Actual combinatorial edge contraction remains outside the current `StableGraph` API.

### Next gate at the time

Begin M5 with the smallest useful stable-curve tautological extension: marked `psi`-classes and their relabelling and pullback behavior. Add integration, pushforward, boundary, kappa, and Hodge data only as ancestor constructions begin to require them.

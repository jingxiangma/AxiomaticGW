# Plan for a proof producing GW reconstruction engine

**Goal fixed on 2026-10-01. Status: planned; implementation has not started.**

Turn AxiomaticGW into a proof-producing engine for Gromov--Witten reconstruction, integrated with SageMath and admcycles for exploration and relation search. The first research release must reconstruct genus-zero, genus-one, and genus-two descendant invariants for all three fixed application targets below. It must provide executable calculations, Lean-checked derivations, and an explicit account of the geometric hypotheses and initial invariants used.

This extends the [M0--M10 roadmap](AxiomaticGWRoadmap.md). It preserves the existing even-cohomology, rational-coefficient, finite-labelled, and coefficientwise Novikov conventions. The general architecture may support higher genus later; completion of this programme is judged against the fixed genus-two applications, not against additional abstract interfaces alone.

## Fixed applications and completion contract

The application targets are smooth complex projective surfaces with rational cohomology:

| ID | Fixed target | State-space basis | Effective class coordinates to implement |
| --- | --- | --- | --- |
| X0 | $\mathbb P^2$ | $1,H,\mathrm{pt}$ | $dH$, with $d\in\mathbb N$ |
| X1 | $\mathbb F_1=\mathrm{Bl}_p\mathbb P^2$ | $1,H,E,\mathrm{pt}$ | $aE+bF$, with $F=H-E$ and $a,b\in\mathbb N$ |
| X2 | $\mathrm{Bl}_{p,q}\mathbb P^2$, for two distinct points, the degree-seven del Pezzo surface | $1,H,E_1,E_2,\mathrm{pt}$ | $aE_1+bE_2+cL$, with $L=H-E_1-E_2$ and $a,b,c\in\mathbb N$ |

These are required applications, not interchangeable examples. Their algebraic models must have codimension grading, $\int_X\mathrm{pt}=1$, $H^2=\mathrm{pt}$, $H E_i=0$, and $E_iE_j=-\delta_{ij}\mathrm{pt}$. Positive-degree products above the dimension vanish. The first Chern class is $3H-\sum_i E_i$. Establish the effective-monoid identifications as part of the application specification; the executable coordinate models do not themselves prove a geometric identification.

Use anticanonical degree $e(\beta)=c_1(X)\cdot\beta$ as the positive energy. Its weights on the listed monoid generators are respectively $3$, $(1,2)$, and $(1,1,1)$. This yields finite bounded-energy sets and finite splittings. Preserve every curve-class coordinate: equal energy does not identify Novikov monomials. In particular, do not restrict all classes to $dH-\sum_i m_iE_i$ with $m_i\geq0$; exceptional components require the full additive monoid.

The theorem-level goal is a terminating reconstruction procedure for any finite, dimension-compatible descendant query in genus at most two for X0, X1, and X2, relative to the named geometric input package and a finite, audited set of seed values or proved seed formulas. A finite numerical table is a regression gate, not a replacement for this theorem. Conversely, a theorem reducing to an unspecified family of two-point invariants does not complete the numerical application.

The geometric query domain includes all positive effective classes, even when the curve arity is unstable, and degree-zero classes at stable arities. Degree-zero unstable requests must be rejected as outside that domain or explicitly tagged as evaluations of an auxiliary convention. They must never be reported as geometric invariants merely because a formal dimension equation holds.

The first release must deliver:

1. An executable query interface accepting a target, genus, effective curve class, and a finite list of basis insertions with descendant powers.
2. An exact rational result, a reusable Lean theorem certifying the result under explicit hypotheses, and a readable derivation with its relation and seed dependencies.
3. A terminating reconstruction theorem and uniqueness from the declared initial data for each of the three targets.
4. The fixed benchmark suite below, including every required zero, without dropping difficult cases.
5. A Sage/admcycles exporter and a Lean replay path that works without Sage or network access once certificates have been generated.

Full construction of moduli stacks and virtual fundamental classes remains the separate M10 geometry programme. The research release certifies deductions from stated geometric inputs. It must not label a conditional arithmetic result as an unconditional construction of the geometric invariant.

## Fixed numerical benchmarks

Let $e=e(\beta)>0$. The following bounds are project acceptance choices, not claims about computations already performed.

| Suite | Required queries for each of X0, X1, and X2 |
| --- | --- |
| Primary | Every $N^X_{g,\beta}=\langle\mathrm{pt}^{\,e+g-1}\rangle^X_{g,\beta}$ with $g=0,1,2$ and $e\leq12$. |
| One descendant | In genus two, every $\langle\tau_1(D)\mathrm{pt}^{\,e}\rangle^X_{2,\beta}$, for $D=H,E_i$ present in the target basis, and every $\langle\tau_1(\mathrm{pt})\mathrm{pt}^{\,e-1}\rangle^X_{2,\beta}$, with $e\leq12$. |
| Few markings | All genus-two queries with zero, one, or two labelled basis insertions, positive effective class $e\leq4$, and nonnegative descendant powers satisfying the virtual-dimension condition. This is a finite suite and includes higher powers of psi. |
| Exceptional and degree zero | The audited initial values and seed formulas actually needed by reconstruction, together with the corrected string/dilaton exceptional cases and positive-degree queries whose curve arity is unstable. |

For a surface, the codimension condition is

$$
\sum_i\bigl(k_i+\deg(\gamma_i)\bigr)=e(\beta)+g-1+n.
$$

Use integer arithmetic to state this equation and to decide unstable exceptions. Invalid degree combinations must have a justified vanishing result or a precise out-of-domain result, rather than an arithmetic underflow convention.

The primary bound includes plane degree four, so the genus-two plane benchmark is not confined to the first trivial cases. All positive-energy splittings stay within the same energy bound; zero-class factors are handled by the seed package. Additional markings or descendant powers required internally by a proof must still be supported even when they lie outside the displayed benchmark families.

Before accepting a reconstruction implementation, freeze an exact query manifest and independently sourced expected values or derivations. Record which comparisons reuse the same algorithm; agreement between two executions of shared code is not independent evidence. If resources prevent the fixed suite from completing, report an incomplete milestone and improve the implementation. Any change to the targets or bounds must be an explicit revision of this goal.

## What the existing project supplies

The current repository supplies perfect pairings and contraction, CohFT/GW interfaces, positive effective classes, Novikov algebra, descendants and ancestors, decorated stable graphs, free strata modules, and formal relation quotients. The [mathematics-to-Lean map](../MathematicsToLean.md) identifies the public declarations.

Several current interfaces are specifications rather than computational or geometric implementations:

- [EffectiveCurveMonoid](../../AxiomaticGW/Coefficients/EffectiveCurveClass.lean) proves finiteness, but its bounded sets and splitting lists are noncomputable. Executable enumeration needs separate implementations and equality/completeness proofs.
- [CertifiedStrataProduct](../../AxiomaticGW/Tautological/StrataAlgebra.lean) accepts an algebra product and its laws; it does not construct the common-refinement product.
- [StrataRealization](../../AxiomaticGW/Tautological/StrataRealization.lean) is a graded linear map. Product, gluing, pushforward, and integration compatibility require further mathematics.
- [GetzlerStrataEncoding](../../AxiomaticGW/Tautological/Getzler.lean) does not yet construct the seven normalized graph cycles or prove their geometric relation.
- The optional graph pullback and descendant comparison packages do not replace proofs connecting explicit graph operations to primitive gluing and genuine stable-map descendants.

The current [unstable extension](../../AxiomaticGW/GW/Descendants/FullPotential.lean) is a correctness blocker. The status audit exhibited that its string law forces the pairing to vanish under normalized three-point integration; its dilaton law forces the genus-one one-point invariant to vanish and uses truncated natural subtraction at unstable arities. Repair and regression coverage are the first gate.

## Stages and dependencies

Every stage below is currently **planned**. Completion requires the stated mathematical result and executable evidence; adding a structure whose fields assume that result is insufficient.

| Stage | Deliverable | Depends on |
| --- | --- | --- |
| R0 | Correct normalization and numerical unstable sectors | Existing M6, M8, M9 |
| R1 | Fixed target algebra, geometric input ledger, and finite seed specification | R0 for final validation; source and algebra work can begin in parallel |
| R2 | Executable curve and decorated-graph presentations | Existing graph syntax; R1 target coordinates |
| R3 | Verified strata operations and explicit relation encodings | R2 |
| R4 | Sage/admcycles certificate exchange and Lean checker | Prototype after R2; full gate requires R3 |
| R5 | Sound transfer from tautological relations to GW equations | R0, R1, R3, R4 |
| R6 | Genus-zero and genus-one reconstruction for all three targets | R5 |
| R7 | Genus-two reconstruction and the fixed numerical applications | R6 and the selected genus-two relations |
| R8 | Reproducible research release and independent use | R7 |

### R0 Correct normalization and unstable sectors

Repair the exceptional string and dilaton statements, including the signed coefficient $2g-2+n$, and distinguish geometric invariant values from auxiliary unstable conventions such as a two-point metric used in calibration. Preserve correct stable-sector laws. Construct a numerical interface for positive-degree stable maps whose stabilized curve arity is unstable, with relabelling, multilinearity, dimension, and the required string/dilaton/divisor compatibility; connect it to the existing stable invariants rather than building an unrelated competing theory.

**Acceptance:** the normalized genus-zero three-point invariant and the point value $\langle\tau_1\rangle_1=1/24$ are compatible with the corrected equations. Use explicit numerical boundary fixtures and prove the corrected specializations; merely assuming the corrected package and restating its projection is not a regression test. Check the genus-zero zero/one/two-marking and genus-one zero-marking transitions and document every exceptional condition. The genus-one degree-zero correction for a surface must be target-dependent; audit its Euler-characteristic contribution in R1 rather than hardcoding the point value for every target. This gate tests exceptional compatibility and does not require constructing all-genus geometric point cohomology. Full numerical reconstruction models are required in R6/R7; keep that distinction in M9's status.

### R1 Specify the three targets and all geometric inputs

Implement the rational graded Frobenius data for X0, X1, and X2 and verify the pairing, cup product, divisor pairing, first Chern degree, and coordinate conversions. Audit the exact surface-specific reconstruction route and initial cases in Wennink's Section 8, including exceptional curve classes and degree-zero contributions. The general reconstruction theorem in Section 7 leaves lower-point data to be supplied; it is not by itself a finite numerical seed algorithm.

Maintain a dependency ledger separating: algebra proved in Lean; named geometric relations and push-pull laws; stable-map descendant identities; target-specific seed values or formulas; and geometric identification of each algebraic target. Every external mathematical input must state its exact proposition and source. Exclude any optional optimization whose mathematical identity has not been proved or explicitly included in this ledger.

**Acceptance:** all three target algebra models compile; the finite seed specification and its sufficiency argument are written down; no non-seed reconstruction target is admitted as a seed to bypass its derivation. Direct seed queries report their supplied or proved values and dependencies. Include symbolic treatment of arbitrary marking multiplicities in degree-zero terms where required, instead of disguising an infinite seed family as a finite list. Record a pinned SageMath/admcycles environment and a separate reproducible reference environment for any historical comparison code.

### R2 Make finite computations executable

Implement computable bounded-energy enumerators and class splitting algorithms for the fixed monoids, and prove their completeness against the existing abstract API. Implement finite labelled presentations of decorated graphs, explicit isomorphism witnesses, and automorphism enumeration with correctness proofs. Connect these presentations to the existing quotient syntax without rewriting the foundations wholesale.

**Acceptance:** equivalent graph presentations, including loop branch swaps and repeated decorations, give the same semantic class; multiplicities and automorphism orders are checked. Curve splits include exceptional components and preserve the full class. Enumeration is complete for specified finite bounds. The initial graph corpus includes stable $(g,n)$ with $g\leq2$, $n\leq6$, and codimension at most three; this corpus is a test range, not a restriction on later relabelling or pullback theorems.

### R3 Construct strata calculus and normalize the relations

Construct the common-refinement product with the node excess factor $-\psi_h-\psi_{h'}$. Implement the gluing and forgetful operations consumed by the selected reconstruction arguments, including their psi and kappa corrections. Prove their combinatorial identities and connect the product to the current contract. Supply the semantic compatibility theorems needed for realizations; algebra laws alone do not identify a geometric strata product.

Keep the repository's raw gluing-pushforward convention. Explicitly convert external conventions that divide by graph automorphism orders or average marking orbits. Construct the genus-zero boundary relation, the seven Getzler cycles, and the selected genus-two relations from an identified Pixton relation family. For each generator, distinguish its explicit graph vector from the geometric theorem that its realization vanishes.

**Acceptance:** checked low-genus product and push-pull examples; exact Getzler normalization; explicit genus-two relation vectors; and certificates of all convention conversions. A quotient that kills a supplied vector is not accepted as a proof of its geometric vanishing.

### R4 Integrate Sage and admcycles through certificates

Use Sage/admcycles to enumerate candidates, explore products, search relation spans, and solve exact rational systems. Build a project-owned exporter: a turnkey Lean proof exporter is not assumed to exist. Export the sparse graph expressions, generator provenance, and finite derivations needed for independent checking.

Implement a Lean certificate datatype, its formal strata/known-relation semantics, and a checker soundness theorem in that semantics. R5 separately proves preservation under geometric realization and GW evaluation. The parser and Sage process are outside the mathematical trust boundary: they supply candidate data only. The acceptance theorem must be indexed by the exact requested claim, and the replay interface must match its expression or target/query, relation system, conventions, and claimed value to that request. Keep the semantic generator hypotheses visible. Kernel-checked proof replay is the release standard; external Boolean answers or unchecked native computations are not substitutes.

**Acceptance:** replay valid WDVV, Getzler, and selected genus-two certificates without Sage. With the requested claim held fixed, reject certificates corrupted in their coefficients, edge incidences, normalization factors, labels, or generator references; changing the requested query or claimed value must not reuse an unrelated theorem. Demonstrate a searched consequence using an explicit linear-combination witness. Failure to find a witness reports unresolved membership, not nonvanishing or completeness of the relation system.

### R5 Prove the relation to GW equation translation

Define the evaluation of a decorated stratum against primary/ancestor insertions and prove the general-graph splitting formula from compatible gluing, pushforward, projection, and integration data. Account for every curve splitting, inverse-metric contraction, automorphism coefficient, and marking multiplicity. Prove soundness for each certificate operation.

Extend the translation to genuine stable-map descendants using the required pullback/comparison formulas and the R0 numerical unstable sectors. Do not identify stable-curve psi decorations with stable-map psi insertions without this step.

**Acceptance:** machine-checkable theorems that the explicit genus-zero, genus-one, and selected genus-two relations imply their stated GW equations. The hypotheses must be named geometric compatibility laws and relation inputs, not the desired final recurrence. The point and constant models test appropriate subinterfaces; they do not certify a surface's geometric GW theory.

### R6 Reconstruct genera zero and one

Derive and implement the genus-zero recursion and a Getzler-based genus-one recursion for X0, X1, and X2, including descendant reduction for arbitrary finite queries in both genera. Prove a well-founded reduction order, validity of every solved coefficient, and uniqueness from the specified initial data. An implementation that evaluates recursively must also prove that every recursive call decreases the measure, including descendant reductions, equal-energy terms, and zero-class branches.

**Acceptance:** all genus-zero and genus-one primary benchmarks and required seed-support computations have exact outputs and replayable proofs. Include positive-degree unstable-arity cases used by the algorithm, boundary cases for difference equations, and comparisons with published or independently derived values. Shared-source comparisons must be labelled as such.

### R7 Reconstruct genus two for the fixed applications

Derive the required descendant reduction and surface-specific recursions from the encoded genus-two relations. Formalize the reduction to lower complexity and then discharge the remaining lower-point values through the finite surface-specific seed algorithm. Prove that the implementation agrees with the stated mathematical recursion, terminates on each allowed finite query, and determines the answer uniquely under the input package.

**Acceptance:** all three fixed targets pass every benchmark suite, including higher psi powers in the few-marking tests. Release both the general reconstruction theorems and the concrete exact tables. Track proof-checking time, search time, peak memory, certificate size, and any unsupported request separately. A table with missing cases, an unspecified seed oracle, or an assumed recurrence does not complete R7.

### R8 Release a usable research workflow

Provide a documented query format, a command-line interface and a Sage-facing entry point, machine-readable rational outputs, readable derivations, and exportable Lean theorems. A result must identify its target, curve coordinates, insertions, normalization, geometric assumptions, seed dependencies, tool versions, and certificate.

**Acceptance:** a fresh checkout replays the fixed corpus offline using Lean alone. A separate pinned Sage job regenerates representative certificates. A researcher follows the documentation to derive and certify an additional relation consequence and compute additional queries for one of X0--X2 without modifying foundational Lean files. Record the computation and its assumptions as a worked research example; do not promise mathematical novelty as a software acceptance test.

## Sage and admcycles exchange contract

The integration is part of the goal, beginning with an exporter prototype at R2/R4 and continuing through the release. It is not a future optional plugin.

Each versioned certificate must carry:

- Exact integers and rational numerators/denominators, with no floating-point coefficients.
- Graph vertices, genera, incident half-edges, edge pairing, external labels, psi powers, and kappa decorations, together with the genus and degree to be checked.
- The moduli locus for every expression and relation generator. The first release requires the full stable-curve locus (st); reject relations valid only on compact type, rational tails, smooth curves, or other open loci unless a separate justified transfer is supplied.
- The source and destination stratum conventions, automorphism and orbit weights, and enough data to check the normalization conversion.
- Named relation generators with their parameters and semantic hypotheses, and a finite derivation using supported relabelling, product, gluing, forgetting, and rational linear-combination rules.
- For elimination or reconstruction, the original equations, exact row-operation or linear-combination witnesses, nonzero pivots, the recursive dependency graph, and the seed references.
- Target and query data, schema version, tool versions or commits, and content digests for reproducibility. Digests identify data; they are not mathematical proof.

admcycles reports about zero classes or a chosen quotient basis must be unpacked into explicit known-relation witnesses. Vectors in the kernel of an intersection pairing and conjectural completeness assumptions must not be promoted to geometric relations. If the selected software version cannot export provenance, extend the adapter or reconstruct the derivation; do not trust the final zero flag.

Separate three jobs: exploration/search in pinned Sage, proof replay in Lean, and comparison with independent numerical references. The routine Lean build must not install or run Sage. Preserve compact checked fixtures in the repository; larger generated search artifacts belong in a versioned corpus with reproducible manifests. Pin or disable external relation-data lookup so regeneration does not depend on a mutable online cache. Record external software licenses and provenance, and avoid silently vendoring historical code into the Lean library.

## Mathematical assumptions and research claims

Every final theorem must make its dependence on unformalized geometry explicit through hypotheses, not new Lean axioms. The planned guarantee is: for any GW theory satisfying the specified geometric relations, numerical laws, target identification, and seed data, the checked procedure returns its invariant.

There are three separate obligations: correctness of finite combinatorial and rational computations; soundness of their interpretation in the axiomatic GW theory; and applicability of that theory to the geometric surface. R2--R7 must prove the first two, with precisely scoped geometric inputs for the second. The third remains conditional until the relevant geometry is formalized. Proving existence of an arbitrary formal solution of the recursions does not establish that it is the geometric GW theory.

The seed inventory is a critical gate. The goal is not satisfied by assuming all answers, by assuming reconstruction itself, or by recording arbitrary higher-genus invariants as free inputs. Full Pixton ideal completeness, odd cohomology, arbitrary rational surfaces, higher genus, and a virtual-class construction are outside this first release.

## Validation and progress recording

For Lean changes, compile changed modules and downstream targets, run the repository's build/test/lint gates, scan for placeholders and substitute axioms, inspect key axiom dependencies, and test concrete public examples. For executable mathematics, prove soundness and the completeness needed by the application; numerical agreement alone is supplementary evidence.

For each completed stage, update this plan's status, the relevant M0--M10 entries, the mathematics-to-Lean map, and the implementation progress record. Record exact commands, fixture and dependency versions, scope reviewed, assumptions remaining, and resource measurements. Create files and abstractions only when the stage has a concrete consumer.

The next implementation task is R0: retain the normalized-theory counterexample as review evidence, correct the exceptional equations conservatively, and add genuine normalization regressions. R1's source/seed audit and R2's finite-presentation design can proceed in parallel; accepting their downstream numerical results depends on R0.

## Sources and source audit

These sources guide the planned mathematics and interoperability work. Their results are not automatically Lean theorems. Access date for the sources below: **2026-10-01**.

| Source | Planned use | Reuse information |
| --- | --- | --- |
| Ezra Getzler, [Intersection theory on Mbar 1 4 and elliptic Gromov Witten invariants](https://arxiv.org/abs/alg-geom/9612004) | Genus-one relation, normalization, and reconstruction benchmark | Paper linked only; redistribution license not checked |
| Thomas Wennink, [Reconstruction theorems for genus 2 Gromov Witten invariants](https://arxiv.org/abs/2210.04038), especially Sections 7 and 8 | Distinguish general lower-point reconstruction from the surface-specific finite-seed algorithm; select genus-two relations | Paper linked only; redistribution license not checked |
| Vincent Delecroix, Johannes Schmitt, Jason van Zelm, [admcycles](https://arxiv.org/abs/2002.01709) | Strata computations and natural operations | Paper linked only; redistribution license not checked |
| admcycles developers, [project page](https://www.math.uni-bonn.de/people/schmitt/admcycles), [relation API](https://modulispaces.gitlab.io/admcycles/DRmodule.html), and [tautological API](https://modulispaces.gitlab.io/admcycles/tautological_ring.html) | Pin supported APIs; implement provenance extraction and convention conversion | Sage's [package entry](https://doc.sagemath.org/html/en/reference/spkg/admcycles.html) lists GPLv2+ for the package; confirm the chosen revision |
| Thomas Wennink, [gwreconstruction software](https://github.com/Wennink/gwreconstruction) | Reproduce published computations as one reference implementation | Repository identifies GPL-3.0 and an old admcycles snapshot; pin separately and do not assume current API compatibility |

Audit exact equations against the source text before implementation, including signs, automorphism normalization, symmetric marking averages, exceptional cases, and seed ranges. The target ring conventions stated above are part of this plan's specification; copied formulas or rendered-source artifacts must not silently change them.

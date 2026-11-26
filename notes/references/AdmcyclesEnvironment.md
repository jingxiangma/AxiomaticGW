# Sage and admcycles integration baseline

Audit date: **2026-10-01**. SageMath **10.9** and admcycles **1.4** are installed in the dedicated native Apple Silicon environment `axiomatic-gw-sage`, at `/opt/homebrew/Caskroom/miniforge/base/envs/axiomatic-gw-sage`. The package installation, Sage version command, and Python dependency check succeeded. Exact mathematical smoke-test results are recorded below. This environment does not constitute an R4 exporter or a Lean certificate checker.

**2026-10-02 follow-up:** The unmarked genus-two, marked four-point WDVV, and Getzler exporters and Lean replay described below are implemented and verified within their fixed frames. The earlier source-audit boundaries remain historical evidence; general marked-graph normalization and operation provenance, geometric realization, and the full R4 release remain open.

## Exploration environment

| Component | Pin | Evidence |
| --- | --- | --- |
| SageMath | `10.9=py312hb3a2cf9_0`; sagelib `10.9=np2py312h37053f4_0` | Native `osx-arm64` conda-forge packages |
| Python | `3.12.14=hd05a0c4_3_cpython` | Installed in the same environment |
| admcycles | 1.4, source commit `ea8abbb6245406c735e1d615841c41dcc83b590e` | Released [PyPI 1.4](https://pypi.org/project/admcycles/1.4/) wheel |
| admcycles wheel | SHA256 `273ca218a2ec2a7f87f5939989b681a5b42eb55b891630ffb2bdf227ca8eed73` | Verified by pip's `--require-hashes` installation |
| psutil | `7.2.2=py312hbd136b4_3` | Explicit conda dependency used by admcycles |

The [conda lock](../../environments/sage-osx-arm64.lock) records all 394 conda package URLs and SHA256 hashes. The [pip requirements](../../environments/admcycles-requirements.txt) pin admcycles and its wheel/source-distribution hashes. The source-distribution SHA256 is `f60b95ec19408c27d85a4fe695130e20e0a7a6b61f8c6011cb80828772821ff6`; this installation used the wheel. Sage's [installation guide](https://doc.sagemath.org/html/en/installation/conda.html) supports native macOS arm64 through conda-forge.

The initial source-audit candidate was Sage 9.7, because admcycles 1.4's [CI configuration](https://gitlab.com/modulispaces/admcycles/-/blob/ea8abbb6245406c735e1d615841c41dcc83b590e/.gitlab-ci.yml) tests that version. The installed exploration environment uses Sage 10.9 instead, with the runtime checks below establishing only the tested compatibility. No historical Sage 9.7 environment has been installed.

From the repository root, use the existing installation with:

```bash
conda activate axiomatic-gw-sage
sage
```

The following commands reconstruct the pinned package set on macOS arm64. Choose an unused environment name when retaining the current installation:

```bash
conda create -n axiomatic-gw-sage --file environments/sage-osx-arm64.lock
conda run --no-capture-output -n axiomatic-gw-sage python -m pip install \
  --require-hashes --no-deps -r environments/admcycles-requirements.txt
conda run --no-capture-output -n axiomatic-gw-sage python -m pip check
conda run --no-capture-output -n axiomatic-gw-sage python scripts/admcycles_smoke.py
```

Use this environment's `python`, which imports Sage, for Python scripts and pip. This Sage 10.9 distribution's new launcher does not accept the older `sage -pip` option. The package lock was exported from the successful installation; replay into a second environment has not been tested.

## Runtime validation

The [smoke script](../../scripts/admcycles_smoke.py) uses fresh temporary Sage and admcycles caches, disables online relation lookup, and prints exact rational data and deterministic digests. Two independent runs passed and produced byte-identical [JSON reports](../../environments/admcycles-smoke-osx-arm64.json). The checks establish:

- The genus-one kappa integral is exactly $1/24$.
- `FZ_matrix(2, 2, (), MODULI_ST)` agrees with the pinned upstream $7\times8$ full-stable-locus fixture.
- An explicit rational row vector satisfies `lambda * M = v` for a separately specified nonzero target.
- The pushforward and monomial kappa coordinate conversions are nontrivial two-sided inverses, and preserve the relation witness.
- All eight raw generator vectors and the target round-trip through the public `TautologicalRing` API without quotient reduction.

Raw graph coordinates and exact arithmetic are included in the report. Its full SHA256 is `142c06e43218a470cd90daee0064ea6c2b49bbe37dba0372441c8ee4a75244b0`. The report is a computational regression, not a geometric proof or a Lean certificate. The only warnings were upstream uses of the deprecated `Algebras` category constructor (Sage issue 38502); no local suppression or package patch was applied.

Sage startup succeeded with `DOT_SAGE=/tmp/axiomatic-gw-sage-version conda run --no-capture-output -n axiomatic-gw-sage sage --version`, returning `10.9`. `conda run --no-capture-output -n axiomatic-gw-sage python -m pip check` returned `No broken requirements found`. The initial sandboxed startup could not write to the default `~/.sage/cache`; using a temporary cache resolved that test-environment restriction. The smoke script handles cache isolation itself.

The two smoke runs used `/opt/homebrew/Caskroom/miniforge/base/envs/axiomatic-gw-sage/bin/python scripts/admcycles_smoke.py`. The exploration-runtime part of R1 now has an installed, hash-pinned, tested environment. The historical comparison environment and all R4 proof-export obligations remain open.

## Separate historical comparison

Pin [Wennink/gwreconstruction](https://github.com/Wennink/gwreconstruction/tree/40f8913ef543fc21e5fadf3beb67b78955ca0253) at `40f8913ef543fc21e5fadf3beb67b78955ca0253` (2022-10-07). Its bundled `Reconstructing GWI in genus 2.zip` has SHA256 `f8d96f7c09244ee9696951d96b6a7d93431b2a09fd24cf568baf4350c70288b8`. The repository loads `reconstructioncode/init.sage` and supplies a historical admcycles copy; no reproducible Sage version was identified in that revision.

Keep this environment separate so the exploration installation cannot shadow the bundled implementation. A later revision, `7dbafbe98928d3abc0d76f97a4a72d04958af625`, changes a deprecated memory API; using it is a separately recorded comparison configuration. No historical code has been vendored or executed in this project. Comparisons with this implementation share the reconstruction source and must not be presented as independent evidence.

## Exporter obligations identified in the source audit

The pinned source provides exact strata vectors through `TautologicalRing`, `generators`, `vector`, and `from_vector`. Graph and decoration data are available through the DR graph/stratum representation. Use `moduli='st'`, rational coefficients, and distinct labels; preserve the `symm=0` convention when requesting unsymmetrized relation rows. The [tautological API](https://modulispaces.gitlab.io/admcycles/tautological_ring.html) and [DR API](https://modulispaces.gitlab.io/admcycles/DRmodule.html) are useful references, but current online documentation must be checked against the pinned implementation.

The [relation implementation](https://gitlab.com/modulispaces/admcycles/-/blob/ea8abbb6245406c735e1d615841c41dcc83b590e/admcycles/DR/relations.py) exposes FZ parameters, coefficients, and relation rows. Derived/boundary routines do not retain the complete provenance needed by this project. The exporter must retain each seed and each gluing, multiplication, and relabelling derivation before row reduction. For candidate vector `v` and exported relation matrix `M`, export exact `lambda` with `lambda * M = v`; Sage's [linear-algebra tutorial](https://doc.sagemath.org/html/en/tutorial/tour_linalg.html) documents the `solve_left` convention. A failed span search reports an unresolved query.

Two conversions require explicit checked witnesses:

1. Relation rows use a pushforward kappa basis in paths where `.vector` uses monomial kappa coordinates. The source calls `convert_vector_to_monomial_basis` before row reduction.
2. `FZ_coeff` includes factors involving `2^h1` and graph automorphisms. Convert the complete external expression to the project's raw gluing-pushforward convention; do not append another automorphism division by guesswork.

Neither `is_zero`, quotient basis coordinates, predicted rank, nor the kernel of an intersection pairing supplies the required geometric relation proof. The Lean checker must bind the eventual certificate to the exact requested expression, relation system, locus, and normalization. No exporter/checker is claimed by this audit.

## Graph coordinate conventions audited on 2026-10-02

The installed `admcycles/DR/graph.py` and `admcycles/admcycles.py::Graphtodecstratum` were inspected directly. In the polynomial incidence matrix, rows after the first are vertices; column zero records vertex genus in its constant term and the exponent of kappa_i as the coefficient of `X^i`. Each other column is either an internal edge (header zero) or an external leg (nonzero header, carrying its label). A non-loop incidence `1 + a*X` carries half-edge psi exponent `a`. A loop entry `2 + a*X + b*X^2` encodes the two branch exponents `a` and `b`; its second exponent is not weighted by two. The converter reads these coefficients separately and preserves external labels.

The DR `Graph.num_edges()` counts every column except column zero, including external legs. Its `h1()` is `ncols - nrows + 1`, also including those leg columns. Neither value may be copied directly into the Lean graph's internal-edge count or first Betti number. An exporter must count the zero-header internal columns and use `internalEdges + 1 - vertices` for the connected graph. This is an integration convention, not a claim that the upstream methods are defective.

The inspected `DR/relations.py::FZ_coeff` divides its accumulated coefficient by `2^G.h1() * autom_count(...)`. The complete marked-relation formula must be converted consistently; replacing this exponent in isolation is not justified by the graph-field distinction. The existing unmarked genus-two smoke test cannot detect a marked-leg counting mistake. An eventual marked-graph exporter regression and checked relation-normalization witness remain required. This source audit neither implements an exporter nor proves geometric vanishing.

## Fixed-frame Lean replay implemented on 2026-10-02

`scripts/export_admcycles_certificate.py` reads the pinned smoke JSON, strictly decodes exact rational and raw graph data, and emits Lean source. The frame is held independently fixed in `AxiomaticGW/Tautological/Fixtures/AdmcyclesGenusTwo.lean`: genus two, no markings, codimension two, all eight raw stratum columns, seven relation rows, both kappa-coordinate conversion tables, and a separately fixed nonzero request. All source and destination fields are bound by `AcceptsExchange`; its conditions are proved equivalent to the Boolean checker. A source hash is an optimization/reproducibility identifier, not a proof.

The accepted theorem proves membership in the supplied formal relation span. `RelationCertificate.evaluation_eq_zero` deduces evaluated vanishing only under explicit proofs that each row vanishes under that same linear evaluation. Neither a formal quotient nor these finite tables prove the geometric Pixton relations. The two-sided kappa-coordinate tables are proved inverse on every rational vector; their geometric coordinate interpretation remains a comparison obligation.

Regenerate and replay with:

```bash
python3 scripts/export_admcycles_certificate.py environments/admcycles-smoke-osx-arm64.json \
  > /tmp/admcycles-replay.lean
lake env lean /tmp/admcycles-replay.lean
python3 scripts/test_admcycles_certificate.py
```

This path requires Lean and ordinary Python, with no Sage or online data lookup. The frozen `AxiomaticGWTest/Tautological/AdmcyclesReplay.lean` is part of `lake test`. Kernel replay uses direct semantic graph equalities and exact rational witnesses, rather than evaluating an entire quotient equality in a closed Boolean proof. The native graph search algorithm is unchanged by the proof-facing `standardCandidates`/`validCandidates` normalization APIs.

`environments/admcycles-certificate-replay.json` records **23 passing cases**: the baseline, an alternative row witness, and a loop-branch exchange are accepted; altered coefficients, generator references, graph incidence, normalization, coordinate conversions, source/destination requests, and malformed schemas are rejected. No `native_decide` or substitute axiom is used. The fixed WDVV and Getzler follow-ups below add marked replay; general marked graphs, operation provenance, and geometric realization remain required for the full R4/R5 gates.

## Marked four-point WDVV replay

`Tautological/WDVV.lean` fixes raw boundary partitions `01|23`, `02|13`, and `03|12`, with distinct semantic columns and automorphism order one. The two fixed rows are `(1,-1,0)` and `(0,1,-1)`; the independently held request is `(1,0,-1)`. Its nonzero formal expression is a consequence with witness `(1,1)`. This is not formal identification of the graphs.

`scripts/search_wdvv_certificate.py` uses the pinned public `separable_boundary_divisor` constructor and checks raw vector round-trips. The three marked graphs occur at admcycles raw indices 5, 6, and 7. It exports their actual incidence, decorations, exact raw factors, explicit one-based-to-zero-based label conversion, named Keel generator references, tool/source pins, and a searched rational witness. Caches are isolated and online lookup is disabled. It does not use an external zero flag as a geometric theorem. The installed Sage emits an upstream category deprecation warning; the mathematical checks succeed.

Regenerate candidates with Sage and replay with ordinary Python and Lean:

```bash
conda run --no-capture-output -n axiomatic-gw-sage python scripts/search_wdvv_certificate.py \
  > /tmp/wdvv-candidate.json
python3 scripts/export_wdvv_certificate.py /tmp/wdvv-candidate.json > /tmp/wdvv-replay.lean
lake env lean /tmp/wdvv-replay.lean
python3 scripts/test_wdvv_certificate.py
```

The frozen candidate report is `environments/wdvv-candidate-osx-arm64.json`; `AxiomaticGWTest/Tautological/WDVVReplay.lean` is compiled by `lake test`. Fresh Sage generation and ordinary Python export reproduce these files byte for byte. Producer hashes and exploratory raw vectors are provenance, not Lean evidence of geometric validity. Replay emits incoming graph data and proves their semantic equality to the separately compiled frame, including marking incidence and every decoration.

`environments/wdvv-certificate-regressions.json` records **30 passing cases**: three accepted replays (baseline, vertex exchange, branch exchange), ten kernel rejections, and seventeen parser rejections. Changed marked partitions and a different valid kappa column are rejected despite valid graph syntax. Other cases change normalization, rows, requests, witnesses, genera, incidence, powers, locus, references, label conversion, tool pins, or exact encodings. `environments/wdvv-validation.json` records the build/test/lint gates, source hashes, and an 80-declaration axiom audit using only standard Lean axioms.

`WDVVRealization.lean` identifies the graph columns with raw boundary point classes and derives original row vanishing from [Keel's four-point boundary relation, Section 4, Theorem 1, Part I(2)](https://www.math.colostate.edu/~renzo/teaching/Moduli16/keel.pdf), retained as the explicit property `WDVV.BoundaryClassesEqual`. Primitive separating graph-map composition, normalization, relabelling, and proper push-pull/integration then give the accepted full-curve-class GW convolution. Tests retain both ordered exceptional splits and both zero factors in `E₁+E₂`. No final numerical recurrence is a hypothesis. This scoped four-marking consumer does not construct geometric surface/GKM CohFT classes, establish stable-map descendant comparison, or finish arbitrary-background reconstruction.

## Marked Getzler replay

`GetzlerGraphs.lean` fixes all 33 labelled raw graphs in the seven cycles of [Getzler, Theorem 1.8](https://arxiv.org/pdf/alg-geom/9612004). External labels are 0--3. Each cycle is a sum over distinct marking-orbit members, with the raw gluing coefficient divided by the label-fixing graph automorphism order:

| Cycle | Orbit size | Graph automorphism order | Getzler coefficient per raw column |
| --- | ---: | ---: | ---: |
| delta22 | 3 | 1 | 12 |
| delta23 | 12 | 1 | -4 |
| delta24 | 6 | 1 | -2 |
| delta34 | 4 | 1 | 6 |
| delta03 | 4 | 2 | 1/2 |
| delta04 | 1 | 2 | 1/2 |
| deltaBeta | 3 | 2 | -1 |

These graph automorphism orders are distinct from generic stabilizers of points of the moduli stack. The source component stacks already include their stabilizers. A separate extra division on elliptic tree terms would change the relation. Lean checks complete S4 orbits, their sizes, all 33 graph classes, and the normalization factors.

The held request isolates delta23 and has raw coefficients `-3, 1, 1/2, -3/2, -1/8, -1/8, 1/4` on the seven groups. Sage finds the row witness `-1/4`. Both the original relation and the requested expression are proved nonzero in the free strata module.

```bash
conda run --no-capture-output -n axiomatic-gw-sage python scripts/search_getzler_certificate.py \
  > /tmp/getzler-candidate.json
python3 scripts/export_getzler_certificate.py /tmp/getzler-candidate.json \
  > /tmp/getzler-replay.lean
lake env lean /tmp/getzler-replay.lean
python3 scripts/test_getzler_certificate.py
```

The frozen report is `environments/getzler-candidate-osx-arm64.json`; its generated `AxiomaticGWTest/Tautological/GetzlerReplay.lean` is compiled by `lake test`. Fresh-cache Sage generation and ordinary Python export reproduce both files byte for byte. Sage also computes the seven-cycle intersection matrix and matches the published matrix, with rank six. This is an independent normalization diagnostic, not a Lean proof of the geometric relation. Online lookup is disabled and all caches are temporary.

The 36 offline cases comprise four accepted replays, fourteen kernel rejections, and eighteen parser rejections. They cover equivalent vertex/edge/branch presentations and rational witnesses, changed valid marking partitions and graph topology, disconnectedness, genera, decorations, raw factors, orbifold factors, named-cycle slots, original rows, held claims, witnesses, references, exact integer encodings, and malformed schemas. `environments/getzler-certificate-regressions.json` records the outcomes.

`GetzlerRealization.lean` transfers accepted data to integrals against any held cohomology insertion, including actual GW classes with external ancestor powers. Its inputs are the named geometric `GetzlerRelationGeometry` theorem and identification of its cycles with the explicit normalized graph sums. `GetzlerGluing.lean` constructs all 33 marked columns from stable components and elementary gluings. `GetzlerGraphs.exchange_gw_eq_zero` now transfers accepted replay to their primary iterated full-class contractions through the generic `GluingExpression.gwIntegral_eq_contraction` theorem. Fundamental normalization and primitive raw graph-map/Gysin laws are explicit inputs; no final numerical recurrence is assumed. `GetzlerGraphs.exchange_ancestor_eq_zero` further extends the same incoming certificate to arbitrary external ancestor powers, using the existing cotangent pullback laws and the same realization compatibility. New node powers are zero; marking powers and states use the same bijections. Zero powers recover the primary equation. `GetzlerGraphs.exchange_ancestor_with_markings_eq_zero` now supports any finite number of additional markings. Its graph expansion is derived from the two primitive laws in `GluingForgetfulCompatibility`; arbitrary powers are inserted after pullback. Stable-map descendant comparison and general decorated forgetting remain open. The follow-up evidence is recorded in [Getzler GW validation](../../environments/getzler-gw-validation.json) and [ancestor validation](../../environments/getzler-ancestors-validation.json). The [validation manifest](../../environments/getzler-validation.json) records build/test/lint results, reproducibility, source hashes, and the 97-declaration standard-axiom audit.

### Additional-marking exploration

```bash
conda run --no-capture-output -n axiomatic-gw-sage python scripts/explore_getzler_forgetful.py \
  > /tmp/getzler-forgetful-exploration.json
```

The [frozen exploration report](../../environments/getzler-forgetful-exploration.json) compares independently constructed vertex placements with admcycles forgetful pullbacks in raw coordinates. The 33 undecorated Getzler columns give 91 terms with one new marking and 257 with two, preserving the original coefficients, held request, and exact witness. A symmetric genus-two graph checks multiplicity two for coincident placements; a psi-class countercheck detects the required negative rational-tail correction. Thus the vertex-only construction is scoped to undecorated graphs. The script pins its input and producer sources, disables online lookup, and uses temporary caches. These remain Sage exploration checks. The subsequent Lean implementation now proves the finite placement construction, count, codimension preservation, and class/GW soundness conditional on two primitive geometric base-change laws. Eleven regressions check the actual marked graphs, multiplicity, label conversion, and original decoded certificate consumer. The [forgetful validation manifest](../../environments/getzler-forgetful-validation.json) records this separate proof evidence. It does not turn Sage output into a proof of geometric relation validity.

### Surface polynomial follow-up

```bash
conda run --no-capture-output -n axiomatic-gw-sage python scripts/explore_surface_getzler.py \
  --polynomials-dir /tmp/surface-getzler-polynomials \
  > /tmp/surface-getzler-exploration.json
```

The complete sparse polynomials are saved as reproducible gzip JSON by `--polynomials-dir`; the report documents the state codes and monomial schema. The [surface exploration report](../../environments/surface-getzler-exploration.json) independently expands the frozen admcycles Getzler frame in Sage's exact rational field. It retains full curve coordinates, ordered inverse-metric branches, negative exceptional weights, and repeated insertion multiplicities. Component variables are keyed by genus, full class, and insertion multiset. The line cases for P²/F₁/Bl₂P² collect 2,313/11,824/53,825 raw contributions into 251/1,388/6,550 monomials. Substituting classical cubic tails, retaining a single elliptic all-point variable, and setting other component variables to zero gives coefficient -9 in each case and in E₁+E₂. This is a formal coefficient probe, not a GW invariant or a recurrence proof. The script uses the held raw graphs without querying a relation oracle, performs no online lookup, and puts Sage caches in a temporary directory.

Lean now proves the same graph evaluator's interpretation and the soundness of collecting symmetric component variables in `MvPolynomial`. The smaller E₁+E₂ coefficient probe is kernel-checked. Native Lean execution independently agrees with the three larger Sage probes; their raw kernel reductions were interrupted for excessive checking cost and are not counted as proved numerical regression results. The general symbolic soundness theorem is kernel-checked for arbitrary additional markings and powers. See the [validation record](../../environments/surface-polynomial-validation.json) for this distinction, the source pins, and the remaining recursion/performance gates.

### Primary reduction follow-up

```bash
conda run --no-capture-output -n axiomatic-gw-sage python scripts/explore_surface_reduction.py \
  --output /tmp/surface-primary-reduction-exploration.json \
  --lean-replay /tmp/surface-primary-reduction-replay.lean
lake env lean /tmp/surface-primary-reduction-replay.lean
```

The new script checks both hashes of every frozen compressed polynomial, applies signed dimension and positive-class primary string/divisor rules using exact Sage rationals, and saves every reduced term in the [exploration report](../../environments/surface-primary-reduction-exploration.json). The three line polynomials shrink from 251/1,388/6,550 to 13/23/40 monomials; E₁+E₂ shrinks from 853 to two. All 1,570 distinct component substitutions are emitted as `decide +kernel` examples, bound to their explicit genus, full class, insertion pairs, coefficient, and residual variable. The [archived replay](../../environments/surface-primary-reduction-replay.lean) also compiles directly with `lake env lean environments/surface-primary-reduction-replay.lean`, without Sage or network access. Repeated point insertions and unstable positive-degree queries are retained; degree-zero inputs and nonzero powers remain ancestors. The [validation manifest](../../environments/surface-primary-reduction-validation.json) records the exact replay hash and command outcome.

The general Lean substitution theorem is proved for any ancestor polynomial and is consumed by the original Getzler certificate theorem. The generated finite checks verify agreement of the independent Sage component rules with that Lean implementation. They do not certify the earlier independent sparse graph expansion or its polynomial collection, prove the geometric input laws, or solve a numerical GW recurrence. No relation oracle or online lookup is used.

### Degree-zero primary reduction follow-up

```bash
conda run --no-capture-output -n axiomatic-gw-sage python scripts/explore_surface_degree_zero.py \
  --output /tmp/surface-degree-zero-exploration.json \
  --lean-replay /tmp/surface-degree-zero-replay.lean
lake env lean /tmp/surface-degree-zero-replay.lean
```

The script checks the pinned primary-reduction report and helper hashes, substitutes the genus-zero classical cubic and the existing genus-one divisor seed values, and collects exact rational coefficients. The [complete report](../../environments/surface-degree-zero-exploration.json) retains all 14 output monomials: 1/4/8 for the three line examples and one for E₁+E₂. All four have leading elliptic coefficient −9. These finite coefficients do not establish a uniform nonzero pivot or decreasing recurrence.

The [archived Lean replay](../../environments/surface-degree-zero-replay.lean) checks 66 distinct component rules with `decide +kernel` and proves each complete collection identity by rational ring arithmetic, for every assignment to its residual variables. It replays with `lake env lean environments/surface-degree-zero-replay.lean`, without Sage or network access. The general theorems in `Surfaces/DegreeZeroPolynomial.lean` separately prove that the substitution preserves actual invariant evaluation and the original incoming Getzler equation. The genus-zero cubic is derived from existing string/grading/metric laws; genus one consumes the finite divisor seed equalities. Nonzero powers and higher genera remain untouched. The earlier independent raw sparse graph expansion, geometric hypotheses, seed validity, and numerical solutions are not certified by this replay. See the [validation manifest](../../environments/surface-degree-zero-validation.json) for exact pins and outcomes.

### Exact graph expansion and term certificates

The follow-up [exporter](../../scripts/export_surface_equations.py) uses the pinned Sage result as candidate coefficients and the original 33-column frame to propose an uncollected witness. The fixed Lean requests specify the full class, markings, states and powers independently. Run:

```bash
python3 scripts/export_surface_equations.py --output /tmp/surface-getzler-replay.lean
lake env lean /tmp/surface-getzler-replay.lean
python3 scripts/test_surface_equations.py
```

Every generated case first checks exact multiset equality for each of the 33 original graph columns, with the proved dimension and primary reductions applied at terminal components. There are 16/34/72/3 total uncollected contributions. Finite-sum congruence combines those checks, and a final comparison checks all coefficients over both monomial supports. The 132 column checks and four coefficient comparisons use `decide +kernel`; the resulting equations have 1/4/8/1 terms. The intermediate witnesses separate graph calculation from collection and retain each column's contribution. File generation, hashes and executable diagnostics provide provenance or feedback; acceptance requires successful kernel replay. These commands need neither Sage nor network access.

`GluingExpression.eval_surfaceTerms` and `GetzlerGraphs.polynomial_primaryTerms` prove that the finite calculation denotes the established graph evaluator and reduced polynomial. `exchange_checkedPrimaryTerms_eq_zero` consumes the original incoming Getzler presentation and the same geometric hypotheses. The Python consistency comparison shares the graph frame and component rules with the earlier exploration; geometric validity and seed validity remain explicit inputs. Uniform pivots, decreasing recursions and the full numerical benchmark suites remain further work.

The checked singleton equations give the two zero values in [`LowDegree.lean`](../../AxiomaticGW/Surfaces/LowDegree.lean). The [validation manifest](../../environments/surface-term-expansion-validation.json) records the kernel replay, regressions, source pins and remaining scope. This certifies the complete reduced equations directly; it does not upgrade the separately archived unreduced polynomial files to checked artifacts.

### Exceptional-class relation search

The [exceptional search](../../scripts/explore_exceptional_getzler.py) reuses the pinned admcycles-derived Getzler frame and exact component rules. It varies the four external basis labels, retains every full-class split, and uses Sage rational matrices to check the resulting three-equation system. Its cache is temporary and requires no write to the user's Sage configuration. Reproduce it with:

```bash
conda run -n axiomatic-gw-sage python scripts/explore_exceptional_getzler.py \
  --output /tmp/surface-exceptional-exploration.json
lake build AxiomaticGWTest.Surfaces.Exceptional
python3 scripts/test_surface_equations.py
```

The [report](../../environments/surface-exceptional-exploration.json) records nine requests, 21 surviving uncollected contributions, and a common coefficient matrix of rank three and determinant −81/2. It also records 45 dimension-compatible energy-one basis multisets whose directly expanded equations vanish. These are exploratory calculations using shared source data, not an independent geometric computation or an exhaustive relation search.

[`ExceptionalGetzler.lean`](../../AxiomaticGW/Surfaces/Fixtures/ExceptionalGetzler.lean) checks each selected complete equation against the Lean graph evaluator with `decide +kernel`. This replay needs neither Sage nor network access. [`Exceptional.lean`](../../AxiomaticGW/Surfaces/Exceptional.lean) then derives the three exceptional-class vanishings under the existing geometric laws and finite seeds. No additional seed is introduced, and the full class L = H−E₁−E₂ remains separate. The [validation record](../../environments/surface-exceptional-validation.json) distinguishes these proofs from the Sage search and remaining research gates.

### WDVV and strict-line base cases

The [base-case search](../../scripts/explore_wdvv_base_cases.py) uses the pinned three-column WDVV and 33-column Getzler frames with exact Sage rational arithmetic. It retains the full class, marking placements, inverse-metric signs and repeated variables in six WDVV and three Getzler requests. Reproduce the checked examples with:

```bash
conda run -n axiomatic-gw-sage python scripts/explore_wdvv_base_cases.py \
  --output /tmp/surface-wdvv-base-cases.json
lake build AxiomaticGWTest.Tautological.WDVVForgetful AxiomaticGWTest.Surfaces.WDVVBaseCases
python3 scripts/test_surface_equations.py
```

The [report](../../environments/surface-wdvv-base-cases.json) records 652 surviving uncollected contributions and 19 collected monomials. The two-point-blowup genus-zero system determines N₀(L;0)=1 from the existing line and Eᵢ seeds. Three requests in 2L give a rank-three system of determinant 1026. The Lean fixtures check every complete equation with `decide +kernel`; the numerical consumers derive nine further conditional values. The plane conic exercises the arbitrary-marking WDVV theorem with two added point insertions. No elliptic seeds are required for the genus-zero WDVV deductions, and no L-class seed is added. The [validation manifest](../../environments/surface-wdvv-validation.json) records the separate proof evidence and remaining geometric obligations.

The companion [finite pivot probe](../../scripts/explore_wdvv_pivots.py) uses Python exact fractions and the same pinned frame/component rules:

```bash
python3 scripts/explore_wdvv_pivots.py --energy-bound 12 \
  --output /tmp/surface-wdvv-pivot-exploration.json
```

Its [493-case report](../../environments/surface-wdvv-pivot-exploration.json) covers every full effective class of energy three through twelve, excluding the plane line seed. Energy-one/two base cases are separate. Each selected equation has the proposed nonzero coefficient and only positive, strictly lower-energy genus-zero point queries after removing its leading term. This is finite symbolic exploration using shared sources, not a uniform Lean theorem or an independent numerical GW computation. Research-scale enumeration, coefficient isolation and termination proofs remain open.

## Genus-one cotangent certificate and ancestor equations

The [psi search](../../scripts/search_genus_one_psi.py) uses the same pinned environment, temporary caches and disabled online lookup. It preserves the two original 3-spin parameter choices on the full stable locus, checks that they generate the complete returned source matrix, converts to monomial kappa coordinates and solves the exact held request. The [report](../../environments/genus-one-psi-exploration.json) records raw graph decorations and node automorphisms; two fresh-cache runs were byte-identical.

```bash
conda run --no-capture-output -n axiomatic-gw-sage python scripts/search_genus_one_psi.py \
  --output /tmp/genus-one-psi-exploration.json
python3 scripts/export_genus_one_psi.py /tmp/genus-one-psi-exploration.json \
  --output /tmp/genus-one-psi-replay.lean
lake env lean /tmp/genus-one-psi-replay.lean
python3 scripts/test_genus_one_psi.py -v
lake build AxiomaticGWTest.Tautological.PsiBoundaryExpansion
```

The [held Lean frame](../../AxiomaticGW/Tautological/GenusOnePsi.lean) is independent of incoming data. Its columns are the raw kappa class, external psi class and nonseparating pushforward; the loop's two automorphisms are kernel checked. The [archived replay](../../AxiomaticGW/Tautological/Fixtures/GenusOnePsiReplay.lean) proves each incoming decorated graph isomorphism and checks original rows, normalization, request and witness. Thus a proposed zero claim, a normalized coefficient 1/12 substituted for raw 1/24, or a change in a graph, row, witness or automorphism count is rejected. The nine Python tests include seven separately compiled negative fixtures. Ordinary replay requires only Lean.

The original rows' geometric vanishing is still an explicit hypothesis. [`PsiBoundaryExpansion.lean`](../../AxiomaticGW/Tautological/PsiBoundaryExpansion.lean) combines accepted replay with primitive cotangent, tail-divisor and gluing compatibility to derive the genus-one ancestor equation at any number of added markings; genus zero starts from dimension vanishing. The source's intersection values are diagnostics, not independent geometric proof or GW seeds. Stable-map descendant comparison and total numerical descendant reconstruction remain open. See the [validation manifest](../../environments/low-genus-psi-validation.json).

## Marked genus-two cotangent-square search and replay

The [fixed-frame search](../../scripts/search_genus_two_psi_square.py) uses Sage 10.9/admcycles 1.4, rational full-stable coordinates, fresh ephemeral caches and disabled online lookup. It preserves all seventeen raw codimension-two generators on $\overline M_{2,1}$. The six original FZ parameters are `((3),0)`, `((1,1,1),0)`, `((1,1),1)`, `((),3)`, `((1),0)`, `((),1)`; the parameter bound is `3*r-g-1 = 3`, not the codimension. The additional elliptic row records the actual graph-replacement destinations `[8,9,14]` for `102 kappa_1 - 30 psi_1 - 3 loop`. The two kappa-coordinate conversions are recorded before solving the boundary elimination problem. Decorated automorphism orders come from `autom_count`; a psi factor on one loop branch breaks a symmetry counted by the underlying undecorated graph.

The [report](../../environments/genus-two-psi-square-exploration.json) has SHA256 `6b9c75fd1555575fd036348e943881f6ba5cb8e83b7b7f51e64f7448286e5e1d`. Two fresh executions produced identical bytes. Seventeen intersection-pairing checks vanish and the diagnostic $\int\psi_1^4$ is $1/1152$; these Sage diagnostics are not geometric relation proofs. The [Lean frame](../../AxiomaticGW/Tautological/GenusTwoPsiSquare.lean) holds the raw columns, exact request and original rows separately from the [generated replay](../../AxiomaticGW/Tautological/Fixtures/GenusTwoPsiSquareReplay.lean). It proves the graph meaning of the elliptic gluing, both coordinate inverses, the rational consequence and its conditional class/CohFT interpretation. Original generator vanishings remain geometric inputs. No numerical genus-two surface value is certified here.

```bash
/opt/homebrew/Caskroom/miniforge/base/envs/axiomatic-gw-sage/bin/python scripts/search_genus_two_psi_square.py --output /tmp/genus-two-psi-square.json
python3 scripts/export_genus_two_psi_square.py environments/genus-two-psi-square-exploration.json --output AxiomaticGW/Tautological/Fixtures/GenusTwoPsiSquareReplay.lean --check
lake build AxiomaticGW.Tautological.Fixtures.GenusTwoPsiSquareReplay AxiomaticGWTest.Tautological.GenusTwoPsiSquare
python3 -m unittest discover -s scripts -p test_genus_two_psi_square.py -v
```

The exporter and Lean replay require neither Sage nor network access. Provenance checks reject wrong labels, loci, parameters, source pins and gluing maps. Kernel regressions distinguish incorrect separating branches from an equivalent loop-branch presentation, and test raw factors, decorated automorphisms, kappa-coordinate conversion, source rows, the exact witness and a jointly falsified zero claim. See the [validation record](../../environments/genus-two-psi-square-validation.json) for outcomes and resource observations. This fixed search supplements the R3/R4 infrastructure; it does not complete the general relation calculus or the BP/$L_{2,4}$ reconstruction route.

## Installation scope

The initial inspection found Miniforge base and `envs/agent`, neither containing Sage or admcycles. Installation created the separate environment above; no existing environment or shell startup file was changed. No historical comparison code has been run. Full package doctests, arbitrary higher-genus computations, and the eventual project-owned certificate exchange remain unverified by this smoke test.


## Decorated forgetful pullback comparison

The [Lean executable](../../scripts/DecoratedPullback.lean) exports the actual signed expansion from `CotangentTerm.addMarkings`. The [comparison script](../../scripts/explore_decorated_pullback.py) rebuilds these decorated graphs in pinned Sage/admcycles and compares them with `forgetful_pullback`. It checks all twenty BP diagrams and all six label assignments separately for one and two added markings, plus squared/product cotangent powers, zero powers, empty original label sets, unequal loop-branch powers and repeated symmetric placements.

```bash
lake build decoratedPullback
/opt/homebrew/Caskroom/miniforge/base/envs/axiomatic-gw-sage/bin/python -B scripts/explore_decorated_pullback.py
```

The default command builds and runs the current Lean executable. `--lean-input path.json` allows comparison of a separately captured native payload; its exact hash is recorded. Each run uses an ephemeral cache with online lookup disabled. The [held diagnostic report](../../environments/decorated-forgetful-exploration.json) records 252 cases, 1,159 signed terms and four rejected incorrect expansions. Canonical decorated raw incidence is compared in every case; 250 additional raw-vector equalities include both complete weighted BP equations. Their free raw supports have 118 and 315 coordinates. No relation quotient, class-zero oracle or intersection number is used. Two fresh-cache runs, one with supplied native output and one with a newly run executable, produced identical reports.

The native/Sage comparison is computational evidence. The universal pullback formula and bounds are separately proved in Lean, and the BP consequence uses the original accepted certificate and explicit primitive geometry. It does not supply a new GW seed or numerical invariant. See the [validation record](../../environments/decorated-forgetful-validation.json).

## Exact surface BP contractions

The [native exporter](../../scripts/SurfaceBP.lean) emits both dimension-filtered symbolic contractions and the affine equations obtained from the existing lower-genus algorithms. The [Sage checker](../../scripts/explore_surface_bp.py) independently enumerates component curve assignments and signed inverse-metric states on the actual admcycles pullbacks of all twenty published diagrams and six marking assignments. Ten cases include the plane line with two extra points, the F₁ fiber with one extra point, exceptional curves on both blowups and the strict line on the two-point blowup.

```bash
lake build surfaceBP
/opt/homebrew/Caskroom/miniforge/base/envs/axiomatic-gw-sage/bin/python -B scripts/explore_surface_bp.py --output /tmp/surface-bp.json
lake build AxiomaticGW.Surfaces.Fixtures.GenusTwoBP AxiomaticGWTest.Surfaces.GenusTwoTerms
```

The checker rebuilds and runs the native executable by default; `--lean-input` accepts a separately captured payload and records its hash. The executable accepts case names for focused diagnostics. Fresh caches and disabled online lookup keep the comparison offline. Two fresh runs give the identical [6995-byte report](../../environments/surface-bp-exploration.json), SHA256 `744d94ab338f0d284b979b57d581038ffd34b5dc7961a27fd5b930816b7b28bc`. Wrong exceptional metric signs, omitted marking assignments, discarded rational tails and collapse of full classes to energy are detected.

Lower-genus numerical values are shared outputs of the already proved Lean algorithms: the independent comparison checks graph contraction and substitution, not a second derivation of those numbers. Sample matrix ranks describe only the listed ancestor equations. Three small complete polynomials have separate Lean kernel replay requiring neither Sage nor the native executable. General affine support and the geometric equation are also kernel proofs. Neither the sampled ranks nor numerical agreement certify an invertible genus-two recursion or imported CohFT classes; see the [validation record](../../environments/surface-bp-validation.json).

## Normalized surface BP equations and native GKM calibration

The [normalizer](../../scripts/explore_normalized_surface_bp.py) independently applies string, dilaton and divisor one marking at a time, then subtracts positive-degree rational tails using the pinned [native GKM first-calibration matrices](../../environments/gkm-first-calibration-comparison.json). It first reruns the original admcycles graph contraction comparison. Full curve coordinates and ancestor/descendant tags remain distinct.

```bash
lake build surfaceBPNormalized
/opt/homebrew/Caskroom/miniforge/base/envs/axiomatic-gw-sage/bin/python -B scripts/explore_normalized_surface_bp.py --output /tmp/surface-bp-normalized.json
lake build AxiomaticGW.Surfaces.GenusTwoDerivedInitialValues AxiomaticGWTest.Surfaces.FirstDescendantReduction
```

By default the checker builds and runs both native exporters. `--ancestor-input` and `--lean-input` accept captured original and normalized payloads; both hashes are recorded. The [report](../../environments/surface-bp-normalized-exploration.json) checks ten equations, 85 individual substitutions and five additional probes, including multiple exceptional classes, a nonzero mixed-class tail and a retained higher power. Three new incorrect variants are distinguished: a positive rational-tail sign, a missing divisor cup term and a positive exceptional square. The four original graph mutations are also rejected. The small primitive-class equations alone did not detect the tail-sign mutation; the explicit nonzero-tail probes close that test gap.

The original lower-genus BP values remain shared Lean outputs. GKM matrices are previously checked ordinary first-calibration data, not imported semisimple CohFT classes. Sage agreement and finite sample ranks do not prove uniform pivots or uniqueness. Separate Lean theorems prove normalization and two derived initial values under named source geometry and the original finite seeds. Kernel replay requires neither Sage nor GKM; the [validation manifest](../../environments/surface-bp-normalized-validation.json) records the tested scope and outstanding gates.

## Two-marked genus-two cotangent product

The [held report](../../environments/genus-two-psi-product-exploration.json) uses 38 raw monomial graph columns on Mbar(2,2), ten original interior 3-spin rows, and three separating images of the previously held component rows. The input-label map is 1→0, 2→1. Both kappa-coordinate tables retain the correction from the kappa-one square to kappa-two. Raw pushforwards are not divided by graph automorphisms.

The complete boundary has 25 terms. Its only genus-two component occurs on a rational-tail graph with coefficient three and psi on the genus-two node branch. That component has one marking. All other terms have component genus at most one. Thus the relation does not assert that every dependency has lower genus. Original class-level source validity and primitive realization laws remain explicit; no new numerical seed or complete L24 equation is certified.

```bash
/opt/homebrew/Caskroom/miniforge/base/envs/axiomatic-gw-sage/bin/python -B scripts/search_genus_two_psi_product.py --output /tmp/genus-two-psi-product.json
python3 -B scripts/export_genus_two_psi_product.py environments/genus-two-psi-product-exploration.json --output AxiomaticGW/Tautological/Fixtures/GenusTwoPsiProductReplay.lean --check
lake build AxiomaticGW.Tautological.GenusTwoPsiProductGluing AxiomaticGWTest.Tautological.GenusTwoPsiProduct
python3 -B scripts/test_genus_two_psi_product.py
```

Only the search requires Sage/admcycles. Export and Lean replay work without Sage or network access. Kernel regressions reject eight altered mathematical claims, including omission of the same-genus tail, while accepting an isomorphic loop-branch presentation. See the [validation record](../../environments/genus-two-psi-product-validation.json) for reproducibility, assumptions and exact commands.


## Genus-two psi pullbacks and the complete L24 experiment

[`GenusTwoPsiForgetful.lean`](../../AxiomaticGW/Tautological/GenusTwoPsiForgetful.lean) derives arbitrary added markings from the original square/product source rows and primitive decorated pullback laws. The new fixed comparisons are the square on two and three markings and the product on three markings. Their raw vectors have 23, 53 and 62 nonzero entries. The [incoming replay](../../AxiomaticGW/Tautological/Fixtures/GenusTwoPsiPullbacksReplay.lean) checks them against the actual independently held Lean constructions and the existing 38- and 100-column frames. Graph coverage is proved separately, so an unsuccessful lookup cannot silently use column zero. Negative corrections, marking order and the retained genus-two product term are tested.

```bash
conda run -n axiomatic-gw-sage python scripts/search_genus_two_psi_pullbacks.py --output /tmp/psi-pullbacks.json
python3 -B scripts/export_genus_two_psi_pullbacks.py environments/genus-two-psi-pullbacks-exploration.json --output AxiomaticGW/Tautological/Fixtures/GenusTwoPsiPullbacksReplay.lean --check
lake build AxiomaticGW.Tautological.Fixtures.GenusTwoPsiPullbacksReplay AxiomaticGWTest.Tautological.GenusTwoPsiPullbacks
python3 -B scripts/test_genus_two_psi_pullbacks.py
conda run -n axiomatic-gw-sage python scripts/search_l24_normalization.py --output /tmp/l24-normalization.json
python3 -B scripts/test_l24_normalization.py
```

The [direct L24 report](../../environments/l24-normalization-exploration.json) retains the entire 721-term relation candidate, its 18-term primitive part, every source operation and rational coefficient. It starts with the full BP pullback times the stated psi combination. Twenty-nine genus-two psi reductions, 37 rational psi reductions and five WDVV corrections give the prescribed primitive part. No new interior relation is searched. All 1,516 raw substitutions agree with the independent native `StableGraph.glue_vertex` construction; three complementary intersection diagnostics vanish. Both searches use fresh temporary caches and disabled online lookup, and fresh reruns reproduce their JSON exactly.

The Python L24 operation regression reconstructs the recorded correction rows from the separately certified psi pullbacks, rational expansions and actual WDVV contexts and verifies the complete rational sum. The contextual maps and coefficient assembly now have the separate Lean replay below. The subsequent initial replay below now proves the BP coordinate comparison and full realized-class equation under the original geometric hypotheses. Original geometric source validity remains explicit, no new numerical seed is assumed, and no full L24 surface recursion or invariant is certified here. See the [validation record](../../environments/genus-two-psi-pullbacks-validation.json).

## Checked L24 corrections and initial-class comparison

The [correction exporter](../../scripts/export_l24_corrections.py) now binds the exact marking average, four primitive pictures, raw frame, all source-operation contexts and original source pins. Every one of the 29 high-power, 37 rational-psi and five WDVV rows has a Lean graph interpretation and kernel coefficient replay. Ordered finite coefficient records are checked before accumulation, retaining zero entries and repeated destinations; balanced tables avoid excessive kernel lookup cost. The independently held primitive diagrams and the complete 721-term sum are checked separately. No final class vanishing is inferred from intersection diagnostics.

```bash
python3 -B scripts/export_l24_corrections.py environments/l24-normalization-exploration.json --output AxiomaticGW/Tautological/Fixtures/L24CorrectionsReplay.lean --check
lake build AxiomaticGW.Tautological.L24Assembly AxiomaticGWTest.Tautological.L24Contexts
python3 -B scripts/test_l24_corrections.py
lake build decoratedPullback
.lake/build/bin/decoratedPullback > /tmp/decorated-pullback.json
python3 -B scripts/audit_l24_initial.py /tmp/decorated-pullback.json --output /tmp/l24-initial-audit.json
```

The native payload must match the existing decorated-pullback source pin. The [initial-row audit](../../environments/l24-initial-dimension-audit.json) starts from all 120 BP marking assignments and 306 signed terms. Multiplication by the four weighted external psi classes gives 1,224 occurrences; 198 vanish by local component dimension, distributed as 18, 60, 60 and 60. The retained terms produce 45 graph classes outside the correction frame before cancellation. That immutable JSON records the earlier diagnostic stage. The following Lean replay now proves the class-level pruning and exact cancellation; the raw free strata do not discard the dimension-zero terms.

The [initial exporter](../../scripts/export_l24_initial.py) emits only proposed lookup hints and signed coefficient records. It checks eight held source pins and the exact native payload before generating either file. It preserves the original BP operations, independently held auxiliary frame and `initialClaim`. All 409 candidate keys require full Lean graph checks; collisions or missing keys cannot themselves prove coverage. The [860-column frame](../../AxiomaticGW/Tautological/L24InitialGraphs.lean) includes the original 815 columns and 45 auxiliary graphs, with every marking permutation checked. All auxiliary coordinates cancel only after the prescribed average; 33 are nonzero in the unaveraged sum.

```bash
lake -q exe decoratedPullback > /tmp/decorated-pullback.json
python3 -B scripts/export_l24_initial.py /tmp/decorated-pullback.json --output-dir AxiomaticGW/Tautological --check
lake build AxiomaticGW.Tautological.L24Relation AxiomaticGWTest.Tautological.L24Initial
python3 -B scripts/test_l24_initial.py
```

The [checked records](../../AxiomaticGW/Tautological/Fixtures/L24InitialReplay.lean) equal the actual signed pullback, including repeated destinations and all zero markers, before consolidation. [`expression_eq_initial`](../../AxiomaticGW/Tautological/L24InitialClass.lean) proves equality after realization, using the component-dimension theorem. [`realized_full`](../../AxiomaticGW/Tautological/L24Relation.lean) then derives the complete 721-term relation from the original BP, four genus-two psi, two rational psi and WDVV source/compatibility hypotheses. The seven negative kernel tests prove that lost signed terms, unjustified pruning, nonzero pruning markers, wrong destinations/signs, changed normalization and missing averaging permutations cannot reproduce the checked records or target. Eight source-pin mutations, three payload mutations and duplicate JSON keys are rejected. These checks run offline without Sage; the upstream Sage exploration and its original pins are preserved.

See the [validation record](../../environments/l24-initial-class-validation.json). The four 306-entry data declarations use a local elaboration heartbeat budget of 800,000; the proofs remain kernel checked. The complete decorated GW contraction and surface equation family are supplied by the following extension. Geometric applicability, uniform genus-two reconstruction, every fixed benchmark and the full semisimple GKM completion gate remain open. No numerical seed or surface value is added.

## Complete L24 contractions and surface equations

The [gluing exporter](../../scripts/export_l24_gluing.py) proposes actual stable-component constructions for all 815 held columns. Lean checks every vertex, edge, external label and cotangent power against the original frame. The [GW theorem](../../AxiomaticGW/Tautological/L24GW.lean) retains all 721 nonzero coefficients and derives arbitrary-marking, full-curve-class equations from the original source relations and primitive geometry. The [surface implementation](../../AxiomaticGW/Surfaces/L24.lean) substitutes the existing genus-zero/one algorithms and proves affine genus-two support with effective full-class remainders.

```bash
python3 -B scripts/export_l24_gluing.py --output AxiomaticGW/Tautological/L24Gluing.lean --check
python3 -B scripts/export_surface_l24.py --output scripts/SurfaceL24.lean --check
lake build surfaceL24 AxiomaticGW.Surfaces.Fixtures.L24 AxiomaticGWTest.Surfaces.L24
lake -q exe surfaceL24 > /tmp/surface-l24.json
conda run -n axiomatic-gw-sage python -B scripts/explore_surface_l24.py \
  --lean-input /tmp/surface-l24.json --lean-source scripts/SurfaceL24.lean \
  --output /tmp/surface-l24-exploration.json
```

The comparison covers nine complete equations, including exceptional signs, distinct equal-energy classes, a mixed exceptional class and a signed added-marking pullback. Sage uses its own graph incidence data and forgetful operation. Lower-genus values are shared outputs of the Lean algorithms; their substitution is compared, not independently rederived by Sage. The report tests loss of nonprimitive terms, node powers, exceptional metric signs, negative tail corrections and full curve coordinates. Finite matrix ranks do not establish a uniform reconstruction pivot.

The native driver reuses repeated component calculations through [`ResidualCache`](../../AxiomaticGW/Surfaces/GenusTwoCachedTerms.lean). Its stored expressions are proved equal to the original component algorithm, and missing queries use that algorithm directly. `L24Relation.genusTwoTermsCached_eq` proves equality of the complete uncollected expressions for any selected cache keys. A materialized cache object is necessary: the first function-only implementation compiled to repeated cache construction at every vertex. Generated-code inspection checks that the final cache is built once per surface equation. The driver also combines the small per-monomial query sets before collecting repeated terms; `SurfaceL24Export.cacheQueries_eq` proves that this gives exactly the original query set. No external invariant values or additional seed hypotheses enter these optimizations.

The [degree-zero column records](../../environments/surface-l24-plane-zero-columns.json) retain every original column, including zeros, and eighteen uncollected contributions. The [kernel fixture](../../AxiomaticGW/Surfaces/Fixtures/L24.lean) checks bounded groups of columns before collecting the complete equation. It reproduces the residual dilaton equation with coefficients one and minus three and adds no numerical seed. The [normalized fixture](../../AxiomaticGW/Surfaces/Fixtures/GenusTwoNormalizedL24.lean) checks its cancellation after the existing ancestor-to-first-descendant substitution, under any valuation. [General normalized L24 soundness](../../AxiomaticGW/Surfaces/GenusTwoNormalizedL24.lean) uses the same source equations and finite seeds, together with the primitive rational-tail comparison already used for normalized BP.

```bash
python3 -B scripts/export_surface_l24_fixture.py \
  --probe-output /tmp/surface-l24-columns.lean
lake env lean --run /tmp/surface-l24-columns.lean > /tmp/surface-l24-columns.json
python3 -B scripts/export_surface_l24_fixture.py --input /tmp/surface-l24-columns.json \
  --output AxiomaticGW/Surfaces/Fixtures/L24.lean --check
python3 -B scripts/test_l24_gluing.py
python3 -B scripts/test_surface_l24_fixture.py
```

Native profiling identified the old BP normalization lookup in `L24Initial.bp` as a startup bottleneck. That expression now reuses the existing checked `rawPaperCoefficient` lookup; `bp_eq_original` proves equality with the original weighted expression. The source pins were updated for this equivalent implementation. The four coordinate declarations moved verbatim into `Fixtures/L24Claims.lean`, while the original replay module reexports them and retains every assembly proof. Executable declarations similarly moved without changes into the two `L24Terms` modules. The numerical driver uses these smaller imports, avoiding eager initialization of unused source-relation constructions. Public declaration names, held graph data, initial/final coordinate claims and historical reports are preserved. See the [validation manifest](../../environments/surface-l24-validation.json) for commands, resource measurements and the distinct proof and exploration boundaries. Uniform pivots, finite-seed sufficiency, the complete genus-two descendant reconstruction and class-valued semisimple GKM import remain required.

## Combined normalized BP/L24 leading systems

[`GenusTwoNormalizedSupport.lean`](../../AxiomaticGW/Surfaces/GenusTwoNormalizedSupport.lean) proves that normalization preserves affine genus-two support and full effective remainders. All non-input-class dependencies strictly decrease energy. Its coefficient theorem permits leading-matrix extraction using only input-class ancestors and direct normalization; this does not remove calibration corrections from the full equation.

```bash
conda run -n axiomatic-gw-sage python -B scripts/explore_genus_two_leading.py \
  --bp-input /tmp/surface-bp.json --l24-input /tmp/surface-l24.json \
  --output /tmp/genus-two-leading-exploration.json
```

Generate the two native inputs using the preceding BP and L24 workflows. Their exact previously verified payload digests are checked before the pilot runs. The [30257-byte report](../../environments/genus-two-leading-exploration.json) combines nineteen equations into eight finite systems and compares direct extraction with the full recursive reference normalization using the existing pinned GKM calibration. This reuses the earlier reference normalizer and low-genus outputs; it does not independently recheck the original graph computations. Sage computes exact rational ranks. Every dimension-compatible canonical primary/first-descendant column is included, even if absent from the sampled equations. In the plane-line sample the primary column is entirely zero, and the combined rank is 2 of 3; the F₁ fiber rank is 2 of 4. Other equation families or initial constraints are still needed, and no finite rank is promoted to a uniform reconstruction proof. Two fresh-cache runs reproduce the report exactly. See the [validation manifest](../../environments/genus-two-normalized-support-validation.json).


## Direct evaluation of genus-two leading matrices

[`GenusTwoLeadingTerms.lean`](../../AxiomaticGW/Surfaces/GenusTwoLeadingTerms.lean) supplies exact BP/L24 entries without computing positive-class lower-genus invariants. The imported gluing theorem proves the reduction to class-zero other components, and [`GenusTwoLeadingRelations.lean`](../../AxiomaticGW/Surfaces/GenusTwoLeadingRelations.lean) proves equality with the full normalized coefficients. The native program imports the term layer; importing the complete relation proof assembly also initializes unused source-coordinate constructions before `main`, as confirmed by the recorded startup profile.

```bash
python3 -B scripts/export_genus_two_leading.py --output scripts/GenusTwoLeading.lean --check
lake build genusTwoLeading
.lake/build/bin/genusTwoLeading > /tmp/genus-two-leading-native.json
conda run -n axiomatic-gw-sage python -B scripts/compare_genus_two_leading.py \
  --input /tmp/genus-two-leading-native.json --output /tmp/genus-two-leading-matrix.json
conda run -n axiomatic-gw-sage python -B scripts/test_genus_two_leading.py
```

The [native payload](../../environments/genus-two-leading-matrix-native.json) contains all canonical columns in twenty-five rows. The [Sage report](../../environments/genus-two-leading-matrix-exploration.json) compares nineteen of them with the pinned complete-equation normalization report, and checks six additional mixed-point BP requests. All six new canonical rows vanish. The plane-line rank remains 2/3 and the F₁ fiber rank 2/4. These finite submatrices do not prove complete support or uniform solvability. No genus-two numerical invariant is added. The comparison shares relation data and direct normalization with the previous workflow; it adds no independent geometric or localization verification.

The initial native import graph was interrupted after a profile located eager initialization in the two-marked psi-product source rows. Only the new evaluator modules were reorganized into executable terms and proof consumers; existing public interfaces and source relations were preserved. The completed native runs took 7.462 and 6.330 seconds and produced identical 9742-byte payloads. The report is reproducible with fresh Sage caches. Request-binding tests reject changed coefficients, curve coordinates, missing columns/cases, repeated cases, invalid denominators and changed labels. The [validation manifest](../../environments/genus-two-leading-validation.json) records exact evidence, assumptions and remaining gates.


## Shifted-degree plane BP coefficients

The [general coefficient evaluator](../../AxiomaticGW/Surfaces/GenusTwoCoefficients.lean) now preserves smaller-class variables, positive-class complements and full calibration tails. Both [family equality theorems](../../AxiomaticGW/Surfaces/GenusTwoCoefficientRelations.lean) refer to the original normalized polynomials. The [plane audit](../mathematics/PlaneGenusTwoShifted.md) explains why mixed-point equations at degree `d+1` are relevant to the missing degree-`d` primary column.

```bash
lake build genusTwoShifted
.lake/build/bin/genusTwoShifted > /tmp/genus-two-shifted-native.json
sage -python -B scripts/explore_genus_two_shifted.py --input /tmp/genus-two-shifted-native.json --output /tmp/genus-two-shifted-exploration.json
sage -python -B scripts/test_genus_two_shifted.py
```

The pinned Sage 10.9 / admcycles 1.4 environment runs in a fresh temporary cache with online lookup disabled. The ten-row native export took 131.098 seconds in the recorded run. All rows agree with direct symbolic multinomial contraction; seven additionally agree with actual admcycles pullbacks and incidence-based contraction. The symbolic matrix has determinant `7776d`, with no interpolation. Shared BP, plane and genus-zero sources are identified explicitly. Nine altered request/encoding cases and a changed numerical coefficient are rejected, and removing the signed pullback correction changes the symbolic row.

The [payload](../../environments/genus-two-shifted-native.json), [exploration](../../environments/genus-two-shifted-exploration.json) and [initial validation record](../../environments/genus-two-shifted-validation.json) distinguish the coefficient algorithm from the symbolic matrix. The subsequent [point-compression proof](../../AxiomaticGW/Surfaces/PointPullbackContraction.lean) now identifies a recursive binomial contraction with the full signed pullback for every number of added primary points. The driver uses its [proved BP coefficient consumer](../../AxiomaticGW/Surfaces/GenusTwoPointCoefficients.lean), reproducing all ten held rows exactly in 68.925 seconds in the recorded run. The exploration report was regenerated to pin that driver.

The [kernel fixture](../../AxiomaticGW/Surfaces/Fixtures/GenusTwoShifted.lean) proves the source-degree-two `PPP` coefficient `-18` on `H_1`; the standalone check took 39.957 seconds and peak child RSS 7866630144 bytes. Two earlier monolithic attempts were interrupted. A second kernel replay proves the shifted `HPP` coefficient `-36` on `N_1`, retaining the separate diagram contributions `-12, 0, 18, -42`; its standalone check took 48.191 seconds. The entire symbolic matrix and the other numerical entries still require replay or uniform proofs. The subsequent [plane normalization proof](../../AxiomaticGW/Surfaces/PlaneNormalization.lean) removes all ordinary plane calibration tails term by term and gives canonical divisor-count and dimension formulas. The [plane coefficient implementation](../../AxiomaticGW/Surfaces/PlaneGenusTwoCoefficients.lean) uses exact component-class pruning, with equality to the complete generic coefficient. The explorer now pins these proof sources and records those completed boundaries separately from the open uniform matrix theorem; see the [plane validation](../../environments/plane-normalization-validation.json). The [new validation record](../../environments/point-pullback-validation.json) records these boundaries. The [effective-remainder evaluator](../../AxiomaticGW/Surfaces/PlaneGenusTwoRemainder.lean) now replaces full source-class splitting throughout the signed point recursion, with an equality theorem and an explicit degree-order check before subtraction. The exporter pins its four support/reindexing modules and records this completed boundary separately from the open uniform symbolic matrix; see the [remainder validation](../../environments/genus-two-remainder-validation.json). No genus-two invariant value, new seed, uniform reconstruction theorem or imported CohFT is asserted.

The [primary-point and cotangent-tail increment](../../environments/genus-two-primary-points-validation.json) proves closed rational placement sums and the full one-psi component at a one-degree plane remainder. The explorer pins the three new proof modules and records these completed boundaries separately from its still-unproved full matrix. The native payload and all ten requested rows are unchanged. The zero-remainder one-psi formula is closed by the following increment; complete matrix support, reconstruction and class-valued GKM integration remain open.

The [zero-remainder and PPP-row increment](../../environments/genus-two-zero-remainder-validation.json) proves the complete classical unit correction, its canonical terminal normalization, and the uniform `PPP` row `(0, -18, 18d)` in the full BP equation. The explorer pins the three new proof modules and records the one-degree-remainder support separately from the still-open other rows and reconstruction. Its search algorithm, numerical requests and expected coefficients are unchanged. Targeted replay and comparison have passed; the validation record identifies the project-wide rebuild still in progress.

The [mixed-plane increment](../../environments/genus-two-mixed-plane-validation.json) proves the rational `HP`/`HH` contractions and source-degree cancellation in all three mixed BP rows. The explorer pins both new proof modules and distinguishes strict support below the equation degree from the still-open canonical support at the degree to be reconstructed. Its numerical algorithm, ten requests, expected coefficients and negative-tail corruption check are unchanged. The full matrix and reconstruction flags remain false.


The [HPP increment](../../environments/genus-two-hpp-validation.json) proves the complete row `(-36, 12-36d, 36d²)`, exact canonical support and strict degree decrease after its three canonical variables are removed. The explorer additionally pins the coefficient-renaming API, canonical component module and full HPP proof. Its numerical calculation and held ten-row input are unchanged. At that checkpoint the proof flags covered only HPP. The following extension completes the coefficient matrix while retaining the open reconstruction boundary.


The [complete plane coefficient-block increment](../../environments/genus-two-plane-system-validation.json) proves HHP and exact canonical support, the extracted HHP/HPP/PPP matrix and determinant `7776d`, strict lower-degree support in all three rows, and an executable rational block solver with correctness and uniqueness. The explorer pins both new proof modules and records the positive-degree three-row scope explicitly. Its held native payload and numerical algorithm are unchanged. The lower-degree recursive evaluator, new invariant values and full class-valued semisimple CohFT import remain unclaimed.

The same audit now includes the proved coefficient collection, retained lower-degree remainder and geometric solved step. The explorer additionally pins `CollectedTerms`, `PlaneShiftedRemainder` and `PlaneShiftedStep`, and records their completed proof boundaries. The numerical rows, matrix, native payload and independent-comparison counts are unchanged. The flag for total lower-degree recursive evaluation remains false.

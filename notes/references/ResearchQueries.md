# Computing a surface invariant

From the repository root, give the query command a JSON file and a new path for its Lean theorem. It returns an exact rational and the geometric interpretation theorem whose hypotheses identify the computation with a GW invariant. A working offline installation needs the Lean toolchain in `lean-toolchain`, the dependencies in `lake-manifest.json`, and the compiled modules for the requested calculation.

## A genus-one calculation on the exceptional curve

For the exceptional curve of the one-point blowup, compute
$\langle\tau_1(E),E,E\rangle_{1,E}$. The order below puts the cotangent power on the first occurrence of the divisor. Save the following as `query.json`.

```json
{"target":"X1","genus":1,"class":[1,0],"insertions":[["E1",1],["E1",0],["E1",0]]}
```

```sh
lake build AxiomaticGW.Surfaces.GenusOneDescendants
python3 -B scripts/gw_query.py query.json --certificate Exceptional.lean
lake env lean Exceptional.lean
```

The output field `ordinary_rational` is `[1,12]`. This is a direct evaluation of the general genus-one descendant algorithm. The exported theorem contains the ordered request and concludes that `SurfaceGenusOne.queryValue?` on that request equals `some (1 / 12 : ℚ)`. Geometric interpretation requires the surface identification, gluing and cotangent compatibilities, the WDVV and Getzler inputs, rational-tail comparison, and the indicated line, exceptional and genus-one divisor seeds. In particular the two primary exceptional insertions involve the signed self-intersection $E^2=-[\mathrm{pt}]$. [Geometric inputs and conventions](../mathematics/SurfaceReconstructionInputs.md) · [Interpretation theorem](../../AxiomaticGW/Surfaces/GenusOneDescendants.lean)

### Request and result

| Field | Meaning |
| --- | --- |
| `target` | `X0` for the plane, `X1` for the one-point blowup, `X2` for the two-point blowup |
| `class` | Nonnegative integer coefficients in the ordered effective bases $(H)$, $(E,F)$, or $(E_1,E_2,H-E_1-E_2)$ respectively |
| `genus` | Integer 0, 1, or 2 |
| `insertions` | Ordered pairs of a basis label and a nonnegative descendant power. Labels are `unit`, `H`, `pt`, and the exceptional labels present on the target (`E1`, `E2`). Repeated markings are retained. |

An empty insertion list is valid at positive degree. At degree zero, the geometric domain requires $2g+n>2$. Codimensions are complex. In the result, `geometric_seed_hypotheses` lists the explicit numerical seed arguments of the named interpretation theorem. The theorem also specifies any required geometric laws. The result gives the query, derivation, exact fraction, Lean version, pinned mathlib revision, certificate SHA-256 and axiom audits. Lean checks that the query has geometric domain, that the returned fraction belongs to the specified request, and that the exported `geometric` theorem gives the requested value under the original geometric inputs. Its full Lean name is in `geometric_theorem`. Use `#print sig` on that name to see every hypothesis. The Python program audits the reported axioms. Each specialized benchmark also checks the corresponding complete query or its equality with the selected canonical family.

Known bounded tables can accelerate a calculation. Other geometric requests use the terminating descendant evaluators, whose kernel replay can be expensive. `--timeout 180` allows 180 seconds for each of the candidate and proof passes. A failed check returns `unverified` with its diagnostic and creates no certificate.

The same entry point accepts exact Sage integers. Launch Sage in the repository after building the relevant module.

```python
import sys
sys.path.insert(0, "scripts")
from gw_query import reconstruct, save_certificate
from pathlib import Path
request = {"target": "X1", "genus": 1, "class": [1, 0],
           "insertions": [["E1", 1], ["E1", 0], ["E1", 0]]}
result, theorem = reconstruct(request)
assert result["ordinary_rational"] == [1, 12]
save_certificate(Path("ExceptionalFromSage.lean"), theorem)
```

## Genus-two plane quartics through thirteen points

For the plane in degree four the anticanonical energy is twelve. Thirteen primary point insertions give a dimension-compatible genus-two request. The reconstruction certificate returns $27$ and identifies the ordered request with the geometric GW evaluation under the plane reconstruction hypotheses. The frozen Belorousski–Pandharipande benchmark records the same primary value as the first entry of the quartic triple $(27,42,25/4)$. The convention counts individually specified point insertions without a factorial. [Published-value manifest and its source](../../environments/plane-genus-two-benchmarks.json)

```sh
lake build AxiomaticGW.Surfaces.PlaneGenusTwoBenchmarks
```

```python
import sys
from pathlib import Path
sys.path.insert(0, "scripts")
from gw_query import reconstruct, save_certificate

quartic = {"target": "X0", "genus": 2, "class": [4], "insertions": [["pt", 0]] * 13}
result, proof = reconstruct(quartic)
assert result["ordinary_rational"] == [27, 1]
save_certificate(Path("PlaneQuartic.lean"), proof)
```

Replay with `lake env lean PlaneQuartic.lean`. The `geometric_theorem` named in the result retains the surface identification, graph and cotangent comparisons, relation certificates, and numerical seeds used by the plane theorem. [Saved quartic certificate](../../environments/gw-research-plane-quartic.lean) · [Degree-four table](../../AxiomaticGW/Surfaces/Fixtures/GenusTwoPlaneTable.lean) · [Plane query checker](../../AxiomaticGW/Surfaces/PlaneGenusTwoBenchmarks.lean)

## Searching for a relation on the separating boundary

In codimension two on $\overline{\mathcal M}_{2}$, compare the separating graph with $\kappa_1$ at an elliptic vertex to the graph with $\psi$ on its incident branch. These are columns 2 and 3 in the reviewed eight-column frame (zero-based). Ask for their difference in monomial-kappa coordinates. The input specifies all eight raw graph coefficients independently of the row weights found by Sage. [Graph definitions and row conventions](../../AxiomaticGW/Tautological/Fixtures/AdmcyclesGenusTwo.lean)

```sh
lake build AxiomaticGW.Tautological.Fixtures.AdmcyclesGenusTwo
conda run -n axiomatic-gw-sage python -B scripts/admcycles_smoke.py > admcycles-rows.json
conda run -n axiomatic-gw-sage python -B scripts/search_admcycles_span.py --report admcycles-rows.json 0 0 1 -1 0 0 0 0 > Separating.lean
lake env lean Separating.lean
```

The witness assigns $1/72$ to row 3 and $-1/72$ to row 4. Their coefficients on the two-edge column cancel and the other two coefficients give precisely $+1,-1$. The exported `in_span` theorem proves membership in the span of the seven fixed rows. Its `evaluated` theorem proves vanishing for any rational-linear evaluation that annihilates those rows. Geometric vanishing uses that premise. Changing the eight arguments searches the same frame for another expression. The saved report is the default input when `--report` is omitted. Only the search and the optional report regeneration require Sage. [Sage search](../../scripts/search_admcycles_span.py) · [Certificate interpretation](../../AxiomaticGW/Tautological/RelationCertificate.lean)

## Comparing with GKM localization

For the worked genus-one example above, generate an independent localization report from the same JSON request and compare the two results. The report retains the complete fraction in the two torus characters. The exported `comparison` theorem binds the ordinary answer to that exact fraction via `EquivariantCoefficients.Specializes`, with a kernel proof that the displayed denominator is regular at zero. Its geometric interpretation still requires the surface inputs. The [saved worked report](../../environments/gkm-research-f1-elliptic-exceptional.json) can replace the exploration output for offline replay.

```sh
conda run -n axiomatic-gw-sage python -B scripts/gkm_research_query.py query.json --producer "$GKM_PRODUCER" --output localized.json
python3 -B scripts/gw_query.py query.json --gkm-report localized.json --certificate Compared.lean
lake env lean Compared.lean
```

The producer computes rational equivariant functions. Its report records both those functions and the ordinary specializations. For the 17 genus-two one-marking cases, regenerate the candidate report in the pinned Sage 10.9 and admcycles 1.4 environment, then compare the generated Lean data with the held export. Set `GKM_PRODUCER` to the pinned producer checkout.

```sh
conda run -n axiomatic-gw-sage python -B scripts/gkm_genus_two_one_marking.py explore --producer "$GKM_PRODUCER" --output one-marking.json
python3 -B scripts/gkm_genus_two_one_marking.py replay one-marking.json --output AxiomaticGW/GKM/Fixtures/GenusTwoOneMarkingClaims.lean --check
lake build AxiomaticGW.GKM.Fixtures.GenusTwoOneMarkingReplay
```

The final command checks the ordinary answers against the surface algorithms. The report carries the incoming numerators, denominators, state labels, powers, and full curve classes. These comparisons share intersection-theoretic inputs with admcycles. The class-valued CohFT comparison and construction of the geometric input laws are separate open requirements. [Exchange conventions and pins](GKMExchange.md)

## Replaying the worked examples offline

The saved certificates for the separating boundary, the exceptional curve and the plane quartic replay using Lean and the pinned dependencies. Each contains the exact requested graph coefficients or the ordered surface query. A preinstalled Lean toolchain and mathlib packages at the revisions in the manifest are sufficient. Build the project modules locally, then check the saved files.

```sh
lake --no-cache build AxiomaticGW.Tautological.Fixtures.AdmcyclesGenusTwo AxiomaticGW.Surfaces.GenusOneDescendants AxiomaticGW.GKM.EquivariantCoefficients
lake env lean environments/admcycles-research-unmarked-separating.lean
lake env lean environments/gkm-research-f1-elliptic-exceptional.lean
lake --no-cache build AxiomaticGW.Surfaces.PlaneGenusTwoBenchmarks
lake env lean environments/gw-research-plane-quartic.lean
```

The separating-boundary certificate exposes the two row weights. The exceptional-curve certificate exposes the arithmetic answer, its regular specialization, its geometric theorem, and the axiom audit. Both of those examples passed offline replay with newly built project modules using the pinned dependency cache. The saved quartic proof also replayed against the compiled modules of the previous published commit. [Separating-boundary proof](../../environments/admcycles-research-unmarked-separating.lean) · [Exceptional-curve proof](../../environments/gkm-research-f1-elliptic-exceptional.lean)

The `--gkm-report` option also accepts the saved genus-zero and genus-one descendant frames, the three-point frame, and the genus-two degree-zero, plane few-marking, fiber, exceptional and strict-line frames. The reader checks the entire report using its original request frame and then selects the exact ordered row.

## Bounded exceptional queries

The fixed few-marking manifest contains 106 requests on the first blowup and 514 on the second with positive plane-degree-zero class and a point marking. Each ordered request has a theorem giving `checkedEval = some 0` for a stable-map intersection theory satisfying exceptional point-pullback support. A descendant on the strict transform of the line can instead be nonzero. For class $H-E_1-E_2$ the one-marking result $\langle\tau_2(H)\rangle_2=1/240$ agrees with GKM. [Point-supported cases](../../AxiomaticGW/Surfaces/Fixtures/GenusTwoExceptionalFewMarkings.lean) · [Strict-line comparison](../../AxiomaticGW/GKM/Fixtures/BlowupTwoLineOneMarkingReplay.lean)

```sh
python3 -B scripts/export_exceptional_few_markings.py --check
lake build AxiomaticGWTest.Surfaces.GenusTwoExceptionalFewMarkings
```

For two-marked queries on the primitive exceptional curves and the strict line, the string and dilaton reductions retain the order of both insertions. For example, the following request has value $1/80$ since the dilaton factor is three and the strict-line singleton has value $1/240$.

```json
{"target":"X2","genus":2,"class":[0,0,1],"insertions":[["H",2],["unit",1]]}
```

Save it as `strict-line.json` and run the following comparison. The standalone arithmetic theorem concerns the unit reduction. Its cited geometric theorem interprets the result using the original reconstruction equations, the string and dilaton laws, and the named seeds. [Ordered two-marking comparisons](../../AxiomaticGW/GKM/Fixtures/GenusTwoUnitPairReplay.lean)

```sh
lake build AxiomaticGW.GKM.Fixtures.GenusTwoUnitPairReplay
python3 -B scripts/gw_query.py strict-line.json --gkm-report environments/gkm-genus-two-unit-pairs.json --certificate StrictLine.lean
lake env lean StrictLine.lean
```

The held divisor-pair report includes both marking orders and the divisor-square correction. On the plane line, $\langle H,\tau_4(H)\rangle_{2,H}= -1/960-1/240=-1/192$. The second term comes from $H^2=\mathrm{pt}$. All six plane comparisons and all 106 blowup comparisons have exact values. On the strict line the original 815-term equation gives the hyperplane canonical value zero. This settles both signs of the divisor-square correction and also proves the point singleton vanishes. [Absolute strict-line replay](../../AxiomaticGW/GKM/Fixtures/BlowupTwoLineCompletedReplay.lean) [Divisor-pair proofs](../../AxiomaticGW/GKM/Fixtures/GenusTwoDivisorPairReplay.lean) · [Exact GKM report](../../environments/gkm-genus-two-divisor-pairs.json)

## Genus-two requests at anticanonical energy one

The fixed few-marking manifest has 52 such requests on F₁ and 240 on the two-point blowup. The latter distinguish $E_1$, $E_2$ and $H-E_1-E_2$, with 80 ordered requests in each class. The plane has no effective class of this energy. The complete GKM report records 18 nonzero values on the first blowup and 96 on the second. All 292 ordinary values are kernel-checked by the original mixed descendant recursion, the marked equations, or exceptional point support. The 13 distinct saved bivariate fractions specialize to those values. For these requests the command also proves that the full incoming function equals the certified function in the coefficient field. An alternative regular presentation of the same function is accepted. A term such as $xy$ that vanishes only at zero changes the function and fails the check. The result exposes the full-field proof in `equivariant_comparison_theorem`. [Native frame](../../environments/gkm-genus-two-energy-one.json) · [Ordered comparison and uniqueness](../../AxiomaticGW/GKM/Fixtures/GenusTwoEnergyOneReplay.lean)

For example, save the following request as `divisor-pair.json`. Both insertions are first descendants of the exceptional divisor on its own curve.

```json
{"target":"X1","genus":2,"class":[1,0],"insertions":[["E1",1],["E1",1]]}
```

```sh
lake build AxiomaticGW.GKM.Fixtures.GenusTwoPositivePairReplay AxiomaticGW.Surfaces.GenusTwoBlowupDescendantReconstruction
python3 -B scripts/gw_query.py divisor-pair.json --gkm-report environments/gkm-genus-two-energy-one.json --certificate PositivePair.lean
lake env lean PositivePair.lean
```

The first blowup now has a certificate for every energy-one request. For a second descendant of the unit paired with a first exceptional descendant, use `[["unit",2],["E1",1]]` in the same class. Build `AxiomaticGW.GKM.Fixtures.GenusTwoEnergyOneF1Replay` and run the same comparison with a new certificate path. The ordinary value is $-5/288$ in either marking order. The pair `[["unit",2],["unit",2]]` gives $19/960$. [Complete first-blowup theorem](../../AxiomaticGW/GKM/Fixtures/GenusTwoEnergyOneF1Replay.lean)

The two-divisor example gives $1/144$. The product relation uses all 25 graphs and the two signed calibration tails. The 31 divisor-pair comparisons include both orders of distinct divisors. To regenerate the complete localization frame, run the pinned Sage environment against the pinned producer. [Product formula](../../AxiomaticGW/Surfaces/Fixtures/GenusTwoPrimitiveDivisorProduct.lean)

```sh
conda run -n axiomatic-gw-sage python -B scripts/gkm_genus_two_energy_one.py explore --producer "$GKM_PRODUCER" --output energy-one.json
python3 -B scripts/gkm_genus_two_energy_one.py replay energy-one.json --output AxiomaticGW/GKM/Fixtures/GenusTwoEnergyOneClaims.lean --check
python3 -B scripts/export_genus_two_energy_one_reductions.py --check
python3 -B scripts/gkm_genus_two_energy_one_equivariant.py replay energy-one.json --output AxiomaticGW/GKM/Fixtures/GenusTwoEnergyOneEquivariant.lean --check
lake build AxiomaticGWTest.GKM.GenusTwoEnergyOne
```

## A nonzero descendant in the fiber class of $F_1$

In the full curve coordinates $(E,F)$, the genus-two fiber request with insertion $\tau_2(\mathrm{pt})$ is

```json
{"target":"X1","genus":2,"class":[0,1],"insertions":[["pt",2]]}
```

Save it as `fiber-point.json` and run the comparison.

```sh
lake build AxiomaticGW.GKM.Fixtures.F1FiberOneMarkingReplay AxiomaticGW.Surfaces.GenusTwoBlowupDescendantReconstruction
python3 -B scripts/gw_query.py fiber-point.json --gkm-report environments/gkm-f1-fiber-one-marking.json --certificate FiberPoint.lean
lake env lean FiberPoint.lean
```

The ancestor contribution is $7/1440$. The signed calibration contributes $-1/1440$, giving a geometric evaluation of $1/240$ under the reconstruction hypotheses. All four fiber singletons have full-field comparisons. [Fiber reconstruction](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1FiberOneMarking.lean) · [Incoming GKM fractions](../../AxiomaticGW/GKM/Fixtures/F1FiberOneMarkingReplay.lean)

## Comparing equal-energy classes on the one-point blowup

The fiber $F=(0,1)$ and the exceptional double $2E=(2,0)$ have anticanonical energy two. The singleton $\tau_3(E)$ distinguishes them. Reconstruction gives $-23/2880$ in class $F$ and $3/320$ in class $2E$. To compute the latter, save the following as `double-exceptional.json`.

```json
{"target":"X1","genus":2,"class":[2,0],"insertions":[["E1",3]]}
```

```sh
lake build AxiomaticGW.GKM.Fixtures.F1DoubleExceptionalOneMarkingReplay AxiomaticGW.Surfaces.GenusTwoBlowupDescendantReconstruction
python3 -B scripts/gw_query.py double-exceptional.json --gkm-report environments/gkm-f1-double-exceptional-one-marking.json --certificate DoubleExceptional.lean
lake env lean DoubleExceptional.lean
```

For a pair with two positive cotangent powers, save this request as `fiber-pair.json`. The expected value is $-113/2880$.

```json
{"target":"X1","genus":2,"class":[0,1],"insertions":[["unit",3],["E1",1]]}
```

```sh
lake build AxiomaticGW.GKM.Fixtures.F1FiberPairsReplay AxiomaticGW.Surfaces.GenusTwoBlowupDescendantReconstruction
python3 -B scripts/gw_query.py fiber-pair.json --gkm-report environments/gkm-f1-fiber-pairs.json --certificate FiberPair.lean
lake env lean FiberPair.lean
```

The held fiber-pair certificate can also be replayed directly with `lake env lean environments/gkm-research-f1-fiber-pair.lean`. It records the ordered query, the arithmetic proof, the equality of rational functions in both torus characters, and their regular specialization. Its geometric theorem retains the reconstruction assumptions. To reproduce the localization with Sage and admcycles, run the following with the pinned producer checkout. The second command uses only the held report and Python.

```sh
conda run -n axiomatic-gw-sage python -B scripts/gkm_f1_energy_two.py fiber-pairs explore --producer /path/to/gkm_localisation --output fiber-pairs.json
python3 -B scripts/gkm_f1_energy_two.py fiber-pairs replay fiber-pairs.json --output AxiomaticGW/GKM/Fixtures/F1FiberPairs.lean --check
```

## Two seed-free vanishing computations

On the two-point blowup let $L=H-E_1-E_2$ and $\beta=E_2+L$. To compute $\langle E_2,\tau_3(H)\rangle_{2,\beta}$, save the ordered request in `divisor.json`.

```json
{"target":"X2","genus":2,"class":[0,1,1],"insertions":[["E2",0],["H",3]]}
```

```sh
lake build AxiomaticGW.Surfaces.GenusTwoZeroDivisorPairs
python3 -B scripts/gw_query.py divisor.json --certificate Divisor.lean
lake env lean Divisor.lean
```

The divisor equation gives zero. The coefficient of the original singleton is $E_2\cdot(E_2+L)=-1+1=0$. The correction term contains $E_2\smile H=0$. Replacing $E_2$ by $E_1$ leaves the energy and cotangent degrees unchanged, but the intersection coefficient becomes one. The certificate checks the full class and the marked states. [Divisor theorem](../../AxiomaticGW/Surfaces/GenusTwoZeroDivisorPairs.lean) · [Signed-cup and class controls](../../AxiomaticGWTest/Surfaces/GenusTwoZeroDivisorPairs.lean)

For a positive-degree request with no markings, save `{"target":"X0","genus":0,"class":[5],"insertions":[]}` as `empty.json` and run the same query command with `empty.json --certificate Empty.lean`. Its total insertion codimension is zero and its complex virtual dimension is fourteen. The emitted theorem derives zero directly from the surface grading. Both examples report an empty numerical seed list. Adding `--gkm-report environments/gkm-zero-divisor-bl2-partial.json` to the divisor query also compares its full torus rational function after building `AxiomaticGW.GKM.Fixtures.BlowupTwoZeroDivisorPairsPartial`. The snapshot lists each complete native curve class in `coverage.complete_classes`. [Dimension proof](../../AxiomaticGW/Surfaces/DimensionVanishing.lean) · [Native class receipts](../../environments/gkm-zero-divisor-bl2-partial.json)

## A nonconstant equivariant descendant of a plane line

The ordinary value of $\langle\tau_2(\mathrm{pt})\rangle_{0,H}$ is zero. With the pinned point lift, the full equivariant answer is $2y-x$. Save the following as `plane-line.json`.

```json
{"target":"X0","genus":0,"class":[1],"insertions":[["pt",2]]}
```

```sh
lake build AxiomaticGW.GKM.Fixtures.PlaneLineOneMarkedPointReplay AxiomaticGW.Surfaces.DimensionVanishing
python3 -B scripts/gw_query.py plane-line.json --gkm-report environments/gkm-research-plane-line-point-square.json --certificate PlaneLine.lean
lake env lean PlaneLine.lean
```

The saved example also replays directly with `lake env lean environments/gkm-research-plane-line-point-square.lean`. At the point supporting the lift, the two tangent weights are $x-y$ and $-y$. For any power $k$ the two marked directions give the sum $[y^k-(y-x)^k]/x$. Lean proves that this quotient is polynomial and is nonzero for every $k>0$. Its constant term is one at $k=1$ and zero otherwise. The ordinary comparison uses the original genus-zero line reconstruction at $k=1$ and the signed virtual dimension at every other power. Replacing $2y-x$ by $3y-x$ preserves the ordinary zero and fails the exported full-field proof. The pinned producer check can be reproduced with `conda run -n axiomatic-gw-sage python -B scripts/check_gkm_plane_line_point.py --producer /path/to/gkm_localisation`. It checks all 30 individual contributions and the edge, tangent, insertion and source factors on each supported locus. Lean sums the six original marked-end terms. The geometric source of the factors and the unstable conventions is Liu–Sheshmani, Theorem 4.7 and equations (4.7)–(4.8). [Localization formula](https://sigma-journal.com/2017/048/sigma17-048.pdf#page=19) · [Two-flag formula](../../AxiomaticGW/GKM/Fixtures/PlaneLineOneMarkedPoint.lean) · [Ordinary geometric comparison](../../AxiomaticGW/GKM/Fixtures/PlaneLineOneMarkedPointReplay.lean)

For the preceding plane-line example the numerator before cancellation is $2xy-x^2$ and the denominator is $x$. A single-query GKM report may retain this presentation in `equivariant`. The query command performs exact polynomial division and exports `submitted_presentation_theorem`, which identifies the original quotient with the certified regular function. For a removable fraction whose reduction still has a denominator, supply a `regular_representative` beside `equivariant` on the same report row, using the same sparse polynomial encoding. The evaluator checks that its denominator is nonzero at the origin and that the cross products of the two presentations agree. A genuine pole such as $y/x$ has no such witness. [Exact coefficient results](../../AxiomaticGW/GKM/HomogeneousSpecialization.lean)

## Comparing the mixed exceptional class on the two-point blowup

The mixed class $E_1+E_2$ has coordinates $(1,1,0)$. Save the following ordered pair as `mixed.json`.

```json
{"target":"X2","genus":2,"class":[1,1,0],"insertions":[["unit",2],["unit",3]]}
```

```sh
lake build AxiomaticGW.GKM.Fixtures.BlowupTwoMixedExceptionalReplay AxiomaticGW.Surfaces.GenusTwoBlowupDescendantReconstruction
python3 -B scripts/gw_query.py mixed.json --gkm-report environments/gkm-bl2-mixed-exceptional.json --certificate Mixed.lean
lake env lean Mixed.lean
```

The GKM report contains all 105 ordered, dimension-compatible queries with at most two marks in this class. Each exact two-variable rational function is zero. For every mixed exceptional class, a successful GKM comparison also supplies `empty_graph_comparison_theorem`. Its two conclusions certify emptiness for the request’s full class and equality of the supplied torus function to zero. The toric edge proof explains why the connected localization sum is empty before integration. A geometric identification of that graph sum with the stable-map virtual class is a separate input. [GKM report](../../environments/gkm-bl2-mixed-exceptional.json) · [Connected fixed-graph support](../../AxiomaticGW/GKM/Fixtures/BlowupTwoExceptionalGraphSupport.lean)

To reproduce the native values with Sage and the pinned producer, then check the held Lean fraction table offline, run the following from the research checkout.

```sh
conda run -n axiomatic-gw-sage python -B scripts/gkm_bl2_mixed_exceptional.py explore --producer /path/to/gkm_localisation --output mixed-report.json
python3 -B scripts/gkm_bl2_mixed_exceptional.py replay mixed-report.json --output AxiomaticGW/GKM/Fixtures/BlowupTwoMixedExceptional.lean --check
```

## Reducing genus-two Hodge integrals at localization vertices

For the two-point blowup the nonzero example $\langle\tau_1(E_1),\tau_1(E_1)\rangle_{2,E_1}=1/144$ can be reproduced using eight directly integrated Hodge seeds. Save `{"target":"X2","genus":2,"class":[1,0,0],"insertions":[["E1",1],["E1",1]]}` as `e1-pair.json`. The following command records the full equivariant function and compares it with the unmodified producer's held answer. The emitted proof checks the twelve genus-two vertex values used in the calculation.

```sh
conda run -n axiomatic-gw-sage python -B scripts/gkm_hodge_reduction.py --producer /path/to/gkm_localisation --query e1-pair.json --reference environments/gkm-genus-two-energy-one.json --output vertices.json
python3 -B scripts/gkm_hodge_vertex_certificate.py vertices.json --output Vertices.lean
lake build AxiomaticGW.GKM.GenusTwoVertexHodgeReduction
lake env lean Vertices.lean
```

The ordered Hodge indices satisfy $0\le i\le j\le2$. A string marking gives one summand per positive surviving cotangent exponent, including repeated exponents. Removing a dilaton marking leaves the factor $2+n$ for $n$ remaining markings. With every exponent at least two, dimension bounds the number of markings by $3-i-j$. Exactly eight seed keys survive. The proof uses the displayed seed numbers and the explicit dimension, symmetry, string and dilaton equations. Direct admcycles checks include the repeated string case, the unmarked dilaton case and all eight seeds. [Hodge forgetful equations](https://www.cambridge.org/core/journals/canadian-mathematical-bulletin/article/relations-for-quadratic-hodge-integrals-via-stable-maps/FC766E772B9761D4FA4AA475D9F3B596) · [Lean reduction](../../AxiomaticGW/GKM/GenusTwoVertexHodgeReduction.lean)

For an application that supplies stable-curve pushforwards and Hodge classes, Lean derives the string and dilaton equations under the rational-tail laws, the three-point volume normalization and the genus-two unmarked value of $\kappa_0$. Given the one-marked Hodge square, seven seed evaluations then determine the integrated source at every valence. Run `lake build AxiomaticGWTest.GKM.GenusTwoLocalizationIntegrand` to replay the bivalent example. [Geometric source assumptions and theorem](../../AxiomaticGW/GKM/Fixtures/GenusTwoHodgeSeedGeometry.lean)

When the source geometry also satisfies the point-target DVV relation and the elliptic normalization $\langle\tau_1\rangle_1=1/24$, the three pure cotangent seed values follow from constant polynomial certificates. The other four Hodge integrals and the one-marked square remain explicit geometric comparisons. Replay these deductions with `lake build AxiomaticGW.GKM.Fixtures.GenusTwoHodgeDVV`. [Original equations and seed values](../../AxiomaticGW/GKM/Fixtures/GenusTwoHodgeDVV.lean)

The geometric vertex certificate derives the remaining four integrals as well. Its inputs include the one-marked genus-two Picard relation, the restrictions of the Hodge bundle to the two boundary normalizations, the one-marked square $\lambda_1^2=2\lambda_2$, and the original elliptic cotangent relation. It recovers $1/480$, $5/576$, $7/5760$ and $1/5760$, respectively. The bivalent graph on $2L$ with a central $\tau_3(E_2)$ uses this theorem with weights $(-x,y)$ and both flags of weight $-x$. It gives the native signed rational function before specialization. [Geometric inputs and vertex theorem](../../AxiomaticGW/GKM/Fixtures/GenusTwoHodgeGeometricVertex.lean) · [Strict-line fixed locus](../../AxiomaticGW/GKM/Fixtures/StrictLineGeometricLocus.lean)

The primitive exceptional cubic query now also returns an `integrated_locus_comparison_theorem`. Its conclusion identifies the supplied two-character function with the sum of actual stable-curve integrals and the native unstable endpoint factors. The assumptions identify the first and second Chern packets in the chosen curve model and realize the original PPZ rows, boundary restrictions, DVV and universal-curve laws. The rank-two square follows inside the proof. The surface virtual localization formula remains a separate geometric comparison. [Claim-bound certificate](../../environments/gkm-research-bl2-exceptional-cubic.lean) · [Second Chern certificate](../../AxiomaticGW/GKM/Fixtures/GenusTwoHodgeNormalizedPacket.lean)

For a stable genus-one vertex, the two tangent directions contribute Hodge indices in $\{0,1\}$. With both indices zero, the terminating point-target recursion evaluates the cotangent integral. With one positive index, the integral is $(n-1)!/(24\prod_i d_i!)$ when $1+\sum_i d_i=n$, and vanishes otherwise. With both indices positive it vanishes because the square of the elliptic Hodge class is zero. The class comparison uses the raw nonseparating boundary divided by 24. Five profiles checked against the pinned GKM producer include $\int\lambda_1\psi_2\psi_3=1/12$ and $\int\psi_3^3=1/24$ on $\overline{\mathcal M}_{1,3}$. Replay them offline with `lake build AxiomaticGWTest.GKM.EllipticHodgeEvaluation`. [Integral theorem](../../AxiomaticGW/GKM/EllipticHodgeEvaluation.lean) · [Producer profiles](../../AxiomaticGWTest/GKM/EllipticHodgeEvaluation.lean)

A second held calculation uses $2E_2+2L$, with the ordered insertions $\tau_5(H),E_2$. Its 139 distinct genus-two vertex values replay offline with `lake env lean environments/gkm-hodge-reduction-double-ruling.lean`. The reduced graph sum is zero. Its ordinary GW value follows separately from the seed-free divisor equation. These vertex certificates check numerical Hodge reductions. The attachment of vertices to fixed loci and the geometric localization formula remain separate comparison steps. [Twelve-vertex certificate](../../environments/gkm-hodge-reduction-exceptional-pair.lean) · [139-vertex certificate](../../environments/gkm-hodge-reduction-double-ruling.lean)

## Genus-two descendants on a doubled exceptional curve

For a positive multiple of either exceptional curve, the change of the hyperplane lift at each marked point can be expanded before specializing. The extra character on the first axis is $x$. The coefficient for a subset of markings is the sum over all fixed loci with the corresponding hyperplanes replaced by units. If these complete coefficients are regular at zero, only the empty subset contributes to the ordinary value. This proof allows individual fixed-locus terms to have poles, works at arbitrary positive cover degree and arity, and retains the comparison of the insertion-free weights as a geometric input. [Ordinary marked graph transport](../../AxiomaticGW/GKM/Fixtures/ExceptionalOrdinaryTransport.lean)

Changing the degree from the primitive exceptional curve to its double gives a different calculation. For the full class $2E_i$, the genus-two singleton $\tau_3(E_i)$ has ordinary value $3/320$ on each blowup axis. The two-point blowup contributes $29/5760$ from the ancestor and $25/5760$ from the calibration tails. On both of its exceptional curves the ordered pairs $(1,\tau_4(E_i))$, $(\tau_1(1),\tau_3(E_i))$, and $(E_i,\tau_3(E_i))$ have values $3/320$, $9/320$, and $-3/160$, respectively, in either order. The unchanged localization producer returned these same constants as full two-character functions. The arithmetic proof uses reconstruction under the geometric inputs listed in the output. [Singleton calculation](../../AxiomaticGW/Surfaces/Fixtures/BlowupTwoDoubleExceptionalDivisor.lean) · [Twelve ordered comparisons](../../AxiomaticGW/GKM/Fixtures/BlowupTwoDoubleExceptionalPairs.lean)

The complete doubled-exceptional archive contains 105 requests per axis. In 136 rows, relabeling the own exceptional divisor gives the same ordered request on $F_1$ and the same complete field value as the original $F_1$ reconstruction. The other 74 rows contain a foreign exceptional divisor and have zero field value. For example, on $2E_1$ the field for $(\tau_2(1),\tau_3(1))$ is the constant $27/1280$. On the two-point blowup, Lean verifies the original reconstruction for every one of the 210 rows, including the 64 interior pairs. For instance, the two own-divisor markings with cotangent powers one and two give $-7/160$ in either order. The certificate records the ordered query, original reconstruction, complete rational function and ordinary specialization. [Reference archive](../../environments/gkm-bl2-double-exceptional-few-markings.json) · [Target-side proof](../../AxiomaticGW/GKM/Fixtures/BlowupTwoDoubleExceptionalCompleteReplay.lean) · [Cross-surface proof](../../AxiomaticGW/GKM/Fixtures/BlowupTwoDoubleExceptionalComparison.lean)

```sh
python3 -B scripts/gkm_bl2_double_exceptional_few_markings.py replay environments/gkm-bl2-double-exceptional-few-markings.json --output AxiomaticGW/GKM/Fixtures/BlowupTwoDoubleExceptionalFewMarkings.lean --check
lake build AxiomaticGWTest.GKM.BlowupTwoDoubleExceptionalComparison
```

As a target-side example, $\langle E_1,\tau_4(1)\rangle_{2,2E_1}=1/384$. Both terms of the divisor equation contribute. The intersection $E_1\cdot 2E_1=-2$ multiplies $13/3840$, and the lowered descendant $\tau_3(E_1)$ contributes $3/320$. Their sum is $1/384$. Save the following request as `double.json`. [Target-side theorem](../../AxiomaticGW/GKM/Fixtures/BlowupTwoDoubleExceptionalTargetReplay.lean) · [Standalone proof](../../environments/gkm-research-bl2-double-exceptional-marked.lean)

```json
{"target":"X2","genus":2,"class":[2,0,0],"insertions":[["E1",0],["unit",4]]}
```

```sh
lake build AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalMarked AxiomaticGW.GKM.Fixtures.BlowupTwoDoubleExceptionalComparison
python3 -B scripts/gw_query.py double.json --gkm-report environments/gkm-bl2-double-exceptional-few-markings.json --certificate Double.lean
lake env lean Double.lean
```

## The doubled strict line and the two rulings

With $L=H-E_1-E_2$ on the two-point blowup, the five dimension-compatible singleton descendants in class $2L$ have values $13/3840$ for the unit, $-3/320$ for each divisor, and zero for the point. Each answer has an original reconstruction and a full incoming field comparison. The original reconstruction verifies the five singletons on each ruling $E_i+L$ as well. On $E_1+L$, the $E_1$ and $E_2$ insertions give $1/2880$ and $-23/2880$, respectively. These values exchange on $E_2+L$. On both rulings the unit gives $-9/640$, the hyperplane gives $-7/960$ and the point gives $1/240$. The 300-pair archive retains exact ordered references on all three curves. Together with the mixed and doubled exceptional archives, the native index covers all 630 requests at energy two. [Strict-line reconstruction](../../AxiomaticGW/GKM/Fixtures/BlowupTwoDoubleLineReplay.lean) · [Full native index](../../AxiomaticGW/GKM/Fixtures/BlowupTwoEnergyTwoNativeCoverage.lean)

For an ordered pair on $E_1+L$, $\langle\tau_4(1),E_2\rangle=-127/5760$. The divisor intersection is one, so the divisor equation adds the singleton values $-9/640$ and $-23/2880$. The fifty string, dilaton and divisor pairs on each of the three curves have original reconstruction witnesses and independent native field comparisons. The sixteen additional strict-line pairs with one point and a positive cotangent reduction all vanish. [Ruling and marked-pair proofs](../../AxiomaticGW/GKM/Fixtures/BlowupTwoPositivePlaneEnergyTwoReplay.lean) · [Strict-line point pairs](../../AxiomaticGW/GKM/Fixtures/BlowupTwoDoubleLinePointPairReplay.lean)

On $E_2+L$, the query with $\tau_1(\mathrm{pt}),\tau_1(E_1)$ in that order gives $1/144$ and binds native pair row 193. Replacing $E_1$ with $E_2$ gives zero. The full ruling divisor–point comparison contains 24 ordered requests, including the alternative shape $\tau_2(D),\mathrm{pt}$. Its arithmetic proof checks the signed target graph terms and its field proof checks the specified ruling. [Original graph contractions](../../AxiomaticGW/Surfaces/Fixtures/BlowupTwoRulingDivisorPoint.lean) · [Native row binding](../../AxiomaticGW/GKM/Fixtures/BlowupTwoRulingDivisorPointReplay.lean)

For $\langle\tau_3(E_2)\rangle_{2,2L}$, save the following as `line.json`.

```json
{"target":"X2","genus":2,"class":[0,0,2],"insertions":[["E2",3]]}
```

```sh
lake build AxiomaticGW.GKM.Fixtures.BlowupTwoDoubleLineReplay
python3 -B scripts/gw_query.py line.json --gkm-report environments/gkm-bl2-positive-plane-energy-two-singletons.json --certificate Line.lean
lake env lean Line.lean
```

The result is $-3/320$. The signed contribution of the graph with a marked genus-two center and two rational leaves can also be inspected separately. At $x=11,y=3$ this single graph gives $-107/38720$. Its proof reads the two covers, oriented flags, insertion, and symmetry directly from the graph. [Individual graph calculation](../../AxiomaticGW/GKM/Fixtures/StrictLineGraphVertices.lean)

Offline replay reads both original torus characters. Adding a positive power of a character to the numerator preserves its ordinary value and fails the field comparison. To regenerate the native reports, run the following in the pinned Sage environment. Each exploration starts a fresh Sage process with its own admcycles cache, including consecutive calls from the same notebook. [Standalone proof](../../environments/gkm-research-bl2-double-line-singleton.lean)

```sh
python -B scripts/gkm_bl2_positive_plane_energy_two.py singletons explore --producer /path/to/gkm_localisation --output singletons.json
python -B scripts/gkm_bl2_positive_plane_energy_two.py pairs explore --producer /path/to/gkm_localisation --output pairs.json
```

## A genus-two equivariant exceptional descendant

On the exceptional curve $E$ of $F_1$, the pinned lifts give $\langle\tau_3(E)\rangle_{2,E}^{T}=(x+y)/240$. On the two-point blowup the same formula holds on $E_1$, while $E_2$ gives $(y-2x)/240$. The character substitution $(x,y)\mapsto(y-x,-x)$ carries the first answer to the second. Each ordinary GW value is zero by virtual dimension. The full fractions distinguish the two exceptional curves. [Three formulas](../../AxiomaticGW/GKM/Fixtures/ExceptionalGenusTwoCubicReplay.lean)

Save `{"target":"X2","genus":2,"class":[1,0,0],"insertions":[["E1",3]]}` as `exceptional.json`.

```sh
lake build AxiomaticGW.GKM.Fixtures.ExceptionalGenusTwoCubicReplay
python3 -B scripts/gw_query.py exceptional.json --gkm-report environments/gkm-research-bl2-exceptional-cubic.json --certificate Exceptional.lean
lake env lean Exceptional.lean
conda run -n axiomatic-gw-sage python -B scripts/check_gkm_exceptional_genus_two.py --producer /path/to/gkm_localisation
```

There are six fixed loci on each axis. The two choices of marked endpoint with genus split $(1,1)$ vanish because $\psi^3$ exceeds the dimension of the marked elliptic vertex. For a genus-two vertex with flag weight $w$ and transverse character $t$, the ten Hodge inputs give $1/(1152tw^2)$ at the unmarked end and $-11/(2880w)+7/(5760t)$ at the marked end. Summing the four surviving terms cancels the flag poles. The exported certificate checks the complete fraction against this sum. Its ordinary GW theorem uses the surface grading. The signed graph expression uses the localization conventions and the eight explicit vertex seeds. Geometric identification with equivariant GW theory still requires the virtual localization formula. [Support and marking classification](../../AxiomaticGW/GKM/Fixtures/ExceptionalDegreeOneLoci.lean) · [Signed Hodge sum](../../AxiomaticGW/GKM/Fixtures/ExceptionalGenusTwoCubic.lean) · [Native vertex ledger](../../environments/gkm-hodge-reduction-exceptional-cubic.json)

# GKM input exchange and state transport

Audit date: **2026-10-03**. This implements the initial target/query export, algebraic state transport, claim-bound Lean replay of the complete classical state-space tables, full curve coordinates and invariant-edge conventions, and ordinary first-calibration matrices for all three surfaces. It does **not** yet import a geometric CohFT, certify a numerical localization derivation, or reconstruct the fixed genus-two tables. The three targets and all benchmark bounds in `notes/milestones/GWReconstructionPlan.md` remain unchanged.

## Producer and reproducibility

The local producer is `/Users/jma/Documents/gitlab/gkm_localisation`, package `gkm_localization`. `environments/gkm-localization-source.json` pins revision `a09c6625b280312721c5e0f2f915791781339aa5` and SHA256 hashes of its five Python modules. The exporter checks these before importing the package, verifies the imported package location, disables online admcycles lookup, and isolates all caches. No producer code is vendored or modified. No redistribution license was found in the inspected checkout; reuse permission is not established.

The environment is the existing native macOS arm64 Sage **10.9**, admcycles **1.4** installation documented in `notes/references/AdmcyclesEnvironment.md`. Two fresh-cache runs, accepting the checkout root and the package path respectively, produced byte-identical `environments/gkm-inputs-osx-arm64.json`. Its SHA256 is `062a32a9919fa5ddf806c353f5bb56256ca5dca31d170c246b9bfa39c3b11376`, with 308,271 bytes. `environments/gkm-input-regeneration-osx-arm64.json` records the commands and confirms that producer source hashes remained unchanged. Sage emitted only the existing upstream `Algebras` deprecation warning.

From the repository root:

```bash
conda run --no-capture-output -n axiomatic-gw-sage python scripts/export_gkm_inputs.py \
  --producer /Users/jma/Documents/gitlab/gkm_localisation > /tmp/gkm-inputs.json
python3 scripts/check_gkm_inputs.py /tmp/gkm-inputs.json
python3 scripts/test_gkm_inputs.py /tmp/gkm-inputs.json
lake build AxiomaticGW.GKM.StateSpaceTransport AxiomaticGWTest.GKM.StateSpaceTransport
```

Only candidate generation requires Sage and the pinned producer. Candidate-input checking and proof export use Python's standard library. The frozen state-space and curve/edge certificates and their Lean replay require neither Python package. Stable-map localization-graph derivations, numerical queries, and actual CohFT inputs remain open.

The research interpretation now includes the checked external psi graph action in `Tautological/LegPsi.lean`. `LegPsiRealization.lean` transfers exact row witnesses to integrated stable-curve equations from original row vanishing and a primitive cotangent compatibility law, and identifies normalized fundamental evaluation with an existing class-valued CohFT ancestor. These theorems can consume a transported CohFT once supplied; they do not create its classes, establish geometric graph splitting, identify stable-map descendants, or resolve the equivariant grading and ordinary-comparison obligations below.

The nonseparating extension now constructs actual graph gluing with all node powers and proves its quotient and degree behavior. `CohFT/NonseparatingPushforward.lean` derives boundary contraction from optional primitive proper push-pull laws; `GW/NonseparatingBoundary.lean` retains the complete curve class and every source ancestor power. `NonseparatingRealization.lean` connects these equations to the rational graph operation and checked relation witnesses under raw graph-map composition. A supplied, transported GKM CohFT can use this consumer with the required geometric inputs. No GKM CohFT classes or reconstruction action have thereby been imported, and general graph splitting and stable-map comparisons remain open. Raw gluing coefficients are not divided by automorphism orders; gluing can create new symmetries and identify distinct source columns.

The separating extension adds the bilinear graph operation and product Gysin interpretation. `Linear/SeparatingContraction.lean` allows nonmultiplicative linear component integrals. `GW/SeparatingBoundary.lean` keeps all ordered full-class splits, including zero factors and distinct equal-energy exceptional classes. `SeparatingRealization.lean` derives normalized fundamental ancestor evaluation and transfers checked original row certificates from either component. These are further consumers for a supplied GKM CohFT/GW theory with the named geometric inputs; they do not provide its classes, localization derivation, or ordinary specialization.

The marked WDVV consumer now fixes the three four-point boundary graphs, their raw factors, original rows, and exact requested consequence. `RelabelRealization.lean` derives the corresponding state reindexing; `WDVV.exchange_gw_eq_zero` consumes accepted replay and proves the full-class convolution equation from boundary point-class equality, graph composition, and proper integration. It works over the existing generic rational coefficient algebra and preserves equal-energy exceptional classes. The ordinary GW grading/comparison requirements below still apply to a localized GKM theory. The [marked replay guide](AdmcyclesEnvironment.md#marked-four-point-wdvv-replay) records the 30 exchange cases; no CohFT classes or semisimple reconstruction action are imported by this addition.

To regenerate and replay the exact classical state certificates without Sage:

```bash
python3 scripts/export_gkm_certificate.py environments/gkm-inputs-osx-arm64.json \
  --output /tmp/gkm-state-certificate.lean
lake env lean /tmp/gkm-state-certificate.lean
lake build AxiomaticGW.GKM.Fixtures.SurfaceReplay AxiomaticGWTest.GKM.SurfaceReplay
python3 scripts/test_gkm_certificate.py
```

The default exporter includes X0, X1, and X2. `--target X0`, `--target X1`, or `--target X2` selects a smaller replay; the entire input still receives the independent preflight. Export reports `emitted_candidate_proof`; successful Lean compilation is required for certification. The checked default export is frozen in `AxiomaticGW/GKM/Fixtures/SurfaceReplay.lean` and imported by the root library.

To regenerate and replay full curve and invariant-edge conventions:

```bash
python3 scripts/export_gkm_curve_certificate.py environments/gkm-inputs-osx-arm64.json \
  --output /tmp/gkm-curve-certificate.lean
lake env lean /tmp/gkm-curve-certificate.lean
lake build AxiomaticGW.GKM.Fixtures.CurveReplay AxiomaticGWTest.GKM.CurveReplay
python3 scripts/test_gkm_curve_certificate.py
```

This exporter also supports per-target selection. It emits finite labels as constructors with kernel-checked range proofs. Invalid labels cannot silently wrap modulo the number of points. The default replay is frozen in `GKM/Fixtures/CurveReplay.lean` and imported by the root library.

## First calibration coefficient

At zero primary deformation, `GW/Descendants/TwoPointCalibration.lean` constructs the operator coefficient from
$\eta(x,S_{m+1,\beta}y)=\langle x,\tau_m(y)\rangle_{0,\beta}$.
The node occupies the first slot, the retained marking the second, and matrix rows are output coordinates. `Linear/TwoPointOperator.lean` proves sewing and conjugation under a change of state space. The constant coefficient is identity at class zero only; positive inverse-loop coefficients at class zero vanish. No auxiliary two-point metric is mistaken for a GW invariant.

The first coefficient uses primary two-point invariants. Existing WDVV reconstruction and finite seeds determine it, and dimension proves uniform vanishing above energy three. The independently held `Surfaces/Fixtures/FirstCalibration.lean` table checks every remaining class, retaining exceptional signs and all zero entries. Its ten nonzero matrices occur in the line, exceptional, ruling and strict-line classes. Primary relabelling proves first-order self-adjointness, without asserting full symplecticity.

The native explorer computes every positive full class with energy at most three using the pinned producer's `StableMapsGKM.integrate(0,2,...)`. It raises the node with the complete equivariant inverse metric before specializing the resulting regular expression at the ordinary origin. Two fresh-cache runs produce the same 393,350-byte report, `environments/gkm-first-calibration-comparison.json`: 1 plane class, 5 F₁ classes and 19 two-point-blowup classes, comprising **564 matrix entries**. Ten matrices and 27 entries are nonzero; fifteen complete zero matrices remain in the corpus. Only the existing upstream Sage deprecation warning appears.

```bash
conda run --no-capture-output -n axiomatic-gw-sage python scripts/explore_gkm_first_calibration.py \
  --producer /Users/jma/Documents/gitlab/gkm_localisation --output /tmp/gkm-first-calibration.json
python3 scripts/export_gkm_first_calibration.py environments/gkm-first-calibration-comparison.json \
  --output AxiomaticGW/GKM/Fixtures/FirstCalibrationReplay.lean --check
lake build AxiomaticGW.GKM.Fixtures.FirstCalibrationReplay AxiomaticGWTest.Surfaces.TwoPointCalibration
python3 scripts/test_gkm_first_calibration.py -v
```

To emit a candidate replay for a fresh report, pass `/tmp/gkm-first-calibration.json`, choose a temporary `--output` path, omit `--check`, then compile that file with `lake env lean`. Export success alone is not certification.

The standard-library exporter independently checks exact equivariant multiplication and regular specialization using sparse polynomials over `Fraction`. It emits the actual incoming ordinary entries, full curve vectors, basis labels, inverse-loop powers and retained psi powers. Lean checks their finite coverage, indexing and equality to the held surface table, then connects that table to primary reconstruction. Digests supply provenance only. The seven Python tests include two separately compiled false fixtures: a jointly zeroed correlator/operator/claim and a swap of equal-energy exceptional classes. Both pass arithmetic preflight and fail kernel replay.

These checks compare native localization with a WDVV reconstruction path while sharing target bases, curve conventions and geometric normalizations. Equivariant arithmetic and specialization of these new matrices are checked in Python, not newly proved in Lean. Lean certifies the ordinary matrix entries as consequences of the existing primary reconstruction; it does not certify the localization derivation. The higher-calibration extension below now removes the stable-descendant callback using a derived mixed comparison. Geometric realization of its primitive inputs, full symplecticity, nonzero primary deformation and actual CohFT-class/reconstruction-action import remain separate required gates. The [validation manifest](../../environments/two-point-calibration-validation.json) records this distinction and all exact commands.

## Higher calibration recursion

The derived [matrix recursion](../../AxiomaticGW/Surfaces/CalibrationRecursion.lean) now reconstructs every zero-primary-deformation calibration coefficient from the already checked first coefficient, the classical anticanonical cup operator and full effective-class splittings. Its soundness theorem consumes the original WDVV laws, finite line/exceptional seeds, and explicit virtual cotangent/diagonal/stabilization inputs. It does not assume a stable-descendant callback or a solved numerical recursion.

The [held request list](../../AxiomaticGW/Surfaces/Fixtures/HigherCalibration.lean) contains thirty higher-coefficient matrices: powers two and three at each of the ten nonzero first-coefficient classes; powers four, five and six for the plane line; power four for the plane conic; and powers two and three for each double exceptional class. This is a selected comparison suite, not complete energy-twelve descendant coverage. It contains 582 ordinary matrix entries. The retained marking has cotangent power one less than the inverse-loop power; the first marking remains the node with power zero.

Generate the exact native report in the pinned Sage environment, then export or check the offline Lean replay:

```bash
/opt/homebrew/Caskroom/miniforge/base/envs/axiomatic-gw-sage/bin/python scripts/gkm_calibration_recursion.py explore --producer /Users/jma/Documents/gitlab/gkm_localisation --output environments/gkm-higher-calibration-comparison.json
python3 scripts/gkm_calibration_recursion.py replay environments/gkm-higher-calibration-comparison.json --output AxiomaticGW/GKM/Fixtures/HigherCalibrationReplay.lean --check
lake build AxiomaticGW.GKM.Fixtures.HigherCalibrationReplay
python3 scripts/test_gkm_calibration_recursion.py -v
```

Omit `--check` to regenerate the saved Lean source. The explorer verifies the producer source pin before importing it, isolates caches and disables online admcycles lookup. Exact Python preflight checks equivariant inverse-metric multiplication and regular ordinary specialization. Lean independently checks each incoming ordinary entry against `reconstructedCalibrationMatrix` at its actual power, class and basis labels, plus power indexing, basis bijectivity and coverage of the separately held list. It never trusts the explorer's own expected values. The geometric localization theorem and CohFT classes are not certified by this finite comparison.

The [validation manifest](../../environments/mixed-descendant-comparison-validation.json) records the complete commands, mathematical input boundary, preservation checks and rejection tests. These regressions retain negative descendant coefficients, zero matrices, rational multiple-cover values and distinct equal-energy exceptional classes.

## Version-one candidate schema

The bundle has `schema_version=1`, `kind=gkm_localization.fixed_target_inputs`, and `proof_status=candidate_data`. Its `cohft` object explicitly records `classes`, `quantum_product`, `r_matrix`, and `translation` as null. The producer currently exposes numerical descendant integrals and finite GKM target data; these do not supply the missing class-valued theory or reconstruction action.

The coefficient domain is the fraction field of `QQ[x,y]`, where `x,y` are additive equivariant characters of codimension one. Curve classes are separate complete coordinate vectors, not a Laurent variable or a single energy. Encodings are:

| Object | Encoding and checked meaning |
| --- | --- |
| Rational | `[numerator, denominator]`, exact integers and strictly positive denominator |
| Polynomial | Sorted sparse `[exponent_vector, rational_coefficient]` terms, with two nonnegative exponents, no repetitions, and no sparse zero terms |
| Rational function | Numerator and nonzero denominator polynomials, plus a term witnessing a genuinely nonzero denominator coefficient |
| Tangent character | Two integer coefficients in the additive `x,y` basis |
| Fixed point | A sorted pair of fan-ray identifiers; the fixed fan is independently specified by the checker |
| Query | Genus, complete effective class, distinct integer insertion labels, basis indices, nonnegative psi powers, curve-stability flag, and exact candidate value |

No JSON expression is executed as code. Duplicate object keys, booleans masquerading as integers, floating coefficients, invalid denominator witnesses, and incompatible coefficient metadata are rejected. Hashes identify reproducibility data; mathematical checks do not follow from a hash.

The basis is ordered as `unit,H,E1,...,pt`. For fixed-point Euler factors `E_p`, the exported tables satisfy:

| Table | Rows, columns, and formula |
| --- | --- |
| `basis_to_fixedpoint` = B | Fixed points by basis states; restrictions of the chosen toric lifts |
| `fixedpoint_to_basis` = C | Basis states by fixed points; both `BC=1` and `CB=1` |
| `metric` | Basis by basis; `Bᵀ diag(E_p⁻¹) B` |
| `inverse_metric` | Basis by basis; `C diag(E_p) Cᵀ` |
| `products[i][j][k]` | Coefficient of basis state k in the product of i and j; restriction equals pointwise multiplication |
| `c1_coordinates` | Coordinates of the sum of tangent characters; equivariant unit terms are retained |

The hyperplane lifts are `D2` on X0/X1 and `D0+D3` on X2; exceptional lifts are `D3,D4`, and the point lift is `D0 D2`. Dual fan characters determine each toric divisor restriction. The checker verifies these lifts, rather than accepting an arbitrary algebra with the same ordinary limit.

## Full curve and edge conventions

| Target | Effective coordinates | Signed lattice coordinates | Energy |
| --- | --- | --- | --- |
| X0: P² | dH | dH | 3d |
| X1: F1 | aE+bF | bH+(a-b)E | a+2b |
| X2: two-point blowup | aE1+bE2+cL | cH+(a-c)E1+(b-c)E2 | a+b+c |

Here `F=H-E` and `L=H-E1-E2`. The exporter selects these complete coordinates explicitly; the producer's default independent wall coordinates are not used as a substitute. Divisor intersections and generator walls derive the lattice map and energy, and the checker compares both to the fixed surface contract.

Edges preserve their endpoints, common fan wall, oriented additive character, complete effective class, and normal-bundle branch identifiers and degree. The checker verifies the entire fan adjacency, the tangent-character multiset at each point, and `w(p,u)-w(q,v)=degree*w(p,q)` for the other incident branches. Edge classes must agree with every divisor intersection, as well as energy. Consequently, exchanging exceptional classes of equal energy is detected. Reversing an edge with the corresponding weight sign and branch exchange is accepted.

These finite checks do not prove the fans' identification with geometric surfaces, the effective-monoid bijections, or a stable-map localization formula. Covering degrees, localization-graph automorphisms, and stabilization maps are obligations of the future derivation schema, not fields supplied by this initial target export.

`GKM/CurveConventionCertificate.lean` now binds this portion of the export to independently held `Fixtures/CurveFrames.lean` requests. `Accepts` checks all fan rays, cone labels, unordered tangent pairs and their duality, the full lattice matrices and energy weights, generator walls, and all twelve invariant edges. It also proves that the same fan characters produce the held state's Euler factors and Chern sums. It checks wall bijections and complete fan adjacency, source/target tangent signs, full edge classes, normal branches, signed normal degrees, and character transitions. Twenty-six divisor intersections are proved as symbolic localization traces and compared to `SurfaceTarget.divisorIntersections`.

`transport_correct`, `transport_injective`, `transport_add`, and `energy_correct` hold for arbitrary effective classes, including exceptional components; they do not merely test energy-twelve samples. `edge_firstChern` connects the normal degree to the existing actual divisor pairing. `intersection_trace` uses the accepted state-space restrictions and Euler factors, and `intersections_specialize` proves regular ordinary values for the complete sums. Closed finite checks use ordinary kernel-checked `decide`, and field identities use symbolic arithmetic. The certificate supplies no stable-map localization formula.

## Connected graph support on the exceptional face

For the two-point blowup write the full effective class as \((a,b,c)\) in \((E_1,E_2,L)\), where \(L=H-E_1-E_2\). At \(c=0\), connected fixed-graph support exists **if and only if** \(a=0\) or \(b=0\). The accepted edge table has just two edges on this face. Edge index 2 joins fixed points 1 and 2 and carries \(E_1\). Edge index 4 joins fixed points 3 and 4 and carries \(E_2\). Each source edge contributes its positive covering degree times the full target edge class. A vanishing coordinate forces every source edge onto the same face, and connectivity keeps every vertex image on one side of the cut. The origin has a contracted-vertex support. Each positive axis has a single covered edge in either orientation. These existence statements concern decorated incidence before genus and marking constraints. [Pinned edge table](../../AxiomaticGW/GKM/Fixtures/CurveReplay.lean) · [General support lemma](../../AxiomaticGW/GKM/FixedGraphSupport.lean) · [Exact face classification](../../AxiomaticGW/GKM/Fixtures/BlowupTwoExceptionalGraphSupport.lean)

In particular \((1,1,0)\) has empty connected support at every genus and number of markings. Any finite sum of contributions indexed by such supports is zero in every additive coefficient group or monoid, including a class-valued sum before integration. Identification of an actual geometric CohFT class with a virtual-localization sum still requires the geometric localization and stabilization comparison. Adding \(L\) allows a connected three-edge path at \((1,1,1)\). [Class-sum theorem](../../AxiomaticGW/GKM/Fixtures/BlowupTwoExceptionalGraphSupport.lean) · [Covered-edge and connecting-path controls](../../AxiomaticGWTest/GKM/BlowupTwoExceptionalGraphSupport.lean)

The pinned `StableMapsGKM.fixed_loci` returns decorated fixed graphs before integration. For \((1,1,0)\), its nine enumerations at \(g,n\in\{0,1,2\}\) all return the empty set. The same check replays both pure exceptional endpoints and a connected graph through \(L\). The raw `StableMapGKM` constructor accepts the disconnected union of the two exceptional edges, so testing its `check()` in isolation would miss the connected-domain requirement. The enumerator grows connected graphs from a vertex or a tree. Its `localization_contribution` method returns a rational function after evaluating the vertex factors. [Pinned-source graph check](../../scripts/check_gkm_exceptional_graph_support.py)

```bash
lake build AxiomaticGWTest.GKM.BlowupTwoExceptionalGraphSupport
/opt/homebrew/Caskroom/miniforge/base/envs/axiomatic-gw-sage/bin/python -B \
  scripts/check_gkm_exceptional_graph_support.py --producer /Users/jma/Documents/gitlab/gkm_localisation
```

For a \(d\)-sheeted exceptional cover, write \(w\) for the primitive oriented tangent weight and \(t\) for the normal weight at that endpoint. The native normal obstruction is \(\prod_{j=1}^{d-1}(t+jw/d)\). The edge factor multiplies it by \((-1)^d/((d!)^2(w/d)^{2d})\). Reversing the edge sends \((w,t)\) to \((-w,t+w)\) and reverses the product indices. The resulting field element is identical. Every individual edge and every vertex tangent normalization in a connected exceptional support transports under the appropriate character substitution. On the unmarked single-cover graph the two unstable vertices and the order-\(d\) deck group give a total of \(-(w/d)^2/d\) times the edge factor. The pinned producer checks both orientations in degrees one through six on all three exceptional curves. [Multiple-cover proof](../../AxiomaticGW/GKM/Fixtures/ExceptionalCoverFactors.lean) · [Native check](../../scripts/check_gkm_exceptional_genus_two.py)

At a genus-two surface vertex, all incident flag powers are enumerated by their exact sum after subtracting the marked powers and both Hodge indices. The eight seeded Hodge recurrences then determine the complete source factor at arbitrary valence. It respects changes of characters and permutations of the two tangent directions. For the graph in class \(2E\) with two unramified rational leaves and a genus-two center, Lean identifies the full curve coordinates and the two-element symmetry group. At \((x,y)=(2,5)\) on the first exceptional axis, putting \(\tau_3(E)\) on the center gives the vertex value \(-199/466560\) and signed graph value \(-199/116640\). Putting \(\tau_1(E),\tau_2(E)\) on the center gives \(1/2916\) and \(2/729\). These individual contributions retain their exact rational functions before choosing torus weights. Geometric interpretation requires the Hodge input and virtual localization. [Vertex formula](../../AxiomaticGW/GKM/GenusTwoLocalizationVertex.lean) · [Transport on the exceptional axes](../../AxiomaticGW/GKM/Fixtures/ExceptionalGenusTwoVertexTransport.lean) · [Bivalent fixed locus](../../AxiomaticGW/GKM/Fixtures/ExceptionalDoubleCoverChain.lean)

For an arbitrary number of flags, the source curve now has a class in rational stable-curve cohomology tensored with the character field. At tangent weight $u$ its rank-two Hodge factor is $u-\lambda_1+\lambda_2/u$. The flag series at nonzero weight $w$ is a genuine inverse of $w-\psi$ because the next cotangent power beyond the dimension vanishes. Multiplication and integration of these factors give exactly the finite Hodge sum, including the sign and the order of the markings. The calculation requires stable-curve cohomology and the two Hodge classes as geometric inputs. Assembling the global fixed-locus pushforward still requires the virtual localization comparison. [Class-level proof](../../AxiomaticGW/GKM/GenusTwoLocalizationIntegrand.lean) · [Integrated bivalent example](../../AxiomaticGWTest/GKM/GenusTwoLocalizationIntegrand.lean) · [Liu–Sheshmani localization formula](https://arxiv.org/abs/1407.1370)

The forgetful pushforward derives the string and dilaton equations for integrals of a pulled-back Hodge class times any cotangent monomial. The string sum counts repeated markings separately. With the three-point volume normalized to one and $\kappa_0=2$ on the unmarked genus-two curve, dilaton gives $2+n$ with $n$ surviving markings. Hodge naturality also forces every Hodge monomial of codimension greater than three to vanish on each marked space. A one-marked identification $\lambda_1^2=2\lambda_2$ therefore determines the square at every arity and eliminates one of the eight numerical seed comparisons. The bivalent source $-199/466560$ follows from the factored class and the remaining seven seed evaluations. Identifying the actual Hodge classes with the decoded admcycles classes still requires geometric input. [Forgetful integral identities](../../AxiomaticGW/Tautological/ForgetfulIntegrals.lean) · [Class identities](../../AxiomaticGW/GKM/GenusTwoHodgeProducts.lean) · [Seven-seed integration theorem](../../AxiomaticGW/GKM/Fixtures/GenusTwoHodgeSeedGeometry.lean)

The point-target DVV relation gives three of those seven numbers. The finite expansions of $\langle\tau_4\rangle_2$, $\langle\tau_2\tau_3\rangle_2$ and $\langle\tau_2^3\rangle_2$ collect to constant polynomials $1/1152$, $29/5760$ and $7/240$. Every term retains the genus and the powers at its own marks, and each separating term retains its labeled subset. The geometric inputs for these deductions are DVV, the three-point volume one and $\langle\tau_1\rangle_1=1/24$. The four remaining integrands are $\lambda_1\psi^3$, $\lambda_1\psi_1^2\psi_2^2$, $\lambda_2\psi^2$ and the unmarked $\lambda_1\lambda_2$. At opposite nonzero tangent characters the rank-two Euler factors multiply to $-u^2$ before integration under the same one-marked square identification. [Point-target calculation](../../AxiomaticGW/PointTarget/DVVCalculation.lean) · [Four-input vertex theorem](../../AxiomaticGW/GKM/Fixtures/GenusTwoHodgeDVV.lean) · [Opposite tangent factors](../../AxiomaticGW/GKM/GenusTwoHodgeProducts.lean)

A second route derives all eight genus-two numbers from class identities. The genus-two Picard row gives $10\lambda_1=\tfrac12\xi_{\rm irr,*}1+2\xi_{1,*}1$. The two graph integrals against $\psi^3$ are $1/24$ and zero. After adding a marking, the corresponding integrals against $\psi_1^2\psi_2^2$ are $1/6$ and $1/576$. The Hodge restriction on the nonseparating normalization has a trivial quotient. On the separating normalization its two elliptic lines give a sum for the first Chern class and a product for the second. Identifying each elliptic line with $1/24$ of the labeled rational self-gluing, together with the one-marked rank-two square, gives $\int\lambda_2\psi^2=7/5760$ and $\int\lambda_1\lambda_2=1/5760$. The original genus-one cotangent relation fixes the elliptic normalization from the three-point volume. The realization of these identities in the chosen curve model and virtual localization for the target remain geometric inputs. [Picard computation](../../AxiomaticGW/GKM/Fixtures/GenusTwoHodgePicardMoments.lean) · [Boundary restrictions](../../AxiomaticGW/GKM/Fixtures/GenusTwoHodgeNormalization.lean) · [Geometric vertex](../../AxiomaticGW/GKM/Fixtures/GenusTwoHodgeGeometricVertex.lean)

On the doubled strict line, the original GKM producer independently gives $-107/38720$ at $(x,y)=(11,3)$ for the bivalent graph with a central $\tau_3(E_2)$ insertion. Lean checks its signed field expression and the factor of two from interchanging the leaves. For the doubled exceptional curves, the native transport checker compares the individual factors, incidence and all graph symmetries across 318 fixed loci on three curves. [Strict-line graph](../../AxiomaticGW/GKM/Fixtures/StrictLineDoubleCoverChain.lean) · [Native transport checker](../../scripts/check_gkm_double_exceptional_transport.py)

The second Chern packet has a direct codimension-two certificate. Eleven of the fourteen original PPZ rows prove \(960\lambda_2=\xi_{\mathrm{dbl},*}1+4(\xi_{\mathrm{marked},*}1+\xi_{\mathrm{unmarked},*}1)\) in the seventeen-column presentation. The first term is the labeled double loop. The two mixed graphs put a self-gluing on opposite sides of the separating node. Multiplying the Picard relation by \(\lambda_1\) and restricting to the boundary gives twice the same \(\lambda_2\). Thus the source identification of the two Chern packets, the PPZ rows and the Hodge restrictions suffice for the one-marked square. The formula for the primitive cubic exceptional descendant uses this proof and integrates all six signed loci. Its equivariant value is \((x+y)/240\) on either first exceptional axis and \((y-2x)/240\) on the second axis of the two-point blowup. Each specializes to zero. [Second Chern certificate](../../AxiomaticGW/GKM/Fixtures/GenusTwoHodgeNormalizedPacket.lean) · [Six integrated loci](../../AxiomaticGW/GKM/Fixtures/ExceptionalCubicGeometricLoci.lean) · [Replayable query](../../environments/gkm-research-bl2-exceptional-cubic.lean)

### Surface covers and source vertices

For a cover of degree $d$, write $u=w/d$ for the outgoing tangent, $n$ for the transverse character, and $k=da$ for the pullback of the normal degree $a$. If $k\ge0$, the normal contribution is the reciprocal of $\prod_{j=0}^{k}(n-ju)$. If $k<0$, it is $\prod_{j=1}^{-k-1}(n+ju)$. Reversing the cover sends $(u,n)$ to $(-u,n-ku)$ and preserves the entire edge factor, including the tangent deformation. The two integral characters are independent on each of the twelve invariant curves of the fixed fans. This gives nonzero denominators over the original field for every covering degree. Sage independently evaluated every wall at one, two and three sheets. [Orientation and edge weights](../../AxiomaticGW/GKM/SurfaceLocalizationEdge.lean) · [Denominator proof](../../AxiomaticGW/GKM/SurfaceEdgeNonvanishing.lean) · [All three fans](../../AxiomaticGW/GKM/Fixtures/SurfaceEdgeReplay.lean)

At a stable rational vertex let \(D=n-3\), where \(n\) counts both marks and flags. Write \(d_i\) for the marked powers, \(r=D-\sum_i d_i\), \(u,v\) for the two tangent characters and \(w_s\) for the incident flag characters after division by each covering degree. When \(r\ge 0\) the complete source factor is

\[
  \frac{D!}{uv\,r!\prod_i d_i!}
  \left(\prod_s w_s^{-1}\right)
  \left(\sum_s w_s^{-1}\right)^r .
\]

Excess marked degree gives zero. The proof integrates the ordered marked and flag powers with the genus-zero string equation and three-point volume, then sums the flag profiles with the multinomial theorem. It also covers degree-zero contracted vertices with no flags. At \(u=2,v=3\), markings \((0,1)\) and flags \((2,3/2,1)\) give \(13/54\). [Vertex integral and closed formula](../../AxiomaticGW/GKM/RationalLocalizationVertex.lean) · [Mixed-cover and empty-flag tests](../../AxiomaticGWTest/GKM/RationalLocalizationVertex.lean)

At a stable elliptic vertex the two Hodge indices give four ordered pairs. The rational cotangent recursion handles \((0,0)\). One positive index gives \((n-1)!/(24\prod_i d_i!)\) in top degree from the raw nonseparating boundary. The two-positive-index term vanishes by the square of the elliptic Hodge class. For an unmarked end with one flag \(w\), summing all terms gives \(1/(24w^2)-(1/u+1/v)/(24w)\). This reduces to \(-1/(24uv)\) for an unramified flag \(w=u\). A cubic descendant on the opposite one-flag elliptic vertex exceeds its dimension and kills both elliptic splits of the primitive exceptional graph. [All marked powers](../../AxiomaticGW/GKM/EllipticHodgeEvaluation.lean) · [Signed flag expansion](../../AxiomaticGW/GKM/EllipticLocalizationVertex.lean) · [Exceptional endpoints](../../AxiomaticGW/GKM/Fixtures/ExceptionalEllipticVertex.lean)

The common genus-zero through genus-two evaluator takes its marking powers and oriented flag characters directly from the imported graph support. Distinct incident covers retain their own half-edge labels. The evaluator rejects vanishing denominators, including a balanced unstable node. On the doubled strict line it reconstructs all three vertices, both edges, the marked insertion and the order-two automorphism factor, giving the complete signed contribution of that locus. [Graph evaluator](../../AxiomaticGW/GKM/SurfaceLocalizationVertex.lean) · [Doubled strict-line replay](../../AxiomaticGW/GKM/Fixtures/StrictLineGraphVertices.lean)

The pinned producer exposes these factors on actual decorated stable maps. The following check compares the 36 multiple-cover edge values and five rational and three elliptic vertices on each target fan. It exercises unequal characters, multiple covers and excess marked degree, and checks the full curve coordinate of each graph. [Native comparison](../../scripts/check_gkm_stable_vertices.py)

```bash
sage -python scripts/check_gkm_stable_vertices.py --producer /path/to/gkm_localisation
lake build AxiomaticGWTest.GKM.SurfaceLocalizationEdge AxiomaticGWTest.GKM.RationalLocalizationVertex AxiomaticGWTest.GKM.EllipticHodgeEvaluation
```

## Checked mathematics and validation boundaries

`AxiomaticGW/GKM/FixedPointAlgebra.lean` constructs the actual commutative Frobenius algebra on fixed-point functions. Its trace is `sum_p a(p)/E_p`; nonzero Euler factors prove perfectness. Its inverse metric is derived from the same factors, and contraction recovers a state. No independent metric inverse or semisimplicity assertion is inserted as an assumption.

`AxiomaticGW/Linear/PairingTransport.lean` proves transport of a perfect metric and its canonical copairing along a linear equivalence. It proves invariance of two-slot, nonseparating, and separating contractions with arbitrary output modules. `AxiomaticGW/CohFT/Transport.lean` uses these results to construct `CohFT.comap`, proving the relabelling, flat-unit, normalization, and both gluing laws. Returning through the inverse equivalence preserves every cohomology-valued class.

`AxiomaticGW/GKM/StateSpaceTransport.lean` turns **Lean-proved** two-sided inverse restriction matrices into that equivalence. It proves the transported metric formula and both inverse-metric products. It transports multiplication as a bilinear map, with associativity, commutativity, unit, and Frobenius invariance. The coefficient vectors' existing pointwise multiplication is not installed as their surface product. A mixed-basis regression with distinct Euler factors exercises this distinction, a nonzero off-diagonal metric, and the existing full constant-target CohFT model.

`GKM/EquivariantCoefficients.lean` uses the genuine fraction field of `MvPolynomial (Fin 2) ℚ`. `Specializes` requires a representative with denominator nonzero at the ordinary origin. `Specializes.unique` proves independence of that representative, and `not_specializes_inverse` excludes a nonzero polynomial's reciprocal when the polynomial vanishes at zero. There is no evaluation homomorphism from the whole fraction field to ℚ.

`GKM/StateSpaceCertificate.lean` defines `Accepts request tables`, indexed by the independently held restrictions, Euler factors, tangent sums, unit label, and ordinary surface tables. Acceptance proves both basis inverses, Euler nonvanishing, weighted metric and inverse-metric formulas, every product coefficient, the unit, the first Chern coordinates, and regular ordinary comparisons. Its `metric_correct`, `product_correct`, and `unit_correct` theorems identify the actual transported algebra. `Fixtures/SurfaceFrames.lean` computes the requested ordinary data from the existing rational surface algebra. `Fixtures/SurfaceReplay.lean` separately proves every serialized denominator nonzero and proves acceptance for all three exported state tables: **216 product coefficients**, **50 metric entries**, and **50 inverse-metric entries**, with no Sage dependency or unchecked native decision.

The Python checker independently implements sparse polynomial arithmetic over `Fraction` and verifies rational-function identities by cross multiplication, without Sage's polynomial or matrix routines. This remains supplemental evidence for the complete bundle. The state-space exporter emits actual symbolic proofs against the fixed Lean requests; it does not treat preflight success as a proof. Nonzero polynomial evaluations are used only to certify denominator nonvanishing. If the initial point is a root, the exporter searches a degree-bounded exact grid for a nonvanishing witness, whose value is then checked by Lean. No symbolic equality is proved by sampling.

Ordinary metric and product comparisons apply to the complete expressions. Individual Euler reciprocals are allowed to have poles and are not specialized independently. Algebraic regularity and agreement with the ordinary surface model are now proved for the state tables; geometric identification of that model remains an input.

The localized algebra is not an ordinary graded GW state space over this field. For the plane, the certified pairing of `H` and `pt` is `-y`, which is nonzero, although their ordinary codimensions sum to three rather than the surface dimension two. The existing `GradedStateSpace.pairing_vanishes` cannot hold with those assignments over an ungraded coefficient field. Bare `CohFT` transport remains valid. Applying the ordinary GW dimension laws requires checked specialization of the full theory or an explicit treatment of equivariant coefficient degrees; no grading law is weakened to force a direct import.

The nine initial query comparisons are, on every target, `<H>_(1,0)=-1/8` and `<tau_1(H)>_(2,0)=-1/960`, plus the plane line through two points, F1 fiber through one point, and an unmarked exceptional class on X2, each with value one. The constant seeds and exceptional value are independently specified from the existing Wennink input ledger; the producer's F1 benchmark specifies the fiber case. GKM Hodge calculations share admcycles dependencies, so this is not independent verification of those mathematical components. These are initial interoperability regressions, not the full fixed query manifest or positive-degree genus-two reconstruction.

`environments/gkm-input-checks.json` records the three-target checks. `environments/gkm-input-regressions.json` records **34 passing command-line cases**, including equivalent rational representatives and reversed edges, and rejection of altered geometry, tables, normal bundles, same-energy curve classes, requested queries, and claimed values. Mutations receive a fresh digest before checking.

`scripts/test_gkm_certificate.py` passes **eighteen state-certificate cases**: the default three-surface replay, two equivalent representatives, four controlled export rejections, and eleven kernel type rejections when an existing certificate is rebound to altered tables or requests. One equivalent representative is regular at zero but vanishes at the initial nonvanishing sample. The exporter also transports its nonvanishing proof through the ring identity used when denominator clearing changes its polynomial form. `environments/gkm-state-certificate-regressions.json` records the cases, proof hashes, sizes, timings, and the final independent recheck of that conversion. `environments/gkm-state-certificate-axioms.json` records eighteen key declarations, all using only standard Lean axioms.

`AxiomaticGWTest/GKM/SurfaceReplay.lean` consumes the certificates through the actual perfect pairing and bilinear product, testing the complete metric, exceptional self-intersection sign, distinct exceptional classes, the nonzero equivariant `H`/`pt` pairing, and an individual Euler pole. Full build, test, and lint passed; only the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean` remains.

The curve exporter suite passes **24 cases**: four kernel replays for the baseline, reversed edges, reordered edge lists, and exchanged tangent-branch order; fourteen controlled export rejections; and six kernel claim-binding rejections. `AxiomaticGWTest/GKM/CurveReplay.lean` also proves non-acceptance of five concrete corruptions, rather than only testing failed proof reuse, including a state Euler request inconsistent with the fan. The two exceptional classes used in its corruption example have equal energy but distinct transported lattice vectors. `environments/gkm-curve-certificate-regressions.json` pins the exact sources and proof hashes; `environments/gkm-curve-certificate-axioms.json` records eleven new declarations using only standard Lean axioms. The default proof is 17,848 bytes and took about twenty-two seconds for standalone replay in this run. These are target-data replay timings, not GW reconstruction timings.

## Three-marked genus-zero descendant replay

The [proved evaluator](../../AxiomaticGW/Surfaces/ThreePointDescendants.lean) reconstructs arbitrary three-point descendants from the finite genus-zero seeds under the named geometric comparison inputs. The [held suite](../../AxiomaticGW/Surfaces/Fixtures/ThreePointDescendants.lean) contains 27 cases across the three surfaces. Native exploration calls the producer's three-point integration directly, without a copy of the Lean descendant recurrence. It retains exact equivariant fractions and complete ordered insertion requests. Ordinary specialization is checked by exact Python arithmetic; the [Lean replay](../../AxiomaticGW/GKM/Fixtures/ThreePointDescendantReplay.lean) checks each incoming value against the proved evaluator at that value's actual full class, powers and labels.

```bash
conda run --no-capture-output -n axiomatic-gw-sage python scripts/gkm_three_point_descendants.py explore \
  --producer /Users/jma/Documents/gitlab/gkm_localisation --output /tmp/gkm-threepoint.json
python3 scripts/gkm_three_point_descendants.py replay environments/gkm-three-point-descendants.json \
  --output AxiomaticGW/GKM/Fixtures/ThreePointDescendantReplay.lean --check
lake build AxiomaticGW.GKM.Fixtures.ThreePointDescendantReplay
python3 scripts/test_gkm_three_point_descendants.py
```

Two fresh-cache native runs are byte-identical. The seven offline tests include a fresh positive kernel control and three coherent false claims, each with a separate kernel counterexample: zeroing a nonzero value, exchanging insertion requests, and exchanging equal-energy exceptional classes. Exact fraction coherence alone passes preflight in these corruptions and does not constitute acceptance. The [validation manifest](../../environments/mixed-ancestor-reduction-validation.json) records proof assumptions, timings, source pins and remaining obligations. These cases do not certify the producer's localization derivation or import a semisimple CohFT, and they do not replace the fixed genus-two application suites.

## Genus-zero descendant replay at all arities

The [full evaluator](../../AxiomaticGW/Surfaces/GenusZeroFullDescendants.lean) now reconstructs every genus-zero query on the original geometric domain from the finite seeds and explicit geometric inputs. Its stable sector uses the proved psi-boundary ancestor recursion; positive-degree unstable arities use the earlier terminating anticanonical adapter with a constructed state callback. The [additional held suite](../../AxiomaticGW/Surfaces/Fixtures/GenusZeroDescendants.lean) has 34 requests: 12 on P², 10 on F₁ and 12 on Bl₂P², at arities 0, 1, 2, 4, 5 and 6. It includes degree-zero psi multinomials, repeated states, negative and fractional values, distinct exceptional classes with equal energy, and empty positive-degree requests.

```bash
conda run --no-capture-output -n axiomatic-gw-sage python scripts/gkm_genus_zero_descendants.py explore \
  --producer /Users/jma/Documents/gitlab/gkm_localisation --output /tmp/gkm-genus-zero.json
python3 scripts/gkm_genus_zero_descendants.py replay environments/gkm-genus-zero-descendants.json \
  --output AxiomaticGW/GKM/Fixtures/GenusZeroDescendantReplay.lean --check
lake build AxiomaticGW.GKM.Fixtures.GenusZeroDescendantReplay
python3 -m unittest discover -s scripts -p 'test_gkm_*descendants.py' -v
```

The common explorer keeps the old three-point interface and adds explicitly parameterized request families; each call uses the actual request's marking count. Native GKM never calls the Lean recursion. Both paths share the fixed target state/class conventions and underlying geometric normalizations. Exact Python preflight checks the retained equivariant fractions and their regular ordinary specialization. The [Lean replay](../../AxiomaticGW/GKM/Fixtures/GenusZeroDescendantReplay.lean) separately checks every ordinary claim and full request against the proved evaluator. Numerical agreement does not certify localization geometry or import CohFT classes.

The [validation manifest](../../environments/genus-zero-descendant-validation.json) records the fresh-cache comparison, all-arity kernel checks and four coherent false-claim tests: replacing a nonzero value by zero, exchanging distinct psi monomials, exchanging unstable insertion requests and exchanging equal-energy exceptional classes. Each corruption passes rational-function coherence and has a separate kernel counterexample. The original three-point tests are also retained. This extends the shared regression corpus; it does not reduce the fixed genus-two or semisimple compatibility gates.

## Genus-one descendant replay at all arities

The [elliptic evaluator](../../AxiomaticGW/Surfaces/GenusOneDescendants.lean) constructs all descendants from the original WDVV/Getzler/psi relations, finite seeds and explicit geometry. The [held suite](../../AxiomaticGW/Surfaces/Fixtures/GenusOneDescendants.lean) contains 41 requests: 14 plane, 12 one-blowup and 15 two-blowup cases, at arities 0, 1, 2, 3 and 4. All 34 nonzero values are fractional, including fourteen negative answers. The seven zeros remain in the coverage requirement.

```bash
conda run --no-capture-output -n axiomatic-gw-sage python scripts/gkm_genus_one_descendants.py explore \
  --producer /Users/jma/Documents/gitlab/gkm_localisation --output /tmp/gkm-genus-one.json
python3 scripts/gkm_genus_one_descendants.py replay environments/gkm-genus-one-descendants.json \
  --output AxiomaticGW/GKM/Fixtures/GenusOneDescendantReplay.lean --check
lake build AxiomaticGW.GKM.Fixtures.GenusOneDescendantReplay
python3 -m unittest discover -s scripts -p 'test_gkm_*descendants.py' -v
```

The common transport now accepts an explicit genus, preserving genus zero as its existing default. Both runs use the pinned producer, fresh ephemeral caches and disabled online lookup. The reports agree byte for byte. Exact equivariant fraction and ordinary specialization checks remain Python preflight; the incoming ordinary numbers are then separately certified by Lean against their full query. No localization recursion is copied into the exporter.

For a concrete offline research query, import `AxiomaticGW.Surfaces.GenusOneDescendants` and replay the conic descendant:

```lean
open AxiomaticGW
example : SurfaceGenusOne.queryValue? (X := .plane)
    ⟨1, ![2], [⟨.point, 5⟩]⟩ = some (1/32) := by decide +kernel
```

`SurfaceGenusOne.queryValue?_eq_checkedEval` identifies that number with the actual invariant under the documented finite seeds and geometric inputs. The [consumer regression](../../AxiomaticGWTest/Surfaces/GenusOneDescendants.lean) supplies the actual exported WDVV, Getzler and elliptic psi presentations to this theorem. The [validation manifest](../../environments/genus-one-descendant-validation.json) records kernel rejection of six coherent corruptions: a false zero, doubled raw-loop factor, substitution of an ancestor for a descendant, exceptional sign reversal, exchanged marking multiplicities and exchanged equal-energy classes. Every rejection has a fresh positive control and a separately proved counterexample.

The two numerical implementations share geometric normalizations and intersection-theoretic foundations, including the producer's admcycles inputs. Agreement is therefore a useful comparison with an independently implemented computation, not independent verification of all mathematics. Full semisimple CohFT import and every fixed genus-two gate remain mandatory.

## Genus-two degree-zero descendant certificates

The [one-point ancestor evaluator](../../AxiomaticGW/Surfaces/GenusTwoOnePointAncestors.lean) derives the three constants $7/640$, $7/720$ and $49/5760$ for the insertion $\bar\psi_1^2\,1$ at class zero, in target order X0, X1, X2. They are outputs of the decorated boundary contraction, not new seeds. The [native report](../../environments/gkm-genus-two-degree-zero.json) records the same values from `StableMapsGKM.integrate(2,1,...)`, together with exact equivariant expressions and unchanged producer pins. Two fresh runs with online lookup disabled produced identical bytes.

```bash
conda run --no-capture-output -n axiomatic-gw-sage python scripts/gkm_genus_two_degree_zero.py explore \
  --producer /Users/jma/Documents/gitlab/gkm_localisation --output /tmp/gkm-genus-two-zero.json
python3 scripts/gkm_genus_two_degree_zero.py check environments/gkm-genus-two-degree-zero.json
python3 -B scripts/gkm_genus_two_degree_zero.py replay environments/gkm-genus-two-degree-zero.json \
  --output AxiomaticGW/GKM/Fixtures/GenusTwoDegreeZeroReplay.lean --check
lake build AxiomaticGW.GKM.Fixtures.GenusTwoDegreeZeroReplay
lake build AxiomaticGWTest.Surfaces.GenusTwoDegreeZeroDescendants
python3 -B scripts/test_gkm_genus_two_degree_zero.py -v
```

The [degree-zero comparison](../../AxiomaticGW/GW/Descendants/DegreeZeroComparison.lean) now proves that every mixed invariant in class zero equals its ancestor with the two cotangent powers added at each marking. The proof uses the primitive rational-tail geometry, emptiness of positive tail splittings of zero and induction on the total stable-map power. It applies to every finite stable marking set. No calibration values or final comparison identity are assumed.

The [query consumer](../../AxiomaticGW/Surfaces/GenusTwoDegreeZeroDescendants.lean) composes that theorem with the existing one-point algorithm. Its final `degreeZeroOnePointQueryValue?_sound` concludes the actual `SurfaceQuery.checkedEval` equality from the original low-genus seeds, four relation presentations and named geometric inputs. It covers degree-zero genus-two one-point powers at least two; unsupported sectors return `none`. The [replay](../../AxiomaticGW/GKM/Fixtures/GenusTwoDegreeZeroReplay.lean) now kernel-checks all three complete incoming requests and ordinary values. Thus each target has a certified nonzero shared descendant case, with the geometric hypotheses retained and no genus-two value added as a seed.

The Python `check` command remains a numerical diagnostic. `replay` emits the actual proof obligations; `replay --cached` reuses the accepted fixture only after Lean checks both the full incoming requests and values. The five regression methods include a positive binding control, eight malformed request/provenance changes, a duplicate JSON key, coherent false zeros and eight actual kernel rejections: three false values and altered genus, class, power, state or arity. Both computations share target conventions and intersection-theoretic foundations, including admcycles/Hodge inputs. These certificates prove the ordinary descendant claims under the stated inputs; symbolic localization derivations, ordinary-specialization geometry, actual CohFT classes and the full interoperability gate remain open. See the [descendant validation record](../../environments/genus-two-degree-zero-descendant-validation.json) and the [earlier ancestor audit](../../environments/genus-two-one-point-ancestor-validation.json).

## Full BP equation and the class-valued bridge

The [BP GW consumer](../../AxiomaticGW/Tautological/BelorousskiPandharipandeGW.lean) is formulated over an arbitrary commutative rational algebra and the existing full effective curve monoid. It uses an actual class-valued GW theory, primitive realization and cotangent/gluing laws, and original 3-spin row validity. Its exact twenty-diagram equation preserves all curve splittings and six marking assignments. The [Sage exchange](../../environments/belorousski-pandharipande.json) supplies relation-search data; its [Lean replay](../../AxiomaticGW/Tautological/Fixtures/BelorousskiPandharipandeReplay.lean) checks the incoming graphs, coefficients, normalization and operation provenance against the held published equation.

This interface is available to the required semisimple CohFT bridge, but this step does not import or identify a GKM CohFT class. Full coefficient grading, denominator nonvanishing, reconstruction-action hypotheses where used, descendant–ancestor comparison and ordinary specialization remain required. There are no new GKM numerical claims in this BP step; the producer checkout is unchanged. See the [validation record](../../environments/belorousski-pandharipande-validation.json).

## Genus-two plane line comparison

The [native report](../../environments/gkm-plane-genus-two-line.json) records the pinned producer's exact evaluations of $\langle\mathrm{pt}^4\rangle_{2,1}$, $\langle\tau_1(H)\mathrm{pt}^3\rangle_{2,1}$ and $\langle\tau_1(\mathrm{pt})\mathrm{pt}^2\rangle_{2,1}$. All three are zero. The run uses a fresh temporary cache and disables online lookup. Full ordered requests, exact equivariant fractions, producer digests and environment versions are retained.

The [generated replay](../../AxiomaticGW/GKM/Fixtures/PlaneGenusTwoLineReplay.lean) binds each ordinary value to the complete canonical plane query and the finite BP reconstruction table. The native comparison, kernel replay and corruption tests pass. With the full request held fixed, Lean rejects a false ordinary value even when its equivariant fraction has been changed consistently; eight further request/provenance corruptions are rejected before replay. Python checks exact equivariant specialization separately. This is not a proof of the producer's localization derivation or an import of CohFT classes. The two implementations share geometric normalizations and intersection-theoretic foundations.

```bash
conda run --no-capture-output -n axiomatic-gw-sage python scripts/gkm_plane_genus_two.py explore \
  --producer /Users/jma/Documents/gitlab/gkm_localisation --output /tmp/gkm-plane-genus-two.json
python3 -B scripts/gkm_plane_genus_two.py replay environments/gkm-plane-genus-two-line.json \
  --output AxiomaticGW/GKM/Fixtures/PlaneGenusTwoLineReplay.lean --check
lake build AxiomaticGW.GKM.Fixtures.PlaneGenusTwoLineReplay
python3 -B scripts/test_gkm_plane_genus_two.py
```

These three zeros cover only the line requests. They do not satisfy the required nonzero genus-two shared descendant on each of X0--X2, the full fixed benchmark suite or the class-valued semisimple bridge.

## Certified plane few-marking suite

The fixed plane bound gives 48 ordered genus-two descendant requests: three with one marking and 45 with two. The [held manifest](../../environments/genus-two-plane-few-markings-requests.json) is determined only by the benchmark bounds and signed virtual dimension. [Lean coverage](../../AxiomaticGW/Surfaces/Fixtures/GenusTwoPlaneFewMarkingRequests.lean) proves its equality with the complete mathematical domain and rejects duplicate requests through injectivity.

The pinned native producer computed [all 48 candidates](../../environments/gkm-plane-genus-two-few-markings.json), with exact equivariant fractions and ordinary values. Preflight checks the full requests, provenance and specialization; eleven request/provenance/coefficient corruptions are rejected. The separate Lean executable `lake exe planeGenusTwoFewMarkings` evaluates the original descendant algorithm using its accepted degree-one canonical table. Its [complete native run](../../environments/genus-two-plane-few-markings-native.json) finished successfully, and all 48 exact requests and values match the GKM report. Nine additional corruptions of the Lean report are rejected. Complete numerical agreement is now complemented by successful 48-query kernel replay; these remain distinct forms of evidence.

`python3 scripts/gkm_plane_few_markings.py frame` generates the held request source; `replay` generates the numerical proof source; `compare` requires full, duplicate-free exact agreement with the separate Lean report. Candidate generation still does not import CohFT classes or certify the producer's localization derivation. Shared admcycles and intersection-theoretic dependencies remain explicit.

The optional split export keeps the expensive numerical proofs separate from final table acceptance:

```bash
python3 -B scripts/gkm_plane_few_markings.py replay \
  environments/gkm-plane-genus-two-few-markings.json \
  --output AxiomaticGW/GKM/Fixtures/PlaneGenusTwoFewMarkingsReplay.lean \
  --split-computation --check
lake build AxiomaticGW.GKM.Fixtures.PlaneGenusTwoFewMarkingsReplay
```

The data module preserves the complete incoming requests and values. Four arithmetic sectors cover indices 0--2, 3--20, 21--35 and 36--47, respectively. They compute against an explicit canonical candidate table, without assuming its acceptance. The final assembly proves that this table is exactly `GenusTwoPlaneLine.values` and uses the existing canonical-table acceptance theorem to recover the original descendant algorithm. Thus an arithmetic sector alone is not a certified geometric answer, and an unfinished sector cannot be replaced by additional seed values. The original direct exporter and the `bind` interface remain available. All four sectors and final 48-query acceptance now pass. The one-marked sector checks `1/128`, `-1/960` and `-1/240`. The two-marked sectors reuse 291 certified component values, all 39 original ancestor equations and the complete mixed expansions, retaining the same public statements and canonical data.

The [one-point consumer](../../AxiomaticGWTest/GKM/PlaneGenusTwoOnePoint.lean) now composes the three checked arithmetic values with the accepted canonical table. It proves the original `planeQueryValue?` answers for the full requests `tau_5(1)`, `tau_4(H)` and `tau_3(pt)` in plane degree one. Its build passes. Their geometric interpretation uses the existing `planeQueryValue?_eq_checkedEval` and its unchanged named inputs and three seeds. These are certified nonzero ordinary descendants on X0. The degree-zero replay above also certifies a shared nonzero descendant on X1 and X2. Their positive-degree genus-two reconstruction, complete numerical suites and actual CohFT bridge remain required.

The `bind` command generates a shorter incoming-claim proof using the complete checked 48-value fixture. It checks both the full query and exact value before reusing that fixture's theorem. This path now passes for all 48 claims and rejects a coherently forged ordinary value. A separate kernel proof verifies that the forged value differs from the held value, independently of the rejection diagnostic. All six exchange test methods pass. See the [component replay validation](../../environments/genus-two-plane-component-replay-validation.json) and [public lookup](../../AxiomaticGW/Surfaces/PlaneGenusTwoFewMarkingBenchmarks.lean). This certifies ordinary descendant claims under the original inputs, without asserting geometric validity of the producer's localization calculation or importing CohFT classes.

The [full three-target request manifest](../../environments/genus-two-few-markings-requests.json) freezes 5,199 requests before blowup values are computed: 48 for X0, 656 for X1 and 4,495 for X2. `python3 scripts/genus_two_few_marking_requests.py --output environments/genus-two-few-markings-requests.json --check` checks deterministic regeneration. Its X0 subset is identical to the existing plane manifest. The [general Lean domain](../../AxiomaticGW/Surfaces/GenusTwoFewMarkings.lean) proves coverage against the original benchmark predicate on every target. Python manifest checks additionally retain complete curve coordinates and verify the classwise marking counts. This request inventory does not certify numerical answers or imported CohFT classes.

## Raw Hodge candidate expressions and exact regrouping

The [frozen raw packet](../../environments/admcycles-hodge-strata-candidates.json) contains nine ordered lambda-index products on the full stable genus-two, one-marked locus, extracted from pinned Sage 10.9/admcycles 1.4 raw decorated strata. All 553 nonzero source occurrences and 45 explicit degree components remain, including zeros. The [decoder](../../AxiomaticGW/GKM/Fixtures/AdmcyclesHodgeStrataCandidates.lean) checks 61 incidence presentations and 373 decorated encodings, using exact rational coefficients, all kappa powers at indices 1 through 4, leg and node psi, ordered branches and the marking map from source label 1 to `Fin 1` index 0. No extra automorphism divisor or tautological relation quotient is introduced.

The two mixed source products have 122 and 108 terms. The [fixed isomorphism witness](../../environments/admcycles-hodge-strata-isomorphism-witness.json) retains every occurrence. Its [Lean replay](../../AxiomaticGW/GKM/Fixtures/AdmcyclesHodgeStrataIsomorphisms.lean) checks 111 decorated-graph identifications, regroups both actual coordinate vectors into 44 columns, and proves `raw12Degree3 = raw21Degree3` in the free strata module. The equality is consequently preserved by any given rational linear realization. This proves consistency of these two fixed expressions; it does not identify them with Hodge classes or construct a general geometric product.

The two offline proof exporters verify their helper source pins before execution. A fresh pinned Sage run of the portable raw exporter passes in 4.747 seconds. Its complete packet agrees with the frozen original except for the recorded exporter digest; all 553 occurrences and 45 components are unchanged. The two upstream `Algebras` deprecation warnings are retained in the record, and the frozen provenance is preserved. Pure offline tests reproduce both sets of Lean sources byte-for-byte and reject corrupted coefficients, graph decorations, permutations, branch maps, occurrence lists and source bindings:

```bash
python3 scripts/test_admcycles_hodge_certificate.py
python3 scripts/test_admcycles_hodge_isomorphisms.py
lake build AxiomaticGW.GKM.Fixtures.AdmcyclesHodgeStrataCandidates AxiomaticGWTest.GKM.AdmcyclesHodgeStrataCandidates
lake build AxiomaticGW.GKM.Fixtures.AdmcyclesHodgeStrataIsomorphisms AxiomaticGWTest.GKM.AdmcyclesHodgeStrataIsomorphisms
```

The 28 Python tests and targeted public builds pass; all 651 audited declarations use only standard Lean axioms. The [validation record](../../environments/admcycles-hodge-strata-validation.json) preserves exact commands, source pins, the two recovered build-wrapper failures, and the absence of saved original Python console logs. Full-project build/test/lint remains pending at this checkpoint. No geometric hypotheses, numerical seeds, global simp rules or instances were added. Hodge-bundle/GRR identification, product and constant-map virtual Euler compatibility, equivariant grading and ordinary comparison, and an actual semisimple GKM CohFT remain required. These representatives do not yet supply geometric GKM class inputs.

## Scalar normalization of the complete candidate assembly

The [assembly](../../AxiomaticGW/GKM/AdmcyclesHodgeStrataNormalization.lean) retains every one of the 45 decoded raw components before realization and projection. Existing graded linearity implies that positive-degree components have zero connected degree-zero projection. The source `(0,0)` component is checked against the existing fundamental stratum; its realization is explicitly required to equal one (`hfund`). The scalar of the complete assembly is then `∑ p, coeff p 0 0`.

The theorem `scalar_assembly_eq_tft` derives agreement with the canonical genus-two, one-marked unit correlator under `h00`, the equality of each supplied `(0,0)` coefficient and Euler weight. Its [generic targeted build and 18-result audit](../../environments/admcycles-hodge-normalization-validation.json) pass. The subsequent [complete coefficient replay](../../AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroFullCoefficientReplay.lean) accepts all 108 actual numerator/denominator pairs from the [compact packet](../../environments/gkm-degree-zero-hodge-strata-factored-candidate.json), retaining the 540 component references. It uses the existing exact two-variable fraction field and proves every denominator nonzero. The [twelve-entry replay](../../AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroCoefficientReplay.lean) binds full zero curve classes, fixed-point indices and cones, both ordered tangent characters, unit restrictions and actual `(0,0)` coefficients to the existing accepted target fixtures. Its Euler-unit identities discharge `h00` for all three concrete targets; `D`, `A` and the explicit `hfund` remain.

The four integrated targets build, all 18 Python tests pass, and all 57 audited declarations use only standard Lean axioms. The [durable coefficient record](../../environments/gkm-hodge-coefficients-validation.json) embeds commands, logs, source pins, source-binding review and the repaired development runs. The portable exporters check helper pins before execution; historical producer paths remain inert packet provenance. Tests preserve every coefficient, reject malformed pair/component/source metadata, and confirm byte-identical replay. They expressly retain positive coefficient changes before projection: the scalar theorem does not certify their geometric meaning or identify the full class.

```bash
python3 scripts/test_gkm_hodge_c00.py
python3 scripts/test_gkm_hodge_coefficients.py
lake build AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroCoefficientReplay AxiomaticGWTest.GKM.HodgeDegreeZeroCoefficientReplay AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroFullCoefficientReplay AxiomaticGWTest.GKM.HodgeDegreeZeroFullCoefficientReplay
```

The [ordered coefficient formula](../../AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroCoefficientFormula.lean) now proves every actual coefficient identity

\[
c_{p,a,b}=\frac{(-1)^{a+b}w_{p,0}^{2-a}w_{p,1}^{2-b}}{w_{p,0}w_{p,1}},\qquad a,b\in\{0,1,2\}.
\]

The indices retain the producer's branch order: `a` belongs to tangent 0 and `b` to tangent 1. The denominator is nonzero because its already checked Euler weight is a unit. With formal symbols $L_1,L_2$ and $L_0=1$, the complete nine-term polynomial is exactly

\[
\sum_{a,b}c_{p,a,b}L_aL_b=
\frac{(w_{p,0}^2-w_{p,0}L_1+L_2)(w_{p,1}^2-w_{p,1}L_1+L_2)}{w_{p,0}w_{p,1}}.
\]

All 108 ordered identities are checked before collecting formal monomials. Nine offline tests and the 16-result integrated axiom audit pass; the [formula validation record](../../environments/gkm-hodge-coefficient-formula-validation.json) retains source conventions, exact commands/logs, helper pins, the repaired finite-index proof failure, and the consumer formatting warnings. Run `python3 scripts/test_gkm_hodge_coefficient_formula.py` to repeat the portable source/order checks. This formal polynomial equality does not identify the raw strata products with Hodge-bundle Chern classes or a GW class.

The [complete-sum regularity replay](../../AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroRegularity.lean) now proves cancellation of every pole in the complete formal polynomial sum. All 108 ordered coefficients enter the sum, and the six collected monomial coefficients are checked separately for each target. Put $Q=x^2-xy+y^2$. The explicit lifts over $\mathbb Q[x,y]$ and their zero-character images are:

| Target | Regular polynomial lift | Ordinary formal polynomial |
| --- | --- | --- |
| P² | $Q+3L_1^2+3L_2$ | $3L_1^2+3L_2$ |
| F₁ | $4L_1^2$ | $4L_1^2$ |
| Bl₂P² | $-Q+5L_1^2-3L_2$ | $5L_1^2-3L_2$ |

For each row, `map_embed_regularLift` identifies the lift's coefficientwise image in the existing fraction field with `completePolynomial`, the sum of all actual fixed-point polynomials. `map_atZero_regularLift` specializes only the lift's polynomial torus-character coefficients. There is no map from the full fraction field to the rationals, and no individual pole is specialized. The formal variables $L_1,L_2$ remain independent; no geometric Hodge or Mumford relation is assumed.

The [regularity validation record](../../environments/gkm-hodge-regularity-validation.json) contains the warning-free actual two-target build, eight portable checks, all 28 standard-only axiom results and both failed development probes. Run `python3 scripts/test_gkm_hodge_regularity.py` and `lake build AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroRegularity AxiomaticGWTest.GKM.HodgeDegreeZeroRegularity` to repeat the source-preservation and compilation checks.

The [raw assembly bridge](../../AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroRawAssembly.lean) now transports these complete coefficient sums through the actual 45-component class. Write U = `A.map raw00Degree0`, V = `A.map raw11Degree2` and W = `A.map raw02Degree2`. The complete candidates are Q·U + 3V + 3W for P², 4V for F₁ and −Q·U + 5V − 3W for Bl₂P². These are equalities of the full assembled class, proved by module linearity, explicit empty-component reduction and the accepted raw mixed-pair graph isomorphisms. Only the existing realization `A` is required; `D`, `hfund` and multiplication compatibility are not premises. In particular, V is not replaced by a square of a single-factor image.

The [raw assembly validation record](../../environments/gkm-hodge-raw-assembly-validation.json) retains the warning-free actual build, ten standard-only public audits, exact source/data pins and proof-development history. The subsequent [repository checkpoint](../../environments/genus-two-blowup-reconstruction-validation.json) includes its public umbrella export in the successful 3,018-job default build; lint remains open. The raw assembly still carries stable-curve codimension over the coefficient field. Total equivariant grading, geometric ordinary comparison, identification of raw products with geometric Hodge classes, Hodge/GRR, virtual Euler/stabilization and an actual semisimple CohFT remain required.

## Exact raw degree-two reduction and the geometric input boundary

The [degree-two raw certificate](../../AxiomaticGW/GKM/Fixtures/HodgeDegreeTwoRawRelation.lean) retains all 28 `(1,1)` and 16 `(0,2)` occurrences. Its checked graph bijections and rational regrouping establish `raw11Degree2 = (2 : ℚ) • raw02Degree2` in the free strata module. Combined with the complete raw assembly bridge, this gives Q·A(raw₀₀) + 9·A(raw₀₂), 8·A(raw₀₂), and −Q·A(raw₀₀) + 7·A(raw₀₂) for P², F₁ and Bl₂P². All 46 actual public audits and eleven portable tests pass; exact source pins, complete logs, the original consumer failure and the then-pending umbrella export are in the [validation record](../../environments/gkm-hodge-degree-two-validation.json). The subsequent default build includes that export; the current lint gate remains open. No geometric Mumford relation or multiplicative realization premise is used.

The [existing realization](../../AxiomaticGW/Tautological/StrataRealization.lean) has only a rational linear map and `map_basis_degree`. It does not imply that the fundamental class maps to one, preserve products, or interpret κ decorations. [PsiClasses.kappa](../../AxiomaticGW/CohFT/Tautological.lean) already defines κ as the pushforward of an extra ψ power. [map_mulLegPsi](../../AxiomaticGW/Tautological/LegPsiRealization.lean), [map_stratum_eq_classValue](../../AxiomaticGW/Tautological/GluingForgetful.lean) and [map_decoratedStratum_eq_classValue](../../AxiomaticGW/Tautological/DecoratedGluingRealization.lean) derive ψ/gluing interpretation under their named compatibility laws, but the decorated gluing syntax includes no κ constructor. [CertifiedStrataProduct](../../AxiomaticGW/Tautological/StrataAlgebra.lean) remains an algebraic contract, not an implemented geometric excess-intersection product.

The [degree-one realization](../../AxiomaticGW/GKM/Fixtures/HodgeDegreeOneRealization.lean) now proves the image of the actual five-term expression: −ψ/12 + κ₁/12 plus three ordered raw boundary terms of coefficient 1/24. It checks all five graph bindings and uses the [positive κ generator law](../../AxiomaticGW/Tautological/KappaRealization.lean), independently stated before psi identification, together with the existing primitive psi/gluing laws. The [targeted record](../../environments/gkm-hodge-degree-one-realization-validation.json) includes fourteen standard-only public audits and tests distinguishing the forgotten marking and the kappa decoration. This proves the conditional interpretation; actual geometric satisfaction of the κ/forgetful law and the boundary common-refinement/excess rules for the finite square remain required. Assuming the requested raw product equality would not establish those rules. Identifying the resulting class with Hodge Chern classes further requires the GRR statement and the Chern-character identities in [Mumford, §5](https://www.dam.brown.edu/people/mumford/alg_geom/papers/1983b--EnumGeomModuli-NC.pdf), with the pointed log-κ and raw ordered-node normalizations checked. The present finite raw equality itself proves none of those geometric inputs.

The [node-normal operation](../../AxiomaticGW/Tautological/NonseparatingNodeNormal.lean) now constructs the raw pushforward of the negative sum of the two distinguished source psi decorations, with codimension shift two. The [packet binding](../../AxiomaticGW/GKM/Fixtures/HodgeNodeNormal.lean) preserves actual positions 3 and 4, graphs `rawGraph23` and `rawGraph9`, and both coefficients −1/288. Existing psi/gluing laws and explicit corolla normalization give its conditional realized formula. The [actual record](../../environments/gkm-hodge-node-normal-validation.json) contains three warning-free builds, seventeen standard-only audits and the 53-source lexical import closure. This is the constructed normal expression, not the full boundary square: the pull-push formula must still account for all common refinements, edge identifications and multiplicities before it can justify the requested product or a Hodge interpretation.

The [finite common-refinement classification](../../AxiomaticGW/GKM/Fixtures/LoopSquareRefinements.lean) now covers every generic ordered pair contracting to the actual marked loop, including explicit flag and marking compatibility and connected contracted fibres. The orbit counts 2, 1 and 4 give the [constructed five-slot identity](../../AxiomaticGW/GKM/Fixtures/LoopSquarePacketBinding.lean) at original positions 3, 4, 18, 21 and 23. The [repository validation](../../environments/gkm-loop-square-refinements-validation.json) records sixteen warning-free builds and 48 exact standard-only audits. These finite results still require geometric identification of the fibre-product components and their excess classes before they imply a boundary product or Hodge/CohFT interpretation.

The [explicit gluing descriptions](../../AxiomaticGW/GKM/Fixtures/LoopSquareGluing.lean) now bind the actual double-loop and both ordered parallel constructions to the frozen packet graphs. Existing primitive realization laws give the image of their constructed five-slot combination with explicit compatibility and fundamental normalization. The [actual record](../../environments/gkm-loop-square-gluing-validation.json) verifies two targets and sixteen standard-only audits. No geometric boundary product or excess-intersection comparison has been added as either an input or a conclusion.

The [external-psi consumer](../../AxiomaticGW/GKM/Fixtures/HodgeExternalPsi.lean) now identifies exactly original positions 0, 1, 2, 9 and 15 of the 28-column degree-two packet with the external-psi operation on the five degree-one columns. The square coefficient occurs once and the mixed coefficients twice. Primitive psi compatibility realizes this constructed portion; an explicit 23-occurrence remainder prevents it from being presented as a complete square or geometric Hodge theorem. Its fourteen actual audits are recorded in the [consolidated checkpoint](../../environments/research-reconstruction-checkpoint-validation.json).

The [loop-kappa consumer](../../AxiomaticGW/GKM/Fixtures/HodgeKappaLoopProduct.lean) and [separating-kappa consumer](../../AxiomaticGW/GKM/Fixtures/HodgeKappaSeparatingProduct.lean) now bind actual positions 10–14 under explicit covariant forget/glue composition laws. The new hypotheses quantify over arbitrary source classes; their consequences retain every kappa index and the ordered component conventions. The [actual checkpoint](../../environments/reconstruction-checkpoint130-validation.json) audits the conditional theorems without adding Lean axioms. It does not construct a geometric model of these hypotheses or identify a complete Hodge product or imported CohFT.

A class interpretation of this genus-two unit expression is also distinct from a producer semisimple CohFT. The current producer numerically integrates Hodge/ψ expressions; [state-space transport](../../AxiomaticGW/GKM/StateSpaceTransport.lean) and [CohFT transport](../../AxiomaticGW/CohFT/Transport.lean) consume an existing class-valued theory. An actual comparison still needs class expressions or a justified reconstruction action with all-genus unit/gluing laws, plus the constant-map virtual Euler/stabilization identification. The contracted-vertex Hodge factor in [Graber–Pandharipande, §4](https://arxiv.org/pdf/alg-geom/9708001) supplies the mathematical convention to formalize, not an already accepted localization theorem for these targets.

## Current ordinary validation and structural reuse

The [repository validation checkpoint](../../environments/genus-two-blowup-reconstruction-validation.json) records successful default builds (3,013 jobs, then 3,018 after the five public exports) and a successful configured test run with 52 inherited warnings. Lint failed on 216 classified findings: 153 serialized-name reports, 60 literal identity-witness reports and three missing documentation reports. These are the actual command outcomes; the default build does not include every isolated or newly copied fixture.

The [ordinary F₁ relabelling consumer](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1RootRelabel.lean) now proves equal contractions for original rows 122, 141 and 156 from their unchanged decorated core and actual transported HEEE assignment. Original weighted rows keep the coefficient ratio 7054/12777. The [three-file actual record](../../environments/gkm-f1-root-relabel-validation.json) includes production/test builds and fourteen standard-only audits; numerical-consumer/cache integration and the staged 414-transfer extension remain separate. This improves replay of the existing ordinary reconstruction without importing GKM CohFT classes or proving the outstanding geometric comparisons.

The [ordinary zero-row replay](../../environments/genus-two-f1-root-zero-rows-validation.json) now kernel-checks every zero coordinate and required source genus guard for original indices 0–120, preserving all 815 positions. It has 269 prefix audits plus a generic left-zero lemma and one original row-123 slot audit. These are zeros of the existing guarded contraction and that single dimension-zero slot, with no full row-123/124/125 or full-constant claim. The portable [record checker](../../scripts/check_node_zero_records.py) verifies the embedded actual evidence and canonical source/import closure without reopening temporary files. This numerical replay step does not supply class-valued GKM input or the missing geometric product/comparison laws.

The [subsequent actual cache replay](../../environments/genus-two-f1-actual-cache-validation.json) verifies 235 repository targets and 2,505 exact standard-only audits, including the full 722-component cache and complete original weighted rows 123–125. Their values are 161/38880, −745/50544 and zero, with all 37 root slots checked. The [portable checker](../../scripts/check_f1_actual_numeric_record.py) binds the 582-source import closure, preserves both RSS regimes and the failed attempt, and verifies compressed full logs without reopening temporary evidence. This is ordinary guarded-contraction evidence; the full 815-term contraction and the class-valued semisimple CohFT bridge remain outside this record.

The [full structural-transfer replay](../../environments/genus-two-f1-structural-transfers-validation.json) is now accepted in the actual repository: all seventeen targets and 2,275 exact audits pass for the 414 original coefficient-ratio identities. The source binding preserves decorated cores and transported HEEE assignments and uses no numerical coincidence or new geometric hypothesis. The [portable checker](../../scripts/check_f1_actual_transfers_record.py) verifies all source pins and the unchanged 51-warning multiset in each of 34 complete logs. Representative values, the original Fin 815 sum and class-valued semisimple CohFT interpretation remain distinct acceptance obligations.

For ordinary numerical replay, the [equivalent left-first root evaluation](../../AxiomaticGW/Surfaces/ScalarPointRootOrder.lean) preserves the original ordered factors and dual signs while allowing early zero evaluation. Its [six-audit actual record](../../environments/scalar-point-root-order-validation.json) distinguishes the simple build wrappers, failed 2 GiB Lean audit and successful sampled 3 GiB audit. Only the named five slots are numerically checked by its consumers; missing representative values and the geometric CohFT bridge remain separate.

The [consolidated numerical checkpoint](../../environments/research-reconstruction-checkpoint-validation.json) adds complete representatives 131–139 and 170–173 and twelve numerical transfers. Five bounded adapters bind every original weighted index 0–159 to the same frozen candidate table, leaving 655 indices unassembled. The candidate arithmetic sum 1/288 and actual block-03 sum −1/585 are distinct theorems. These 39 targeted builds and 817 exact audits, including the separate external-psi result, provide neither the full 815-term contraction nor class-valued semisimple CohFT input. Configured tests passed before the final four adapters; earlier lint failures remain unresolved.

The [subsequent actual checkpoint](../../environments/reconstruction-checkpoint130-validation.json) contains 130 targeted builds and 3,629 exact audits, including 67 new canonical representative values and five additional weighted-interval adapters. Every original index 0–319 is now bound to the frozen table; 495 positions remain unassembled. The final configured tests cover 173 historical roots, with later roots explicitly outside that run. Default build success and recorded style warnings do not resolve the earlier lint failure or the separate class-valued GKM bridge.

The [next fixed checkpoint](../../environments/reconstruction-checkpoint96-validation.json) records 96 targeted builds and 2,671 audits, with all original weighted indices 0–447 now assembled and 367 remaining. Its [kappa-square consumer](../../AxiomaticGW/GKM/Fixtures/HodgeKappaSquare.lean) distinguishes the square of realized `rawGraph2` from realization of `rawGraph21`: only the former receives the corrected pushforward formula, under new universal base-change and tail-contraction hypotheses. These inputs have no constructed geometric model here. Configured tests cover 174 historical roots; the earlier default build is inherited, and lint failures remain unresolved.

The [148-target follow-up](../../environments/reconstruction-checkpoint148-validation.json) assembles all original weighted indices 0–607 and audits the [conditional rawGraph21 realization](../../AxiomaticGW/GKM/Fixtures/HodgeKappaCorolla.lean). The new `CorollaForgetfulCompatible` hypothesis ranges over all kappa exponent vectors and positive forgotten indices; generator compatibility and the two-factor product follow using the constructed finite operation and prior primitive geometry. No geometric instance, boundary/excess comparison or complete Hodge product is established. This fixed record contains 4,330 audits and final 176-root configured tests, while its remaining 207 numerical positions and later batches stay outside its assembly scope. New style warnings are recorded; default-build evidence is inherited and lint remains unresolved.

The [complete constant and loop-square checkpoint](../../environments/reconstruction-full-f1-constant-validation.json) closes all original 815 weighted rows and proves the complete F₁ guarded contraction `1/288`. The scalar target-F row is checked, including the target/shifted-source distinction; a complete fiber invariant remains open in this record. The [five-slot loop-square theorem](../../AxiomaticGW/GKM/Fixtures/HodgeLoopSquare.lean) uses the new `LoopSquareGysin.SelfGysinCompatible` hypothesis: an equality of actual pull-push and constructed excess-correspondence operators on every source class. Projection then derives the product; the finite graph classification alone does not supply that geometric input. No instance of the hypothesis, remaining packet products, complete Hodge/GRR comparison or semisimple CohFT realization is accepted. The record contains 131 actual targets, 3,479 exact audits and 178-root configured tests, with source-bound style warnings and unchanged inherited default-build evidence.

The [first positive-class F₁ genus-two query](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1FiberHValue.lean) is now reconstructed as zero: full class `(E,F)=(0,1)`, powers `(1,0,0)` and labels `(H,pt,pt)`. The [saved incoming report](../../environments/gkm-f1-fiber-h.json) and [kernel replay](../../AxiomaticGW/GKM/Fixtures/BlowupF1FiberHReplay.lean) preserve that exact ordered request and incoming ordinary rational. A coherent changed answer still reaches Lean and is rejected; changed class and state/power pairing are also rejected. The configured test root keeps this path in future `lake test` runs. The producer comparison shares conventions and admcycles dependencies and certifies no localization or class-valued CohFT input.

The same [37-target/161-audit checkpoint](../../environments/reconstruction-first-f1-fiber-h-validation.json) includes the mixed and separating-square consumers and the [complete raw-square assembly](../../AxiomaticGW/GKM/Fixtures/HodgeFullSquare.lean). With L the actual five-term degree-one image and Q = x² − xy + y², its three complete candidate classes become Q·A(raw₀₀) + (9/2)L², 4L² and −Q·A(raw₀₀) + (7/2)L². These are conditional on the named all-source-class Gysin laws and existing realization/forgetful/psi inputs; the raw unit terms remain explicit. No such geometric model or identification of L with lambda one is constructed. Final configured checks cover 182 roots, three new style warnings remain recorded, and the post-success stdout-check failure is preserved. The fixed benchmark bounds, nonzero shared genus-two cases, actual semisimple CohFT data and geometric comparison remain required.

For the genus-two, one-marked unit at curve degree zero, Lean now specializes the full saved class candidate in the free rational strata module. It sums all 540 fixed-point, ordered Hodge-pair and degree-component references before setting both torus weights to zero in each decorated-graph coordinate. For \(\mathbb P^2\), \(F_1\) and \(\operatorname{Bl}_2\mathbb P^2\), the resulting cycles are respectively 9, 8 and 7 times the same sixteen-term degree-two packet. The coefficient sum of that packet is \(13/1152\), so each ordinary representative is nonzero in the free module. Its image in geometric cohomology and its identification with a GW class require a realization and a virtual-localization comparison. The pinned producer itself evaluates the Hodge monomials at each contracted vertex. [Specialization proof](../../AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroStrataSpecialization.lean) · [Saved fixed-point packet](../../environments/gkm-degree-zero-hodge-strata-factored-candidate.json)

### Original relations for the genus-two Hodge packet

Write \(L\) for the held five-term degree-one packet and \(B=\frac12\xi_{\rm irr,*}(1)+2\xi_{1,*}(1)\) for the raw ordered loop and marked separating pushforwards. The original full-stable codimension-one 3-spin row has coordinates \((-30,30,42,3)\) on \((\kappa_1,\psi,\xi_{1,*}(1),\xi_{\rm irr,*}(1))\). Lean checks the free-strata identity \(10L-B=-R/36\). Thus \(L=B/10\) holds in the quotient by this row, and in any linear realization killing it. The loop factor accounts for its two ordered branches. [Picard certificate](../../AxiomaticGW/GKM/Fixtures/HodgeGenusTwoPicard.lean) · [Original-row check](../../scripts/check_admcycles_hodge_picard.py) · [3-spin relations](https://arxiv.org/abs/1303.1043)

An independent codimension-two certificate compares the sixteen-term packet \(P\) directly to the boundary square. The exporter regenerates all 14 original PPZ rows (six interior, eight boundary), their 17 ordered monomial columns and the 16 and 28 occurrences of the two held packets. Lean matches every occurrence up to decorated graph isomorphism. The residual \(200P-B^2\) is exactly a linear combination of 12 original rows, including the negative node-psi excess terms in the square. The auxiliary \(\kappa_2\) coordinate cancels. The quotient statement requires no geometric hypotheses. [Source rows](../../AxiomaticGW/GKM/Fixtures/HodgeBoundarySquareRows.lean) · [Certificate and quotient theorem](../../AxiomaticGW/GKM/Fixtures/HodgeBoundarySquareCertificate.lean)

For \(r=0,1,2\) blowups the realization of the ordinary packet is \((9-r)B^2/200\). This proof requires the 12 contributing rows to vanish, the loop self-intersection, mixed and separating self-intersection Gysin laws, the listed fundamental and node-psi compatibilities, and realization of the loop, separating and refined gluing graphs. It requires no independent identification of a kappa or Hodge class and no forgetful pushforward. A geometric GW comparison still requires virtual localization and identification of stabilization of the virtual class with these graph pushforwards. [Realization theorem with full hypotheses](../../AxiomaticGW/GKM/Fixtures/HodgeBoundarySquareRealization.lean) · [Regression tests](../../AxiomaticGWTest/GKM/HodgeBoundarySquareCertificate.lean)

In the pinned Sage environment these commands regenerate the source rows and check both certificates.

```bash
python -B scripts/check_admcycles_hodge_picard.py
python -B scripts/export_gkm_hodge_boundary_square.py --check
lake build AxiomaticGWTest.GKM.HodgeGenusTwoPicard AxiomaticGWTest.GKM.HodgeBoundarySquareCertificate
```


From the repository root, the saved first-H report can be checked offline and its public replay path rebuilt with:

```bash
python3 -B scripts/gkm_f1_fiber_h.py replay environments/gkm-f1-fiber-h.json --output AxiomaticGW/GKM/Fixtures/BlowupF1FiberHReplay.lean --check
lake build AxiomaticGW.GKM.Fixtures.BlowupF1FiberHReplay AxiomaticGWTest.GKM.BlowupF1FiberHReplay
python3 -B -m unittest discover -s scripts -p test_gkm_f1_fiber_h.py -v
```

The test command includes the three negative Lean claims; it requires the accepted local Lean dependencies and runs no Sage exploration.

## F₁ canonical fiber comparisons through energy two

For the fiber class \(F=(0,1)\) in the effective basis \((E,F)\), the genus-two P, N and K requests are respectively \(\langle\tau_1(\mathrm{pt}),\mathrm{pt}\rangle\), \(\langle\mathrm{pt},\mathrm{pt},\mathrm{pt}\rangle\), and \(\langle\tau_1(E),\mathrm{pt},\mathrm{pt}\rangle\). Each ordinary localization value is zero. Together with the H comparison above these cover every canonical family at the fiber. The Lean proofs use the sixteen-state table at \(0,E,2E,F\). Interpretation as geometric GW invariants uses the original BP and L24 equations, the finite seeds, and exceptional point support. [Saved localization report](../../environments/gkm-f1-fiber-remaining.json) · [Lean comparison](../../AxiomaticGW/GKM/Fixtures/BlowupF1FiberRemainingReplay.lean) · [Table proof](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1FiberTable.lean).

The following commands replay the saved report offline and check the ordered query and value against Lean. Regression cases change each incoming value in turn, substitute the equal-energy class \(2E\), switch the exceptional divisor, and move the cotangent power to a different marking.

```bash
python3 -B scripts/gkm_f1_fiber_remaining.py replay environments/gkm-f1-fiber-remaining.json --output AxiomaticGW/GKM/Fixtures/BlowupF1FiberRemainingReplay.lean --check
lake build AxiomaticGW.GKM.Fixtures.BlowupF1FiberRemainingReplay AxiomaticGWTest.GKM.BlowupF1FiberRemainingReplay
python3 -B -m unittest discover -s scripts -p test_gkm_f1_fiber_remaining.py -v
```

To repeat the exploration, run the following command with the pinned Sage/admcycles environment active and set `GKM_PRODUCER` to the pinned producer checkout. The exporter checks the exact equivariant functions at ordinary specialization. The Lean comparison checks the resulting ordinary values.

```bash
python -B scripts/gkm_f1_fiber_remaining.py explore --producer "$GKM_PRODUCER" --output /tmp/gkm-f1-fiber-remaining.json
```

## The strict-transform line on the two-point blowup

The pinned producer returns ordinary value zero for the five canonical
genus-two requests at \(L=H-E_1-E_2\), in effective coordinates \((0,0,1)\).
In order, the insertions are \((\tau_1 H,\mathrm{pt})\),
\(\tau_1\mathrm{pt}\), \((\mathrm{pt},\mathrm{pt})\),
\((\tau_1 E_1,\mathrm{pt})\), and \((\tau_1 E_2,\mathrm{pt})\).
The importer uses the complete ordered descendant key for each row.
[Producer report](../../environments/gkm-bl2-line-canonical.json) ·
[Importer](../../scripts/gkm_bl2_line_canonical.py) ·
[Lean request identities](../../AxiomaticGW/GKM/Fixtures/BlowupTwoLineCanonical.lean)

The reconstruction uses the original hyperplane equation at \(L+E_1\).
The coefficients of the degree-zero columns \(H_0,K_{1,0},K_{2,0}\) are
\(3,1,-3\). Their boundary values contribute \(-7/2880\).
The lower-genus constant uses all 815 positions in the original L24 frame.
[Divisor contributions](../../AxiomaticGW/Surfaces/Fixtures/BlowupTwoLineHDivisors.lean) ·
[Original lower-genus sum](../../AxiomaticGW/Surfaces/Fixtures/BlowupTwoLineHConstant.lean)

The complete lower-genus sum is \(7/2880\), giving \(H_L=0\).
The point, exceptional and primary equations give the same value for the
other four families. All 20 states through effective energy one pass the
original bounded checker, including the five at \(L\). The five incoming
GKM coefficients agree with the reconstruction. Each coherent change of
one ordinary and equivariant coefficient to \(1/19\) fails comparison.
[Full graph certificate and bounded table](../../AxiomaticGW/Surfaces/Fixtures/BlowupTwoLineL24/Assembly.lean) ·
[Five GKM equalities](../../AxiomaticGW/GKM/Fixtures/BlowupTwoLineCanonicalReplay.lean) ·
[Mutation tests](../../scripts/test_gkm_bl2_line_canonical.py)

Of the 815 positions, 121 satisfy the original zero-weight or higher-genus
guard. Lean evaluates 280 decorated representatives and transports 414
others by equality of the four pulled-back labels on the original graph.
Each transport retains its two original rational weights. In total, 180
weighted positions are nonzero. The 458 one-cotangent component values
used in these evaluations are checked at their complete ancestor keys.
The frame, constant, hyperplane value, bounded table and GKM replay all
audit to `propext`, `Classical.choice` and `Quot.sound`.

Run `lake env lean --run scripts/explore_bl2_line_l24.lean` to produce the
815 indexed rational contributions and cumulative sums from the original
component functions. The structural certificate generator compares graph
cores, decorations, decision procedures for labels, and pulled-back
insertions. It regenerates the assignment of every position using only the
original L24 data and the checked set of positions with a genus-two vertex.

```sh
python3 scripts/export_bl2_line_l24_frame.py --check
python3 scripts/gkm_bl2_line_canonical.py replay environments/gkm-bl2-line-canonical.json \
  --output AxiomaticGW/GKM/Fixtures/BlowupTwoLineCanonical.lean --check
lake build AxiomaticGWTest.GKM.BlowupTwoLineCanonical
python3 scripts/test_gkm_bl2_line_canonical.py
```

## A positive-degree fixed-locus class and its unit pullback

On \(\overline M_{0,4}\), take the degree-one plane class with ordered primary insertions \((\mathrm{pt},H,\mathrm{pt},H)\). For the plane fan in the exchange choose toric lifts \((D_0D_1,D_1,D_0D_2,D_2)\). The two point lifts are supported at distinct fixed points, the cones \((0,1)\) and \((0,2)\). This choice forces markings \(1,2\) onto the first endpoint and \(3,4\) onto the second. Exactly one of the 48 fixed loci survives. Both contracted components have three special points. Forgetting the map contracts the unmarked moving line between them to a single node. With the incident flags retained before integration the result is the raw boundary class \(D_{12|34}\) with equivariant coefficient exactly one. [Fixed-locus report](../../environments/gkm-plane-line-boundary-class.json) · [Lean class, coefficient and graph identification](../../AxiomaticGW/GKM/Fixtures/PlaneLineBoundaryClass.lean)

Adding a fifth unit leaves two of the 96 five-marked loci. The two undecorated terms have coefficient one. Their node-psi terms carry coefficients \(+1/y\) and \(-1/y\). At either four-point contracted component the original rational psi relation replaces the flagged psi term by the same labelled tree \(12|5|34\). Lean checks both graph attachments and cancellation, so every rational functional annihilating the two attached relations has a regular ordinary value. Each surviving undecorated graph is one placement in the universal pullback of \(D_{12|34}\). The resulting five-point class is \(D_{125|34}+D_{12|345}\). The Sage run verifies these identities on the source tautological classes and checks that the central tree has degree one. [Class and flat-unit checks](../../AxiomaticGW/GKM/Fixtures/PlaneLineBoundaryClass.lean) · [Missing-pole-partner and marking regressions](../../AxiomaticGWTest/GKM/PlaneLineBoundaryClass.lean)

On the section that bubbles the fifth unit together with the first point, the ordinary restriction gives the original four-point boundary class on the main factor. The incoming three-point tail rows for degrees 0 and 1 are \((1,0,0)\) and \((0,0,0)\) on the node states \((1,H,\mathrm{pt})\). Lean compares all six entries with its genus-zero primary reconstruction. Contracting the complete ordinary inverse metric and both ordered effective degree splits leaves the degree-one main class with node insertion \(\mathrm{pt}\). The class realization uses the sector's graph-map, universal-curve base-change and rational-tail section compatibilities. [Separating restriction and inverse-metric contraction](../../AxiomaticGW/GKM/Fixtures/PlaneLineBoundarySplitting.lean)

The pinned producer at revision `a09c6625b280312721c5e0f2f915791781339aa5` enumerates the maps in `StableMapsGKM.fixed_loci`. Its `StableMapGKM._localization_factors` returns the actual edge, tangent, insertion and automorphism factors and lists the ordered tangent and flag weights of each supported vertex. Its stable-vertex loop selects only total degree \(3g-3+n\) and calls `hodge_integral`, which evaluates a number. The companion exporter uses those pre-integration factors and retains both powers of the flag on the four-point vertex, including the constant term that the integral would discard. General identification with stabilized virtual GW classes still requires class-level virtual localization, the actual stabilization pushforward on every supported map type and its compatibility with gluing and units. The three certified loci use a degree-one bridge with two stable endpoints. [Exporter](../../scripts/gkm_plane_line_boundary_class.py) · [Source pin](../../environments/gkm-localization-source.json) · [Liu–Sheshmani, §4](https://arxiv.org/abs/1407.1370) · [Graber–Pandharipande](https://arxiv.org/abs/alg-geom/9708001)

The first command checks native enumeration, the source factors, the tautological classes, both comparisons and byte-for-byte regeneration. The second replays the saved exchange without Sage.

```bash
python -B scripts/gkm_plane_line_boundary_class.py --producer "$GKM_PRODUCER" --check
python3 -B scripts/gkm_plane_line_boundary_class.py --replay environments/gkm-plane-line-boundary-class.json --check
lake build AxiomaticGWTest.GKM.PlaneLineBoundaryClass
```

## Primitive exceptional classes on the two blowups

The same positive-degree construction gives the ordinary class \(-D_{12|34}\) on \(\overline M_{0,4}\) in each of the following three cases. The first three insertions are lifts of the indicated exceptional divisor. Shifting each lift by a torus character forces the two stable endpoints and leaves its ordinary class unchanged.

| Target | Full class | Fourth ordinary divisor | Flag weight on the first endpoint |
| --- | --- | --- | --- |
| \(F_1\) | \(E=(1,0)\) | \(H-E\) | \(x-y\) |
| \(\mathrm{Bl}_2\mathbb P^2\) | \(E_1=(1,0,0)\) | \(H-E_1-E_2\) | \(x-y\) |
| \(\mathrm{Bl}_2\mathbb P^2\) | \(E_2=(0,1,0)\) | \(H-E_2\) | \(y\) |

The pinned producer enumerates 16 four-marked and 32 five-marked loci for each primitive class. The invariant line has normal degree \(-1\). One four-point locus and two five-point loci support the restrictions. Lean specializes each insertion in the surface basis, multiplies the incoming factors to \(-1\), and checks that integrating the signed divisor gives the value from the surface primary reconstruction. The five-point class with one unit is \(-D_{125|34}-D_{12|345}\) after the two opposite flag-psi residues cancel on the common refinement. [Native exceptional packets](../../environments/gkm-exceptional-boundary-classes.json) · [Signed class and regularity proofs](../../AxiomaticGW/GKM/Fixtures/ExceptionalBoundaryClass.lean)

On the \(15|234\) section the degree-zero tail has coefficient \(-1\) at its own exceptional node and zero at every other node state. The inverse metric contributes the second minus sign. The positive-degree tail vanishes. The original primary reconstruction checks all 28 incoming tail entries across both degrees and the actual target bases. The class formula requires the four-point cotangent relation, graph realization, the universal-curve gluing compatibility and the rational-tail section identity. Virtual localization and comparison of the stabilized virtual class with these finite fixed-locus expressions remain geometric inputs. [Boundary splitting](../../AxiomaticGW/GKM/Fixtures/ExceptionalBoundarySplitting.lean) · [Sign and equal-energy regressions](../../AxiomaticGWTest/GKM/ExceptionalBoundaryClass.lean)

```bash
python -B scripts/gkm_exceptional_boundary_classes.py --producer "$GKM_PRODUCER" --check
python3 -B scripts/gkm_exceptional_boundary_classes.py --replay environments/gkm-exceptional-boundary-classes.json --check
lake build AxiomaticGWTest.GKM.ExceptionalBoundaryClass
```

## Positive-degree small quantum products and the plane idempotents

The pinned producer computes 155 genus-zero primary three-point tensors up to permutation on the six primitive effective generators. The classes are \(H\) on the plane, \(E,F\) on \(F_1\), and \(E_1,E_2,L=H-E_1-E_2\) on the two-point blowup. Every coefficient is regular at the torus origin. The exchange keeps the exact polynomial in the two characters, including zero coefficients. Lean evaluates all 530 ordered basis entries at the ordinary origin and compares them with the established primary reconstruction. Raising the third index uses the actual ordinary inverse pairing. The unit, commutativity and coefficientwise associativity checks retain both ordered splittings of each individual generator. This covers the ordinary augmentation quotient modulo products of positive Novikov monomials. [Native three-point report](../../environments/gkm-small-quantum-generators.json) · [Ordinary reconstruction comparison](../../AxiomaticGW/GKM/Fixtures/SmallQuantumGeneratorComparison.lean) · [First-order multiplication](../../AxiomaticGW/GKM/Fixtures/OrdinarySmallQuantumGenerators.lean)

On the plane write \(P\) for the held point lift, \(P=H(H+x)\), and \(q\) for the full line class. The nonzero degree-one three-point coefficients, up to permutation, are \(\langle H,P,P\rangle=1\) and \(\langle P,P,P\rangle=x-2y\). Lowering the proposed product recovers both values and every zero entry on the original frame. Its degree-zero term is the previously accepted localized product. In this basis \(H\star P=-yP+q\) and \(P\star P=(y^2-xy)P+q(H+x-y)\). Lean verifies the unit, associativity and invariance of the accepted classical metric. The cubic \(H(H+x)(H+y)=q\) represents these coefficients. Identifying them with the formal GW product requires an equivariant GW realization with the named metric and the three-point inputs; the comparison with actual incoming GW data here reaches line degree. [Plane product and GW coefficient interface](../../AxiomaticGW/GKM/Fixtures/PlaneSmallQuantumProduct.lean)

Over \(K=\mathbb Q(x,y)\), work in \(K[q]/(q^2)\). At fixed point \(i\) the hyperplane root moves from \(r_i\in\{0,-y,-x\}\) to \(r_i+q/e_i\), with \(e_i\) the accepted tangent Euler class. Evaluating a state at the three lifted roots is bijective. The inverse images of the three coordinate units are mutually orthogonal primitive idempotents, sum to the flat unit, and reduce to the accepted classical fixed-point projectors. The inverse restriction matrix gives their first-order coefficients explicitly; Lean proves the first projector's correction is nonzero. Higher Novikov orders and an all-genus semisimple reconstruction action remain open. [Idempotent lift and nonvanishing proof](../../AxiomaticGW/GKM/Fixtures/PlaneQuantumIdempotents.lean) · [Regression tests](../../AxiomaticGWTest/GKM/SmallQuantumGenerators.lean)

```bash
python -B scripts/gkm_small_quantum_generators.py explore --producer "$GKM_PRODUCER" --output /tmp/gkm-small-quantum-generators.json
python3 -B scripts/gkm_small_quantum_generators.py replay environments/gkm-small-quantum-generators.json --output AxiomaticGW/GKM/Fixtures/SmallQuantumGeneratorData.lean --check
lake build AxiomaticGWTest.GKM.SmallQuantumGenerators
```

## First-order equivariant primitive bases of the blowups

For each blowup let \(D\) index the primitive effective curve generators and set \(A=K[q_d:d\in D]/(q_d q_{d'}:d,d'\in D)\), where \(K=\mathbb Q(x,y)\). The square-zero algebra retains each full curve label. For an ordered pair \((l,r)\) in the accepted fixed-point order, put \(\Delta a=a_r-a_l\). Its contribution to the three-point tensor is \(k\,\Delta a\,\Delta b\,\Delta c\). Lean checks the following six contributions against every one of the 128 ordered entries on \(F_1\) and 375 on the two-point blowup. The two fixed fibers both contribute to the single class \(F\). [Blowup presentations and native comparison](../../AxiomaticGW/GKM/Fixtures/BlowupQuantumIdempotents.lean)

| Surface | Full class | Fixed-point pair | Cubic weight \(k\) |
| --- | --- | --- | --- |
| \(F_1\) | \(E=(1,0)\) | \((1,3)\) | \(-1/(x-y)^3\) |
| \(F_1\) | \(F=(0,1)\) | \((0,1)\) | \(1/[y^3(x-y)]\) |
| \(F_1\) | \(F=(0,1)\) | \((2,3)\) | \(-1/[x^3(x-y)]\) |
| \(\operatorname{Bl}_2\) | \(E_1=(1,0,0)\) | \((1,2)\) | \(-1/(x-y)^3\) |
| \(\operatorname{Bl}_2\) | \(E_2=(0,1,0)\) | \((3,4)\) | \(-1/y^3\) |
| \(\operatorname{Bl}_2\) | \(L=(0,0,1)\) | \((2,3)\) | \(-1/x^3\) |

For each pair in class \(d\), add \(k\,\Delta a\,(e_l\delta_l+e_r\delta_r)\) to \(T_d(a)\), using the accepted Euler factors. The map \(1+\sum_d q_d T_d\) identifies multiplication with coordinatewise multiplication over \(A\). Hence the lifted projector is \(p_i=\delta_i-\sum_d q_d T_d(\delta_i)\). These projectors form a basis over the full square-zero ring. They are primitive, multiply orthogonally, and sum to the flat unit. The original flat pairing lowers each product coefficient to its incoming three-point tensor. The theorem for a geometric GW theory requires its toric metric and native three-point values to agree. All five directions have an explicitly tested nonzero projector correction. [Square-zero product and projectors](../../AxiomaticGW/GKM/FirstOrderFixedPoints.lean) · [Nonvanishing tests](../../AxiomaticGWTest/GKM/BlowupQuantumIdempotents.lean)

Put \(u_i=\sum_d q_d T_d(\delta_i)_i\). In the primitive basis the Gram diagonal and its inverse are \(g_i=e_i^{-1}(1-2u_i)\) and \(g_i^{-1}=e_i(1+2u_i)\). After choosing \(s_i^2=e_i\) in a field extension, the diagonal scale \(s_i(1+u_i)\) gives unit Gram entries. Lean proves that such a choice exists over an algebraically closed extension and checks the inverse matrix before any root choice. These data fix the normalization for a candidate first loop coefficient \(B\), whose self-adjointness test is \(g_i B_{ij}=B_{ji}g_j\). The pinned producer exposes fixed loci, localization contributions and integrated correlators. Its package supplies no calibrated \(R(z)\) series. Determining positive-loop coefficients and proving their all-genus class action requires additional input. [Metric, scalar extension and adjoint test](../../AxiomaticGW/GKM/Fixtures/BlowupQuantumIdempotents.lean)

```bash
lake build AxiomaticGWTest.GKM.BlowupQuantumIdempotents
```

## Equivariant two-point calibration in the primitive basis

The first and higher calibration archives retain the exact equivariant two-point correlators. For the six primitive generators the retained marking has cotangent powers \(m=0,1,2\), the node has power zero, and \(S\) uses inverse-loop power \(m+1\) at zero primary deformation. These 18 matrices have 348 ordered entries. The exchange computes both the classical anticanonical matrix \(C\) and its divisor coordinates from the pinned surface products. Restriction conjugates \(C\) to the accepted tangent sums \(\chi_i\). Writing \(n=\int_\beta c_1\) and \(F_m(a,b)=\langle a,\tau_m(b)\rangle_{0,\beta}\), the identities checked on the reports are

\[
  nF_0(a,b)=\langle c_1,a,b\rangle_{0,\beta},\qquad
  nF_{m+1}=C^{\mathsf T} F_m-F_m C\quad(m=0,1).
\]

The positive sign is attached to \(C\) at the node and the negative sign to \(C\) at the retained marking. The equivariant divisor comparison uses the original three-point packet at each full class. An identified GW theory recovers the same raised column by contracting the node with its inverse metric. The positive tail then inserts that column into the main component's linear functional. [Incoming coefficient extractor](../../scripts/gkm_equivariant_calibration.py) · [Source matrix comparison](../../AxiomaticGW/GKM/Fixtures/EquivariantCalibrationReplay.lean)

In classical fixed-point coordinates let \(A_{ij}\) be the raised native coefficient at \(z^{-1}q^\beta\) and \(t_{ij}=(\chi_i-\chi_j)/n\). The three checked coefficients are \(A_{ij},t_{ij}A_{ij},t_{ij}^2A_{ij}\). At primitive degree their continuation under the anticanonical commutator is the expansion of \(A_{ij}/(z-t_{ij})\) at infinity. The source comparison reaches the three reported powers. On the diagonal the expression is \(A_{ii}/z\). For \(i\ne j\) the tangent sums are distinct, and expansion at zero begins with \(-A_{ij}/t_{ij}\) and \(-A_{ij}/t_{ij}^2\). The constant term equals the \(i\)-entry of the actual degree-\(\beta\) correction to the primitive projector \(p_j\). For the plane entry \((0,1)\), the primary inverse-loop coefficient is \(-1/[y(x-y)]\) and the gap is \(y\), giving the constant projector correction \(1/[y^2(x-y)]\). In the same coordinate pair \((1,2)\) on the two-point blowup, the raised primary coefficient is \(-y/(x-y)\) along \(E_1\) and zero along \(E_2\). Alternating signed transpose gives the primitive-class sewing identity for the three source powers. [Transition and sewing proofs](../../AxiomaticGW/GKM/Fixtures/SemisimpleCalibration.lean)

This comparison determines a small-\(z\) off-diagonal term of the primitive-degree resolvent. Identifying a complete calibrated positive-loop \(R(z)\) still needs an asymptotic normalization and the higher-order, all-genus comparison. Adding an arbitrary diagonal to a candidate first coefficient preserves the linear symplecticity equation and commutes with the classical spectrum. Under \(T(z)=z(1-R(z)^{-1})\mathbf 1\) it changes the \(z^2\) translation by that diagonal vector. The pinned exchange explicitly leaves its \(R\)-matrix and translation fields empty. [Loop expansion and gauge calculation](../../AxiomaticGW/GKM/CalibrationSpectrum.lean) · [Pinned exchange fields](../../environments/gkm-inputs-osx-arm64.json)

```bash
python3 -B scripts/gkm_equivariant_calibration.py --check
lake build AxiomaticGWTest.GKM.SemisimpleCalibration
```

For each of the six primitive curve directions, choose a translation coefficient $u_d$ and put $C_{ij}=-A_{ij}/t_{ij}^2$ for $i\ne j$, with $C_{ii}=0$. The unique matrix with these off-diagonal coefficients and row sums $u_d$ is $B_d=C+\operatorname{diag}(u_d-C\mathbf 1)$. In the square-zero Novikov ring $B=\sum_d q_dB_d$ is self-adjoint for the actual Gram matrix $G$ of the lifted projectors. With $R(z)=1+zB$, Lean checks both inverse identities, $R(-z)^tGR(z)=G$, and $z(1-R(z)^{-1})\mathbf1=z^2\sum_d q_du_d$. The plane entry $(0,1)$ is $1/[y^3(x-y)]$. The entry $(1,2)$ on the two-point blowup is $y/(x-y)^3$ along $E_1$ and zero along $E_2$. This loop coefficient has zero classical Novikov part. The geometric translation, higher Taylor coefficients and higher Novikov degrees remain to be determined. [Primitive coefficient, metric and translation proofs](../../AxiomaticGW/GKM/Fixtures/PrimitiveLoopTranslation.lean) · [Sign and curve-class checks](../../AxiomaticGWTest/GKM/SemisimpleCalibration.lean)

The full primitive-degree resolvent also has higher powers of $z$. Its Taylor coefficient at power $m$ is $-A_{ij}/t_{ij}^{m+1}$. Lean proves the exact remainder for every truncation order and the reciprocal-Euler transpose sign $(-1)^{m+1}$. On the plane, the $(0,1)$ quadratic coefficient is $1/[y^4(x-y)]$, which is nonzero in the coefficient field. Thus the linear polynomial above supplies only the first Taylor coefficient of the off-diagonal comparison. [Exact Taylor remainder](../../AxiomaticGW/GKM/CalibrationSpectrum.lean) · [All-power native sewing sign](../../AxiomaticGW/GKM/Fixtures/SemisimpleCalibration.lean)

At any finite set of positive Taylor powers the square-zero construction has a precise translation test. At odd powers the diagonal is free and the translation vector fixes it uniquely. At even powers the metric equation forces zero diagonal, so the only admissible translation is the row sum of the native off-diagonal matrix. Under these conditions the finite loop is normalized at zero, has an explicit inverse, preserves the lifted projector metric at opposite parameters, and induces the indicated flat-unit translation. The regression combines the native quadratic and cubic terms and rejects a shifted even-power row. [Finite Taylor loops](../../AxiomaticGW/GKM/Fixtures/PrimitiveTaylorTranslation.lean) · [Regression](../../AxiomaticGWTest/GKM/PrimitiveTaylorTranslation.lean)

## Sewing at composite curve classes

The higher-calibration archive contains 13 requests at sums of two primitive curves. The plane contributes \(2H\) at inverse-loop power 4. On \(\mathbb F_1\), \(E+F\) and \(2E\) occur at powers 2 and 3. On the two-point blowup, \(E_2+L,E_1+L,2E_1,2E_2\) occur at powers 2 and 3, where \(L=H-E_1-E_2\). Each row retains its native toric basis, full effective coordinates and inverse-loop power. [Source requests](../../environments/gkm-higher-calibration-comparison.json) · [Formal request and cut binding](../../AxiomaticGW/GKM/Fixtures/CalibrationSewingFrame.lean)

Write \(F_{k,\beta}(a,b)=\langle a,\tau_{k-1}(b)\rangle_{0,\beta}\) for \(k>0\). For every listed \((p,\beta)\), the following identity holds over \(\mathbb Q(x,y)\):

\[
F_{p,\beta}+(-1)^pF_{p,\beta}^{\mathsf T}
+\sum_{\substack{c+d=\beta\\c,d>0}}\sum_{k=1}^{p-1}
 (-1)^k F_{k,c}^{\mathsf T}\eta^{-1} F_{p-k,d}=0.
\]

The curve sum uses the full effective monoid. Mixed directions occur in both orders and equal directions give one ordered pair. Of 273 toric basis entries, 48 have a nonzero endpoint sum. In the plane point/point entry at \(2H\), both endpoints are \(1/2\), and the three signed interior contributions are \(-1,+1,-1\). On \(\mathbb F_1\), the interior is \(+1\) at the \(E,E\) entry for \(2E\) and power 2. The two-point blowup distinguishes the \(H,E_1\) entry at \(E_2+L\) and \(E_1+L\), with interior contributions 0 and 1. [Matrix proof](../../AxiomaticGW/GKM/Fixtures/CalibrationSewing.lean) · [Nonzero regression cases](../../AxiomaticGWTest/GKM/CalibrationSewing.lean)

For a GW theory with the identified toric metric, primitive two-point descendants at inverse powers 1 through 3 and the specified composite two-point row, the actual coefficient of \(S(-z)^*S(z)\) vanishes on arbitrary states. The proof uses the two-point calibration's unstable conventions for the zero class and zero power, exhaustive effective and loop splittings, and bilinearity. It assumes neither a sewing relation nor an equivariant localization theorem. The positive-loop \(R\)-matrix, flat-unit translation and all-degree symplecticity remain open. [Geometric theorem](../../AxiomaticGW/GKM/Fixtures/CalibrationSewingGeometry.lean)

```bash
python3 -B scripts/gkm_calibration_sewing.py --check
python3 -B scripts/test_gkm_calibration_sewing.py -v
lake build AxiomaticGWTest.GKM.CalibrationSewing
```

## Next required bridge

The ordinary rational blowup equations now have a [uniform H pivot and cross-column cancellation](../../AxiomaticGW/Surfaces/GenusTwoBlowupHContributions.lean), [decreasing H-family coefficient support](../../AxiomaticGW/Surfaces/GenusTwoBlowupHCoupling.lean), and [complete canonical P-row support](../../AxiomaticGW/Surfaces/GenusTwoBlowupPPrimarySupport.lean), including strict lower-plane support of every surviving primary coefficient. These are exact identities of the existing normalized BP/L24 algorithms at full curve classes. They do not import localized CohFT classes, prove equivariant localization or ordinary specialization, or certify either complete blowup numerical suite. No producer source or exchange schema is changed.

The [ordinary exceptional support interface](../../AxiomaticGW/Surfaces/ExceptionalEvaluationSupport.lean) now gives point-supported zero values at positive zero-hyperplane-degree classes and helps derive the [F₁ degree-zero primary point](../../AxiomaticGW/Surfaces/GenusTwoExceptionalInitialValues.lean) from original BP geometry. It concerns the ordinary rational point class in the existing surface theory. A chosen equivariant point lift need not restrict to zero on an exceptional curve, so these theorems require the ordinary comparison before use with localized GKM data. They provide no localization derivation or imported CohFT classes, and full blowup reconstruction and benchmark replay remain open.

Extend kernel replay from the classical state, curve, and invariant-edge data to stable-map localization graphs and relation-to-GW derivations. Export actual CohFT class expressions or an identified semisimple reconstruction action, prove its formal action laws, and retain the geometric comparison hypotheses explicitly. Geometric instantiation of the mixed comparison inputs, full descendant--ancestor potential comparison, higher Novikov product coefficients and a calibrated R-matrix, graph normalization/stabilization, all fixed benchmark query round-trips, and the full shared release corpus remain required. The present target-data certificates and algebraic transport do not discharge those obligations.

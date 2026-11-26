# Implementation progress

This file is the durable implementation record for AxiomaticGW. The [roadmap](AxiomaticGWRoadmap.md) remains the source of truth for milestone status and ordering; this record captures how a completed implementation was delivered and verified.

Each entry records the accepted scope, implementation commit, a link to the canonical mathematics-to-Lean map, principal API, verification evidence, deliberately deferred work, and the next gate. Git history remains the authoritative source for the exact diff.

Older entries preserve their then-current scope and next gate; explicit follow-up paragraphs record work completed by later revisions.

## 2026-11-26. Mixed exceptional support and seed-free divisor equations

For each of the six primitive curve directions, the off-diagonal Taylor entries of the native two-point resolvent satisfy the equivariant metric adjoint equation. A supplied flat-unit translation vector determines the diagonal uniquely. The assembled square-zero loop has a checked two-sided inverse and satisfies the signed symplectic identity for the Gram matrix of the lifted projectors. Identifying a geometric translation and higher-order loop remains open. [Semisimple comparison](../references/GKMExchange.md#equivariant-two-point-calibration-in-the-primitive-basis)

The genus-two few-marking suite has **1,546 of 5,199 distinct ordered requests** with original reconstruction witnesses. Coverage is 48/48 on the plane, 263/656 on $F_1$, and 1,235/4,495 on the two-point blowup. In class $E_1+E_2$, all five singletons and all 100 ordered pairs vanish. Of those 105 rows, 29 were already in the exceptional point frame. Incidence kills every original lower-genus term needed for the mixed interior pairs. Grading and multilinearity extend this conclusion to arbitrary powers and arbitrary cohomology states at up to two markings. The fixed suite has 3,653 open rows, including 110 at energy two on the two-point blowup. [Distinct coverage](../../AxiomaticGW/GKM/Fixtures/BlowupPositivePlaneEnergyTwoBenchmark.lean) · [Original mixed reconstruction](../../AxiomaticGW/Surfaces/Fixtures/BlowupTwoMixedExceptionalInteriorPairs.lean) · [Arbitrary states and powers](../../AxiomaticGW/GKM/Fixtures/BlowupTwoMixedExceptionalGeometry.lean)

The original two-point blowup reconstruction now verifies all 210 ordered requests on $2E_1$ and $2E_2$. The own-divisor singleton uses ten boundary contractions totaling $29/5760$ and four calibration terms totaling $25/5760$. For the 64 interior pairs, 88 of the 352 full-class signed graph terms survive incidence. Their lower-genus components and the primitive and class-zero contributions from the calibration are evaluated on the original target. On each axis eight of the 32 interior values are nonzero. The unit pair gives $27/1280$ and the own-divisor pair gives $-7/160$. Each of the 210 original values agrees with its complete incoming fraction and its regular specialization. Independently, 136 of the fields match reconstructed $F_1$ requests and the other 74 vanish with a foreign exceptional insertion. [Target-side interior proof](../../AxiomaticGW/Surfaces/Fixtures/BlowupTwoDoubleExceptionalInteriorPairs.lean) · [Comparison for all 210 rows](../../AxiomaticGW/GKM/Fixtures/BlowupTwoDoubleExceptionalCompleteReplay.lean) · [Cross-surface comparison](../../AxiomaticGW/GKM/Fixtures/BlowupTwoDoubleExceptionalComparison.lean)

A native 15-row report gives all one-marking references for the two rulings and the doubled strict line. On either ruling the unit descendant is $-9/640$, compared with $-1/120$ on the fiber of $F_1$. Thus simply copying the fiber value would introduce an error of $11/1920$. On $2L$ the three divisor singleton fields are all $-3/320$. For $2L$, the original reconstruction proves all five native singleton values. Its 50 signed graph contributions give a leading unit ancestor of $-1/1152$, divisor ancestors of $-29/5760$, and a zero point ancestor. Eight proper-class keys at $L$ and zero complete the calibration. On the two rulings, 390 original lower-genus component equations and 100 signed graph terms now certify all ten singletons. The two unit descendants both differ from the original $F_1$ fiber by $-11/1920$. The independent native producer also reproduced all 300 two-marked references on these three curves byte for byte. [Ruling reconstruction](../../AxiomaticGW/Surfaces/Fixtures/BlowupTwoRulingOneMarking.lean) · [Ordered pair references](../../environments/gkm-bl2-positive-plane-energy-two-pairs.json). [Double-line proof](../../AxiomaticGW/GKM/Fixtures/BlowupTwoDoubleLineReplay.lean) [Native references](../../environments/gkm-bl2-positive-plane-energy-two-singletons.json) · [Exact comparison](../../AxiomaticGW/GKM/Fixtures/BlowupTwoEnergyTwoSingletonComparison.lean)

For the pinned toric targets, connected positive-cover support exists at every effective curve class on the plane and on $F_1$. On the two-point blowup write the class as $aE_1+bE_2+cL$, where $L=H-E_1-E_2$. A connected graph support exists exactly when $c>0$, $a=0$ or $b=0$. The two exceptional edges have disjoint endpoints and the strict transform of the line joins them. The proof accounts for edge orientation, positive multiplicity and the contracted origin. It also proves vanishing in **any additive target** of a finite sum indexed by connected graphs in a mixed exceptional class of plane degree zero. Identifying the sum with the actual geometric stable-map pushforward remains open. Native fixed-locus enumeration independently found no graph in class $(1,1,0)$ at each of the nine pairs $g,n\in\{0,1,2\}$. [Three-target theorem](../../AxiomaticGW/GKM/Fixtures/SurfaceFixedGraphSupport.lean) · [Class-valued sum](../../AxiomaticGW/GKM/Fixtures/BlowupTwoExceptionalGraphSupport.lean) · [Native controls](../../scripts/check_gkm_exceptional_graph_support.py)

The original marked divisor equation certifies 20 ordered genus-two rows on $F_1$ and 180 on the two-point blowup with an empty singleton table. Both the curve-intersection coefficient and the lowered cotangent correction vanish. Eight $F_1$ rows and 116 two-point blowup rows are disjoint from the earlier energy-one, $F_1$ energy-two, exceptional-point and mixed exceptional frames. At positive degree the new dimension route also certifies ordinary zeros at unstable arities directly from the signed virtual dimension, without numerical seeds. These off-dimension requests lie outside the 5,199-row benchmark. [Divisor proof](../../AxiomaticGW/Surfaces/GenusTwoZeroDivisorPairs.lean) · [Disjoint counts by energy](../../AxiomaticGW/Surfaces/GenusTwoZeroDivisorBenchmark.lean) · [Positive-degree worked examples](../references/ResearchQueries.md#two-seed-free-vanishing-computations)

The plane line with a single point descendant supplies a nonconstant full-field test. The sum over the six possible marked ends is $[y^k-(y-x)^k]/x$ at every power $k$ of the cotangent class. Its ordinary values come from the original genus-zero line reconstruction and grading. At $k=2$ the native report gives $2y-x$ while the ordinary value is zero. Offline replay rejects $3y-x$ at the same request. Native graph enumeration checks all six marked loci and all contributions at $k=0,1,2,3,6$. [Polynomial and regularity](../../AxiomaticGW/GKM/Fixtures/PlaneLineOneMarkedPoint.lean) · [Ordinary interpretation](../../AxiomaticGW/GKM/Fixtures/PlaneLineOneMarkedPointReplay.lean) · [Research command](../references/ResearchQueries.md#a-nonconstant-equivariant-descendant-of-a-plane-line)

For every positive multiple of an exceptional curve, the two endpoint choices and all positive covering multiplicities transport from the exceptional axis of $F_1$. The torus characters agree on $E_1$ of the two-point blowup. On $E_2$ the substitution is $(x,y)\mapsto(y-x,-x)$. It preserves regular ordinary specialization and carries the eleven recorded bridge factors to their counterparts. The chosen hyperplane lifts differ on $E_1$, so this transport alone gives no equality for arbitrary insertions. Point insertions kill the marked restriction product on every nonzero exceptional support, and an insertion of the other exceptional divisor kills it on a pure axis. These graph proofs cover all 106 and 514 earlier exceptional point requests on the two blowups, including arbitrary class-valued weights at the vertices. [Character transport](../../AxiomaticGW/GKM/Fixtures/ExceptionalCharacterField.lean) · [Marked benchmarks](../../AxiomaticGW/GKM/Fixtures/ExceptionalMarkedGraphBenchmark.lean)

The unchanged producer has checked the entire 20-row divisor suite on $F_1$. Native receipts on the two-point blowup accumulate by full curve class. The archived snapshot checks both directions of coverage at every curve class it lists. Its independent ordinary proof also applies to the remaining rows of the 180-row divisor benchmark. [Full $F_1$ comparison](../../AxiomaticGW/GKM/Fixtures/ZeroDivisorPairsReplay.lean) · [Two-point blowup snapshot](../../environments/gkm-zero-divisor-bl2-partial.json)

At a genus-two surface localization vertex two tangent directions contribute $\lambda_i\lambda_j$. Grading, relabeling, string and dilaton reduce every such integral to eight possible keys, including the unmarked $\lambda_1\lambda_2$ integral. The marked raw strata relation implies that the entire $\lambda_1^2$ sector is twice the $\lambda_2$ sector when their one-point seeds are identified with the two decoded strata integrals. Reduced Sage exploration recovered $1/144$ for $\langle\tau_1(E_1),\tau_1(E_1)\rangle_{2,E_1}$, in full-field agreement with the unchanged producer. The Lean certificates check the supplied vertex values against the eight recorded seed numbers. Identifying those numbers with geometric Hodge integrals requires the stated geometric inputs. [Vertex recursion](../../AxiomaticGW/GKM/GenusTwoVertexHodgeReduction.lean) · [Raw sector comparison](../../AxiomaticGW/GKM/Fixtures/HodgeVertexDegreeTwo.lean) · [Worked replay](../references/ResearchQueries.md#reducing-genus-two-hodge-integrals-at-localization-vertices)

All eight genus-two localization vertex moments now have geometric deductions. The cotangent recurrences give the three pure $\psi$ integrals. Integration of the genus-two Picard relation against $\psi^3$ and $\psi_1^2\psi_2^2$ gives the two remaining first-Chern integrals. Normalization of the Hodge bundle on the loop and separating divisors and the rank-two square account for the other three. These results assume the named curve and Hodge class identities. They apply at arbitrary valence and to the signed bivalent $2L$ graph with a central $\tau_3(E_2)$. The pinned offline admcycles calculation reproduced the PPZ row $[-30,30,42,3]$ and its residual multiplier $-1/36$. [Proof of the eight inputs](../../AxiomaticGW/GKM/Fixtures/GenusTwoHodgeGeometricVertex.lean) · [Strict-line graph](../../AxiomaticGW/GKM/Fixtures/StrictLineGeometricLocus.lean)

A separate search among the fourteen original codimension-two PPZ rows gives eleven nonzero rational multipliers. Lean uses them to identify the second Chern packet with its boundary expression and derives the one-marked square from the two Chern-packet identifications, PPZ and the Hodge normalization laws. The primitive exceptional cubic query now integrates the six signed loci on each exceptional axis under these inputs. [Packet proof](../../AxiomaticGW/GKM/Fixtures/GenusTwoHodgeNormalizedPacket.lean) · [Three exceptional axes](../../AxiomaticGW/GKM/Fixtures/ExceptionalCubicGeometricLoci.lean)

The graph evaluator reads the markings, the two tangent characters and each incident flag from the indexed GKM graph. The pinned Sage producer reproduced 24 stable rational and elliptic vertex values, as well as 36 edge factors at covering degrees one through three, across the three surface fans. For the doubled strict line, all three source factors, the multiplicities, the insertion and the order-two symmetry recover the signed equivariant contribution before specialization. This calculation covers one locus. Summing every locus at this class and identifying the sum with the target virtual class remain open. [Graph evaluator](../../AxiomaticGW/GKM/SurfaceLocalizationVertex.lean) · [Doubled-line graph proof](../../AxiomaticGW/GKM/Fixtures/StrictLineGraphVertices.lean)

The full-field genus-two descendant $\langle\tau_3(E)\rangle_{2,E}^T$ on a primitive exceptional curve now has a six-locus certificate. Summing its ten distinct stable genus-two Hodge signatures gives $(x+y)/240$ on $F_1$ and the first exceptional curve of the two-point blowup, and $(y-2x)/240$ on its second exceptional curve. The unchanged producer reproduced all three formulas. The two torus-weight-dependent answers have the same ordinary value zero. They are off-dimension and add no rows to the 5,199-request suite. [Worked query and geometric inputs](../references/ResearchQueries.md#a-genus-two-equivariant-exceptional-descendant)

## 2026-11-26. Genus-two descendants at energy two on the one-point blowup

In the effective basis $(E,F)$, the two classes of energy two are $(0,1)=F$ and $(2,0)=2E$. Each has four singletons and 64 ordered pairs. Lean proves that the 136 complete requests are distinct and that their image equals the independently defined energy-two benchmark. The three new reports were computed with Sage 10.9, admcycles 1.4 and the pinned GKM producer. Lean checks each exact numerator and denominator in both torus variables and its regular ordinary specialization. [Energy-two coverage](../../AxiomaticGW/GKM/Fixtures/F1EnergyTwoCoverage.lean) · [Fiber pairs](../../environments/gkm-f1-fiber-pairs.json) · [Double-exceptional singletons](../../environments/gkm-f1-double-exceptional-one-marking.json) · [Double-exceptional pairs](../../environments/gkm-f1-double-exceptional-pairs.json)

All 68 fiber requests have a unique Lean-checked comparison tying their ordered input to the original mixed reconstruction or marked equation, the full equivariant fraction, and its ordinary value. Of the 64 pairs, 32 use a marked equation. The other 32 reduce to 19 pulled cotangent squares, four first-power products, and nine lower-power ancestors. For $\langle\tau_2(1),\tau_3(1)\rangle_{2,F}$, all eleven terms of the final pulled square vanish. Calibration gives $-3/80$ in both marking orders. For $\langle\tau_3(1),\tau_1(E)\rangle_{2,F}$ the result is $-113/2880$. The geometric theorem uses the original reconstruction inputs. [Complete fiber comparison](../../AxiomaticGW/GKM/Fixtures/F1FiberPairsReplay.lean) · [Interior pair proofs](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1FiberInteriorPairs.lean) · [Offline research examples](../references/ResearchQueries.md)

In class $2E$ the original mixed reconstruction gives $13/3840,0,3/320,0$ at $\tau_4(1),\tau_3(H),\tau_3(E),\tau_2(\mathrm{pt})$, respectively. The partial singleton table now feeds the original string, dilaton and primary-divisor reductions through a theorem valid for any certified partial evaluator. Combining these equations with exceptional point support verifies 46 of the 64 pairs in $2E$. The coefficients $H\cdot 2E=0$, $E\cdot 2E=-2$, and the signed cup correction enter separately. [Singleton reconstruction](../../AxiomaticGW/GKM/Fixtures/F1DoubleExceptionalOneMarkingReplay.lean) · [Partial-table theorem](../../AxiomaticGW/Surfaces/GenusTwoMarkedPairLookup.lean) · [Marked pairs and point support](../../AxiomaticGW/GKM/Fixtures/F1DoubleExceptionalMarkedPairs.lean)

The other 18 point-free pairs in class $2E$ have positive cotangent powers and use the original mixed ancestor reduction. Fifteen pulled squares, two first-power products and five low-power terms determine all 18. The six nonzero terms of the last pulled square sum to $-29/5760$. The final calibrated value of $\langle\tau_2(1),\tau_3(1)\rangle_{2,2E}$ is $27/1280$. Across both classes, each of the 136 mathematical queries has a unique checked comparison. The unions with previously verified rows contain 255 distinct queries on $F_1$ and 714 on the two-point blowup. Together with the complete 48-row plane suite these certify at least 1,017 of the 5,199 specified few-marking requests. The remaining blowup few-marking slices and the full blowup primary benchmarks through energy twelve are open. [Double-exceptional pairs](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1DoubleExceptionalInteriorPairs.lean) · [Energy-two reconstruction](../../AxiomaticGW/GKM/Fixtures/F1EnergyTwoReplay.lean) · [Distinct checked queries](../../AxiomaticGW/GKM/Fixtures/BlowupFewMarkingCoverage.lean)

The GKM calibration comparison now includes 13 nonlinear sewing coefficients at seven full curve classes on the three surfaces. All 273 matrix entries vanish in the exact two-character field. Of these, 48 need a positive-degree splitting to cancel nonzero endpoint terms. The arbitrary-state theorem identifies these finite coefficients of $S(-z)^*S(z)$ under the toric metric and two-point descendant hypotheses. A class-valued geometric realization and an all-orders $R$-matrix with translation remain open. [Geometric sewing theorem](../../AxiomaticGW/GKM/Fixtures/CalibrationSewingGeometry.lean) · [Coefficient conventions and scope](../references/GKMExchange.md)

Validation for this checkpoint passed `lake --no-cache --no-ansi --wfail build AxiomaticGW` (3,026 jobs), `lake --no-cache --no-ansi test` (4,326 jobs), and `lake --no-cache --no-ansi lint`. The full test log has the same 954 distinct file-and-message warnings as the last pushed revision. All 19 research-query tests, 24 neighboring frame and reconstruction tests, and two nonlinear sewing tests passed. Ten public coverage, reconstruction and sewing theorems were audited with `#print axioms` and use only `propext`, `Classical.choice` and `Quot.sound`. A fresh native exploration reproduced the four $2E$ singleton rows byte for byte. The published fiber-pair certificate replays offline and is reproduced byte for byte by the query command. [Standalone fiber-pair proof](../../environments/gkm-research-f1-fiber-pair.lean)

The next energy-two class on the two-point blowup is $E_1+E_2$. Of its 105 ordered queries, 29 already vanish by the proved exceptional point-support rule under its stated geometric hypothesis. The two exceptional edges of the toric fan have disjoint endpoints. Transferring absence of a connected fixed graph to a geometric integral would require a virtual-localization comparison. The existing mixed reconstruction can instead use the exceptional boundary values at the effective subclasses to tackle the remaining four singletons, 40 marked-equation pairs, and 32 interior pairs. [Certified fan](../../AxiomaticGW/GKM/Fixtures/CurveReplay.lean) · [Exceptional boundary](../../AxiomaticGW/Surfaces/GenusTwoBlowupRecursion.lean)

## 2026-11-26. Complete energy-one reconstruction on both blowups

The mathematical benchmark has 48, 656 and 4,495 ordered requests on the three fixed surfaces. Lean derives these counts by separating the effective classes and solving the virtual dimension equation for the last cotangent power. The 292 native energy-one queries exhaust that slice, and distinct indices give distinct full requests. [Benchmark sizes](../../AxiomaticGW/Surfaces/GenusTwoFewMarkingCounts.lean) · [Energy-one coverage](../../AxiomaticGW/GKM/Fixtures/GenusTwoEnergyOneCoverage.lean)

On $F_1$, reconstruction certifies all 52 energy-one specializations against the native localization frame. Two second descendants of the unit on the exceptional give $19/960$. A second unit descendant paired with a first descendant of the exceptional divisor gives $-5/288$ in either order. On the two-point blowup reconstruction verifies all 240 energy-one rows, including both orders of the second unit descendant with each first divisor descendant. For the strict transform of the line these three pairings give $5/288$. Each of the 292 requests has a unique indexed comparison tying the ordered input, reconstructed value, and complete native rational function to one another. Across the complete few-marking suites, taking the union with exceptional point support, the four fiber singletons, the earlier canonical fiber rows, and the plane suite gives at least 48, 147, and 714 distinct checked requests, respectively. Each numerical value acquires its geometric interpretation under the hypotheses of its reconstruction theorem. [Complete energy-one reconstruction](../../AxiomaticGW/GKM/Fixtures/GenusTwoEnergyOneReplay.lean) · [Exact bivariate comparison](../../AxiomaticGW/GKM/Fixtures/GenusTwoEnergyOneEquivariant.lean) · [Native report](../../environments/gkm-genus-two-energy-one.json) · [Geometric interpretation](../../AxiomaticGW/Surfaces/GenusTwoBlowupDescendantReconstruction.lean)

At energy two, all four dimension-compatible fiber singletons on $F_1$ have exact ordinary and equivariant proofs. For $\tau_2(\mathrm{pt})$, the ancestor contributes $7/1440$ and the calibration contributes $-1/1440$, giving $1/240$. The values for $\tau_4(1)$, $\tau_3(H)$, and $\tau_3(E)$ are $-1/120$, $-7/960$, and $-23/2880$. These are four of the 68 ordered few-marking queries in the fiber class. [Original descendant proof](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1FiberOneMarking.lean) · [Native comparison](../../AxiomaticGW/GKM/Fixtures/F1FiberOneMarkingReplay.lean)

The research command also certifies the genus-two plane quartic with thirteen primary point insertions at $27$. On $F_1$ in the plane-line class $E+F$, four primary points give zero and a first exceptional-divisor descendant with three primary points gives zero. The hyperplane and point canonical values also vanish. Incidence support kills every original lower-genus term at the shifted class $2E+F$ and both class-zero divisor columns. All 24 entries of the F₁ energy-three canonical table now pass the original checker. [Plane worked example](../references/ResearchQueries.md#genus-two-plane-quartics-through-thirteen-points) · [Energy-three proof](../../AxiomaticGW/Surfaces/Fixtures/F1PlaneLineL24Replay.lean)

On the last pushed revision, both GitHub runners lost contact and neither job supplied a failing Lean command. Locally, that revision's library linter reported 216 findings. Regenerating the coefficient tables and graph comparison statements, updating their consumers, and documenting three declarations removed all 216. The warning-fatal default library build and `lake lint` pass in the research checkout. After integrating the 292-row suite and four fiber singletons, `lake --no-cache --no-ansi test` passed all 4,280 jobs. Every file and warning-message pair in this test log was already present in the saved test log for the pushed baseline. The final `python3 -B scripts/test_gw_query.py -v` run passed all 16 tests, including the fiber singletons and rejection of a changed torus-dependent numerator with the same ordinary specialization. Serial proof replay removes a fixed memory ceiling that intermittently interrupted the strict-line point certificate. The retained Hodge source and witness data are byte-identical.

## 2026-11-25. Exceptional descendants, class specialization and researcher queries

The [F₁ table](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1FiberTable.lean) closes all sixteen canonical states through energy two. The [single-marking comparison](../../AxiomaticGW/GKM/Fixtures/GenusTwoOneMarkingReplay.lean) checks all 17 line and exceptional queries against the original descendant evaluators. On a primitive exceptional curve the own-divisor descendant is −1/240 and the unit descendant is 13/2880. On the two-point blowup the opposite-divisor descendant vanishes. These results include the signed calibration terms. The [strict-line follow-up](../../AxiomaticGW/GKM/Fixtures/BlowupTwoLineOneMarkingReplay.lean) gives 13/2880 for the unit and 1/240 for each divisor. The full shifted L24 sum on that line is $7/2880$. It cancels the degree-zero term, so the hyperplane canonical value and the other four canonical values vanish. The point singleton has value zero. The 20-state table through energy one is accepted by the original checker. [Absolute L24 proof and table](../../AxiomaticGW/Surfaces/Fixtures/BlowupTwoLineL24/Assembly.lean)

The [canonical boundary set](../../AxiomaticGW/Surfaces/GenusTwoBlowupBoundaryBenchmarks.lean) has 48 unique plane-degree-zero requests on F₁ and 450 on the two-point blowup through energy twelve. Each has reconstructed value zero. A [separate few-marking certificate](../../AxiomaticGW/Surfaces/Fixtures/GenusTwoExceptionalFewMarkings.lean) checks 106 and 514 explicit requests respectively against the existing manifest. Its conditional geometric theorem uses the vanishing of the point pullback on the exceptional image. These counts describe intersecting benchmark families. For the 540 components of the saved [degree-zero class packet](../../AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroStrataSpecialization.lean), Lean proves a unique ordinary representative in free rational strata, with multipliers 9, 8 and 7 on the three surfaces. Its identification with a geometric CohFT class remains open.

Lean checks 76 ordered two-marked localization comparisons by the string and dilaton equations. These give 16 cases on F₁, 40 exceptional cases on the two-point blowup and 20 on its strict line. Forty are nonzero, and twelve of the zero rows already belong to the exceptional point-support suite. The dilaton pair with the exceptional divisor on its own curve is −1/80. On the strict line the pair with the hyperplane is 1/80. The arithmetic result uses the certified singleton, while its identification with the original evaluator and geometric intersection uses the existing reconstruction hypotheses. [Two-marking proof](../../AxiomaticGW/GKM/Fixtures/GenusTwoUnitPairReplay.lean) · [Geometric theorem](../../AxiomaticGW/Surfaces/GenusTwoBlowupUnitPairs.lean)

The divisor equation gives 112 exact two-marked localization comparisons for the 112 held requests. The plane line provides a nonzero divisor-square correction, $\langle H,\tau_4(H)\rangle_{2,H}=-1/960-1/240=-1/192$. Closing the strict-line scalar settles the twelve divisor corrections that previously depended on it. The two-positive-divisor formula gives 31 further ordered comparisons, twelve nonzero, including $1/144$ for two first descendants of the exceptional divisor on its own curve. The certified plane frame, exceptional point support, singletons, canonical, unit, divisor and positive-divisor frames already cover at least 48 of 48 plane requests, 138 of 656 F₁ requests and 688 of 4,495 two-point blowup requests with duplicates removed. [Completed strict-line replay](../../AxiomaticGW/GKM/Fixtures/BlowupTwoLineCompletedReplay.lean) · [Positive-divisor replay](../../AxiomaticGW/GKM/Fixtures/GenusTwoPositivePairReplay.lean) The geometric hypotheses are those of each individual result. [Divisor-pair replay](../../AxiomaticGW/GKM/Fixtures/GenusTwoDivisorPairReplay.lean) · [Fixed manifest](../../environments/genus-two-few-markings-requests.json)

The full degree-one-in-energy few-marking localization run produced 52 ordered requests on F₁ and 240 on the two-point blowup, split equally between its three primitive curve classes. Their native report has 114 nonzero ordinary values. Lean binds 235 singleton, marked-equation, and primary-point rows to their exact rational answers. The other 57 requests are the independent two-positive-power frame, of which 31 divisor pairs have complete original reconstruction proofs. Under the original geometric inputs, a bound row formally determines both the original descendant evaluator and the geometric GW value. [Held primitive frame](../../environments/gkm-genus-two-energy-one.json) · [Exact row bindings](../../AxiomaticGW/GKM/Fixtures/GenusTwoEnergyOneReductions.lean) · [Interpretation](../../AxiomaticGW/Surfaces/GenusTwoBlowupUnitPairs.lean)

For the degree-zero packet, the original codimension-one 3-spin relation gives the discriminant boundary representative. A second certificate checks 14 original codimension-two rows, 12 with nonzero weights, against 17 graph columns on $\overline{\mathcal M}_{2,1}$. The 16-term class is exactly one two-hundredth of the boundary-square packet in their quotient. With the participating row vanishing, the named boundary realization laws and the loop, mixed and separating Gysin formulas, its ordinary realization on the surface with $r$ blowups is $(9-r)(\delta_{\mathrm{irr}}+2\delta_1)^2/200$. Identifying the imported packet with the stabilized GW class remains open. [Picard relation](../../AxiomaticGW/GKM/Fixtures/HodgeGenusTwoPicard.lean) · [Original-row certificate](../../AxiomaticGW/GKM/Fixtures/HodgeBoundarySquareCertificate.lean) · [Boundary realization](../../AxiomaticGW/GKM/Fixtures/HodgeBoundarySquareRealization.lean)

There is also a positive-degree class comparison on the plane. In degree one, the chosen point and hyperplane lifts select one of 48 four-marked localization graphs. Stabilizing its bridge gives the boundary $12|34$ with ordinary coefficient one. A fifth unit marking selects two of 96 graphs. Their flag cotangent terms have opposite poles, which cancel after the original four-point relations identify their common stratum. Lean checks this finite unit comparison and the indicated separating restriction under the listed graph-realization and rational-tail laws. Surface-wide stabilization and semisimple CohFT gluing remain open. [Class and unit comparison](../../AxiomaticGW/GKM/Fixtures/PlaneLineBoundaryClass.lean) · [Separating restriction](../../AxiomaticGW/GKM/Fixtures/PlaneLineBoundarySplitting.lean)

On the primitive exceptional curves of both blowups the corresponding four-marked class has coefficient $-1$ with the chosen lifts. The fifth-unit pullback and the specified separating restriction are verified on each of the three exceptional classes. The first-order quantum product calculation checks 155 native symmetric triples for all six effective generators and 530 ordered ordinary-specialization comparisons. The first-order equivariant algebras now have complete orthogonal primitive projectors on all three surfaces. For the blowups the proof uses all 503 incoming equivariant entries, the five separate effective directions, the inverse metric and explicit normalization over a coefficient extension. There are three projectors on the plane, four on F₁ and five on the two-point blowup. The higher-order quantum products and the class-valued semisimple reconstruction remain open. [Exceptional boundary classes](../../AxiomaticGW/GKM/Fixtures/ExceptionalBoundaryClass.lean) · [Small quantum products](../../AxiomaticGW/GKM/Fixtures/SmallQuantumGeneratorComparison.lean) · [Plane idempotents](../../AxiomaticGW/GKM/Fixtures/PlaneQuantumIdempotents.lean) · [Blowup idempotents](../../AxiomaticGW/GKM/Fixtures/BlowupQuantumIdempotents.lean)

The [research workflow](../references/ResearchQueries.md) gives a command-line and Sage entry point. For the genus-one F₁ request with insertions $\tau_1(E),E,E$ at class $E$, direct reconstruction and the pinned producer both give 1/12. Lean proves the regular ordinary specialization of the supplied function and exports a theorem giving the requested geometric GW value under the original reconstruction hypotheses. The two worked certificates replayed in a fresh project checkout with locally pinned dependencies. In a distinct calculation, Sage finds row weights 1/72 and −1/72 for the difference between the separating genus-two graphs decorated by kappa and branch psi. Lean proves formal span membership and vanishing under any linear evaluation killing the seven supplied rows.

The pinned native 17-case GKM exploration reproduced the held report byte for byte. Regenerating the admcycles smoke report reproduced the full graph and rational row coordinates, and the resulting research relation certificate was byte-identical to the certificate from the saved frame. The [research guide](../references/ResearchQueries.md) gives exact regeneration and replay commands. Numerical regression commands include the following.

```sh
python3 -B -m unittest discover -s scripts -p test_gw_query.py -v
python3 -B -m unittest discover -s scripts -p test_admcycles_span.py -v
python3 -B -m unittest discover -s scripts -p test_gkm_genus_two_one_marking.py -v
python3 -B -m unittest discover -s scripts -p test_gkm_f1_fiber_remaining.py -v
python3 -B -m unittest discover -s scripts -p 'test_gkm_genus_two_*pairs.py' -v
lake build AxiomaticGWTest.GKM.GenusTwoPairComparisons AxiomaticGWTest.GKM.HodgeBoundarySquareCertificate
python3 -B scripts/export_exceptional_few_markings.py --check
lake build AxiomaticGWTest.GKM.GenusTwoOneMarkingReplay AxiomaticGWTest.Surfaces.GenusTwoExceptionalFewMarkings
```

## 2026-10-05: First F₁ fiber descendant and the complete conditional raw square

The [first fiber checkpoint](../../environments/reconstruction-first-f1-fiber-h-validation.json) verifies 37 new repository targets and 161 exact standard-only audits. The [full query theorem](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1FiberHValue.lean) proves the reconstructed genus-two value of `tau₁(H), pt, pt` at target `F=(0,1)` is zero. It uses the preceding complete `1/288` contraction, retains the shifted L24 source `E+F=(1,1)`, and checks all 54 original contributions to the remaining H₀/K₀ coefficients. The [incoming GKM replay](../../AxiomaticGW/GKM/Fixtures/BlowupF1FiberHReplay.lean) matches the same full ordered request and ordinary value; its configured regression preserves the dimension condition and target-versus-shifted-source distinction. Nine installed tests pass, including rejection by Lean of a changed value, full class and state/power pairing. This numerical comparison shares conventions and admcycles foundations; it does not prove localization or construct a CohFT.

The [complete raw-square theorem](../../AxiomaticGW/GKM/Fixtures/HodgeFullSquare.lean) now assembles all 28 original occurrences and derives the square of the actual five-term degree-one image, then identifies the degree-two `(0,2)` image with one half of that square. The three fixed-surface assembly consumers retain their signed raw unit terms. New `LoopSeparatingGysin.MixedGysinCompatible` and `SeparatingSquareGysin.SelfGysinCompatible` hypotheses are universal geometric map identities; the product statements follow from these and prior explicit realization/forgetful/psi inputs. No geometric instance, lambda/GRR identification or class-valued semisimple CohFT is supplied.

The record preserves complete logs, failed drafts, 1,547 source pins and successful final 182-root configured checks. Its three new source-bound style warnings are distinguished from inherited warnings. The configured wrapper's incorrect stdout postcondition failed after both Lake commands exited successfully; an independent postcheck verified the frozen sources, with no rerun. The earlier default build is inherited and lint remains unresolved. The next numerical unit is the remaining P/N/K fiber states and the complete F₁ energy-two table; all fixed energy-twelve applications and geometric GKM requirements remain open.

## 2026-10-05: Complete original F₁ contraction and conditional loop-square realization

The [full F₁ constant checkpoint](../../environments/reconstruction-full-f1-constant-validation.json) verifies 131 actual repository targets and 3,479 exact standard-only audits. The final 61 representative values and seven interval adapters close all original indices 0–814, retaining the 94 zero coordinates, 27 genus-guarded rows, 280 representative rows and 414 coefficient-ratio transfers. The [checked complete table](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1WeightedAssembly/CheckedTable.lean) proves every original weighted term equals its claimed value, then derives the complete guarded contraction `1/288`. This is now a contraction theorem, beyond the earlier independent candidate-sum calculation.

The [scalar consumer](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1FiberHConstant.lean) fixes target `F=(0,1)` and shifted source `E+F=(1,1)`: its row constant is `1/288`, the target coefficient is `−1`, and the shifted-source coefficient is `0`. Other genus-two terms remain in the row; no complete fiber invariant is asserted. The [loop-square consumer](../../AxiomaticGW/GKM/Fixtures/HodgeLoopSquare.lean) identifies exactly packet positions 3, 4, 18, 21 and 23 with the square of the actual weighted raw loop class, conditionally on the new explicit `LoopSquareGysin.SelfGysinCompatible` identity and the prior geometric/realization inputs. That identity quantifies every source class; no geometric model satisfying it, other boundary products, complete Hodge identity or class-valued semisimple CohFT input is constructed.

The record preserves all actual commands/logs, 1,510 source pins, the successful final 178-root configured tests and the failed proof/supervision history. It explicitly retains the old generic audit's stale `full815_contraction_accepted:false` field and derives its updated scope from the exact checked public types and audits. Numerical phases used the sampled 3 GiB cap; the Hodge phase used 2 GiB. The 233 additional distinct source-bound style-warning blocks include the new loop-square line-length warning. The unchanged 449-source default-build evidence is inherited; lint remains unresolved. Later fiber reductions are outside this fixed checkpoint.

## 2026-10-05: Original F₁ intervals through 607 and conditional raw kappa-square realization

The [148-target checkpoint](../../environments/reconstruction-checkpoint148-validation.json) records 80 additional canonical representative values, five interval adapters and the finite corolla operation with its realization interface, through 4,330 exact standard-only audits. The new intervals bind every original weighted index 448–607 using 72 direct-provider occurrences and 88 coefficient-ratio transfers. With the preceding blocks, indices 0–607 are checked; 207 positions remain outside the assembly accepted by this checkpoint. Later tail batches and the complete-table proof are excluded from this record.

The [finite corolla operation](../../AxiomaticGW/Tautological/CorollaForgetful.lean) preserves the binomial multiplicities of repeated positive kappa factors. The new explicit hypothesis [CorollaForgetfulCompatible](../../AxiomaticGW/Tautological/CorollaForgetfulRealization.lean) requires realization to commute with that constructed operation for every exponent vector and positive forgotten index. Its empty-vector case recovers generator compatibility; its single-factor case, together with the previous primitive geometry, derives the two-kappa product. The [actual rawGraph21 theorem](../../AxiomaticGW/GKM/Fixtures/HodgeKappaCorolla.lean) therefore identifies its realized class with kappa one squared conditionally. A geometric model of the compatibility, boundary/excess comparisons, complete Hodge identification and class-valued semisimple CohFT input remain open.

The record checks 1,138 source pins and preserves the 175-root intermediate and 176-root final configured test runs, all complete logs, and four failed realization prototypes. The source helper's explicit `DecidableEq` parameter supplies the representation needed by `Pi.single`; the classical caller supplies it, with no new geometric restriction. The 256 additional distinct style-warning blocks include two new long-line warnings in the realization production and test sources. The earlier default build and unchanged 449-source closure are inherited without a rerun; the previous lint failure remains unresolved.

## 2026-10-05: Original F₁ intervals through 447 and the conditional kappa-square formula

The [96-target checkpoint](../../environments/reconstruction-checkpoint96-validation.json) verifies 48 additional canonical representative values, [four interval adapters](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1WeightedAssembly/Block13.lean), and the conditional kappa-square development through 2,671 exact standard-only audits. The adapters bind every original weighted index 320–447 using 44 direct-provider occurrences and 84 coefficient-ratio transfers. Together with the earlier blocks they cover indices 0–447; 367 positions still require assembly before the separate candidate sum 1/288 becomes a full contraction theorem.

The [universal forgetful-square laws](../../AxiomaticGW/Tautological/ForgetfulKappa.lean) make two new geometric hypotheses explicit: `ForgetfulSquareCompatibility.base_change` and `contract_tail`, both universal in their source classes. They derive kappa pullback and the corrected two-index pushforward formula. The [actual consumer](../../AxiomaticGW/GKM/Fixtures/HodgeKappaSquare.lean) applies this to the square of the realized degree-one `rawGraph2`; `rawGraph21` is separately bound only to its two-kappa-one decoration. No equality with the realization of `rawGraph21`, geometric model of the hypotheses, or complete Hodge identity is established.

Configured tests passed against a 174-root snapshot captured before the run and rechecked afterwards. The record verifies 1,073 pinned sources, complete lossless logs, and the initial audit-launcher path typo that failed before Lean. The unchanged 449-source default closure and its build result are inherited from the preceding checkpoint; no new default build is claimed. The 171 additional distinct style-warning blocks are bound to their sources and retained, and the earlier lint failure remains unresolved. Later numerical sources and adapters are outside this fixed run.

## 2026-10-05: Original F₁ intervals through 319 and conditional kappa products

The [next repository checkpoint](../../environments/reconstruction-checkpoint130-validation.json) verifies 130 targeted builds and 3,629 exact standard-only axiom audits. It adds 67 canonical representative values, six numerical transfers, and [five interval adapters](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1WeightedAssembly/Block09.lean) for original indices 160–319. Together with the earlier adapters, every original weighted row 0–319 is bound to the same frozen candidate table. The new intervals use 69 direct-provider occurrences and 91 original coefficient-ratio transfers; they do not unfold the component evaluator. The remaining 495 positions still require assembly before the candidate arithmetic sum 1/288 can establish the full contraction.

The [loop-kappa](../../AxiomaticGW/GKM/Fixtures/HodgeKappaLoopProduct.lean) and [separating-kappa](../../AxiomaticGW/GKM/Fixtures/HodgeKappaSeparatingProduct.lean) consumers derive the relevant products from new, explicit covariant forget/glue composition hypotheses, universal in their source classes. They bind actual degree-two positions 10–14 to the corresponding kappa-decorated boundary expressions. These are conditional theorems with no new Lean axioms; the geometric hypotheses are not instantiated here. Kappa-square interpretation, geometric boundary/excess comparisons, complete Hodge identification and actual class-valued semisimple CohFT input remain open for this checkpoint.

Final configured tests passed for 173 recorded test roots, and the default build passed at 3,018 jobs. The record separately preserves the earlier 172-root test run, all complete command logs, the initial metadata-staging failure, and an honestly reconstructed correction to that earlier source snapshot. Its 1,111-source union and exact log hashes are checked offline; shared lossless log fragments keep the existing decoded-size bound. Source-bound style warnings remain recorded, and the earlier lint failure was not rerun. Later sources and tests are outside this fixed checkpoint.

## 2026-10-05: Checked numerical intervals and the external-psi portion

The [consolidated repository checkpoint](../../environments/research-reconstruction-checkpoint-validation.json) records 39 targeted builds and 817 exact standard-only axiom audits. The first 35 targets check complete original F₁ representatives 131–139 and 170–173, twelve numerical transfers, the external-psi consumer, the frozen 815-entry rational table, and the actual interval 96–127. Four later production adapters complete [blocks 00–04](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1WeightedAssembly/Block04.lean), binding every original weighted row 0–159 to that same table. Block 03 sums to −1/585. The [candidate table](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1CandidateWeightedTable.lean) sums to 1/288, but 655 original positions remain unassembled; its arithmetic theorem does not establish the full contraction.

The [external-psi result](../../AxiomaticGW/GKM/Fixtures/HodgeExternalPsi.lean) binds five exact degree-two packet occurrences to the existing psi operation on the five degree-one columns. It retains the single square coefficient, doubles the four mixed coefficients, and leaves the other 23 occurrences explicit. Its realization uses the existing primitive psi compatibility; no boundary/kappa product or geometric Hodge/CohFT identification follows.

Configured test preflight and `lake --no-ansi --no-cache test` passed between the 35-target phase and the four later adapters, with 1,826 replayed warnings in each log. The record includes full logs, canonical configuration/source pins, a source-bound review of style warnings, and the initial monitor permission failure before any target build. The earlier 216 lint failures remain open and lint was not rerun. No later full-project acceptance is inferred from the four adapter builds.

## 2026-10-05: Constructed gluing images and an equivalent order for root evaluation

The [gluing consumer](../../AxiomaticGW/GKM/Fixtures/LoopSquareGluing.lean) constructs the double loop by two ordered nonseparating gluings and the parallel graph by separating gluing, explicit label transport and nonseparating gluing. Both ordered branch placements and the separately decoded packet occurrence are retained. Existing primitive compatibility laws evaluate the constructed five-slot packet expression, keeping the fundamental-normalization input explicit. The [actual record](../../environments/gkm-loop-square-gluing-validation.json) covers two warning-free targets, sixteen standard-only audits and 69 source files. This is not a geometric boundary-square or excess/pull-push theorem.

The [root evaluation helper](../../AxiomaticGW/Surfaces/ScalarPointRootOrder.lean) checks the left child for zero first and proves equality with the existing separating summand for arbitrary component data. Neither evaluator's states, signs, curve splits nor point allocations change. The [regressions](../../AxiomaticGWTest/Surfaces/ScalarPointRootOrder.lean) check three actual zero slots and a positive hyperplane and negative exceptional slot. Its [actual record](../../environments/scalar-point-root-order-validation.json) covers two builds and six standard-only audits; the generic build is warning-free and the consumer replays 1,788 dependency warnings from the frozen catalogue.

The RootOrder record retains the failed drafts and failed `--memory=2048` audit. The successful audit uses `--memory=3072` with a sampled 3 GiB RSS cap; the two build runs used simple wrappers, whose child-usage reports are not sampled RSS evidence. Its 505-source closure is explicitly a post-validation snapshot. Both records have a [portable checker](../../scripts/check_gluing_root_order_records.py), with ten targeted corruption/portability controls. No complete new row, full Fin 815 constant or geometric CohFT comparison follows.

## 2026-10-05: All 414 structural transfers accepted in the repository

Seventeen bounded [transfer modules](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1RootRelabelTransfers/Batch00.lean) now prove every source-derived transfer among the 694 evaluated original rows and their 280 structural classes. Each proof retains the identical decorated gluing core, actual transported HEEE assignment and original rational coefficient ratio. The six earlier pilots are included in the 414. No backend value is evaluated and no extra geometric or equivariance hypothesis is introduced.

All seventeen actual targets pass in a combined 302.666 seconds. The exact 2,275-name public audit passes in 2.223 seconds with standard Lean axioms only. The [portable record](../../environments/genus-two-f1-structural-transfers-validation.json) preserves the 301-source lexical import closure, complete commands and logs, and the earlier isolated acceptance. All 34 build/prerequisite logs contain the exact 51 frozen H121 warning blocks; one log emits them in a different order, with no new warning.

`python3 scripts/check_f1_actual_transfers_record.py` reuses the existing bounded-decompression and strict-audit utilities to verify the embedded evidence without temporary files or compiled artifacts. Seven targeted corruption/portability controls pass. These are structural equalities: numerical values still require their accepted representative proofs, and the full original Fin 815 assembly and unchanged research application suites remain separate gates. This record supplies no geometric CohFT identification.

## 2026-10-05: Actual F₁ component-cache replay and three further original rows

The [actual cache validation](../../environments/genus-two-f1-actual-cache-validation.json) now records 227 successful dependency-ordered repository builds for the complete 722-component cache and its selected numerical consumers, followed by eight repository builds for original rows 123–125. The exact 2,332-name and 173-name public audits pass using standard Lean axioms only. Its 582-source lexical import closure includes the previously accepted left-zero helper and row-123 dimension-zero slot. This completes the separate repository replay left open by the earlier isolated-cache checkpoint.

The checked weighted values are [row 123](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1RootRepresentative0123Checked.lean) = 161/38880, [row 124](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1RootRepresentative0124SecondChecked.lean) = −745/50544 and [row 125](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1RootRepresentative0125.lean) = 0. Each proof accounts for all 37 original root slots. The selected earlier numerical consumers and six structural transfers remain tied to their original relation coefficients and cached components; these six transfers are already part of the larger 414-transfer frame.

The record preserves the first run's 21 successful targets and subsequent sampled-RSS failure, followed by the explicitly approved 3 GiB continuation and eight later builds. Complete commands, logs and earlier plans are embedded losslessly with bounded decompression and SHA checks. The repeated warnings are classified as 1,805 distinct source-bound heartbeat-option, unscoped-option and line-length blocks; no warning-free build is claimed. `python3 scripts/check_f1_actual_numeric_record.py` verifies the installed evidence without temporary files, compiled artifacts or Lean, and [all twenty corruption controls](../../scripts/test_f1_actual_numeric_record.py) pass.

This record accepts the named cache and original-row proofs. It does not accept all 414 standalone transfer batches, the full 815-term F₁ contraction, the remaining fixed application suites or any geometric semisimple CohFT comparison. The finite Hodge refinement classification and its unresolved geometric pull-push interpretation are unchanged.

## 2026-10-05: Complete finite refinements of the marked genus-two raw loop

The [refinement classification](../../AxiomaticGW/GKM/Fixtures/LoopSquareRefinements.lean) now proves that every generic ordered pair of contractions to the actual marked raw loop has a source isomorphic to the loop, double loop or parallel-edge graph. Genericity retains all source edges; each contraction checks connectedness and the arithmetic genus of its entire contracted complement. The vertex map, injected flags, node involution and old marking are explicit. The three finite automorphism actions have respectively 2, 1 and 4 orbits, with trivial stabilizers on the accepted pairs. Completeness follows from the existing graph enumerator and derived size bounds, rather than a supplied list of representatives.

The [packet binding](../../AxiomaticGW/GKM/Fixtures/LoopSquarePacketBinding.lean) preserves original positions 3, 4, 18, 21 and 23. Their sum equals `(1/24)^2` times the constructed refinement expression: twice the signed node expression, plus the double-loop stratum and four times the parallel-edge stratum. Both original parallel presentations and their coefficients are retained. The difficult three-vertex/two-edge enumeration case is proved by the contradiction between global genus two and contracted-fibre genus one; none of its hypotheses or conclusions was weakened.

The [actual validation record](../../environments/gkm-loop-square-refinements-validation.json) embeds sixteen successful repository builds, the exact 48-name standard-only axiom audit and the 68-source lexical import closure. There are no warnings. The [regressions](../../AxiomaticGWTest/GKM/LoopSquareRefinements.lean) check shared versus distinct retained edges, exclusion of a loop plus bridge and an edgeless corolla, and the actual packet positions. The isolated acceptance preserves five earlier failed probes separately.

This is a complete finite graph classification and a free-strata identity. The geometric fibre-product components and their excess/pull-push comparison have not been constructed. Establishing that comparison is the next step before claiming a boundary square, Hodge product or class-valued GKM CohFT.

## 2026-10-05: The signed node expression and its two actual packet occurrences

The [nonseparating node construction](../../AxiomaticGW/Tautological/NonseparatingNodeNormal.lean) applies the two existing leg-psi operations at the ordered future node markings, negates their sum and performs raw nonseparating gluing. It raises codimension by two. The existing psi and gluing compatibility laws derive its realized image as the pushforward of the source class times the negative sum of the two node cotangent classes.

The [fixed packet consumer](../../AxiomaticGW/GKM/Fixtures/HodgeNodeNormal.lean) binds original positions 3 and 4 of the 28-occurrence degree-two expression to those two ordered branches, preserving both coefficients −1/288. Their sum equals 1/288 times the constructed node expression. The concrete realized corolla formula also retains its explicit fundamental-normalization input. This proves neither a boundary self-intersection formula nor the complete common-refinement product, and does not identify a geometric Hodge or CohFT class.

All three actual repository targets and all seventeen public axiom checks pass with standard Lean axioms and no warnings. The [node validation record](../../environments/gkm-hodge-node-normal-validation.json) embeds the complete actual logs, the combined 288-name audit, configuration pins and the exact 53-source import closure. It preserves the earlier isolated proof history separately. The next geometric step is the full pull-push/common-refinement formula, with both shared-edge and disjoint-edge contributions and their multiplicities.

## 2026-10-05: Every original F₁ coefficient-zero and genus-guarded row

Six bounded fixtures prove all 94 actual zero relation coordinates and all 27 nonzero coordinates removed by the existing genus guard. Applying the existing root-assembly zero lemmas proves `originalWeighted j = 0` for every original index 0 through 120, retaining the full Fin 815 frame. These are guarded weighted rows; no vanishing of an unguarded geometric invariant is asserted. The source-coverage partition remains 3 accepted representatives, 277 remaining representatives, 414 structural-transfer targets, 94 zero coordinates and 27 nonzero guarded rows; the partition itself does not prove the pending representative values or transfers.

The [generic left-zero contraction lemma](../../AxiomaticGW/Surfaces/ScalarPointRootZero.lean) also proves [one original row-123 slot](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1Root123DimensionZero.lean) zero from the left component's dimension guard, without evaluating the unchanged right subtree. The [actual zero-row record](../../environments/genus-two-f1-root-zero-rows-validation.json) covers eight repository builds and 271 exact standard-only audits: 269 for the six prefix fixtures, one generic lemma and this one slot. Seven fixture builds replay exactly the 51 frozen H121 warning blocks already present in the configured test run; the generic helper is warning-free. All twelve installed exporter tests pass.

Both records can be checked without temporary logs, compiled artifacts or Lean using `python3 scripts/check_node_zero_records.py`; [regression tests](../../scripts/test_node_zero_records.py) exercise the canonical configuration/source paths, exact lexical imports and dependency order, audit coverage, inherited warnings and scope boundaries. No complete value for row 123, 124 or 125, full F₁ constant, additional benchmark or geometric GKM gate is accepted by these records.

## 2026-10-05: Default build and configured tests pass; lint remains open

The [current reconstruction validation record](../../environments/genus-two-blowup-reconstruction-validation.json) records successful `lake build` runs at 3,013 jobs and, after five public exports, 3,018 jobs. The added exports are the raw Hodge assembly, degree-two raw relation, five-term degree-one realization, scalar relabelling helper and kappa realization. The final umbrella build passed in 3.552 seconds without warnings. This supersedes the earlier pending-export checkpoints without changing their historical evidence or any pinned mathematical source.

The configured `lake test` driver passed in 311.720 seconds with 52 inherited warnings: the existing private-module warning and the frozen H121 heartbeat-option/line-length warnings. `lake lint` failed with 216 findings: 153 `defsWithUnderscore` reports on serialized declaration names, 60 `synTaut` reports on literal identity witnesses and three `docBlame` reports. These findings remain an open maintenance gate; no linter was disabled and no mathematical proof was changed by this checkpoint. The record retains exact commands, complete logs, source pins and the earlier rejected metadata-only lint attempt.

These commands validate their configured default and test targets. They do not validate every isolated or newly copied fixture, complete the 722-component cache's separate repository replay, certify the remaining blowup numerical suites, or construct an actual class-valued semisimple GKM CohFT. The fixed applications, bounds and geometric input obligations are unchanged.

## 2026-10-05: Exact external-label reuse for original F₁ rows

The [scalar relabelling helper](../../AxiomaticGW/Surfaces/ScalarPointRelabel.lean) proves equality when the actual transported insertion assignments agree, for arbitrary component data, curve class and added markings. The [fixed consumer](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1RootRelabel.lean) binds original rows 122, 141 and 156 to the same decorated gluing core and the actual HEEE assignment. Their contractions agree; their original relation coefficients remain distinct, giving weighted ratio 7054/12777 from row 122 to either row 141 or row 156. This uses no evaluated component backend, additional geometric hypothesis or assumed numerical coincidence.

The [three-file repository validation](../../environments/gkm-f1-root-relabel-validation.json) records the production build (6.723 seconds), [consumer build](../../AxiomaticGWTest/Surfaces/BlowupF1RootRelabel.lean) (3.284 seconds) and all fourteen exact public axiom audits (2.750 seconds), with standard Lean axioms only. Only inherited frozen H121 warnings were replayed. Separate numerical consumers and cache prerequisites have been copied with their accepted source bytes, but their actual repository validation remains pending at this checkpoint. The 414-transfer extension is also a separate staged package. Neither structural reuse nor a native candidate total completes the original 815-row F₁ constant or its fixed numerical suite.

## 2026-10-05: First F₁ root assembly validated in the repository

Four byte-identical accepted fixtures now have actual repository validation: the 48-component H121 cache replay, the complete 32-part original term-121 replay, the generic assembly over the original Fin 815 frame, and one dimension-zero slot at original term 122. The weighted term 121 remains exactly 1/2160. The zero-slot theorem holds for every certified residual cache and follows from the left elliptic component's dimension guard, before evaluating its right subtree. No curve class, coefficient, root slot, evaluator, geometric assumption or public API changed.

The [validation record](../../environments/genus-two-f1-root-zero-validation.json) preserves all 54 dependency-ordered repository build outcomes and the 156 exact axiom audits. Fifty-one targets were rebuilt with a positively observed Lean process; three were already current. The maximum sampled per-Lean RSS was 1,639,366,656 bytes, under the unchanged 2 GiB RSS limit, with at most one observed Lean child in this build lane. The actual repository audit passed in 1.876 seconds with only standard Lean axioms. Sampling is a development resource observation, not a controlled benchmark. The frozen heartbeat-option and line-length style warnings are source-bound and recorded separately. Earlier partial/failed runs remain visible in the evidence.

The portable record checker validates the 284-source closure, each exact source import list, the current lakefile/manifest/toolchain hashes, exact build commands, warning locations, audit coverage and acceptance boundaries without reading the original temporary logs or compiled artifacts. `python3 scripts/check_f1_root_zero_record.py environments/genus-two-f1-root-zero-validation.json` passes. `python3 scripts/test_f1_root_zero_record.py --checker scripts/check_f1_root_zero_record.py --record environments/genus-two-f1-root-zero-validation.json` passes all seventeen regression and corruption tests, including an altered import list that preserves all source hashes and graph reachability, configuration drift, missing/substituted build coverage, unobserved rebuild claims, hidden failed history and foreign axioms. This record does not accept the separate full 722-component cache's actual rebuild, the complete 815-term numerical constant, a geometric GW value or the full-project build. The separate 37-slot row122 acceptance remains separately recorded.

The next priority is exact structural reuse and full root-slot replay for the remaining original F₁ terms, followed by the unchanged numerical suites.

## 2026-10-05: Kappa pushforward and all five actual degree-one source terms

The [kappa realization bridge](../../AxiomaticGW/Tautological/KappaRealization.lean) introduces the positive kappa corolla and its extra-marking psi source. A named generator-level compatibility proposition compares their realized images through the existing forgetful pushforward. Together with the existing upstairs psi law and fundamental normalization, it derives the image as `PsiClasses.kappa`; the compatibility law remains explicit geometric input. No axiom, global instance, simp rule or change to an existing definition was introduced.

The [degree-one source realization](../../AxiomaticGW/GKM/Fixtures/HodgeDegreeOneRealization.lean) checks the five actual decoded columns and derives their complete image: −ψ/12 + κ₁/12 plus the raw nonseparating and both ordered separating contributions, each with coefficient 1/24. The finite proof normalizes the singleton kappa decoration through the existing bounded-vector theorem before graph-isomorphism checking. It retains the original marking, the forgotten label `none`, the upstairs power two, and all raw coefficients. It does not identify this expression with a Hodge or GW class, assert a product law, or construct a semisimple CohFT.

`lake build AxiomaticGW.GKM.Fixtures.HodgeDegreeOneRealization` passes in 3.807 seconds; `lake build AxiomaticGWTest.Tautological.KappaRealization` passes in 2.413 seconds. The fourteen actual public axiom checks pass in 2.005 seconds with standard Lean axioms only. The [regressions](../../AxiomaticGWTest/Tautological/KappaRealization.lean) distinguish kappa from equal-degree external psi, distinguish the forgotten marking from an old marking, and include an empty original marking set. The [validation record](../../environments/gkm-hodge-degree-one-realization-validation.json) preserves exact sources, commands, audit source/output, and the three earlier local proof failures. Final targeted validation reports no warnings. Umbrella export and the concurrent full-project build remain pending.

The next geometric obligation is to justify the named kappa compatibility in a realization and derive the boundary/product rules needed for the actual finite square. Hodge/GRR identification, virtual Euler/stabilization, ordinary comparison, and genuine class-valued GKM CohFT data remain separate requirements. No milestone or fixed application suite is marked complete by this conditional bridge.

## 2026-10-05: One exact degree-two raw class for all three complete candidates

The [degree-two raw replay](../../AxiomaticGW/GKM/Fixtures/HodgeDegreeTwoRawRelation.lean) proves `raw11Degree2 = (2 : ℚ) • raw02Degree2` directly in the free strata module. All 28 and 16 original occurrences, their exact rational coefficients and every decoration are retained. Thirty-one finite decorated-graph checks collect them into the sixteen actual `(0,2)` source columns. This is an identity of these frozen raw expressions; it is not a geometric Mumford theorem or a proof that a raw expression realizes to a Hodge class.

For Q = x² − xy + y², U = A(raw₀₀) and W = A(raw₀₂), the complete candidates are now Q·U + 9W for P², 8W for F₁, and −Q·U + 7W for Bl₂P². The proofs use the previously accepted complete assembly identities and rational linearity alone, with no `D`, `hfund` or product hypothesis. The actual two-target build passes in 12.334 seconds without warnings; all 46 actual public axiom checks pass in 3.819 seconds using only standard Lean axioms, and all eleven integrated Python tests pass in 0.383 seconds (0.268 seconds reported by unittest). The [validation record](../../environments/gkm-hodge-degree-two-validation.json) preserves complete source bindings, exact commands/logs, corruption controls, the earlier consumer proof failure and its narrowly targeted repair. Umbrella export remains pending until the concurrent full build finishes and the root target is rebuilt.

The source review isolates the next geometric task. `PsiClasses.kappa` already defines κ by a forgetful pushforward, while `StrataRealization` provides only rational linearity and grading; no current law identifies the raw κ decoration with that definition. The existing ψ/gluing realization lemmas cover the other degree-one generators under their named compatibility inputs. The smallest follow-up is that concrete degree-one realization and its finite square, with independently justified κ/forgetful and boundary excess-intersection laws. Hodge/GRR identification, virtual Euler/stabilization, equivariant grading, ordinary geometric comparison and an actual producer class-valued semisimple CohFT remain open. No R4/R5 or full-project completion is claimed.

## 2026-10-05: Complete first F₁ H-component cache preserved for offline replay

The [complete component replay](../../AxiomaticGW/Surfaces/Fixtures/BlowupF1CompleteHComponentsReplay.lean) now preserves all 722 checked lower-genus components, their exact residual expressions and full-key injectivity. Its 268 fixture modules reuse the existing primary tables and 48 earlier component proofs. Every source was copied byte-for-byte from its accepted isolated run; existing sources and compiled artifacts were preserved. The mathematical statements, curve classes, insertion multiplicities, psi powers and fallback evaluator are unchanged.

The [portable validation record](../../environments/genus-two-f1-h-component-cache-validation.json) contains a compressed source/import inventory and deduplicated audit evidence for 125 successful runs and 2,170 exact cache declarations, together with the 14 supporting TRR repairs and 54 earlier failed probes. Only standard Lean axioms occur in the accepted audits. `python3 scripts/check_f1_component_cache_record.py` passes against the repository sources without reading the original temporary logs or compiled artifacts. `python3 scripts/test_f1_component_cache_record.py` passes all 27 tests in 24.802 seconds. Review found and repaired an evidence-checking gap: recorded import lists are now compared with the actual pinned source declarations, including corruption cases that preserve graph reachability.

This accepts the component cache only. The historical selector considered 721 nonzero-coefficient terms; the full original frame has 815 terms, including 94 zero coefficients. Neither complete contraction is accepted by this record. Rebuilding the new fixture closure in the repository, completing every original root-slot proof, and the unchanged fixed application suites remain required. The concurrent full-project build has not yet finished.

## 2026-10-05: Total certified primary backends for all three surfaces

The [point benchmark cache](../../AxiomaticGW/Surfaces/PointBenchmarkCache.lean) reuses the checked genus-zero and genus-one tables through anticanonical energy twelve and preserves the original evaluator outside that bound. Both backends equal the original evaluators as functions on every full curve class. Thus shifted sources of energy thirteen remain supported, and missing entries are never replaced by zero. The existing genus-two scalar constant is unchanged for every target, exceptional shift and state. No numerical seed, geometric hypothesis, global instance or simp rule was added.

The previously running two-point-blowup genus-one table completed successfully, and `lake build AxiomaticGW.Surfaces.GenusOneBenchmarks` now passes for all three surfaces. The new production and consumer targets build in 4.291 seconds; all seven actual public axiom audits pass in 2.033 seconds using only standard Lean axioms. Regression examples check both energy-thirteen fallback branches, distinct full classes of equal energy, and the auxiliary zero-class convention. The [validation record](../../environments/point-benchmark-cache-validation.json) preserves source pins, exact commands and complete logs, including two earlier build-monitor failures. The mathematical checks did not fail in those monitor runs; the final build was separately verified.

This closes the primary-backend reuse step. Complete blowup genus-two constants and numerical suites, full-project validation, geometric GKM compatibility and the research release remain required. The next priority is to finish the first F₁ H-row component cache and replay every original relation index.

## 2026-10-05: Exact root decomposition and original L24 frame

The [root decomposition](../../AxiomaticGW/Surfaces/ScalarPointRootParts.lean) exposes fundamental, separating and nonseparating contributions of the existing scalar point contraction. It traverses outer relabellings and leaves child contractions unchanged. The sum identity holds for arbitrary vertex data, full curve classes and point counts, retaining signed inverse weights, ordered node labels and binomial multiplicities. The [full-frame identity](../../AxiomaticGW/Surfaces/GenusTwoL24FullFrame.lean) restores all 815 original L24 indices by adding only terms whose original coefficient is zero.

This addresses a demonstrated certificate memory limit without changing the mathematics, original API, numerical seeds, global instances or simp rules. The three integrated targets pass `lake build` in 7.152 seconds; the separate seven-result axiom audit passes in 1.985 seconds using only standard Lean axioms. Tests cover signed separating and nonseparating slots and external relabelling. The [validation record](../../environments/genus-two-root-parts-validation.json) contains exact commands, complete logs, source pins and the public audit source. No new numerical row or geometric law is accepted at this checkpoint. The next priority is complete component and root-slot certification of the first F₁ H row; the fixed application suites, full-project validation and geometric GKM bridge remain open.

## 2026-10-05: Complete raw candidate classes after fixed-point cancellation

The [raw assembly bridge](../../AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroRawAssembly.lean) transports the accepted coefficient cancellations through all 45 source components. It proves the 36 empty components zero, retains each nonempty sum, and uses the accepted mixed-pair graph isomorphisms to collect the nine ordered expressions. For Q = x² − xy + y², U = A(raw₀₀), V = A(raw₁₁) and W = A(raw₀₂), the complete actual candidates equal Q·U + 3V + 3W for P², 4V for F₁, and −Q·U + 5V − 3W for Bl₂P². The raw₁₁ and raw₀₂ terms remain their exact degree-two source expressions; no square or geometric Hodge class is substituted.

The actual two-target build passes without warnings in 9.348 seconds (1,825 jobs), and all ten direct-public-import axiom audits pass at the 2 GB cap in 7.492 seconds using only standard Lean axioms. The [validation record](../../environments/gkm-hodge-raw-assembly-validation.json) contains source/data pins, exact commands, complete logs and both development failures. Independent consumers compare the complete blowup classes with the negative raw₀₂ contribution and verify that the original degree-four input is retained before coefficient cancellation. The umbrella export is deliberately pending until the concurrent full build finishes, followed by a root-target rebuild.

These full class equalities require only the existing linear realization `A`; they do not use `D`, `hfund`, scalar projection, or multiplicative compatibility. No existing statement, numerical seed, global instance or simp rule changed, and no axiom was added. Geometric Hodge/GRR and product identification, virtual Euler/stabilization, total equivariant grading, geometric ordinary comparison and actual semisimple CohFT laws remain open. This checkpoint does not complete R4/R5, the fixed research suites or full-project validation. The next mathematical bridge is the geometric realization and comparison of the exact surviving raw expressions.

## 2026-10-05: Complete fixed-point cancellation and regular formal specialization

The [regularity replay](../../AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroRegularity.lean) sums every actual ordered coefficient at all fixed points of P², F₁ and Bl₂P². Eighteen coefficient-sum proofs establish explicit polynomial lifts of the three complete formal Hodge polynomials. Writing Q = x² − xy + y², these lifts are Q + 3L₁² + 3L₂, 4L₁² and −Q + 5L₁² − 3L₂. The existing `embed` homomorphism maps each lift to the complete localized sum; the existing `atZero` homomorphism then evaluates only its polynomial torus-character coefficients, giving 3L₁² + 3L₂, 4L₁² and 5L₁² − 3L₂. Both Hodge symbols remain independent formal variables. No evaluation of the full fraction field at zero is used.

The two integrated targets build without warnings in 17.740 seconds (1,822 jobs). Eight portable Python checks pass in 4.761 seconds (4.513 seconds reported by unittest); all 28 actual public axiom audits pass in 1.305 seconds using only standard Lean axioms. The [validation record](../../environments/gkm-hodge-regularity-validation.json) embeds exact commands, complete logs, source pins, complete-sum arithmetic controls and both earlier failed probes. The first staged version had an incorrectly scoped summation binder; the accepted source parenthesizes each whole summand and disables automatic implicit variables. A later proof-order repair removed remaining warnings. No existing repository theorem, geometric hypothesis, numerical seed, global instance or global simp rule changed, and no axiom was introduced.

This proves regularity and ordinary formal specialization for the complete fixed candidate polynomials. It does not identify raw strata products with geometric Hodge classes, impose a Mumford relation, prove geometric localization, or construct a GW class or semisimple CohFT. The earlier scalar-normalization inputs `D`, `A` and `hfund` remain. The next bridge is to transport the exact coefficient cancellations through the accepted raw class assembly and then establish geometric realization and comparison. Total equivariant grading, geometric ordinary comparison, full-project validation, R4/R5 and all fixed research suites remain open.

## 2026-10-05: Every actual ordered Hodge coefficient satisfies the formal Chern formula

The [formula replay](../../AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroCoefficientFormula.lean) proves the exact ordered genus-two formula for all 108 incoming coefficients. It reuses both recorded tangent characters and the existing denominator and Euler-unit proofs. Every fixed point's complete nine-term polynomial in formal lambda₁ and lambda₂ factors into its two rank-two Chern polynomials divided by their tangent product. The ordered coefficient identities precede the collected polynomial identity, so the latter does not conceal branch order or an asymmetric pair. The producer source pin and its actual ordered weight formula were checked before choosing the statement.

The initial integrated production/consumer build passed in 14.561 seconds with two consumer line-length warnings. A whitespace-only generated-consumer repair leaves the production byte-identical; the final build passes without warnings in 3.410 seconds. The nine integrated Python tests pass in 3.668 seconds (3.561 seconds reported by unittest), and all 16 actual axiom audits pass in 1.807 seconds using only standard Lean axioms. The [validation record](../../environments/gkm-hodge-coefficient-formula-validation.json) embeds the exact sources, commands, complete logs, convention review and earlier finite-index proof failure. Controls check every coefficient and complete polynomial, detect tangent-order/sign changes, reject each of 108 coefficient mutations against the upstream data, and check helper pins before execution. No existing statement, geometric assumption, numerical seed, global instance or simp rule changed, and no new axiom was added.

This closes the exact coefficient-formula obligation, including positive entries. The equality concerns formal symbols; it does not identify the actual raw strata products with geometric Hodge classes, give a GW realization, or establish the constant-map comparison. The earlier scalar theorem still takes `D`, `A` and `hfund`. Geometric Hodge/GRR and product identification, virtual Euler/stabilization, total equivariant grading and ordinary comparison, semisimple GKM CohFT laws, full-project validation and all fixed research suites remain open. R4, R5 and the geometric interoperability gate remain incomplete.

## 2026-10-05: Actual compact Hodge coefficients and scalar normalization

The [c00 replay](../../AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroCoefficientReplay.lean) checks the actual twelve fixed-point records for P², F₁ and Bl₂P², preserving full zero curve coordinates, indices, cones, both ordered tangent characters and unit restrictions. Exact symbolic identities identify every incoming `(0,0)` coefficient with the existing fixture's accepted Euler unit. The [full replay](../../AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroFullCoefficientReplay.lean) decodes all 108 serialized fractions, proves all denominators nonzero and retains all 540 references to the 45 raw components in `candidateClass`. This discharges `h00` in the three concrete applications of the earlier normalization theorem; the existing `D`, homogeneous realization `A`, and explicit fundamental-class input `hfund` remain.

The four integrated targets build in 17.485 seconds (1,821 jobs). The c00 and full offline suites pass all 10 and 8 tests respectively (wrapper times 0.487 and 2.252 seconds); every one of the 108 coefficient mutation controls changes the emitted source. The actual public audit passes in 2.671 seconds with 57 results using only standard Lean axioms. The [validation record](../../environments/gkm-hodge-coefficients-validation.json) embeds exact commands, complete logs, code/data pins, the raw-source binding review, and development failures/warnings. An initial denominator proof needed explicit `one_ne_zero`; three redundant terminal tactics in the full replay were subsequently removed. No theorem statement, numerical seed, global instance or global simp rule changed, and no new axiom was introduced.

Positive-degree coefficients remain in the assembled class. Their geometric Hodge meaning is not proved by its scalar normalization; projection does not determine full classes. The grading is stable-curve codimension over the existing coefficient field. A normalized geometric realization, Hodge/GRR and product identification, constant-map virtual Euler and stabilization, total equivariant grading, ordinary comparison and an actual semisimple GKM CohFT remain required. This checkpoint does not complete R4, R5, the GKM geometric gate, full-project validation or the fixed research application suites. The next priority is the geometric realization and comparison of these actual class expressions.

## 2026-10-05: Exact first-match residual lookup

The [lookup module](../../AxiomaticGW/Surfaces/GenusTwoResidualLookup.lean) adds an executable first-match lookup to the existing `ResidualCache`. Its `values_eq` field proves uniqueness of matching entries, so mathlib's `Multiset.find?` can return the stored expression without the previous membership checks and full summation. An explicit option match preserves a stored zero and evaluates the original, proved-equal fallback only on a miss. The complete L24 constant agrees with the original for every cache selection; no completeness premise, numerical seed, mathematical hypothesis, existing API, global instance or simp rule changed.

The repository build passed in 4.869 seconds and the actual-import audit in 2.145 seconds, with nineteen results using only standard Lean axioms. Independent small consumers cover negative values, cached zero, distinct divisor states in one class, unlisted full classes, empty caches and a nonzero fallback. The [validation record](../../environments/genus-two-residual-lookup-validation.json) preserves source pins, commands and development failures. The first audit used a legacy import and exceeded the memory cap; the corrected module import passed at the same cap.

Numerical certification remains open. All 48 selected lower-genus values for F₁ term 121 and their cache contract have isolated kernel checks, but checking the full contraction in one computation still exceeds 2 GB. The complete first H-row selection now contains 722 full component keys across its 694 lower-genus terms; the remaining 27 terms have the higher-genus zero guard. Native evaluation produced 183 nonzero values, including 81 negative values, and agrees with all 48 earlier values. These candidates do not certify the complete constant `1/288`. The next step is smaller contraction certificates and reuse of the checked component values. Full-project validation and every fixed application suite remain required.

**Subsequent isolated replay:** The original weighted term 121 is now proved equal to `1/2160` by splitting only its outer contraction. All four ordered full curve splittings, four node states and two point distributions are checked. The 32 kernel-checked slots contain the contributions `1/1440` and `−1/4320` and thirty retained zeros. Reindexing and the cache-preservation theorem recover the original term with no extra hypothesis. The separate public-module run and 48-result axiom audit passed in 15.952 seconds at the unchanged 2 GB limit. This staged fixture still uses the separately checked F₁ diagnostic backend; it is not integrated as the final complete-row application package. The full `1/288` constant remains a candidate. The next step is to reuse this bounded decomposition and certify the remaining component values and 693 lower-genus terms.

## 2026-10-05: Complete raw-candidate scalar normalization

The [normalization module](../../AxiomaticGW/GKM/AdmcyclesHodgeStrataNormalization.lean) assembles all 45 actual raw components of the nine ordered genus-two, one-marked candidate expressions. The [generic degree lemmas](../../AxiomaticGW/Tautological/StrataRealizationDegree.lean) extend basiswise homogeneous realization to its rational span and show that positive-degree realizations have zero connected degree-zero projection. The actual `(0,0)` degree-zero component is the fundamental basis vector; the other eight degree-zero components are zero.

The remaining primitive normalization is explicit: `hfund` says that realization sends the fundamental class to one. Under this input, `scalar_assembly` proves that the complete assembly projects to `∑ p, coeff p 0 0`. `scalar_assembly_eq_tft` identifies this scalar with the canonical genus-two unit correlator when `h00` identifies each supplied `(0,0)` coefficient with its Euler weight. Acceptance of the actual 108 coefficient entries is a separate next step; this record does not discharge `h00`. Positive-degree terms remain in the assembled class, and scalar agreement does not prove equality of full classes.

This targeted review closed two missing algebraic APIs without changing existing statements, numerical seeds, axioms, global instances or simp rules. Two conditional-rewrite failures and unused simp arguments in the first staged proof were repaired without changing its mathematics. The integrated production and consumer build passed in 8.238 seconds; all 18 exact axiom-audit results passed in 2.636 seconds using only standard Lean axioms. Consumers cover the complete component frame, rational combinations, the actual mixed expression, empty fixed-point indices and coefficient changes that preserve only the scalar projection. The [validation record](../../environments/admcycles-hodge-normalization-validation.json) retains source pins, commands, complete logs and the audit source.

The grading is stable-curve codimension over the coefficient field. A normalized geometric realization, Hodge/GRR and product identification, virtual Euler and stabilization comparisons, total equivariant grading, ordinary specialization and a semisimple GKM CohFT remain required. Full-project validation and all fixed research benchmarks remain open. The next priority is to replay the 108 coefficient fractions and specialize this theorem to the three fixed targets while retaining `hfund`.

## 2026-10-05: Canonical fixed-point TFT normalization

The [fixed-point TFT module](../../AxiomaticGW/GKM/FixedPointTFT.lean) derives the canonical Casimir, handle element and all-genus correlator from the existing split Frobenius algebra. For invertible weights `e(p)`, the handle coordinate is `e(p)` and the correlator is `∑ p, e(p)⁻¹ * e(p)^g * ∏ s, a(s)(p)`. Keeping the inverse-times-power form includes genus zero and empty markings. In genus two, unit insertions give `∑ p, e(p)`.

This closes a missing algebraic normalization API without assuming a localization formula or changing existing definitions, hypotheses, seeds, instances or simp rules. Distinct-weight tests cover genera zero through two, empty markings, a nonunit insertion and the actual bundled topological CohFT. The repository build passed in 2.957 seconds; the eleven-result axiom audit passed in 1.322 seconds with only standard Lean axioms. A test-only stable-arity elaboration error was repaired without changing its statement. The [validation record](../../environments/gkm-fixed-point-tft-validation.json) preserves the exact commands and source scope.

The next step is to compare this derived normalization with the degree-zero projection of all 45 actual raw Hodge candidate components and the twelve fixed-point Euler coefficients. Geometric Hodge/product/localization identification, semisimple CohFT reconstruction and full-project validation remain open. This is a targeted algebraic review, not a certification of the geometric GKM bridge.

## 2026-10-05: Exact reuse of primary and residual values

**Status:** Four generic cache modules and two fixture-free consumer modules pass their repository builds. The [validation record](../../environments/genus-two-point-cache-validation.json) contains the six source pins, exact commands and all 40 audited results. Full-project validation, the all-target benchmark specialization and positive-degree numerical certification remain pending.

[LowGenusPointCache](../../AxiomaticGW/Surfaces/LowGenusPointCache.lean) replaces only the primary terminals of the existing genus-zero and genus-one ancestor algorithms. Equality is proved for every fuel and full query, without an added dimension or positivity premise. Class-zero constants, psi expansions and unsupported branches are unchanged. [L24 reuse](../../AxiomaticGW/Surfaces/GenusTwoL24PointCache.lean) and the [H/P/N/K dispatcher](../../AxiomaticGW/Surfaces/GenusTwoBlowupPointCache.lean) preserve all source classes, marking counts, signs and weights. [Residual reuse](../../AxiomaticGW/Surfaces/GenusTwoResidualPointCache.lean) materializes the existing `ResidualCache`; its proof field identifies every stored expression with the original expression, and missing keys retain the proved-equal evaluator.

This addresses repeated computation of already certified primary values. No numerical seed, geometric hypothesis, existing theorem statement, global instance or simp rule changed. A staged consumer needed explicit surface arguments; its mathematical statement was preserved. The targeted build passed in 7.235 seconds and the actual-import audit in 2.252 seconds. All 40 results, including the proof-bearing cache constructor, use only `propext`, `Classical.choice` and `Quot.sound`. The source scan found no placeholders, native acceptance, overlong lines or trailing whitespace. This was a targeted mathematical and API review, not a comprehensive audit.

With a separately checked F₁ primary backend, the original 721-term first positive H-row constant now completes as a native diagnostic. Consecutive chunks of 409 and 312 terms have exact sums `1361/67392` and `−1127/67392`, giving `1/288`. Every position occurs once and every weighted contribution equals its source coefficient times its contraction. Term 121 falls from 110.787 seconds to 2.711 seconds and retains contribution `1/2160`. These timings are concurrent diagnostics; the native values are not accepted certificates. The next priority is kernel replay of the selected lower-genus components and the complete constant, followed by the unchanged bounded tables and descendant suites. The goal remains active.

## 2026-10-05: Raw Hodge candidate replay and fixed graph-isomorphism equality

**Status:** The raw admcycles packet and one exact equality of its ordered representatives have targeted repository acceptance. This is progress toward R4 and the class-valued GKM bridge; it does not complete R4/R5, import a semisimple CohFT, or discharge any outstanding numerical benchmark. See the [combined validation record](../../environments/admcycles-hodge-strata-validation.json) and [exchange guide](../references/GKMExchange.md#raw-hodge-candidate-expressions-and-exact-regrouping).

The [raw decoder](../../AxiomaticGW/GKM/Fixtures/AdmcyclesHodgeStrataCandidates.lean) retains all nine ordered lambda-index products on the full stable genus-two, one-marked locus: 553 raw occurrences in 45 explicit degree components, 61 incidence presentations and 373 decorated encodings. It proves graph validity and formal degree using the existing free rational strata module. Coefficients, kappa powers, leg and ordered node psi, source flag provenance, zeros and raw gluing normalization are preserved. The source-labelled lambda products remain candidate geometric representatives.

The [isomorphism replay](../../AxiomaticGW/GKM/Fixtures/AdmcyclesHodgeStrataIsomorphisms.lean) proves equality of the actual 122-term `raw12Degree3` and 108-term `raw21Degree3`. All occurrences map to 44 held columns through 111 checked decorated-graph identifications. Kernel-checked rational sums agree in every column, and linearity proves the equality before imposing any tautological relation. The public consumer also transports this equality through an arbitrary rational linear realization. No claim of generic product commutativity or geometric Hodge identification is made.

The two offline proof exporters preserve the accepted Lean bytes and check helper pins before execution. A fresh portable Sage export passes in 4.747 seconds and reproduces the complete frozen packet except for its new producer digest, retaining both upstream `Algebras` deprecation warnings. Twenty-eight integrated Python tests passed, including exact regeneration, malformed raw data, changed graph hints, omitted/duplicated occurrences, coefficients and flag maps, stale helper/input bindings and protected output files. Their original console logs were not saved; the record identifies the observed tool results without inventing a replacement log. Raw public targets built in 31.100 seconds and the 529-declaration audit passed in 1.721 seconds. Isomorphism targets built in 3.969 seconds and the 122-declaration audit passed in 1.860 seconds. All 651 results use only `propext`, `Classical.choice` and `Quot.sound`. Earlier raw permission-preflight and isomorphism runner-identity failures remain recorded separately; neither is treated as a successful check.

Targeted review found no remaining defect in the accepted finite replay. No existing theorem statement, geometric hypothesis, numerical seed, global simp rule or instance changed; only local elaboration limits were used. This was not a comprehensive geometry or repository review, and the full build/test/lint checkpoint remains pending. The next class-valued bridge obligation is to identify these expressions with the Hodge bundle using the recorded GRR/Chern and kappa/raw-Gysin conventions, then establish product, virtual Euler and stabilization comparisons. Actual semisimple reconstruction data and all unchanged three-surface research gates remain open.

## 2026-10-05: Finite blowup table certificates and scalar replay

**Status:** Six production modules and six public consumer modules are integrated and pass targeted repository builds. They certify finite tables against the existing conditional H/P/N/K reconstruction. Positive-degree numerical tables, the unchanged energy-twelve and few-marking suites, and the full project build/test/lint checkpoint remain incomplete. The [validation record](../../environments/genus-two-blowup-certificate-validation.json) records this boundary.

The finite checker binds every value to its complete curve class and H/P/N/K query. It checks the original collected equation and requires each surviving dependency to be the own query or a stored strictly earlier query. Accepted entries equal the well-founded reconstruction; values outside a cache retain the original algorithm. The nominal class-zero P state remains internal and is not reported as a dimension-compatible invariant.

Scalar replay proves equality with the entire normalized row. An executable complete energy-bounded grid supplies every surviving canonical dependency: the dependency-energy theorem uses cancellation in the actual H/P/N/K coefficients. The H and N lower-genus constants still use the shifted source class, whose energy can exceed the output bound by one. Ordered replay uses the proved own pivots and masks only own/later states; it retains all nonzero earlier candidate columns, including those with zero coefficient. The H constant skips only graph terms already proved to have zero constant because they retain a genus-two component.

This closes a high-priority certificate implementation gap without changing existing theorem statements, geometric hypotheses, seeds, global instances or simp rules. Targeted review found no remaining semantic defect in these additions; it was not a comprehensive repository audit. All twelve modules passed the recorded `lake build` command in 14.965 seconds. The actual-import audit passed in 2.250 seconds: all 100 public production and consumer results use only `propext`, `Classical.choice` and `Quot.sound`. Static checks and `git diff --check` passed. Earlier isolated checks also covered two class-zero generated certificates; they do not establish positive-degree numerical acceptance.

The previous full build was interrupted before completion; process inspection confirmed that its workers were gone before validation resumed. Completed artifacts were retained. A capped exact native profile of the first F₁ H row completed 28 of its 721 held terms before timing out. Term 121 took 110.787 seconds and gave contraction `1/144`, weighted contribution `1/2160`; these are diagnostic native values, not accepted numerical certificates. The next priority is a proved-equal lower-genus evaluator that reuses certified primary tables, followed by complete positive-degree table replay. The research goal remains active.

## 2026-10-04: Complete H/K canonical support and solved scalar rows

**Status:** The original shifted L24 H row now has complete canonical own-H-or-earlier support; every same-plane N/P/K coefficient vanishes. The complete exceptional triple BP row has uniform K_i pivot −18, signed P coefficient 18α_i, zero other same-class K_j coefficients and own-K_i-or-earlier support. Together with the existing P result, H/P/K now have executable scalar steps, strict earlier dependencies and uniqueness relative to earlier values. The primary N row and the combined finite-seed recursion remain open; this is a partial R7 acceptance, not completion of either blowup application.

The [validation record](../../environments/genus-two-blowup-hk-validation.json) preserves exact commands, source pins, failed development attempts and the protected working-tree comparison. The preceding canonical-closure checkpoint remains a historical record of its recorded sources.

### Scope, findings and revisions

- **High H-support gap closed:** [HOtherFamilies](../../AxiomaticGW/Surfaces/GenusTwoBlowupHOtherFamilies.lean) proves all 25 discarded genus-two L24 terms vanish at every full plane-zero remainder for arbitrary requested variables and terminal values. The two surviving original terms have no primary or non-H first-descendant coefficient there. The proof uses actual rational complements, dimension at energies zero/one and already reconstructed exceptional point-value vanishing; no calibration cancellation is assumed merely from an exceptional insertion. The original full-class bound and prior H-column proof then give complete canonical support.
- **High exceptional-row gap closed:** [KCoefficients](../../AxiomaticGW/Surfaces/GenusTwoBlowupKCoefficients.lean) follows the actual four BP diagrams and all six marking assignments. The classical exceptional square contributes minus the point, giving K_i coefficient −18 and P coefficient 18α_i. Different exceptional labels at the same full class are excluded explicitly. Proper subclasses decrease positive energy; the H/P/N sectors are earlier. Negative and zero signed multiplicities remain in the domain.
- [HRow](../../AxiomaticGW/Surfaces/GenusTwoBlowupHRow.lean) reuses the existing shifted L24 row. [KRow](../../AxiomaticGW/Surfaces/GenusTwoBlowupKRow.lean) defines the original exceptional triple BP row. Collection retains all constants and coefficients before removing only the requested singleton. Their scalar steps are respectively the remainder and the remainder divided by 18. Both prove support, exact row decomposition, the solved value, dependence only on earlier canonical values and uniqueness. H also proves agreement of different exceptional shifts under both original equations.
- **Medium reuse/elaboration issues addressed:** Four existing P helper proofs and three helpers in the new K module are public for mixed-row reuse, without changing statements or proof terms. HRow uses the existing L24 recursion depth of 20000 to traverse its 815-column source. The H source's nine-constructor flag-normalization lemma has a local finite heartbeat budget; no kernel proof is replaced by native evaluation. Initial depth and formatting failures are retained in the command ledger.
- Current README, roadmap, reconstruction plan, input ledger and declaration map describe the H/P/K gate and keep primary N, full recursion, benchmarks and GKM/release requirements open. Independent targeted reviews of the K source/tests and both solved-row modules found no concrete semantic defect. Root additionally reviewed the H rational boundaries, actual constructor bindings, survivor and full-row support arguments. This was not a comprehensive repository or geometric-realization audit.

### Mathematical effect and validation

No numerical seed, geometric law, existing production theorem statement, global simp rule or instance was added or changed. Solved-row statements require the original full equations to vanish; they do not assume their desired recurrences. Positive energy is required. Unlike P, H and K do not divide by plane degree or signed intersection. Class-zero and remaining finite-seed reconstruction obligations are not claimed by these rows.

- `lake build AxiomaticGW.Surfaces.GenusTwoCanonicalRelations AxiomaticGW.Surfaces.GenusTwoBlowupPRow AxiomaticGW.Surfaces.GenusTwoBlowupHCoupling AxiomaticGW.Surfaces.GenusTwoBlowupPCoefficients` passed as baseline: 1.064 seconds, 2805 jobs.
- All four new production modules and all four test modules passed targeted builds. `lake build` passed in 3.373 seconds, 2972 jobs; `lake test` passed in 34.914 seconds, 3099 jobs; `lake lint` passed in 6.698 seconds. The only integrated warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.
- `lake env lean /tmp/gw_blowup_hk_audit_20261004.lean` passed in 2.214 seconds. All 67 audited public source and consumer declarations use only `propext`, `Classical.choice` and `Quot.sound`.
- Twenty-four named consumers cover pure exceptional and class-zero boundaries, retained energy-one seeds, negative/zero multiplicity, distinct equal-measure classes, different exceptional labels and shifts, arbitrary point counts, full reducible remainders, correct division signs and independence from ancestor callbacks.
- The ten-file Lean scan found no placeholders, substitute axioms, native proofs or overlong lines. Documentation links, the protected 831-file comparison and `git diff --check` passed. No benchmark query was removed or newly certified by this symbolic checkpoint.

### Primary N investigation and remaining scope

The previously checked zero coefficient in a single EHH row at α_i=0 remains valid, but does not prove that a new blow-down assumption is necessary. Separate exploration of a four-BP-row combination also using EEE gives a candidate N pivot 6d, with checks at plane degrees one, two and three and negative/zero/positive signed multiplicities. This is a directly proposed linear combination of actual relations, not a transcription of the printed source formula. Native diagnostics are not acceptance evidence: the uniform primary coefficient and cancellation of all later K dependencies remain to be proved. No new geometric input or N recurrence is introduced here.

Next prove that N row and its complete support, then assemble finite-seed termination, soundness and uniqueness for both blowups. Complete every fixed primary/first-descendant benchmark and all 656/4495 blowup few-marking queries. Actual class-valued semisimple GKM import, remaining input/provenance obligations and the offline research release remain required. The goal stays active. No producer edit, commit or push was performed.

## 2026-10-04: Complete primary BP/L24 canonical closure and the solved P row

**Status:** The complete normalized primary BP and L24 equations now contain only constants and canonical genus-two descendant variables at full effective subclasses. The collected BP HHH remainder uses only strictly earlier canonical values; at positive plane degree its actual pivot gives an executable P step and uniqueness from those earlier values. This accepts a further partial R7 gate. Complete H/N/K recursion, both blowup applications, actual class-valued GKM input and the research release remain open.

The [validation record](../../environments/genus-two-canonical-closure-validation.json) records exact commands, source pins, repaired development failures and the protected worktree comparison. The preceding P-support checkpoint is preserved as a historical record; four helper proofs now have public visibility with unchanged statements and proofs.

### Scope, findings and revisions

- **High reconstruction gap closed for the P step:** [GenusTwoCanonicalRelations](../../AxiomaticGW/Surfaces/GenusTwoCanonicalRelations.lean) classifies every actual variable in both complete primary relation rows, rather than only variables already assumed to be canonical. Full effective remainders and all signed normalization corrections remain. No ancestor callback survives. Raw support, collected support, actual nonzero coefficient classification and evaluation congruence are proved.
- [L24CotangentSupport](../../AxiomaticGW/Surfaces/L24CotangentSupport.lean) checks that every nonzero one of the 815 original columns has at least two edges. Signed pullback preserves this lower bound; codimension three then bounds every residual psi degree by one. The proof uses kernel computation of the original source, not a native Boolean diagnostic or an assumed support bound.
- [GenusTwoBlowupPRow](../../AxiomaticGW/Surfaces/GenusTwoBlowupPRow.lean) collects cancellations, isolates only the requested P column, retains the lower-genus constant and proves the exact scalar step with denominator 18d. Strict earlier support, independence from ancestor callbacks and uniqueness follow from the original row. Positive plane degree is essential: the positive-energy exceptional generator has zero P pivot.
- **Medium proof elaboration defect repaired:** A mixed-class consumer unfolded the complete graph row through its closed membership hypothesis. Generalizing the same full class before applying the proved support theorem avoids that computation without changing the statement. The constructor-name linter is disabled only for that declaration because its binder scan independently forces the same computation; all binder names were reviewed. Kernel checking remains enabled, and no heartbeat limit was increased.
- Four unchanged helper proofs in PPrimarySupport/PCoefficients are exposed for reuse by the actual H/K coefficient arguments. The umbrella and current mathematical status maps include the three new modules. Independent targeted semantic review found no concrete defect in their mathematical claims; no comprehensive repository audit is claimed.

### Mathematical effect and verification

No numerical seed, geometric hypothesis, existing production theorem statement, global simp rule or instance was changed. The original HHH equation's validity remains an explicit premise of the solved-row theorem. This is not a complete blowup recursion, and degree-zero or zero-plane-degree values are not obtained by division by zero.

- `lake build AxiomaticGWTest.Surfaces.GenusTwoBlowupPRow` passed in 1.979 seconds.
- `lake build` passed in 1.874 seconds, 2968 jobs. `lake test` passed in 34.071 seconds, 3091 jobs. `lake lint` passed in 15.889 seconds. The only integrated warning is the existing private-module warning in `AxiomaticGWTest/Basic.lean`.
- `lake env lean /tmp/gw_canonical_closure_all_axioms_20261004.lean` passed in 4.341 seconds after the test dependencies were built. All 39 audited declarations use only standard Lean axioms. An earlier parallel audit started before a test object existed; that failed invocation is retained separately.
- Fourteen named consumers cover actual arbitrary variables, higher-psi exclusion, class-zero point underflow, nonzero exceptional dependencies, full mixed classes, division signs, ancestor independence and the zero P-pivot boundary.
- Placeholder, substitute-axiom, native-proof and line-length scans passed in the nine-file Lean scope. Documentation links, protected-file comparison and `git diff --check` passed. No fixed numerical benchmark was removed or newly accepted by this checkpoint.

### Remaining scope and next priority

Integrate the separately staged K coefficient/support proof, finish the other-family H support and derive the primary N row. A checked zero pivot at the alpha_i=0 boundary requires a justified blow-down comparison or another actual equation; no uniform N pivot is claimed. Then prove finite-seed sufficiency, termination, soundness and uniqueness for both blowups, and complete their primary, first-descendant and 656/4495 few-marking suites. Complete the remaining R1/R3--R5 input and interoperability gates and R8 offline workflow. The goal remains active; no producer edit, commit or push was performed.

## 2026-10-04: Complete canonical P-row support from exceptional rational tails

**Status:** The complete normalized BP HHH row now has zero primary coefficient at equal plane degree for every full effective class and every point count. Every surviving primary column therefore strictly lowers plane degree. At positive source energy, every surviving canonical column is its own P variable or earlier in the established plane-degree/family/energy order. This closes the pending primary and canonical P-row support gate, not the full blowup reconstruction. Other-family H support, N/K equations, both blowup applications and all GKM/release requirements remain open.

The [validation record](../../environments/genus-two-blowup-p-support-validation.json) records source pins, successful commands, repaired development failures and the protected worktree comparison. The immediately preceding status-only goal turn is classified as **no progress toward implementation**. This continuation revalidated the staged proofs, integrated them into the public umbrella and completed the full gates. The earlier H/P pivot checkpoint remains a historical record of its recorded sources.

### Scope, findings and revisions

- **High reconstruction gap closed for the P row:** An N dependency can have smaller energy while remaining later than P in the chosen order. Energy decrease alone was insufficient. `primary_coefficient_support` now proves strict plane-degree decrease from the actual full BP row, retaining all signed cotangent and calibration corrections. `canonical_coefficient_support` combines this with the existing nonprimary support and actual effective-subclass bounds. Neither theorem assumes a support oracle or recurrence.
- **Medium missing lower-layer result supplied:** [GenusZeroExceptionalPoints](../../AxiomaticGW/Surfaces/GenusZeroExceptionalPoints.lean) proves the reconstructed genus-zero point value vanishes at zero H intersection and energy at least two. At energy at least four the proof uses the original guarded WDVV step; energies two and three use finite kernel checks of the existing reconstruction. The exceptional generator seed remains one. The actual node/two-point rational tail vanishes at every energy, including zero and one by dimension. The module imports only the genus-zero scalar layer.
- [PPrimarySupport](../../AxiomaticGW/Surfaces/GenusTwoBlowupPPrimarySupport.lean) uses those tails to prove point-input calibration cancellation at equal plane degree and the corresponding signed cotangent-pullback equality. All four genus-two BP diagrams and all six marking occurrences are bound to the original normalized equation; the other diagrams already have proved lower-genus coefficient zero. Incomparable classes are excluded by the existing full-class bound, not by a new hypothesis. Lower-plane primary tails remain present.
- **Low documentation gap repaired:** Current status and declaration-map paragraphs now record the complete canonical P support. The coefficient module's old pending-primary wording was updated. Historical progress entries retain their original scope.

An independent read-only review inspected both complete production modules and both tests and found no concrete semantic defect. This was a targeted review of the exceptional boundary, actual graph and normalization identities, and order support; it was not a comprehensive repository or geometric-realization audit.

### Mathematical effect and validation

No numerical seed, geometric hypothesis, existing theorem statement, global simp rule or instance was added or changed. These are algebraic identities of the existing reconstructed functions and full normalized equations. The P coefficient remains −18d and requires positive plane degree to be invertible; the new support theorem does not assert that pivot at degree zero or construct a complete recurrence.

- `lake build AxiomaticGW.Surfaces.GenusZeroExceptionalPoints AxiomaticGWTest.Surfaces.GenusZeroExceptionalPoints AxiomaticGW.Surfaces.GenusTwoBlowupPPrimarySupport AxiomaticGWTest.Surfaces.GenusTwoBlowupPPrimarySupport` passed as the integration baseline: 0.861 seconds, 2794 jobs.
- `lake build` passed: 3.566 seconds, 2965 jobs. `lake test` passed: 25.141 seconds, 3085 jobs. `lake lint` passed: 10.236 seconds. The only test warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.
- `lake env lean /tmp/gw_blowup_p_support_all_axioms_20261004.lean` passed: 5.864 seconds. All 38 public production and consumer declarations use only `propext`, `Classical.choice` and `Quot.sound`.
- Twenty-one named consumer tests cover arbitrary exceptional multiplicities, mixed classes, preservation of the generator/fiber seeds, energy-zero/one tails, smaller-energy primary variables that are later in the family order, negative signed multiplicities, incomparable and higher-plane classes, the original complete BP constructor, and the canonical support theorem.
- Placeholder, substitute-axiom, native-proof and line-length scans are clear in the six-file Lean integration scope. `git diff --check` and local documentation-link checks passed. Agent ledgers retain the earlier finite-vector and implicit-target inference failures, their repairs and final completed commands. No fixed benchmark was removed or accepted on native diagnostics alone.

### Remaining scope and next priority

Lift canonical normalization through the complete relation rows, finish other-family H support and derive the N/K equations, then assemble finite-seed reconstruction for both blowups. Complete their unchanged primary, first-descendant and 656/4495 few-marking suites. Actual class-valued semisimple GKM import, justified comparisons and the offline research release remain mandatory. Work on these next steps is outside this checkpoint. The goal remains active; no producer edit, commit or push was performed.

## 2026-10-04: Uniform blowup H pivot and coefficient support in the H/P rows

**Status:** The full normalized shifted H row now has coefficient −1 at every positive-energy full class. Its nonzero H columns are either the exact requested class or strictly earlier in the established reconstruction order. The BP HHH row has zero same-class primary N coefficient; every surviving nonprimary column at a different class has smaller plane degree, and all surviving K columns have smaller plane degree. These are accepted symbolic R7 steps. Other-class primary P support, other-family H support, N/K reconstruction and both complete blowup applications remain open. Every fixed benchmark and the class-valued GKM/release requirements are retained.

The [validation record](../../environments/genus-two-blowup-pivot-validation.json) records the precise source scope, commands, assumptions, failures and preservation checks. The earlier [foundation checkpoint](../../environments/genus-two-blowup-foundation-validation.json) remains a historical validation of its recorded source versions. The preceding interrupted turn ended before a tool action and is classified as no progress; this continuation revalidated the files, repaired the pending import and completed the integration checks.

### Review and findings

- **High reconstruction gap addressed for H columns:** The old well-founded measure alone did not eliminate different full classes at equal measure. The exact normalized equation now cancels those columns. The shifted source H column also vanishes because it needs more added points than the row supplies. The resulting coefficient-support theorem assumes no support oracle and does not assert that individual uncollected terms vanish.
- **High reconstruction gap addressed for nonprimary P columns:** A later-family K column could have smaller energy but equal plane degree, which would not decrease in the order H/P/N/K. The complete BP row now excludes this possibility by proving strict plane-degree decrease. Other-class primary N tails remain explicit.
- **Medium reuse and dependency issues repaired:** The primary coefficient proof uses the actual generic cotangent constructor instead of importing a plane application. Five existing HH/join helper proofs are exposed with unchanged statements; two primary-coefficient helpers and the general HHH marking-orbit identity are reused by subsequent support work. No global simp rule or instance is added.
- **Low integration issues repaired:** New public order regressions needed a public import; the initial private import failed compilation. Two wrapped documentation lines and stale pending-pivot descriptions were corrected. Targeted independent reviews found no concrete mathematical defect in the new coefficient, coordinate and support statements; this was not a comprehensive repository audit.

### Revisions and mathematical effect

[HVanishing](../../AxiomaticGW/Surfaces/GenusTwoBlowupHVanishing.lean) proves ten actual coefficients zero: seven chains with an external exceptional main marking and three rational H/exceptional forks. [ExceptionalComplement](../../AxiomaticGW/Surfaces/GenusTwoBlowupExceptionalComplement.lean) evaluates the remaining rational forest with its ordered splittings and negative exceptional inverse metric. [HContributions](../../AxiomaticGW/Surfaces/GenusTwoBlowupHContributions.lean) assigns the original terms 57/64 the contributions −1/2 each and binds their sum to the full normalized row, including all constants and other variables.

[HSupport](../../AxiomaticGW/Surfaces/GenusTwoBlowupHSupport.lean) proves vanishing below the required point budget. Two [coordinate lemmas](../../AxiomaticGW/Surfaces/GenusTwoBlowupOrder.lean) classify every plane-zero energy-one remainder as its actual exceptional generator. [HCoupling](../../AxiomaticGW/Surfaces/GenusTwoBlowupHCoupling.lean) combines these facts with the existing effective-subclass bound to prove self-or-earlier H coefficient support at positive target energy. Full coordinates, negative signed multiplicities and the distinct exceptional labels are retained.

[PPrimary](../../AxiomaticGW/Surfaces/GenusTwoBlowupPPrimary.lean) proves same-class primary N coefficient zero and hyperplane calibration cancellation at equal plane degree. [PSupport](../../AxiomaticGW/Surfaces/GenusTwoBlowupPSupport.lean) follows all four genus-two BP diagrams and all six marking assignments to prove nonprimary support and strict lower-plane K support. The existing coefficients H/P/K = 18/−18d/0 retain their positive-energy condition, and the P pivot separately requires positive plane degree. No seed, geometric hypothesis, benchmark bound or existing theorem statement was weakened or changed.

### Verification

- `lake build` passed: 2.915 seconds, 2963 jobs.
- `lake test` passed: 27.642 seconds, 3081 jobs. The sole warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.
- `lake lint` passed: 8.071 seconds.
- `lake env lean /tmp/gw_blowup_pivot_all_axioms.lean` passed: 1.662 seconds. All 123 selected production/helper/consumer declarations use only `propext`, `Classical.choice` and `Quot.sound`.
- Seven new production modules and their tests, the order extension, helper visibility changes and the public umbrella are integrated. The seven new test files contain 58 named results; three additional public order regressions preserve the equal-energy class distinction and the necessary plane-degree hypothesis.
- Placeholder, substitute-axiom, native-proof and line-length scans are clear in the 17-file Lean scope. `git diff --check` passed. Exact targeted builds, repaired failures, source pins and documentation-link checks are retained in the validation record. Expensive optional H/P test elaborations were explicitly retired through their original handles and replaced by finite coordinate identities or a smaller independent kernel regression; no fixed research benchmark was removed.

### Remaining scope and next priority

Finish other-class primary P support using the original cotangent and calibration terms, then assemble the full canonical P-row decrease theorem. The follow-up genus-zero exceptional-point and primary-tail investigation is separate from this accepted source snapshot. Other-family H support, N/K reconstruction, finite-seed sufficiency for both blowups, all their numerical certificates, actual semisimple CohFT import and the offline research release remain required. The goal remains active. No producer edit, commit or push was performed.

## 2026-10-04: Blowup canonical support and exact shifted-H coefficient frames

**Status:** The genus-two blowup foundations now have public integration: canonical full-class support, ordinary exceptional point support, the derived F₁ class-zero primary point, a well-founded labelled order, generic first-descendant coefficient isolation, exact shifted-H coefficient formulas with 27 and 21 terms and a 12-term positive-energy expression, and uniform BP HHH first-descendant coefficients. This is partial R7 progress. Remaining uniform pivots, cancellation of competing full-class columns, both blowup recursions and their complete numerical suites remain required. The three targets, benchmark bounds and full semisimple GKM completion gate are unchanged.

The [validation record](../../environments/genus-two-blowup-foundation-validation.json) separates successful commands, proof-development failures, native diagnostics and deliberately retired optional jobs. The immediately preceding status-only goal turn is classified as **no progress toward implementation**. This continuation revalidated the current baseline, integrated the proved modules, extended consequential consumer regressions and checked the new coefficient identities.

### Scope, findings and revisions

- **High remaining reconstruction gap:** Source-relative subclass support alone does not establish termination for the shifted H source β+Eᵢ. The new order proves exactly when a same-family remainder decreases. An energy-one exceptional remainder can leave a different full class at equal measure, including different ruling classes at positive plane degree. The original equations must cancel or solve those coefficients; no decrease hypothesis is substituted for that proof.
- **High application gap narrowed:** Canonical primary and first-descendant families now have exact signed dimension, domain and normalization support. A zero evaluation pullback kills the complete descendant integrand and its linear virtual integral. The named ordinary `ExceptionalPointSupport` condition then supplies every point-supported positive exceptional canonical value. Class zero and queries without a point are excluded. F₁'s class-zero primary point is derived from the full BP equation, this support input and the existing exceptional divisor seed; it is not added as a primary seed.
- **Medium dependency defect repaired:** The new generic coefficient helper initially reached a plane application through a convenience import. It now proves the specialized tail vanishing directly from the generic remainder constructor. Existing public signatures and all assumptions are preserved; no existing module was moved or refactored.
- **Medium repeated coefficient work reduced:** Generic first-descendant coefficients equal direct normalization even at a smaller full class. Primary calibration tails remain in the complete polynomial, with a regression retaining coefficient one. The class-pruned component is proved equal to the original coefficient. The complete shifted-H row has a kernel-checked 27-column genus-two frame. The six actual primary-main graphs share a fixed rational chain and are proved to have zero coefficient for every class, remainder and added-point count. Their removal gives an exact 21-term formula with all signed point corrections, inverse-metric factors and rational complements retained. The nine actual one-flag genus-two terms then vanish when their point allocation is less than target energy. At the positive-energy shifted request this gives an exact 12-term frame, for every effective remainder. The unconditional formulas keep the zero-energy case.

The new BP HHH coefficient module derives all six marking occurrences from the actual four genus-two paper diagrams, with exact point-count condition e(β)=n+1. At positive energy the same-class H coefficient is 18, the point-descendant coefficient is −18d, and every exceptional first-descendant coefficient is zero. The P coefficient is nonzero at positive plane degree d. Pure exceptional classes retain H coefficient 18 and P coefficient zero, while the actual class-zero coefficient is checked separately. Negative signed exceptional multiplicities are retained. These are coefficients of the complete normalized equation, not a solved recurrence; same-class primary N terms and all lower-class support still require their own analysis.

A read-only second review of the eight earlier production modules and corresponding tests found no concrete semantic defect. It explicitly checked ordinary support, zero-class exceptions, primary calibration tails, full-class labels and the limits of the order and coefficient formulas. This is a targeted review, not a comprehensive audit of the pre-existing worktree.

### Mathematical effect and validation

The computational support, order and coefficient identities add no numerical seed or recurrence assumption. Exceptional vanishing and the F₁ initial deduction have a new, explicit class-level geometric evaluation-support hypothesis whose construction remains open. All positive exceptional multiples, mixed coordinates and signed negative multiplicities remain in scope. The previous plane theorems and two-point-blowup initial results are unchanged.

- `lake build` passed with 2,956 jobs in 1.708 seconds; `lake test` passed with 3,067 jobs in 26.951 seconds; `lake lint` passed in 6.793 seconds after the final twelve-term proof. The only integrated test warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.
- `lake build AxiomaticGW.Surfaces.GenusTwoBlowupHUniform AxiomaticGWTest.Surfaces.GenusTwoBlowupHUniform` passed in 5.843 seconds. The corresponding P-coefficient two-file target passed in 4.804 seconds. All nine production modules and eight matching surface test modules compile through the full gates; they contain 86 consequential regression examples or named results.
- The selected `lake env lean` audits cover 122 distinct declarations and report only `propext`, `Classical.choice` and `Quot.sound`. Refreshed public-umbrella consumers check both the full shifted-H identity and the nonzero P coefficient. No placeholder, substitute axiom, native proof decision, global simp rule or new global instance is added.
- The validation record preserves exact commands and log digests, final source pins, development failures, scope review, documentation links and the protected worktree comparisons. Four expensive optional H arithmetic probes/tests were deliberately terminated through their original handles; none is accepted as a numerical certificate. Native mixed-class values are diagnostics only. No original fixed benchmark is dropped.

### Remaining scope and next priority

Prove the symbolic shifted-H coefficient equals −1 and cancel every competing same-measure full-class column. Then finish primary and lower-class support for the P row, derive the N/K equations, and prove finite-seed reconstruction. Native multiple/mixed-class coefficient probes remain diagnostics; finite examples do not establish the uniform result. Ordinary exceptional support must be used after a justified ordinary comparison, rather than applied directly to an arbitrary equivariant point lift. Actual class-valued semisimple CohFT import, localization derivation replay and the offline research release remain mandatory. No producer edits, commit or push were performed.

## 2026-10-04: Complete plane few-marking certificates through shared component replay

**Status:** All 48 held plane genus-two few-marking requests now have kernel-checked values bound to their original ordered queries. All 291 lower-genus components, 39 ancestor rows and 539 original boundary terms are checked. Together with the twelve canonical certificates and the general plane descendant theorem, this completes the fixed plane genus-two numerical suites under the original geometric inputs. Both genus-two blowup reconstructions, full class-valued GKM interoperability and the research release remain open; the full goal stays active.

The [validation record](../../environments/genus-two-plane-component-replay-validation.json) preserves completed commands, source pins, repaired development failures and deliberately retired runs. The preceding status-only turn is classified as a **verified wait**: it polled the two original component replay handles and confirmed that both remained live. This continuation completed the component corpus, ancestor table, descendant assembly, incoming claim binding and public lookup.

### Review and findings

- **Medium proof-checking bottleneck:** Whole boundary replay repeatedly evaluated the same low-genus components. The new `ResidualCache.ofEntries` requires a proof of every stored expression and injective full keys. `ancestorReductionTermsCached_eq` preserves every term of the original square/product equation, including repeated terms and signs. The separately checked point-ancestor row gives `-9/640`, which is an ancestor value and is not confused with its stable-map descendant.
- **Medium nested repetition:** The remaining elliptic components repeated their own rational and elliptic dependencies. `ancestorValue_eq_step`, `cachedLowerValue_eq` and `ellipticStepCached_eq` prove that a partial cache preserves the original elliptic recursion. The native cache-selection hints supply no mathematical premise; missing keys use the original algorithm. The full psi-three component group fell from 1,677 seconds to 163 seconds. The psi-four replacement passed in 252 seconds; its older run was deliberately retired after the new theorem and a production component proof passed. The old psi-three process had already completed successfully before the retirement check, and was not killed.
- **Low integration defects:** Exporting the completed lookup exposed missing docstrings and numerical-row naming lint reports in generated fixtures. Generator-owned documentation and narrowly scoped naming annotations preserve the existing indexed API. A negative GKM test also depended on the exact wording of Lean's failed decision diagnostic. It now verifies rejection of the intended binding statement and separately proves that the forged number differs from the held value.

### Revisions and mathematical effect

The [component exporter](../../scripts/export_plane_genus_two_components.py) generates individually checked values and per-equation partial caches. Its [native explorer](../../scripts/PlaneGenusTwoComponents.lean) regenerates the complete 291-component candidate data and the 56 elliptic selection hints; both match their held data. The [ancestor exporter](../../scripts/export_plane_genus_two_ancestor_cache.py) uses those proved caches for the previously unfinished equations. The original GKM arithmetic sectors retain their public statements and now reuse the accepted table and complete descendant expansions.

The public [few-marking lookup](../../AxiomaticGW/Surfaces/PlaneGenusTwoFewMarkingBenchmarks.lean) returns an exact rational value only for the fixed complete ordered request domain. Its soundness theorem identifies the result with the original descendant algorithm; its domain theorem proves both coverage and exclusion of outside queries. Public regressions include the nonzero point-pair value `1/144`, the unit-pair value `7/320`, and rejection of changed class or dimension. The unchanged plane geometric theorem supplies the conditional interpretation.

No seed, geometric hypothesis, benchmark bound, original theorem statement or reconstruction algorithm was weakened or changed. No simp rule or typeclass instance was added. The new cache identities are unconditional equalities of the implemented algorithms. Numerical GKM agreement is still separate from geometric localization validity and actual CohFT import.

### Verification and remaining scope

The validation record lists the exact successful build, test, lint, exporter and kernel-rejection commands and distinguishes earlier unsuccessful runs. Fifty-seven public declaration axiom audits report only `propext`, `Classical.choice` and `Quot.sound`. All seventeen Python exchange test methods pass across the component, ancestor and full GKM suites. They include false nonzero and dimension-zero components, a coherent wrong terminal, altered zero-valued comparison terms, a value-preserving boundary forgery and a coherently false incoming GKM claim.

The final review preserves the large pre-existing worktree; no comprehensive audit of that worktree, producer change, commit or push is claimed. Kernel replay still has material memory costs, recorded separately from runtime. The next mathematical priority is finite-seed genus-two reconstruction on both blowups, including uniform solvability and all fixed benchmark queries. The full semisimple CohFT bridge, general operation provenance and offline research release remain required.

## 2026-10-04: Split descendant replay and proved cotangent dimension pruning

**Status:** All 48 original plane descendant–ancestor expansions and their cache-based values are now kernel checked. The finite ancestor table has six accepted low-psi rows, six total-psi-two rows and four total-psi-six rows. The other 23 ancestor rows and final table assembly remain pending. The full research goal, both blowup applications and actual semisimple CohFT interoperability remain open.

The [validation record](../../environments/genus-two-plane-cache-performance-validation.json) records completed checks, failed and deliberately superseded runs, source pins and live handles. The preceding status-review turn counts as **progress through new evidence**: polling found the original Point-sector build had terminated with heartbeat-limit failures, which changed the next implementation action. No result from that failed module was counted as accepted.

### Review, findings and changes

- **Medium proof-checking bottleneck:** The direct two-marked Point replay reached Lean's four-million-heartbeat limits. A stack sample of the separate cached-descendant job showed extensive definitional reduction. Splitting the exact mixed expansion from its rational evaluation gives the same 48 full-query statements in 27.093 seconds in the production fixture. Each `comparison_i` checks every ancestor key, coefficient and repeated term before `cached_computation` evaluates the supplied cache. The superseded combined proof was deliberately stopped after the complete replacement passed, rather than restarted after an observation timeout.
- **Medium missing computational vanishing theorem:** The original lower-genus ancestor recursions expanded components whose cotangent degree exceeds the stable-curve dimension. `GluingExpression.surfaceEval_zero_of_cotangent_bound` proves that every contraction above the sum of component dimensions has a vanishing factor, including loops. `SurfaceGenusZero.ancestorValueFuel_zero_of_cotangent_bound` and its elliptic analogue derive the corresponding vanishing for every fuel and full effective class. Their `ancestorValue_pruned` identities expose this branch while retaining the original evaluator elsewhere; only local evaluation attributes are used.
- The earlier direct-kernel zero-row experiment had been stopped at a measured 6.1 GB physical footprint. The new proved pruning certified that exact row in 38.559 seconds. All four total-psi-six boundary equations then passed as a production module in 206.182 seconds. The older unpruned psi-three job was deliberately retired after the new identities and this positive control were checked; its replacement remains a separate observed job.
- **Certificate integrity:** Three new coherent forgeries change or omit a zero-valued comparison term while preserving the final candidate value. Preflight arithmetic accepts them; actual Lean comparison replay rejects all three. Existing coherent false-terminal rejection and full-query checks remain in place.

### Mathematical effect and public use

No existing definition, theorem statement, numerical seed or geometric hypothesis changed. The dimension result is an unconditional property of the implemented low-genus ancestor algorithms. It is not a stable-map descendant vanishing rule: the existing checked plane `tau_5(1)` value `1/128` and other mixed-comparison regressions remain nonzero. The original query interface and all fixed benchmark bounds are retained.

The public [point-pair certificate](../../AxiomaticGW/GKM/Fixtures/PlaneGenusTwoPointPair.lean), prepared before this continuation, also has a verified readable derivation: the complete ancestor product equation gives `29/2880 + 3*(-1/960) = 1/144`, and both descendant correction terms vanish. Its exact incoming GKM request is bound separately. Its geometric meaning uses the existing plane interpretation theorem and original inputs; it does not certify localization geometry or import CohFT classes.

### Verification and remaining scope

`lake build`, `lake test` and `lake lint` passed for the integrated library and regressions. The configured tests now include all 48 cache-based descendant computations and seven dimension-bound examples, including nonzero values at the exact boundary. The only reported integrated warning is the existing private-module warning in `AxiomaticGWTest/Basic.lean`. Exporter regeneration and all five Python test methods pass, including the actual kernel rejection cases. Eighteen public theorem axiom audits report only `propext`, `Classical.choice` and `Quot.sound`; the four highest-psi row audits are recorded separately.

The integrated checks do not establish the unfinished psi-three/four/five modules or final ancestor-table acceptance. The changes were reviewed against the protected pre-existing worktree; no comprehensive audit of that worktree, commit or push is claimed. The next gate is to finish those exact row proofs, assemble the existing table and query soundness theorems, then run the complete incoming GKM claim-binding suite. Both genus-two blowup reconstructions, general relation provenance, actual CohFT import and the offline research release remain required.

## 2026-10-04: Shared ancestor certificates and complete plane dependency closure

**Status:** Finite ancestor-cache soundness and its plane descendant consumer are proved and exposed through the public library. A native candidate calculation closes all 48 held plane requests on 39 full ancestor keys, retaining all 539 original boundary terms. Six low-psi and six total-psi-two rows are kernel checked. The remaining higher-psi row replay, the cached 48-query calculation and final acceptance are still in progress. The original two-marked Point-sector process continues unchanged. No additional numerical benchmark is counted as accepted from these unfinished jobs; the full goal remains active.

The [validation record](../../environments/genus-two-plane-ancestor-cache-validation.json) distinguishes completed commands, repaired development failures, source pins and the exact live handles. The preceding status-only turn is classified as a **verified wait**: it polled the original Point-sector handle and confirmed it was still running. This continuation adds the checked cache consumer, full candidate dependency closure, executable exporter and actual rejection tests.

### Scope and findings

- **Medium repeated-computation obstacle addressed:** The unchanged mixed comparison has 165 ancestor occurrences across its 48 requests, but only 39 distinct full keys. Expanding their complete original reductions introduces no additional keys. There are 539 uncollected boundary terms and five recursive ancestor occurrences; most repeated work is across requests, rather than repeated variables within a single boundary row. The cache preserves full class coordinates and paired state/power multiplicities, and does not merge queries by energy alone.
- **Medium proof-representation defect repaired in a positive control:** Bare CBV computes the boundary terms but does not establish equality of differently ordered multisets or extensionally equal curve-coordinate functions. The generated replay now checks their decidable equality. A full residual-key positive control passed in 72.359 seconds. The repaired six-row total-psi-two sector then passed in 258.543 seconds; the earlier failed bare-CBV run is retained separately.
- **Low generation issues repaired:** Splitting literal boundary data into one definition per row avoids an elaborator heartbeat limit without dropping terms. Public native entry points now reference public helpers. The registered executable supplies the native implementations required by its imported held-request module. Line-length and option-comment warnings are corrected. An old spelling of the empty-finset lemma in a regression was replaced with the current public API.

### Revisions and mathematical effect

`GenusTwoAncestorCertificate.lean` checks every selected genus-two row against either its original low-psi terminal value or the complete square/product equation, and checks membership of every residual dependency. Strict psi-degree induction proves `checkAncestorValues_sound`. `ancestorValueCached_eq` uses the original evaluator outside the cache. `PlaneGenusTwoAncestorCache.lean` substitutes this accepted family into the unchanged mixed comparison and proves equality with the existing full-query interface. Geometric interpretation additionally uses the existing accepted canonical table and its original degree bound. There are no new numerical seeds, geometric hypotheses, global rewrite attributes or instances, and existing theorem statements are unchanged.

`planeGenusTwoAncestorCache` exports complete candidate rows and all original incoming requests. Two native runs are byte-identical and both retain all 48 queries. The Python exporter validates exact fields, finite keys, dependency closure, strict descent and arithmetic consistency before generating separate data, boundary, descendant and assembly modules. These preflight checks and native agreement do not establish numerical acceptance. Every final claim still requires the actual Lean equations and the accepted canonical table.

### Validation and remaining work

- `lake build AxiomaticGW.Surfaces.GenusTwoAncestorCertificate AxiomaticGW.Surfaces.PlaneGenusTwoQueryCertificate AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneFewMarkingRequests AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneLine` passed the baseline.
- `lake build AxiomaticGW.Surfaces.PlaneGenusTwoAncestorCache` and `lake build planeGenusTwoAncestorCache` passed.
- `lake build AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsLowPsi` passed all six terminal proofs without warnings. `lake build AxiomaticGWTest.Surfaces.GenusTwoAncestorCertificate` passed thirteen public regressions, including actual partial-cache evaluation, the original fallback, and rejection of altered values, curves, states, powers, genus, omitted dependencies and boundary coefficients. A closed three-row cache certifies the original full descendant query `⟨τ₁(pt),τ₁(pt)⟩₂,H = 1/144`. This is an additional two-marked kernel regression; the complete 48-query acceptance remains pending.
- `python3 -B scripts/test_plane_genus_two_ancestor_cache.py -v` passed four test methods, covering all generated statements, all 48 GKM comparisons and 18 malformed-input cases. A coherent forged terminal value propagates consistently through every candidate equation and passes preflight, but its actual Lean proof is rejected; the matching positive control passes.
- `lake env lean /tmp/gw_ancestor_cache_axioms.lean` and `lake env lean /tmp/gw_ancestor_cache_product_axioms.lean` passed thirteen axiom audits, including the nonzero point-pair result and its actual product-relation row. Dependencies are only `propext`, `Classical.choice` and `Quot.sound`.
- The configured `lake build`, `lake test` and `lake lint` gates passed. These gates do not cover the pending higher-psi and final arithmetic fixtures. The only integrated warning is the previously recorded private-module warning in `AxiomaticGWTest/Basic.lean`; the final extended cache regressions also passed afterward.
- Native regeneration, source preservation, placeholder scans, line-length checks and `git diff --check` are recorded in the validation manifest. No original proof worker was restarted because an observation expired. The read-only process inspection initially met a sandbox denial; its approved narrow retry confirmed active CPU use. No automatic approval review rejected an action.

Next finish the remaining 27 ancestor rows of total psi degree three through six, certify the complete cached descendant calculation and connect its acceptance to the existing full incoming-claim tests. Both positive-degree genus-two blowup reconstructions, the full semisimple CohFT bridge, all fixed suites and the offline research release remain required. No commit or push was made.

## 2026-10-04: Complete plane genus-two canonical benchmarks and certified lookup

**Status:** Every fixed plane genus-two primary and first-descendant benchmark through anticanonical energy twelve now has kernel replay. The cubic and quartic scalar certificates, the complete twelve-query table and a bounded full-query lookup are accepted. The quartic triple is `(27, 42, 25/4)`. The public library exposes the new lookup. Configured build, tests and lint pass. The 45 two-marked plane certificates, both genus-two blowup reconstructions, full GKM/CohFT interoperability and the research release remain incomplete; the full goal remains active.

The [validation record](../../environments/genus-two-plane-scalar-replay-validation.json) consolidates the preceding symmetry/coefficient work, its terminal failures, the repaired exporter and the accepted table. The previous status turn discovered the terminal exporter failure and successful configured gates by polling their actual handles; that evidence determined this repair.

### Scope and findings

- **High replay obstacle resolved for the canonical plane suite:** The hybrid quartic attempt was intentionally terminated after its physical footprint reached 18.3 GB on the 16 GiB host. A later fast-CBV positive control still exhausted one million heartbeats on a zero coefficient. The final method checks constants with CBV and rewrites coefficient claims through a proved equality before `decide +kernel`. Its positive controls and coherent false-value tests now pass. The successful quartic replay retains all 504 original component statements, including zeros, and their full signed sums.
- **Medium repeated-work issue addressed:** `PlaneGenusTwoScalarSymmetry` permits reuse only when the transported state functions are equal. All six marking occurrences remain; the quartic has 196 arithmetic representatives. `PlaneGenusTwoFirstCoefficients` proves that primary main components contribute zero to a requested positive-psi coefficient, and that a single psi produces only such primary tail corrections. Its optimized vertex equals the original at every input and keeps the original fallback for primary requests and higher psi powers. These are uniform mathematical identities, not sampled formulas.
- **Medium research-interface gap addressed:** `PlaneGenusTwoBenchmarks` checks the complete incoming query, returns no result outside the positive-degree canonical suite, and proves that every returned value has an accepted full-query certificate. Its coverage theorem reuses the existing complete plane class enumeration through energy twelve. The geometric interpretation remains the original `planeCheckCanonicalClaim_checkedEval_from_geometry`.
- **Low generated-proof warnings repaired:** The table emitter used an unnecessary `<;>` after a single-goal normalization. The final sequential proof eliminates all four warnings. The first edit left the following tactic over-indented and failed parsing; the corrected generator and all affected modules then compiled without warnings. The arithmetic statements and public scalar/table APIs are unchanged.

### Revisions and mathematical effect

The scalar exporter now supports checked marking reuse and the proved coefficient shortcut without changing the default degree-two/three sources. Every original diagram, multiplicity, source-degree guard and effective remainder is preserved. No geometric input, numerical seed, global simp lemma or instance was added. The original three seeds remain `1`, `-1/8` and `-1/960`.

`planeCanonicalBenchmark?` accepts the entire ordered query, including genus, class, labels and powers. `planeCanonicalBenchmark?_sound` binds its result to the accepted table; `planeCanonicalBenchmark_coverage` covers every positive plane class of energy at most twelve. Eleven regressions cover the twelve-query family, the three nonzero quartic answers, the original reconstructed value, a certified zero, and rejection of zero degree, degree five, wrong genus and changed insertion powers. The README gives a public-library example returning `some 27`, with an unsupported request returning `none`.

### Validation

- `lake build AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneDegree3Scalars` completed successfully in 2633.540 wrapper seconds. Its nine-query assembled consumer and standard-axiom audit passed separately in 2.300 seconds.
- `lake build AxiomaticGW.Surfaces.PlaneGenusTwoScalarSymmetry AxiomaticGW.Surfaces.PlaneGenusTwoFirstCoefficients AxiomaticGWTest.Surfaces.PlaneGenusTwoScalarSymmetry AxiomaticGWTest.Surfaces.PlaneGenusTwoFirstCoefficients` passed the fresh continuation baseline in 1.326 seconds. The final new direct-coefficient implementation and nine regression examples had compiled in 23.425 seconds; its separate axiom audit passed.
- `python3 -B scripts/test_plane_genus_two_scalar_parts.py -v` passed all five methods in 32.311 wrapper seconds. These preserve every component and full query, reject 22 malformed inputs, reject an incorrect marking-state reuse hint, and reject coherent opposite component changes that leave every aggregate scalar unchanged.
- `lake build AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneDegree4Scalars` passed without warnings in 384.405 wrapper seconds; Lake displayed 415 seconds. Peak resident memory recorded by the wrapper was 7,867,711,488 bytes. An in-progress one-second sample measured a 5.7 GB physical footprint. These distinct measurements are retained in the record.
- `lake build AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneTable AxiomaticGW.Surfaces.PlaneGenusTwoBenchmarks AxiomaticGWTest.Surfaces.PlaneGenusTwoBenchmarks` passed after the warning repair in 5.915 seconds, without warnings.
- `python3 -B -m unittest discover -s scripts -p test_plane_genus_two_scalar.py -v` passed all three methods, including a coherent false-equation rejection, in 4.349 seconds. `python3 -B scripts/test_plane_genus_two_benchmarks.py -v` passed all three published-comparison and complete-export tests.
- `lake env lean /tmp/gw_plane_canonical_benchmark_axioms.lean` passed twelve axiom audits in 3.942 seconds. Dependencies are only `propext`, `Classical.choice` and `Quot.sound`. The same run returned `some 27`, `some 42`, `some (25 / 4)` and `none` for the documented supported/unsupported lookups.
- `lake build`, `lake test` and `lake lint` passed in 2.467, 27.169 and 9.857 seconds. They now include the full canonical plane table and benchmark interface: 2,909 build jobs and 3,009 test jobs. The only test warning is the existing private-module warning in `AxiomaticGWTest/Basic.lean`. These gates still do not accept the pending two-marked numerical fixtures.
- Exact regeneration of all three component fixtures and the complete table passes. Python syntax, touched Lean line-length and placeholder scans, source preservation and `git diff --check` pass. The producer checkout is clean and untouched. No Sage regeneration, commit or push was made.

### Remaining scope and next priority

The numerical values agree with the held published BP table, which shares the BP relation and lower-genus mathematical inputs; this is not independent verification of those foundations. The results remain conditional on named geometric relations, realization/intersection laws and the finite seeds. No semisimple CohFT class, R-matrix action or geometric localization derivation was imported.

The unchanged `PlaneGenusTwoFewMarkingsPoint` sector is now compiling its twelve two-marked requests. Its success is not assumed. Complete all 45 two-marked proofs, assemble all 48 held plane requests and run their full-query corruption tests. Both genus-two blowup recursions, every remaining fixed benchmark and the class-valued GKM/research-workflow gates remain required.

## 2026-10-04: Certified degree-zero genus-two descendants on all three targets

**Status:** The shared genus-two query `tau_2(1)` in degree zero now has kernel replay and conditional stable-map descendant interpretation on every fixed target: `7/640` on P², `7/720` on F₁, and `49/5760` on Bl₂P². The generic degree-zero comparison applies to every finite stable marking set. Configured build, test and lint gates pass. The running plane cubic certificate, quartic certificate, remaining 45 plane few-marking proofs, full blowup reconstruction and actual class-valued semisimple CohFT import remain open. The complete goal and all benchmark bounds are unchanged.

### Scope and findings

Reviewed the primitive mixed rational-tail step, the effective-monoid zero splitting law, mixed invariant definitions, the existing genus-two one-point ancestor theorem, its finite low-genus inputs, the held GKM degree-zero report and the actual query/provenance parser. The previous goal turn is a verified wait: it polled the original cubic session 94977 live, verified the prior source pins and reported status. This continuation again confirmed that same live session before making the changes below. This is a targeted extension, not a comprehensive audit of the existing dirty repository.

- **High interoperability gap closed within the three shared cases:** The previous numerical diagnostic compared stable-map descendant outputs from GKM with Lean ancestor values. It lacked a proved comparison identifying those specific ordinary descendant claims. The new theorem and consumer supply it directly from primitive rational-tail geometry.
- **Medium missing reusable theorem addressed:** `RationalTailIntersection.mixedInvariant_zero_class` proves equality with the ancestor of the pointwise sum of powers. The induction strictly lowers total stable-map power and preserves every state and marking. Its stable descendant specialization handles arbitrary finite arity, including empty genus-two markings, while retaining the stability hypothesis.
- **High claim-binding requirement implemented:** The new GKM exporter preserves the entire incoming query and ordinary value. Direct replay computes the existing algorithm in Lean; cached replay first checks equality of both the incoming request and value tables. Eight actual kernel corruptions are rejected after a successful control. Merely coherent equivariant and ordinary values do not constitute acceptance.

### Revisions and mathematical effect

`GW/Descendants/DegreeZeroComparison.lean` proves the generic mixed and pure descendant comparison from the absence of positive rational tails of class zero. `Surfaces/GenusTwoDegreeZeroDescendants.lean` adds a partial evaluator for exactly genus two, class zero, one marking and cotangent power at least two. Its final `degreeZeroOnePointQueryValue?_sound` uses the original four relation presentations, finite low-genus seeds, surface identification and named primitive geometry to conclude `SurfaceQuery.checkedEval U q = some claimed`. The intermediate ancestor identification is discharged by the existing theorem, not assumed in the final result.

The generated `GKM/Fixtures/GenusTwoDegreeZeroReplay.lean` checks all three actual held requests and values. The twelve public regression examples cover the three nonzero values, rejection of unsupported genus/class/power/arity, componentwise mixed-power addition, stable empty markings and consumption of all four original exported relation presentations. The public umbrella exposes the new consumer and fixture; existing definitions, theorem statements, seeds and global simp/instance behavior are unchanged. The producer checkout remains clean and untouched, and no Sage regeneration was performed in this continuation.

### Validation

- `lake build AxiomaticGW.Surfaces.GenusTwoOnePointAncestors AxiomaticGW.Surfaces.MixedAncestorReduction` passed the fresh baseline in 4.380 seconds.
- `lake build AxiomaticGW.GW.Descendants.DegreeZeroComparison` passed in 7.958 seconds; the final `lake build AxiomaticGW.Surfaces.GenusTwoDegreeZeroDescendants` passed in 6.136 seconds.
- `lake build AxiomaticGW.GKM.Fixtures.GenusTwoDegreeZeroReplay` passed in 15.645 seconds, with 2,085,502,976 bytes peak resident memory recorded by the wrapper.
- `lake build AxiomaticGWTest.Surfaces.GenusTwoDegreeZeroDescendants` passed all twelve public examples in 9.635 seconds without warnings.
- `python3 -B scripts/test_gkm_genus_two_degree_zero.py -v` passed all five test methods in 27.572 seconds (27.463 seconds reported by unittest). These include eight parser-level query/provenance mutations, a duplicate key, a coherent false zero, exact regeneration, and a positive kernel binding control followed by three false-value and five full-query rejections.
- `lake env lean /tmp/gw_genus_two_zero_axioms.lean` passed seven public axiom audits and printed the final hypothesis list in 3.780 seconds. Dependencies are only `propext`, `Classical.choice` and `Quot.sound`; no genus-two numerical seed or free ancestor family is in the final theorem.
- `python3 -B scripts/gkm_genus_two_degree_zero.py replay environments/gkm-genus-two-degree-zero.json --output AxiomaticGW/GKM/Fixtures/GenusTwoDegreeZeroReplay.lean --check` passed. Both edited Python files parse; the new Lean sources pass line-length and placeholder scans, and `git diff --check` passes.
- `lake build`, `lake test` and `lake lint` passed in 3.874, 83.350 and 54.152 seconds. The configured build covers 2,901 jobs and tests 2,998 jobs. They still exclude acceptance of the unfinished cubic/quartic and complete 48-query numerical fixtures. The only test warning is the existing private-module warning in `AxiomaticGWTest/Basic.lean`.

Three intermediate new-module builds failed during proof development: impossible list branches and singleton evaluation needed explicit simplification, and the `Fin 1` power comparison needed an explicit subsingleton equality before rewriting `Pi.single`. Those failures are retained separately from the successful final builds; no statement or hypothesis was weakened to repair them. An initial documentation patch failed its context check without changing a file, and a malformed tool orchestration call did not execute. Both were corrected. The [validation record](../../environments/genus-two-degree-zero-descendant-validation.json) records the commands, source pins, preservation audit and remaining live job.

### Remaining scope and next priority

These are conditional ordinary descendant certificates. They do not construct a surface's geometric GW theory, prove the producer's localization/specialization, or import a class-valued semisimple CohFT. GKM and Lean share target conventions and intersection-theoretic foundations, including admcycles/Hodge dependencies; that limitation remains explicit. Every required positive-degree and few-marking benchmark stays in scope.

The original cubic worker remains active. A read-only sample at 12:09 UTC reported a stable 10.2 GB physical footprint and active kernel reduction; a subsequent process check showed it using CPU. It was neither restarted nor interrupted in this continuation. Finish that certificate, then the quartic and full twelve-query table, and complete the remaining two-marked plane sectors. Next complete both genus-two blowup recursions and the actual semisimple CohFT bridge. No commit or push was made; the full goal remains active.

## 2026-10-04: Component scalar replay and three certified plane descendants

**Status:** The complete native plane few-marking calculation finished and agrees with every one of the 48 pinned GKM candidates. The one-point arithmetic module now compiles, and a separate consumer composes it with the accepted canonical line table to certify the original descendant algorithm at all three one-marked requests. The complete degree-two component certificate now passes, including all 360 contributions and their assembly into the original six scalars. Configured build, test and lint gates pass. Higher-degree scalar certificates and 45 two-marked proofs remain pending. All three application targets and the complete R0--R8 objective remain unchanged.

### Scope, findings and mathematical effect

- **High resource obstacle:** The previous degree-two monolithic scalar worker had a measured physical footprint of about 20 GB on the 16 GiB host. It was intentionally terminated with SIGTERM, reporting leaf exit 143 and build exit 1. This is neither a mathematical counterexample nor a successful certificate. The preceding memory queue subsequently resumed the preserved genus-one worker after both plane jobs completed.
- **Medium proof-reuse issue addressed:** `PlaneGenusTwoScalarParts` proves exact decomposition into the original diagrams and all six marking assignments. A constant has 96 contributions; an earlier coefficient has 24. The new exporter checks each contribution separately, then sums the proved rational values. The regenerated degree-two fixture preserves its public `constants` and `coefficients_0_1` statements. No zero contribution, cotangent correction, marking multiplicity or source-degree guard is removed.
- **High numerical application gap narrowed:** `AxiomaticGWTest/GKM/PlaneGenusTwoOnePoint.lean` proves the original query values for `tau_5(1)`, `tau_4(H)` and `tau_3(pt)` in plane degree one: `1/128`, `-1/960` and `-1/240`. Its theorem uses the existing accepted canonical table. The geometric soundness theorem and exactly three original seeds remain unchanged. Native agreement for the remaining 45 queries is not kernel acceptance.
- **Low documentation defects repaired:** The first configured lint run found ten missing definition docstrings in the earlier genus-two marking selectors, ancestor evaluator and generated line/request fixtures. Their descriptions and both fixture generators are now updated. A comparison with the protected sources confirms that the four Lean files changed only in docstrings; definitions and proofs are identical.

The source decomposition holds uniformly, including at degree zero. Its public audit checks the nonzero initial constant and rejection of an earlier class greater than the source before natural subtraction. No foundational definition, existing theorem statement, geometric assumption, numerical seed or global rewrite attribute changed.

### Validation

- `lake build AxiomaticGW.Surfaces.PlaneGenusTwoScalarParts` passed; the fresh baseline took 4.499 seconds. `lake env lean /tmp/gw_scalar_parts_audit.lean` passed two boundary examples and four axiom audits in 10.321 seconds. Only `propext`, `Classical.choice` and `Quot.sound` occur.
- `lake env lean --run scripts/PlaneGenusTwoScalar.lean --parts 4 /tmp/gw_plane_scalar_parts_candidates.json` finished in 267.043 seconds. Removing the additional components gives the entire original report exactly, including every full request, dependency, coefficient and value. All twelve queries match the held published manifest. The saved component report is candidate data.
- `lake env lean /tmp/gw_scalar_component_pilot.lean` certified the nonzero degree-two contribution `243/80` in 2.360 seconds, with a standard-axiom audit.
- `lake build AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneDegree2Scalars` passed without warnings. The wrapper records 469.604 seconds and 4,033,888,256 bytes peak resident memory; Lake's displayed elapsed time was 491 seconds. Both readings are retained in the raw record. Degrees three and four were then regenerated with the same complete component coverage; degree three is compiling first.
- `lake env lean /tmp/gw_plane_degree_two_table_audit.lean` passed in 4.067 seconds. The existing table exporter composes the accepted line and degree-two scalars, certifies every row through degree two and all six full positive-degree canonical requests, and audits both public scalar theorems plus table acceptance and claims. Only standard Lean axioms occur. Two `unnecessarySeqFocus` warnings come from the existing table emitter's unchanged `norm_num ... <;>` sequence; the new scalar fixture itself has no warning.
- `python3 -B scripts/test_plane_genus_two_scalar_parts.py -v` passed all three tests in 13.230 seconds: complete aggregate/query preservation and generated coverage, twenty-two malformed inputs, and a real Lean positive control followed by rejection of a coherent `+1,-1` component forgery. The forgery preserves every aggregate scalar and reconstructed value. Generation retains 360, 360 and 504 component obligations at degrees two, three and four.
- The existing `lake exe planeGenusTwoFewMarkings environments/genus-two-plane-few-markings-native.json` run finished successfully in 5,183.017 seconds including its dependent rebuild. All 48 requests and values match the pinned producer. Five available `test_gkm_plane_few_markings.py` methods pass, including all twenty GKM/Lean preflight corruptions. The full-fixture kernel binding test still awaits the two-marked sectors.
- `lake build AxiomaticGW.GKM.Fixtures.PlaneGenusTwoFewMarkingsOnePoint` completed in 1,784.173 seconds. `lake build AxiomaticGWTest.GKM.PlaneGenusTwoOnePoint` then passed in 4.969 seconds. Its acceptance axiom audit passed in 7.786 seconds, again with only standard Lean axioms.
- The three existing published-benchmark tests and two existing scalar preflight tests pass. The new degree-two exporter `--check`, Python syntax and `git diff --check` pass. Higher-degree vector formatting was wrapped before generation; degree-two source remained byte-identical during its running build.
- The preserved `lake build AxiomaticGWTest.Surfaces.PlaneGenusTwoCertificate AxiomaticGWTest.Surfaces.GenusOneCertificate` run finished successfully in 13,953.750 seconds. The configured `lake build` and `lake test` then passed. The initial `lake lint` failure was isolated to the ten missing docstrings above. All four documented modules compile, the three line-export tests including real kernel binding pass, and the five available few-marking exporter tests still pass.
- After those documentation fixes, `lake build`, `lake test` and `lake lint` passed in 3.639, 34.366 and 32.507 seconds respectively. The configured build covers 2,898 jobs and tests 2,994 jobs; it does not accept the separately pending degree-three/four or full few-marking fixtures. The only configured test warning is the existing private-module warning in `AxiomaticGWTest/Basic.lean`.

The [validation record](../../environments/genus-two-plane-scalar-parts-validation.json) preserves commands, source pins, the intentional interruption and current pending jobs. The degree-two component worker was observed using a 3.1 GB physical footprint at 11:35 UTC; this is an in-progress measurement, not a completed peak-memory guarantee. The cubic worker later occupied 10.2 GB while the remaining one-point test occupied 4.9 GB. A temporary supervisor preserved the cubic worker with SIGSTOP and automatically resumed it after the successful full test run; the supervisor has completed. The previous status review discovered the successful one-point arithmetic build, enabling the accepted-table composition above. No commit or push was made.

### Remaining work and next priority

Check the running degree-three certificate, regenerated degree four and the assembled twelve-query table. Complete the three two-marked arithmetic sectors and their full-query corruption test, then revalidate their integration. Both genus-two blowup reconstructions, actual class-valued semisimple GKM import and the research release remain required.


## 2026-10-04: Reusable plane few-marking arithmetic certificates in progress

**Status:** The first independent arithmetic pilot passed: the original descendant calculation against the literal line candidate table returns `1/128` for the held one-marked `tau_5(1)` query. This is not yet acceptance of that canonical table or of the complete 48-query suite. The exporter now separates four reusable numerical sectors from final table acceptance. The common data module compiles without warnings, and kernel checks preserve all original incoming queries and values. Numerical-sector compilation, final acceptance, the higher-degree plane table and integrated validation remain pending. The full R0--R8 goal and all three application targets remain unchanged.

The [arithmetic validation record](../../environments/genus-two-plane-few-marking-arithmetic-validation.json) separates successful commands, the intentional source-warning repair, and live jobs. The preceding status turn completed the original single-query pilot and verified the prior source pins; it therefore supplied evidence for this implementation step.

### Scope, findings and revisions

- **Medium proof-reuse obstacle addressed:** The old numerical module imported the canonical line certificate before performing any arithmetic. The new data module and four computation modules can be checked independently of that certificate. Each complete input query and incoming value remains explicit. The final assembly identifies its literal candidate table with `GenusTwoPlaneLine.values` and invokes the existing acceptance theorem before recovering `planeQueryValue?`.
- **High application gap remains:** Generated claims and the single-query pilot do not complete the required numerical suite. No generated sector or assembly is counted as accepted until its actual Lean build succeeds. The complete native comparison and coherent false-value binding test still await their prerequisites.
- **Low generated-source warnings repaired:** The first data build reported an unscoped heartbeat option and an overlong literal array. The exporter now scopes large heartbeat limits to the numerical declarations and wraps that array. Its new arithmetic process was explicitly terminated to make this correction; none of the three older proof jobs was discarded or restarted.

The optional `replay --split-computation` export produces one data module, four arithmetic sectors (3, 18, 15 and 12 claims), and the final assembly. Public request, value, coverage, computation and acceptance declarations retain their statements. The original direct export and cached `bind` output are byte-for-byte unchanged. The numerical calculations use only proved lower-genus caches, and the same vector-lookup equality is activated locally in each sector. There are no new global rewrite attributes, geometric hypotheses or numerical seeds.

### Validation and remaining work

- The baseline `lake build AxiomaticGW.Surfaces.PlaneGenusTwoQueryCertificate AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneFewMarkingRequests AxiomaticGW.Surfaces.Fixtures.PlaneGenusOneSupport` passed in 10.473 seconds.
- The corrected `PlaneGenusTwoFewMarkingsData` module built without warnings as a dependency of the active numerical-sector build.
- `lake env lean /tmp/gw_plane_few_split_data_audit.lean` passed in 87.280 seconds. It checks equality with every saved original request and value and audits six preservation/support theorems; only `propext`, `Classical.choice` and `Quot.sound` occur.
- The three selected exporter methods in `scripts/test_gkm_plane_few_markings.py` pass: deterministic generation, complete split-claim coverage and the existing eleven malformed-input cases. The split exporter `--check` passes. The first Python invocation used the wrong module search path; its failure is retained separately from the successful direct script invocation.
- `git diff --check`, Python syntax, generated Lean line-length and placeholder scans pass. The protected 711-file snapshot has no missing original files or unrelated edits.
- The original independent pilot `lake env lean /tmp/gw_plane_few_marking_cbv_independent.lean` completed in 395.000 seconds with a standard-axiom audit. Its literal table is a candidate until composed with the canonical acceptance theorem.

The complete one-marked sector is being compiled. A separate `cbv` pilot for the degree-two constant `81/20` was intentionally terminated after 791.266 seconds without an accepted result: direct system measurements showed 16 GiB of physical memory, about 30 GiB of swap in use and all five expensive proof workers waiting on memory. This is a resource diagnostic, not a mathematical counterexample or successful scalar certificate.

The native plane build and one-marked sector continue. A monitored scheduling process temporarily suspends the existing genus-one and degree-two workers without discarding their progress. It automatically resumes the degree-two worker after both current plane jobs exit, then resumes the genus-one worker after degree two exits; worker exit alone is never treated as successful proof acceptance. The queue record and session are recorded in the validation manifest. The two-marked sectors, full assembly, numerical corruption tests, remaining scalar degrees and fresh integrated build/test/lint are required next. No commit or push was made.

## 2026-10-04: Complete few-marking request domains and bounded plane certificates

**Status:** The unchanged genus-two few-marking domain now has a complete Lean enumerator for all three fixed targets. The held manifest has 5,199 ordered requests: 48 plane, 656 one-blowup and 4,495 two-blowup cases, with matching Lean interpreter counts. The plane request list additionally has kernel-checked finite coverage, injectivity and arity counts. Its bounded descendant claim checker is proved sound against the original algorithm. Full numerical computation and kernel replay of the 48 plane values remain in progress; the blowup values, remaining R7 suites and actual class-valued GKM import remain required.

The [scoped validation record](../../environments/genus-two-few-markings-validation.json) records source pins, exact completed checks and explicitly pending jobs. This is a targeted continuation, not a fresh integrated build or a comprehensive review of the dirty repository.

### Scope, findings and revisions

- **High benchmark-coverage gap addressed:** `SurfaceGenusTwo.mem_fewMarkingQueries_iff` proves exact coverage from the original positive-class, energy-four, arity-two and signed dimension conditions on every fixed target. Full curve coordinates and ordered state/power pairs are retained. The power bound is seven on the blowups, rather than the plane-specific six. The Python manifest is frozen independently of numerical answers, keeps one complete request per line, and preserves the old plane subset exactly. Its serialization checks are distinct from the Lean completeness proof.
- **High claim-binding gap addressed in the carried implementation:** `MixedAncestorBounds.lean` proves bounded substitution through every rational-tail transfer. `planeDescendantValueWith_eq`, `planeQueryValueWith?_eq` and `planeCheckDescendantClaim_sound` use an accepted canonical table without losing genus, full class, ordered insertions or the claimed rational value. Six regression examples passed, including actual degree-zero descendant evaluation and rejection of a false value, wrong genus and out-of-range class. A fresh downstream build after the following representation change passed all 25 claim, descendant and ancestor regression examples.
- **Medium runtime defect corrected, with integration pending:** A native stack sample identified recursive `Fin.cases` lookup during product-relation initialization. Three existing tables now use arrays: the 38 boundary coefficients and the 25 boundary indices and decorated expressions. Kernel equality proofs against the saved pre-edit vectors show that every coefficient and term is unchanged. The direct consumers, both L24 replays, the plane geometric reconstruction and its direct regression consumers compiled. The numerical line-table and executable rebuild is still in progress. The old diagnostic run was deliberately stopped after identifying the defect, not treated as a successful numerical computation.
- **Medium exchange cost addressed, pending its numerical prerequisite:** `gkm_plane_few_markings.py bind` emits a short proof checking both incoming queries and values against the complete checked fixture. A coherent false-value regression is prepared. Neither is counted as successful kernel replay until the full numerical fixture compiles. The existing exporter still emits the unchanged direct-computation proof source.

No seed, geometric hypothesis, theorem conclusion, global simp lemma or instance was added to the reconstruction. The fixed targets and every acceptance bound are unchanged. The general enumerator and its optimized plane specialization are proved equivalent in a public regression. No mathematical defect was found in the focused previously accepted query or bounded-tail definitions.

### Validation and evidence

- `lake build AxiomaticGW.Surfaces.Queries AxiomaticGW.Surfaces.PlaneGenusTwoFewMarkings` passed the continuation baseline.
- `lake build AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneFewMarkingRequests` passed the 48-request coverage, injectivity and 0/3/45 arity counts.
- `lake build AxiomaticGWTest.Surfaces.PlaneGenusTwoQueryCertificate AxiomaticGWTest.Surfaces.PlaneGenusTwoDescendants AxiomaticGWTest.Surfaces.GenusTwoAncestors` passed all 25 examples after the array-dependent rebuild, including the existing product-relation replay.
- `lake build AxiomaticGWTest.Surfaces.GenusTwoFewMarkings` passed the general completeness theorem and seven examples, including exceptional classes, a fiber, the maximal power seven and degree-zero exclusion.
- `lake env lean /tmp/gw_plane_few_marking_array_equivalence.lean` passed all three table equalities against the saved vectors.
- `lake env lean /tmp/gw_plane_few_marking_api_axioms.lean` and `lake env lean /tmp/gw_all_surface_few_marking_axioms.lean` and `lake env lean /tmp/gw_plane_descendant_claim_axioms.lean` passed fourteen public axiom audits. All use only `propext`, `Classical.choice` and `Quot.sound`.
- `lake env lean --run /tmp/gw_all_surface_few_marking_counts.lean` completed and returned 48, 656 and 4,495. These interpreter counts supplement the coverage theorem; they are not numerical GW certificates or kernel cardinality proofs for the blowups.
- `python3 -B scripts/test_genus_two_few_marking_requests.py` passed both tests, including unchanged plane requests, no duplicate full queries, complete class counts and the independent classwise one-/two-marking count formulas.
- `python3 -B scripts/genus_two_few_marking_requests.py --output environments/genus-two-few-markings-requests.json --check` passed deterministic regeneration.
- The two plane export tests independent of numerical replay passed, including eleven malformed-request, provenance or coefficient-coherence rejections. Full comparison and kernel corruption tests await the numerical fixture.

Development errors in a consumed hypothesis and empty-list dependent transport were repaired without changing the statements. A single-query optimized replay pilot failed to load the L24 artifact while that exact dependency was being rebuilt; no numerical proof was accepted from the pilot. The subsequent L24 correction replay finished successfully after 1,234 seconds and its initial-expression replay after 292 seconds. Their plane geometric consumers and the fresh descendant regressions also passed. No live process was restarted merely because a polling observation expired.

### Remaining work and next priority

The preceding status-only goal turn is classified as a **verified wait**: it polled the specific native build, genus-one downstream rebuild and degree-two scalar handles, all confirmed live. This continuation made progress through the general coverage theorem, frozen full request manifest, completed audits and exchange work. The same three original jobs remain under observation; successful completion is recorded only after their handles return a terminal result.

Next finish the 48-query plane calculation and kernel fixture, then run its full incoming-claim tests. Fresh direct dependent checks now pass. Complete degree-two through degree-four scalar certificates and integrated build/test/lint, followed by the full genus-two blowup algorithms and semisimple CohFT bridge. No commit or push was made. The full goal remains active.

## 2026-10-04: Conditional reconstruction of every plane genus-two descendant

**Status:** Every finite genus-two plane basis query now has a terminating evaluator and a theorem identifying its checked geometric value under the original relation/intersection inputs and exactly three finite seeds. The ancestor proof closes the low-psi and lower-genus identifications; the descendant proof uses the existing reconstructed calibration and primitive rational-tail comparison. This completes the plane theorem-level descendant composition. R7 remains open for the fixed numerical suites and both blowups; the full class-valued GKM and release gates are unchanged.

The [validation record](../../environments/genus-two-plane-descendant-validation.json) records current source pins, exact commands, corrected development failures and the still-running certificate jobs. This is a targeted implementation and review, not a comprehensive audit of the dirty repository.

### Scope and findings

Reviewed the actual square/product selector, occurrence-frame transport, strict psi and full-class support bounds, plane low-psi identification, mixed ancestor reduction and reconstructed calibration. The preceding status turn observed the existing line/GKM rebuild finish successfully; this evidence enabled the scalar exchange and public-audit checks completed here. Both remaining long-running sessions were revalidated without restart.

- **Critical carried development failure corrected:** The unfinished `GenusTwoAncestorGeometry.lean` failed while elaborating insertion transport from a query whose genus is propositionally two. An intermediate equality resolves elaboration without changing the statement. A subsequent downstream build exposed a private auxiliary proof in an exported row-index type; using the definitionally identical public `Fin.castAdd` embedding removes that dependency.
- **High application gap closed for the plane:** `planeAncestorValue_eq_eval`, `planeDescendantValue_eq` and `planeQueryValue?_eq_checkedEval` now compose the original geometric equations with the finite-seed algorithms. No final recurrence, free ancestor family or calibration oracle remains in the final query theorem.
- **Medium computational reuse gap addressed:** `ancestorValue_congr` uses proved nonincreasing class energy to restrict terminal-family agreement to a bound. `planeAncestorValueWith_eq` therefore permits any accepted canonical table to evaluate all ancestors in its certified degree range, independently of marking count and cotangent power.

### Revisions and mathematical effect

`GenusTwoAncestorGeometry.lean` proves frame transport, interpretation of both selected geometric steps and soundness of the generic terminating ancestor recursion once its terminal values are identified. `PlaneGenusTwoDescendants.lean` supplies the plane ancestor and stable-map descendant evaluators and ordered query interface. Genus two is curve-stable at every arity, so the theorem includes empty markings and degree zero. Other genera are rejected by this genus-specific interface.

The final numerical assumptions are precisely the rational line value 1, elliptic hyperplane value −1/8 and genus-two hyperplane value −1/960. Original square/product generator hypotheses and primitive geometry remain explicit. The square elliptic row is supplied by the existing genus-one row, and the three product component rows by BP source indices 4, 5 and 13. No duplicate source-vanishing hypothesis or new numerical seed is added. Existing public statements and global simp/instance behavior are preserved; the row-index presentation change is definitionally equivalent.

Eight new public regression examples include the actual ordered descendant results `⟨τ₂(1)⟩₂,₀ = 7/640` and `⟨τ₁(H),τ₁(1)⟩₂,₀ = -1/320`, reordering, empty markings, unsupported genera, bounded table substitution and consumption of all six held relation presentations. The numerical equalities are kernel computations of the proved algorithm; their geometric interpretation retains the stated hypotheses. The first value also agrees with the existing pinned GKM degree-zero diagnostic, whose localization derivation and CohFT classes are still not certified.

### Validation

- `lake build AxiomaticGW.Surfaces.GenusTwoAncestors AxiomaticGW.Surfaces.PlaneGenusTwoLowPsi AxiomaticGW.Surfaces.MixedAncestorReduction` passed as the baseline.
- `lake build AxiomaticGW.Surfaces.GenusTwoAncestorGeometry` passed after repairing the carried elaboration error.
- `lake build AxiomaticGW.Surfaces.PlaneGenusTwoDescendants` passed with all final source changes, including bounded table substitution.
- `lake build AxiomaticGWTest.Surfaces.PlaneGenusTwoDescendants AxiomaticGWTest.Surfaces.GenusTwoAncestors` passed all eight new examples and eleven existing recursion examples, without warnings.
- `lake env lean /tmp/gw_plane_descendants_axioms.lean` passed twelve public axiom audits and printed the final query theorem's complete input list. Dependencies are only `propext`, `Classical.choice` and `Quot.sound`.
- The previously running `lake build AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneLine AxiomaticGW.GKM.Fixtures.PlaneGenusTwoLineReplay` completed successfully. `lake env lean /tmp/gw_plane_scalar_publish_axioms.lean` then passed all ninety-three pending scalar/line/GKM public audits with only standard axioms.
- `python3 -B scripts/test_plane_genus_two_scalar.py` and `python3 -B scripts/test_gkm_plane_genus_two.py` each passed three tests, including actual kernel rejection of a coherent forged equation or changed answer.
- `python3 -B scripts/gkm_genus_two_degree_zero.py check environments/gkm-genus-two-degree-zero.json` passed the three held comparisons; this did not rerun Sage or certify localization.
- `python3 -B scripts/check_plane_genus_two_benchmarks.py environments/genus-two-plane-scalar-native.json` still matches all twelve published queries. Degree-two and higher scalar kernel replay remains separate.

New development errors in a shadowed hypothesis name, exported proof reference, proof-goal ordering and test simplification were repaired. A diagnostic attempt to print the generated private identifier used invalid Lean name syntax; that scratch command's failure is recorded, not counted as a successful audit. The final public audit and downstream fixture consumer pass. The sandbox initially denied a read-only process listing; the approved narrow retry confirmed both original Lean processes were actively using CPU. No automatic approval review rejected an action.

### Remaining work and next priority

The genus-one two-point-blowup downstream rebuild and degree-two scalar certificate remain live. Degree-three/four scalar replay, the complete plane table, the fixed higher-power few-marking suite and integrated build/test/lint remain pending. No duplicate full build was started while the existing dependent rebuild was running. Prior integrated validation remains historical evidence, not validation of every current file.

Next finish the plane numerical certificates and few-marking suite, then complete the genus-two blowup recursions and actual semisimple CohFT bridge. Existing degree-zero one-point ancestor results also offer a direct route to shared nonzero GKM descendant certificates on all three targets once their comparison is composed. No commit or push was made; the full goal remains active.

## 2026-10-04: Low-psi plane queries and terminating genus-two ancestor reduction

**Status:** The plane evaluator now covers arbitrary finite insertion lists with total psi degree at most one, with geometric interpretation under the unchanged inputs and three seeds. Both complete square/product reductions are derived from their original geometric generators after arbitrary added markings. Executable marking selection and a terminating ancestor recursion have strict psi descent, sufficient-fuel independence and uniqueness relative to the low-psi terminal family. The final plane geometric consumer and higher-power stable-map descendant comparison remain required. R7, both blowups, the numerical certificate gates and full class-valued GKM interoperability remain open.

The [validation record](../../environments/genus-two-psi-reduction-validation.json) records the source hashes, successful checks, intermediate development failures and still-running certificate jobs. The full objective and every fixed benchmark are unchanged.

### Scope and findings

Reviewed the existing direct normalization, canonical plane interpretation, original marked square/product relations, signed marking pullback, codimension and edge-count bounds, lower-genus surface contractions and sorted query frames. The preceding status-only turn is conservatively classified as no progress; this turn revalidated the live process handles and made the mathematical changes below. This is a targeted extension, not a comprehensive review of the dirty repository.

- **High application gap advanced:** Arbitrary low-psi plane queries now reduce to the already reconstructed canonical triple, preserving every ordered state/power occurrence. An accepted bounded canonical table also evaluates these queries throughout its certified range.
- **High reconstruction gap addressed:** The actual signed pullback is proved equal to one smooth leading monomial with coefficient one plus a boundary remainder. Every remainder term retains codimension two and a positive edge count. Its residual genus-two dependencies have strictly smaller total psi degree, with the full effective class retained. No signed correction is omitted, including corrections of the product relation's genus-two tail.
- **Medium executable-interface gap addressed:** A finite selector chooses a square or two distinct positive occurrences. The marking frame carries states and powers together, and lowering removes exactly two powers. Structural recursion now has a proved sufficient bound and uniqueness relative to its terminal family.
- **Remaining high gap:** The final theorem must compose the recursive query transport and both geometric reduction theorems with the proved plane low-psi interpretation. The generic low-psi parameter is not a newly assumed geometric seed family. Neither this parameterized uniqueness theorem nor the finite regression is claimed as completed arbitrary-descendant reconstruction.

### Revisions and mathematical effect

`LowPsiDescendant.lean` identifies primary descendant keys and proves direct normalization for total psi degree at most one at genus at least two. `PlaneGenusTwoLowPsi.lean` supplies the plane evaluator, finite-table replacement theorem and full ordered `checkedEval` interpretation. Its descendant interpretation uses string, dilaton and divisor laws; its ancestor interpretation additionally uses the existing rational-tail comparison and proved plane cancellation. The comparison is not generalized silently to either blowup.

`GenusTwoPsiSupport.lean` isolates the leading term and proves codimension, edge, genus, dimension, class and strict psi bounds for the complete residual polynomials. `GenusTwoPsiReduction.lean` derives their surface interpretation from the original six square interior rows and elliptic source, or the original ten product interior rows and three component sources, together with the existing primitive realization laws and lower-genus identifications.

`GenusTwoAncestorMarkings.lean` implements both selections and proves exact power restoration. `GenusTwoAncestors.lean` applies the corresponding signed relation and recurses on total psi degree. It consults its terminal family only at total psi degree at most one. No original theorem signature, numerical seed, global instance or simp attribute changes. The public umbrella and scoped documentation expose the additions; unrelated work and the GKM producer are preserved.

### Validation

- `lake build AxiomaticGW.Tautological.GenusTwoPsiForgetful AxiomaticGW.Surfaces.DecoratedTermDegree` passed as the baseline.
- `lake build AxiomaticGW.Surfaces.PlaneGenusTwoLowPsi AxiomaticGWTest.Surfaces.PlaneGenusTwoLowPsi` passed; its twelve regression examples cover degree zero, repeated-divisor corrections, string/dilaton normalization and reordered insertions. Literal quartic triples in these tests check normalization arithmetic only.
- Targeted builds of `AxiomaticGW.Surfaces.GenusTwoPsiSupport`, `AxiomaticGW.Surfaces.GenusTwoPsiReduction`, `AxiomaticGW.Surfaces.GenusTwoAncestorMarkings` and `AxiomaticGW.Surfaces.GenusTwoAncestors` all passed without warnings.
- `lake build AxiomaticGWTest.Surfaces.GenusTwoPsiReduction` passed eight examples, including preservation of the held Sage pullback expression, the negative genus-two tail coefficient and exact boundary evaluation `-1/320` from the certified degree-zero triple.
- `lake build AxiomaticGWTest.Surfaces.GenusTwoAncestors` passed eleven examples, including reversed marking frames, repeated positive insertions, exact power lowering, fuel independence and the same nonzero value through actual recursive query selection.
- Three `lake env lean` audit files checked eleven low-psi declarations, twenty-five reduction declarations and thirty-six marking/recursion declarations. All seventy-two audits passed with at most `propext`, `Classical.choice` and `Quot.sound`; no placeholder or substitute axiom was added.
- `python3 -B scripts/check_plane_genus_two_benchmarks.py environments/genus-two-plane-scalar-native.json` still matches all twelve full published requests. This remains separate from pending higher-degree kernel replay.

Intermediate elaboration errors in new proofs and test constructors were repaired, and the axiom-audit generator was corrected to ignore a comment line. The exploratory interpreter process was deliberately stopped after the overlapping kernel regression succeeded; its exit 143 is recorded as a resource-management cancellation, not as successful computation. No live certificate process was restarted because an observation expired.

### Remaining work and next priority

At the last process inspection, the existing line/GKM rebuild, genus-one two-point-blowup consumer rebuild and degree-two scalar certificate were still live. Degree-three/four scalar replay, the full plane table, dependent exchange checks, full build/test/lint and the scalar public audit remain pending. Previous integrated validation is retained as a historical checkpoint, not represented as validation of every current file.

Next compose the actual query-frame reductions with the original geometric inputs and plane low-psi theorem, then derive the complete stable-map descendant evaluator. Continue the same live scalar certificate jobs. Both blowup reconstructions, all fixed suites, actual semisimple CohFT import and the reproducible research release remain required. No commit or push was made; the goal remains active.

## 2026-10-04: Complete plane candidates and geometric certificate interpretation

**Status:** The interpreted plane calculation through degree four completed, and all twelve full queries match the independently held published BP table. A new final interpretation theorem turns an accepted canonical certificate into the requested geometric `checkedEval` result under the existing class-level inputs and the same three finite seeds. The higher-degree scalar certificates, final line/GKM rebuild and genus-one downstream rebuild remain in progress. R7 and the full semisimple CohFT contract remain open.

The [benchmark validation record](../../environments/genus-two-plane-benchmark-validation.json) records the completed commands, source pins, prerequisite failure and explicitly pending checks.

### Scope and findings

Reviewed the complete candidate payload, all earlier nonzero dependencies in each equation, full ordered query coverage, the scalar exporter and its table assembly, and the existing geometric reconstruction theorem. The previous status turn made concrete progress by observing successful completion of the specific degree-four run and comparing all twelve held published requests. This is a targeted review, not a comprehensive audit of the dirty repository.

- **High application gap advanced:** The complete candidate table now returns `(0,0,0)`, `(0,0,0)`, `(0,-1/4,-1/12)` and `(27,42,25/4)` in degrees one through four. The published comparison passes for every full request. Higher-degree kernel acceptance is still required.
- **Medium reusable-interface gap closed:** `PlaneGenusTwoClaim.lean` proves geometric admissibility of every canonical query and derives `query.checkedEval U = some claimed` from the actual claim checker and `planeCanonicalValues_from_geometry`. Its geometric and seed hypothesis list is copied unchanged from the existing theorem; it does not assume the desired recurrence or an invariant family.
- **Medium proof-maintenance gap addressed:** The exporter can place closed arithmetic proofs in separate modules for degrees two, three and four. The short table assembly reuses their named scalar theorems, retaining all complete constants and coefficients of nonzero earlier values. Existing monolithic output is unchanged byte for byte at bounds one and four.
- **Low documentation defect repaired:** The README's older statement that no evaluated genus-two benchmark was claimed conflicted with its checked line results. The current overview now distinguishes certified line values, the complete numerical candidate comparison and pending higher-degree proof replay.

### Revisions and mathematical effect

The saved report is `environments/genus-two-plane-scalar-native.json`; despite the historical filename, its producer ran through Lean's interpreter. Its SHA256 is `ccf66a351c974d15aabe21613a4cfa2e90db20aaf28d273765583e50e587b862`. It records all three equations per degree, their full lower-genus constants and every coefficient multiplying a nonzero earlier value. The quartic rows retain both nonzero cubic descendants. No expected reference value was substituted into the calculation.

`export_plane_genus_two_scalar.py --split-scalars` emits the three `GenusTwoPlaneDegree*Scalars.lean` modules and `GenusTwoPlaneTable.lean`. Those files remain pending validation artifacts until their builds succeed; their presence is not a certified quartic result. `test_plane_genus_two_benchmarks.py` checks the complete published comparison and rejects a different quartic system even when its altered constants and answer are internally consistent.

`PlaneGenusTwoClaim.lean` composes two existing soundness results and is imported by the public umbrella. Its domain lemma uses genus-two stability, including degree zero. Existing theorem signatures, geometric hypotheses, numerical seeds, global instances and simp lemmas are unchanged. The producer checkout and full goal are unchanged.

### Validation and pending work

- `lake build AxiomaticGW.Surfaces.PlaneGenusTwoCertificate` passed as the baseline.
- `lake env lean --run scripts/PlaneGenusTwoScalar.lean 4 /tmp/gw_plane_scalar_supported_candidates.json` completed with exit zero in 855.755 seconds.
- `python3 -B scripts/check_plane_genus_two_benchmarks.py environments/genus-two-plane-scalar-native.json` passed all twelve complete published requests.
- `python3 -B scripts/test_plane_genus_two_benchmarks.py` passed three methods, including coherent-forgery rejection and complete split-export obligations.
- The split exporter `--check` reproduced all four generated modules byte for byte.
- `lake build AxiomaticGW.Surfaces.PlaneGenusTwoClaim` passed without warnings. `lake env lean /tmp/gw_plane_claim_axioms.lean` audited both new public theorems successfully; only `propext`, `Classical.choice` and `Quot.sound` occur.
- An early rerun of `scripts/test_plane_genus_two_scalar.py` failed because the line scalar `.olean` was absent during its active rebuild. Both its positive and negative kernel cases reported that missing import. This is recorded as an incomplete prerequisite check; it is not counted as successful corruption rejection. Retry after the same live line build finishes.

The degree-two scalar proof build, final line/GKM rebuild and existing genus-one two-point-blowup consumer rebuild were polled live. No process was restarted because an observation expired. Full build/test/lint and the full degree-four certificate are still required.

### Next priority

Complete the scalar kernel certificates, replay the full plane table and its exact query claims, then finish arbitrary genus-two descendants, both blowup applications and the required class-valued GKM bridge. Keep the goal active. No commit or push was made.

## 2026-10-04: Exact plane scalar replay, line certificates and quartic support

**Status:** The initial constant and canonical line values have kernel certificates, the pinned native GKM line comparison has exact-query replay, and both exchange corruption suites pass. Both lower genera now have certified primary support through plane degree five for the shifted quartic equations. The full degree-four candidate calculation and final dependent/project-wide revalidation are still in progress. R7 and the class-valued semisimple GKM contract remain open; all fixed targets, bounds and seed obligations are unchanged.

The [scalar validation record](../../environments/genus-two-plane-scalar-validation.json) records the exact completed commands, source pins and explicitly pending checks.

### Scope and findings

Reviewed the original affine BP constant and remainder, their scalar implementations, finite-table/query checker, plane line replay, and the exact GKM request/value binding. Also reviewed the shared primary-graph primitive used by genus-one replay and the lower-genus support consumed by the quartic source equations. This is a targeted increment, not a comprehensive review of the dirty repository.

- **High computational gap addressed:** The old whole-polynomial initial calculation was impractical. An exact scalar constant, proved equal to the original equation, now checks `C = 1/80` and derives `(N₀,H₀,P₀) = (0,-1/960,0)` without an additional numerical seed.
- **High application step completed:** The original three line equations give constants `(1/10,1/20,1/40)` and coefficients `(96,48,24)` on `H₀`. Their full remainders vanish. The checked finite table proves all three canonical line values zero and binds the GKM ordinary answers to their complete ordered requests.
- **Medium computational mismatch repaired:** The sixteen lower-genus BP diagrams have total genus two but every component has genus at most one. The shared primary scalar recursion and its exact dimension pruning are now available without a total-genus restriction; its BP interpretation uses the actual component bound. Existing genus-one public signatures and proofs of interpretation are preserved.
- **High internal-support gap addressed:** Quartic reconstruction uses source degree five, beyond the original energy-twelve table cache. Separate complete genus-zero/one support tables through energy fifteen certify the quintic values `87304` and `87192`. The cache remains equal to the original algorithms at every degree, with fallback above the new support bound. The fixed application bound remains energy twelve.
- **Medium replay defect repaired:** The line assembly needed explicit finite-vector reduction at index two. Separate scalar modules avoid repeating expensive numerical proofs when editing the short assembly. A positive-control regression now exercises the generic exporter, and a coherently forged equation is rejected by Lean.

No new geometric input, numerical seed, global simp lemma or instance is introduced. No mathematical defect was found in the focused previously accepted definitions. The previous status turn made progress by completing the line and GKM replay builds and polling the specific ongoing jobs.

### Revisions and mathematical effect

`Coefficients/AffineEvaluation.lean` evaluates finite affine terms as their constant plus singleton coefficients. `GenusTwoConstant.lean`, `ScalarPointContraction.lean` and `GenusTwoPrimaryConstant.lean` derive exact scalar constants, preserving signed tails, point multiplicities and the vanishing of a retained genus-two component even at higher total graph genus. `GenusOneScalar.lean` and `GenusOneDimension.lean` expose the existing primary graph computation with its precise component-based interpretation.

`PlaneGenusTwoConstant.lean` and `PlaneGenusTwoCoefficientReplay.lean` reuse only proved primary values and preserve every effective remainder. `PlaneGenusTwoInitialValues.lean` proves the derived initial triple. `PlaneGenusTwoScalar.lean` and `PlaneGenusTwoCertificate.lean` identify the full finite scalar table with the original terminating canonical recursion and bind a returned value to the actual genus, class, insertion order and powers.

The line scalar/assembly fixtures and `GKM/Fixtures/PlaneGenusTwoLineReplay.lean` check the three incoming zero values. Python separately verifies equivariant coefficient coherence; these theorems do not prove localization or construct a class-valued CohFT. The producer checkout is unchanged. Its run used temporary caches, Sage 10.9, admcycles 1.4 and disabled online lookup.

The primary candidate exporters now accept an optional energy bound and distinct output namespaces. Their existing energy-twelve outputs reproduce byte for byte. `export_plane_genus_two_support.py` produces the separate degree-five support; the existing kernel checkers prove every class in both genera. `PlaneGenusTwoScalar.lean` is an interpreted exploration driver, and `export_plane_genus_two_scalar.py` emits full table/query certificates. Candidate arithmetic is never treated as proof.

The [twelve-query benchmark manifest](../../environments/plane-genus-two-benchmarks.json) independently records the BP paper's equation (12) conventions and section 3.5 values through degree four. It expects the quartic triple `(27,42,25/4)`, before the complete current candidate report is available. It shares the BP mathematical relation and lower-genus inputs; the published table is not an independent verification of those foundations.

### Validation and pending work

Completed commands include:

- `lake build AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneLine AxiomaticGW.GKM.Fixtures.PlaneGenusTwoLineReplay` passed before the equivalent cache extension. Its final dependent rebuild is running.
- `lake build AxiomaticGW.Surfaces.Fixtures.PlaneGenusOneSupport` passed, including both complete support tables.
- `lake build AxiomaticGW.Surfaces.PlaneGenusTwoCertificate AxiomaticGWTest.Surfaces.PlaneGenusTwoCertificate` passed with eighteen consumer examples. A long documentation line found in that run has been repaired and its source rebuilt without that warning.
- `python3 -B scripts/test_plane_genus_two_scalar.py` and `python3 -B scripts/test_gkm_plane_genus_two.py` passed all six methods: fourteen scalar and eight GKM preflight corruptions, plus both real Lean coherent-forgery rejections with positive controls.
- `python3 -B scripts/test_plane_genus_two_support.py` passed three methods, including real rejection of an altered quintic rational value.
- `python3 -B -m unittest discover -s scripts -p 'test_surface_genus_*_tables.py'` passed all sixteen existing methods. Both original exporter `--check` commands reproduce their frozen outputs.
- `lake env lean /tmp/gw_plane_scalar_final_axioms.lean` passed all seventy current core declaration audits; dependencies are limited to `propext`, `Classical.choice` and `Quot.sound`. The expanded fixture audit awaits the dependent rebuild.
- Source placeholder/substitute-axiom, new global-attribute, line-length, Python syntax and diff-whitespace checks pass. All 454 preceding validation pins matched at the combined increment's start; unrelated baseline work is preserved.

The compiled exploration executable was profiled in an unrelated eager L24 initializer and deliberately superseded by the interpreted driver. The first interpreted quartic run was superseded only after the degree-five cache was proved equivalent and its replacement reproduced the first three candidate rows. It was explicitly interrupted; neither run is falsely reported as completed. The replacement uses a separate output path. No process was restarted solely because a polling observation expired.

The existing genus-one two-point-blowup consumer rebuild, the final line rebuild and complete quartic candidate run remain live. Full project build/test/lint and the expanded fixture audit remain to be completed for the final increment. The last integrated baseline remains the preceding reconstruction validation record.

### Next priority

Finish the complete quartic candidate report, compare all twelve held published requests and kernel-check the remaining plane remainders. Then complete arbitrary plane descendants, both blowups, every fixed suite and the actual semisimple CohFT bridge. The goal stays active. No commit or push was made.

## 2026-10-04: Finite-seed reconstruction of the canonical plane genus-two families

**Status:** The three canonical plane families now have a terminating executable recursion, uniqueness from the original BP equations and soundness under the existing geometric inputs and three finite seeds. The initial primary entry is derived from the original source-degree-one HPP equation. Full build, test, lint and all 33 public declaration axiom audits pass. Efficient numerical evaluation and the fixed genus-two benchmark replay remain open; R7 and the full research goal are not complete. No new numerical seed or geometric hypothesis is supplied.

### Scope and findings

Reviewed actual raw-term dependencies, edge and cotangent bounds under signed forgetting, primary/first-power plane normalization, collected remainder support, the initial HPP sector, well-founded recursion and its geometric consumer. The increment protects a 641-file baseline and a 645-file continuation snapshot. The preceding status-only turn is classified as no implementation progress; it established that the unfinished cotangent-bound build had ended with an error, rather than remaining live.

- **Critical draft build defect repaired:** `DecoratedTermDegree.decoratedTerms_psi_bound` needed explicit relabelled edge-count reduction and finite-sum transport. This was a failure in the unfinished new proof, not the previously validated coefficient-system baseline.
- **High planned gap closed:** `genusTwoTerms_primary_psi_le_one` bounds every residual component of the complete primary BP expansion by one psi power. Plane normalization then gives only the three canonical families at their exact degrees. The collected remainder uses strictly smaller canonical triples.
- **High planned gap closed:** The original source-degree-one HPP equation determines the initial primary entry from the existing genus-two H seed and a closed lower-genus computation. Recursion no longer needs an arbitrary smaller-degree value family. Its geometric theorem consumes the original equations and exactly the existing line, elliptic H and genus-two H seed equalities.
- **Medium proof robustness issue repaired:** Concrete degree-zero type conversion unnecessarily expanded the full polynomial. Uniform HPP wrappers and an abstract constant in the initial-sector proof avoid that expansion; the final source/consumer build completes successfully without weakening any statement.
- **High remaining computational gap:** The exact initial constant and subsequent full remainders still need practical numerical evaluation and kernel replay. No new genus-two benchmark value has been certified.

No defect was found in the focused pre-existing mathematical definitions. Existing public statements, seed values and geometric laws are preserved. No global simp lemma or instance is introduced.

### Revisions and mathematical effect

[`TermSupport.lean`](../../AxiomaticGW/Coefficients/TermSupport.lean) provides membership rules for actual rational terms. [`DecoratedTermDegree.lean`](../../AxiomaticGW/Surfaces/DecoratedTermDegree.lean) proves that edges consume codimension and survive signed forgetting. [`BPCotangentSupport.lean`](../../AxiomaticGW/Surfaces/BPCotangentSupport.lean) applies this bound to all twenty boundary diagrams, all six marking occurrences and arbitrary additional primary markings, on each fixed surface.

[`PlaneCanonicalSupport.lean`](../../AxiomaticGW/Surfaces/PlaneCanonicalSupport.lean) proves canonical support using signed dimension equations, including degree zero and unit/divisor corrections. [`PlaneShiftedClosure.lean`](../../AxiomaticGW/Surfaces/PlaneShiftedClosure.lean) proves that every retained remainder variable is one of the three families at strictly smaller degree, and derives uniqueness by strong induction.

Let `C = planeShiftedConstant 0 1`, the complete initial HPP equation evaluated with every genus-two variable zero. [`PlaneGenusTwoInitial.lean`](../../AxiomaticGW/Surfaces/PlaneGenusTwoInitial.lean) proves that the equation is exactly `-36*N0 + 12*H0 + C`, with no other genus-two dependency. The existing `H0 = -1/960` seed determines `N0 = (C - 1/80)/36`; the nominal P query at degree zero vanishes by dimension. `C` is computed by the existing lower-genus algorithms, not supplied as a seed. Its numerical simplification to `1/80` has not been kernel-checked, so this increment does not assert `N0 = 0`.

[`PlaneGenusTwoRecursion.lean`](../../AxiomaticGW/Surfaces/PlaneGenusTwoRecursion.lean) defines the terminating recursion and proves the full positive-degree equations and uniqueness. [`PlaneGenusTwoReconstruction.lean`](../../AxiomaticGW/Surfaces/PlaneGenusTwoReconstruction.lean) proves that it computes the actual canonical invariants under the named geometry and seed values `1`, `-1/8`, `-1/960`. This is a conditional reconstruction theorem for three families, not an arbitrary genus-two query evaluator. The public umbrella imports it. The [mathematics-to-Lean map](../MathematicsToLean.md), [plane note](../mathematics/PlaneGenusTwoShifted.md), seed ledger and milestone status now record this scope.

### Validation

The [validation manifest](../../environments/genus-two-plane-reconstruction-validation.json) records source pins, exact commands and terminal outcomes, standard axiom dependencies and deliberately interrupted development experiments.

- Baseline `lake build AxiomaticGW.Surfaces.PlaneShiftedStep` passed. Final `lake build AxiomaticGW.Surfaces.PlaneGenusTwoReconstruction AxiomaticGWTest.Surfaces.PlaneGenusTwoRecursion` passed. The later full test includes all twelve final consumer examples.
- `lake build` passed, 2870 jobs. `lake test` passed, 2956 jobs. `lake lint` passed. The test suite retains only the pre-existing `AxiomaticGWTest/Basic.lean` private-module warning.
- `lake env lean /tmp/gw_plane_reconstruction_axioms.lean` checked all 33 public declarations in the eight new source modules. Their assumptions are limited to `propext`, `Classical.choice` and `Quot.sound`.
- The pinned Sage Python's `-B scripts/test_genus_two_shifted.py` passed three methods and ten corruption checks. `-B scripts/explore_genus_two_shifted.py --input environments/genus-two-shifted-native.json --output /tmp/gw_plane_closure_shifted_report.json` reproduced the saved report byte for byte, including ten held native rows and seven admcycles comparisons. These unchanged coefficient comparisons do not evaluate new invariants. The existing Sage Algebras deprecation remains.
- Nested-comment-aware placeholder and substitute-axiom scans, new global attribute checks, local links, source pins, line lengths, `git diff --check` and the scoped final diff are checked by the manifest generator. Unrelated work is preserved; the GKM producer revision and five source pins are unchanged.

Two experimental whole-polynomial proofs of the candidate constant `C = 1/80` were intentionally interrupted because of their cost and produced no numerical certificate. Several obsolete proof-conversion diagnostics were also stopped before switching to the uniform structural proof; the manifest separates these from ordinary repaired elaboration errors. All validation commands above have terminal success records. No existing build was restarted merely because an observation timed out.

### Next priority

Provide efficient exact evaluation and kernel certificates for the initial constant and complete plane remainders, then replay the frozen plane primary and first-descendant suites. Arbitrary higher descendants, both blowups, all remaining fixed benchmarks, class-valued semisimple GKM import and the R8 researcher workflow remain required. The goal stays active and unchanged. No commit or push was made.

## 2026-10-04: Complete plane coefficient system and geometric solved step

**Status:** The complete shifted HHP/HPP/PPP matrix, its determinant `7776d`, exact solver and strict degree support are proved. Coefficient collection now turns that support result into an actual decreasing remainder, and the solved canonical step follows from the original geometric BP equations. The integrated build, targeted consumers, axiom audits and repeated offline Sage comparisons pass. The full test suite and lint also pass; no R7 acceptance, new invariant value, seed or geometric hypothesis is claimed.

### Scope and findings

Reviewed the actual middle BP node, all four genus-two diagrams and six marking occurrences, dimension guards, signed equal-point cotangent tails, coefficient extraction from the complete normalized equations, the positive-degree matrix and its solver, polynomial collection and finite singleton isolation, and the existing BP geometric interpretation. The preceding status-only goal turn was a verified wait: full-suite session 59029 was polled and confirmed live. Work resumed from protected snapshots of 636 files; the combined coefficient-system increment is also compared against the earlier 633-file snapshot.

- **High planned gap addressed:** The HHP row and complete canonical support are proved, closing the actual three-row matrix rather than merely checking a symbolic table. Its determinant is nonzero at every positive degree.
- **High planned gap addressed:** A coefficient bound alone did not yet justify recursion over raw graph terms. Collection is now proved to remove cancellations, and every variable in every retained remainder term has smaller degree, genus two and the original dimension condition.
- **High planned gap addressed:** The exact matrix/remainder evaluation, negative right-hand side, canonical-step uniqueness and geometric interpretation are connected. No final recurrence is assumed.
- **High remaining gap:** Smaller-degree genus-two variables still need reduction to a closed recursive state and evaluation from the unchanged finite seeds. The step is not a total invariant evaluator.

No defect was found in the focused pre-existing mathematical definitions. Existing public statements are unchanged. The plane wrapper discharges its empty exceptional-divisor seed obligations internally. No global simp lemma, instance, substitute axiom or numerical seed is added.

### Revisions and mathematical effect

[`PlaneHyperplaneRow.lean`](../../AxiomaticGW/Surfaces/PlaneHyperplaneRow.lean) proves the complete HHP row `(-108d, -27d²+27d+12, 27d³+9d²)`. The classical outer two-hyperplane branch retains its inner line. Both equal-point psi terms retain their negative tails before cancellation. The raw formula covers zero degree and zero/one added points without an invalid natural-subtraction simplification.

[`PlaneShiftedSystem.lean`](../../AxiomaticGW/Surfaces/PlaneShiftedSystem.lean) extracts the actual three canonical coefficients from each original normalized equation. At positive degree the determinant is `7776d`; `planeShiftedSolve` has specification and uniqueness theorems. The positive-degree condition is essential for PPP. Every other nonzero collected singleton coefficient has smaller degree, including ancestor tags.

[`CollectedTerms.lean`](../../AxiomaticGW/Coefficients/CollectedTerms.lean) merges complete monomial coefficients and discards zero totals, with evaluation and coefficient preservation over every commutative rational algebra. It also isolates finite sets of singleton variables while preserving constants and other monomials.

[`PlaneShiftedRemainder.lean`](../../AxiomaticGW/Surfaces/PlaneShiftedRemainder.lean) collects each equation before removing its three distinct canonical requests. It proves raw-term dependency decrease for this retained remainder, the exact identity `eval(p_i) = (M x)_i + eval(remainder_i)`, and independence of its right-hand side from all current/higher-degree values. Two solutions agreeing on smaller degrees have the same canonical triple. [`PlaneShiftedStep.lean`](../../AxiomaticGW/Surfaces/PlaneShiftedStep.lean) applies this solved step to actual invariant evaluation under the existing original source relations, primitive geometry and finite low-genus seeds.

Fifteen [coefficient-system examples](../../AxiomaticGWTest/Surfaces/PlaneShiftedSystem.lean) cover the inner line, signed tails, small-point boundaries, quartic row, changed requests, higher ancestors, determinant and exact solver. Eleven [remainder examples](../../AxiomaticGWTest/Surfaces/PlaneShiftedRemainder.lean) cover complete cancellation, repeated coefficients, raw zero terms, constants, nonlinear monomials, absent isolated variables, initial query distinctness, degree-one dependencies, higher-degree independence, sign and uniqueness. Neither suite asserts new GW values.

### Validation

The [validation manifest](../../environments/genus-two-plane-system-validation.json) records exact commands, source pins, assumptions, development failures and any live checks.

- `lake build AxiomaticGW.Surfaces.PlaneShiftedSystem` passed as this continuation's baseline. `lake build AxiomaticGWTest.Surfaces.PlaneShiftedSystem` and `lake build AxiomaticGWTest.Surfaces.PlaneShiftedRemainder` pass all 26 examples. Final new source and consumer builds have no warnings.
- `lake build` passes with the new geometric step in the public umbrella: 2862 jobs. The older combined build session 17306 also finished successfully, resolving the pending build recorded in the HPP entry.
- `lake env lean /tmp/gw_plane_shifted_axioms.lean` and `lake env lean /tmp/gw_plane_remainder_axioms.lean` audit all 33 new public theorems. Their assumptions are limited to `propext`, `Classical.choice` and `Quot.sound`.
- Two fresh-cache Sage 10.9 / admcycles 1.4 runs of `scripts/explore_genus_two_shifted.py` are byte-identical: ten held native rows and seven admcycles comparisons. The pinned environment's `python -B scripts/test_genus_two_shifted.py` passes three methods and ten corruption checks. The native payload and numerical exploration algorithm are unchanged; no new native run or speedup is claimed.
- The original full `lake test` session 59029 completed all 2943 jobs with exit zero, retaining the existing `AxiomaticGWTest/Basic.lean` private-module warning. `lake lint` passes for the integrated `AxiomaticGW` library. The final `lake test` rerun passes all 2947 jobs, including the new consumer and every downstream module affected by the later umbrella import; its only warning is the same existing private-module warning.
- Final diff, nested-comment-aware placeholder/axiom scan, source-pin and local-link checks are recorded by the manifest generator. All unrelated baseline files are protected.

Development repairs concerned finite-vector index reduction, higher-order rewrite inference, coefficient-filter normalization, conjunction order, and explicit solver denominator simplification. One earlier new-test run was stopped only after a separate prefix replay established a concrete rewrite error; the final repaired target passes. No established long-running build or test was restarted because observation timed out. The existing Sage Algebras deprecation remains.

### Next priority

Prove that all smaller-degree genus-two requests in the selected equations reduce to a closed recursive state, evaluate its degree-zero sector from the existing finite seeds, and construct the total plane evaluator with termination, soundness and uniqueness. Then finish the fixed plane suites, both blowups, arbitrary descendants, full class-valued semisimple GKM import and the R8 research workflow. The full goal remains active and unchanged; no commit or push was made.

## 2026-10-04: Canonical components and the complete plane HPP row

**Status:** The full normalized plane BP equation now has a proved HPP row `(-36, 12-36d, 36d²)`, exact canonical support at the reconstructed degree, and strict degree decrease after removing its three canonical variables. Targeted Lean, axiom, consumer and offline Sage checks pass. HHP, the complete reconstruction matrix, finite-seed reconstruction, the fixed genus-two suites and full GKM/CohFT interoperability remain open. The existing broader build is still live; no milestone acceptance or goal scope changes.

### Scope and findings

Reviewed coefficient renaming, the exact signed dimension conditions, primary and first-psi normalization, unit string/dilaton corrections, the actual inner BP node, classical rational products, and every marking occurrence in HPP. The preceding goal turn was progress: it repaired the canonical component draft and checked its fifteen public axiom dependencies. This turn began with a passing direct baseline, all 434 previous source pins matching the protected state, and snapshots of 630 files.

- **High planned gap addressed:** Closed primary, single-unit, single-hyperplane, repeated-hyperplane and paired-unit component coefficients are proved without excluding degree zero or small marking counts.
- **High planned gap addressed:** The entire HPP equation is identified uniformly, including every requested variable at degree `d`. Removing the three canonical requests leaves strictly smaller degrees.
- **Medium regression issue corrected:** The first higher-ancestor test used a dimension-incompatible key. It now uses power `3d+1` with a hyperplane state, with a separate kernel check of its degree-one dimension compatibility.
- **High remaining gap:** HHP and its complete canonical support must still be proved before the symbolic determinant can establish the full reconstruction pivot.

No mathematical defect was found in the focused pre-existing definitions. Existing public statements and numerical algorithms are preserved. No numerical value, seed, geometric hypothesis, global simp rule or instance was introduced.

### Revisions and mathematical effect

[`RenamedCoefficient.lean`](../../AxiomaticGW/Coefficients/RenamedCoefficient.lean) proves coefficient collection through renamed sums and scalar multiples, including collisions and zero coefficients. [`PlaneCanonicalComponents.lean`](../../AxiomaticGW/Surfaces/PlaneCanonicalComponents.lean) derives exact canonical components. A single unit psi contributes two primary copies after its negative point-tail correction; with another non-unit state, the primary-unit and unit-psi cases contribute respectively one and three. Repeated hyperplanes retain the primary correction even at degree zero.

[`PlaneMixedRows.lean`](../../AxiomaticGW/Surfaces/PlaneMixedRows.lean) exposes the actual inner rational node and proves its classical contractions. External-state symmetry retains the node and all six marking occurrences. All four genus-two diagrams yield the HPP formula with coefficients `-36`, `12-12n` and `12nd` under the exact guard `n=3d`. `normalized_plane_hyperplane_two_points_canonical` identifies it with the full source-degree-`d+1` normalized polynomial; `normalized_plane_hyperplane_two_points_row` gives `(-36, 12-36d, 36d²)`. `normalized_plane_hyperplane_two_points_lower` combines full canonical support with source-degree cancellation to prove strict decrease outside the canonical block.

Thirteen [consumer examples](../../AxiomaticGWTest/Surfaces/PlaneMixedRows.lean) cover colliding renamings, zero scaling, degree-zero unit corrections, zero-point truncation, both psi placements, the repeated-hyperplane correction, the quartic row, changed point counts, dimension-compatible higher ancestors and decreasing degree. They certify equation coefficients, not new invariant values.

### Validation

The [validation manifest](../../environments/genus-two-hpp-validation.json) records commands, source hashes, axiom dependencies, repaired development failures and pending checks.

- `lake build AxiomaticGW.Surfaces.PlaneCanonicalComponents` passed as the initial baseline. The subsequent source target `lake build AxiomaticGW.Surfaces.PlaneMixedRows` passed with 2793 jobs, and `lake build AxiomaticGWTest.Surfaces.PlaneMixedRows` passed with 2794 jobs and all thirteen examples. The final source and test builds have no warnings.
- `lake env lean /tmp/gw_hpp_axioms.lean` checked all 36 public declarations across the three newly delivered modules. Their assumptions are limited to `propext`, `Classical.choice` and `Quot.sound`.
- Two fresh-cache offline Sage 10.9 / admcycles 1.4 runs of `scripts/explore_genus_two_shifted.py` produce byte-identical reports with all ten held native/symbolic matches and seven admcycles comparisons. The pinned environment's `python -B scripts/test_genus_two_shifted.py` passes three methods and ten request/coefficient corruption checks. The native input payload is unchanged; no new native execution or performance improvement is claimed.
- `git diff --check` passes. The source scan finds no proof placeholders or substitute axioms. All unrelated baseline files remain unchanged.
- Combined build session 17306 was polled and confirmed live after the new checks. Its last reported completion remains job 5583/5587. It has not been restarted. Umbrella integration, full `lake build`, `lake test` and `lake lint` remain pending after that run.

Repaired development failures involved dependent finite-vector reduction, coefficient renaming inference, explicit dimension normal forms, function-valued zero vectors, rewriting an inner vector before its containing vector, and a test simplifier unnecessarily decomposing a full coefficient tuple. They did not require weakening statements or adding assumptions. Sage retains its existing upstream Algebras deprecation.

### Next priority

Prove the HHP row and its full degree-`d` support, then connect the complete matrix to a nonzero pivot and a finite-seed reconstruction. Finish the pending broader verification. Termination, soundness, uniqueness, both blowups, all fixed genus-two suites, class-valued semisimple GKM import and the R8 research workflow remain required.

## 2026-10-04: Mixed rational components and strict source-degree support

**Status:** The mixed rational-complement contractions and cancellation of every source-degree genus-two variable in the plane `HHP`, `HPP` and `PPP` equations are proved. Nonzero coefficients have degree strictly below the equation degree. Targeted proof, consumer and exchange validation passes; the existing broader rebuild is still running. The full `HHP`/`HPP` matrix rows, canonical support at the degree to be reconstructed, pivots and reconstruction remain open. No milestone acceptance, fixed application, benchmark, seed or GKM requirement changes; the goal remains active.

### Scope and findings

Reviewed the actual BP gluing label maps, classical and line rational factors, inverse-metric dual states, six marking assignments, signed one-psi remainder formulas and full-equation coefficient consumers. The previous status-only turn was a verified wait because it polled the confirmed-live combined build. Before editing, all 431 prior source pins matched and 624 worktree files were snapshotted. The directly relevant baseline build passed.

- **High planned gap addressed:** Mixed `HP`/`HH` complements now have proved closed contractions. The classical `HH` branch remains present when the line lies on the main expression.
- **High planned gap addressed:** All three mixed equations now have proved source-degree cancellation and strict support below their source degree, for every requested variable and added-point count.
- **High remaining gap:** Strict support below source degree `d+1` permits variables at degree `d`. Their complete canonical support and the two missing uniform matrix rows must still be proved before a degree-`d` reconstruction step follows.

No mathematical defect was found in the focused pre-existing declarations. Existing public statements and executable numerical algorithms are unchanged. No numerical seed, geometric hypothesis, global simp lemma or instance was added. No commit or push was made.

### Revisions and mathematical effect

[`PlaneMixedPointContractions.lean`](../../AxiomaticGW/Surfaces/PlaneMixedPointContractions.lean) proves the binomial rational factors, external-pair symmetry, and the actual main/node label maps. A line with `HP` gives a unit main node plus `n` times a hyperplane main node. `HH` gives the `n` and `choose(n,2)` line placements plus the classical point-node term retaining main remainder one. The BP single-psi specializations preserve the original external or node psi slot. The equal-point zero-remainder psi swap follows from equality of the terminal insertion multisets, with both unit corrections zero.

[`PlaneSourceDegree.lean`](../../AxiomaticGW/Surfaces/PlaneSourceDegree.lean) retains all six marking occurrences and proves the three source cancellations. In `HPP` and `PPP`, classical rational factors vanish. In `HHP`, the last two diagrams survive separately and cancel with coefficients `3` and `-3`. The full normalized-equation theorems cover primary, first-descendant and higher-ancestor variables. Together with the existing curve support, `normalized_plane_two_points_degree_lt` and `normalized_plane_two_hyperplanes_degree_lt` bound every nonzero coefficient strictly below the equation degree.

Twelve [regressions](../../AxiomaticGWTest/Surfaces/PlaneMixedPointContractions.lean) cover the classical branch at zero points, small binomial boundaries, nontrivial placement weights, rational-slot symmetry, two individually nonzero HHP source terms, their complete cancellation, higher ancestors, degree zero and the strict support API. The explorer pins the two new proof files and records the three completed proof boundaries; the full-matrix and reconstruction flags remain false.

### Validation

The [validation manifest](../../environments/genus-two-mixed-plane-validation.json) records exact commands, source pins, development failures and pending integration.

- `lake build AxiomaticGWTest.Surfaces.PlaneMixedPointContractions` passed with 2791 jobs and twelve examples, without new warnings. Both new source modules compiled successfully.
- `lake env lean /tmp/gw_mixed_plane_axioms.lean` checked all 36 new public results; every result uses only `propext`, `Classical.choice` and `Quot.sound`.
- Two fresh-cache offline Sage 10.9 / admcycles 1.4 runs of `scripts/explore_genus_two_shifted.py` produce identical reports, retaining all ten held native/symbolic matches and seven actual admcycles comparisons. The pinned environment's `python -B scripts/test_genus_two_shifted.py` passes three methods and ten request/coefficient corruptions. The held native payload and computation algorithm are unchanged; this increment does not claim a new native execution or speedup.
- The original combined target build in session 17306 is still live, waiting on the existing expensive genus-one table after job 5583/5587. It has not been restarted. Root imports for `PlanePointContractions` and the new source-degree module, followed by full `lake build`, `lake test` and `lake lint`, remain pending after that build.

Development failures concerned finite-vector reduction, dependent decoration and label elaboration, a simplifier under nested sums, and consumer aliases causing excessive unfolding. They were repaired without changing the intended statements or expected values. Initial failed commands are retained separately from successful reruns. Sage still emits its existing upstream Algebras deprecation.

### Next priority

Complete pending umbrella integration and broader verification. Normalize the mixed main components and identify all degree-`d` variables with `(N_d,H_d,P_d)`; prove the `HHP` and `HPP` rows and the nonzero reconstruction pivot. Then establish finite-seed sufficiency, decreasing dependencies, termination, soundness and uniqueness, both blowup applications and every fixed genus-two suite. Actual class-valued semisimple GKM import, action conditions, geometric comparisons, ordinary specialization and the R8 research workflow remain required.

## 2026-10-04: Zero-remainder first powers and the uniform plane PPP row

**Status:** The complete zero-remainder one-psi formula and its canonical normalization are proved. The full normalized plane BP equation now has a proved `PPP` row `(0, -18, 18d)` for every positive degree. Targeted module and consumer checks pass; project-wide revalidation is still running in the existing build and is not claimed complete. The other two matrix rows, full dependency support, reconstruction, all application suites and the semisimple GKM gate remain open. R0/R2 and conditional R6 acceptance are unchanged; the goal remains active.

### Scope, findings and mathematical effect

Reviewed the original point-key API, signed cotangent step, classical rational triples, canonical first-descendant normalization, all four genus-two BP diagrams and their six marking assignments. The preceding user-facing status turn polled the live build and is a verified wait. The next available proof work was completed without restarting that build. The dirty tree and all 618 files at the beginning of the zero-remainder increment were preserved as a baseline; the PPP follow-up also snapshotted its 622-file starting state.

- **Critical unfinished-work issue repaired:** `PlanePointContractions.lean` initially failed elaboration at the dependent decoration and label equivalences. Explicit component types and actual finite label maps repair the intended statement. No mathematical conclusion was weakened.
- **High planned gaps addressed:** The classical unit correction and insertion-order-independent terminal normalization are proved for all finite marking sets. The original four-diagram PPP coefficient is now identified uniformly with the canonical row and with the complete normalized BP equation.
- **High remaining gap:** The other shifted rows, source-degree cancellation, larger-remainder support and well-founded genus-two reconstruction are not proved. The one-degree-remainder support theorem does not discharge those obligations.

No defect was found in the focused existing mathematical definitions. No new seed, geometric input, global simp rule or instance was introduced. Existing public theorem statements remain unchanged. The new general point-key and cotangent-step lemmas preserve arbitrary original powers and the existing specialized interfaces.

[`GenusTwoZeroRemainder.lean`](../../AxiomaticGW/Surfaces/GenusTwoZeroRemainder.lean) proves the terminal coefficient minus `n` times the classical correction when the psi-labelled state is the unit, including the zero-point boundary. [`PlanePointNormalization.lean`](../../AxiomaticGW/Surfaces/PlanePointNormalization.lean) exposes the actual psi-labelled descendant independently of the internal sort. [`PlanePointContractions.lean`](../../AxiomaticGW/Surfaces/PlanePointContractions.lean) proves two-point rational node selection, both vanishing BP diagrams, the two distinct surviving psi slots and the sixfold orbit factor. `normalized_plane_three_points_row` proves `(0, -18, 18d)` in the full original equation. The stronger coefficient formula has the exact guard `n+1=3d` and retains only its two specified descendant queries at a one-degree remainder.

Twelve zero-remainder regressions and nine PPP consumer regressions cover unit corrections, repeated divisors, degree zero, psi-label pairing, changed query multiplicities, higher-power ancestors, the quartic row and the full cubic-variable coefficient `54`. These are coefficient proofs, not new invariant values or completed numerical suites.

### Validation and pending checks

The [combined validation record](../../environments/genus-two-zero-remainder-validation.json) pins source files, successful commands, development failures and the explicit pending checks.

- `lake build AxiomaticGWTest.Surfaces.PlanePointContractions` passed with 2789 jobs and all nine examples. The new source and tests have no remaining warnings.
- `lake env lean /tmp/gw_plane_contractions_axioms.lean` checked 35 results, including the preceding zero-remainder and shifted fixtures. All use only `propext`, `Classical.choice` and `Quot.sound`.
- Two fresh-cache offline Sage 10.9 / admcycles 1.4 runs of `scripts/explore_genus_two_shifted.py` are byte-identical, preserving all ten native/symbolic matches and seven admcycles comparisons. The pinned environment's `python -B scripts/test_genus_two_shifted.py` passes three methods and ten corruption checks. The full matrix and reconstruction flags remain false; only the PPP and its scoped support flags are newly true.
- `lake build genusTwoShifted` passed with 5478 jobs independently of the still-running table target. Two subsequent native executions reproduce the unchanged ten-row, 3694-byte payload exactly, with SHA256 `d540e18782b4a3194f61fc4e9f89ad52fed864028a6888a84fe10a4b6e8337e3`. These are reproducibility checks, not a controlled performance comparison.
- The original combined command `lake build AxiomaticGWTest.Surfaces.GenusTwoZeroRemainder AxiomaticGWTest.Surfaces.PrimaryPointPullback AxiomaticGWTest.Surfaces.GenusTwoRemainder genusTwoShifted AxiomaticGW` remains live. It has already passed the new zero-remainder examples, affected coefficient tests, BP fixtures and the genus-zero tables. The expensive existing genus-one table recheck is still pending. The source edit to the shared point-key module caused this revalidation; it is not a failed or restarted run.
- After that command finishes, the umbrella import for the new PPP module, full `lake build`, `lake test` and `lake lint` still need completion. The accepted preceding checkpoint's results are not reused as if they validated the current source set.

Development failures involved dependent pair inference, reducibility during rewriting, finite-label numerals, a missing direct import, coefficient simplification and one consumer alias. They were fixed without changing the coefficients or adding assumptions. The initial failing test command is retained separately from its successful rerun. Sage retains its upstream Algebras deprecation.

### Next priority

Finish the pending broader verification, then prove the uniform `HHP` and `HPP` rows and complete source-degree cancellation and support. Use those results for finite-seed sufficiency, termination, soundness and uniqueness before the blowup applications and fixed genus-two suites. Actual class-valued semisimple GKM import, action laws, geometric comparison, ordinary specialization and R8 remain required.

## 2026-10-03: Closed primary placements and the one-psi plane line remainder

**Status:** Primary point placements now have closed formulas, and the complete signed plane component with one psi factor and a line remainder has a uniform formula. The zero-remainder one-psi component, full shifted matrix and genus-two reconstruction remain open. R0, R2 and the conditional R6 acceptance are unchanged; R1/R3–R5/R7–R8 remain open. The goal stays active with all three targets, every fixed benchmark and the class-valued GKM requirement preserved.

### Scope, findings and mathematical effect

Reviewed the signed point recursion, primary scalar reduction, plane remainder support, actual cotangent-tail label maps and their coefficient consumers. The targeted baseline passed. All 422 preceding source pins matched and 613 baseline files were snapshotted. The interrupted preceding work was preserved and its unfinished proof completed.

- **High planned gap addressed:** Primary placement sums and every successive one-psi correction at a plane line remainder are now identified with explicit binomial formulas, for arbitrary finite marking sets and point counts.
- **Medium implementation improvement:** Rational primary factors in both separating orientations reuse the existing scalar evaluator, with a whole-family equality proof preserving all nonprimary values.
- **High remaining gap:** The zero-remainder first-power formula and the uniform full matrix, complete support, source-degree cancellation and decreasing reconstruction are unproved.

No mathematical defect was found in the focused pre-existing declarations. No numerical seed, geometric assumption, global simp rule or instance was added. Existing public theorem statements are preserved. The existing `primaryTerms_unit_zero` helper is now public for its actual downstream use; its statement and proof are unchanged.

[`PrimaryPointPullback.lean`](../../AxiomaticGW/Surfaces/PrimaryPointPullback.lean) proves dimension-selected binomial placement and the primary insertion-key formula. [`GenusTwoPrimaryPoints.lean`](../../AxiomaticGW/Surfaces/GenusTwoPrimaryPoints.lean) identifies reconstructed rational factors, classical zero-degree support, plane line support and primary-unit vanishing. [`GenusTwoPointTails.lean`](../../AxiomaticGW/Surfaces/GenusTwoPointTails.lean) follows the actual cotangent-tail label equivalences and proves that the line-remainder coefficient is `-choose(n,2)` times the primary component for a hyperplane psi insertion, `-n` times that component for a point psi insertion, and zero for a unit. The primary component has the psi label replaced by a hyperplane and respectively two or one fewer added points. Small point counts are covered by the theorem. These are coefficient formulas, not new invariant values.

Eighteen new [regressions](../../AxiomaticGWTest/Surfaces/PrimaryPointPullback.lean) cover insufficient/excess points, unit vanishing, exceptional signs, distinct equal-energy classes, classical support and the new formulas. The existing signed coefficient `-3` now uses the uniform theorem; cubic-variable checks give `-108` and `-24`. The existing shifted BP certificates remain unchanged.

### Validation

The [validation manifest](../../environments/genus-two-primary-points-validation.json) records source pins, commands, timings, resource measurements and the proof boundary.

- `lake build AxiomaticGWTest.Surfaces.PrimaryPointPullback AxiomaticGWTest.Surfaces.GenusTwoRemainder genusTwoShifted AxiomaticGW` passed with 5584 jobs; `lake build` passed with 2849 jobs; `lake test` passed with 2928 jobs; `lake lint` passed.
- `lake env lean /tmp/gw_primary_points_axioms.lean` checked twenty-one results. All use only `propext`, `Classical.choice` and `Quot.sound`.
- Two native runs reproduce the unchanged ten-row, 3694-byte payload with SHA256 `d540e18782b4a3194f61fc4e9f89ad52fed864028a6888a84fe10a4b6e8337e3`. No controlled speedup claim is made.
- Two fresh-cache, offline Sage 10.9 / admcycles 1.4 runs of `scripts/explore_genus_two_shifted.py` reproduce the updated report byte for byte, retaining all ten symbolic matches and seven admcycles comparisons. The pinned environment's `python -B scripts/test_genus_two_shifted.py` passes all three methods and ten corruption checks.
- Whitespace, touched-code placeholder/axiom scans, local file links, source preservation and the GKM revision/five-source pins were checked. All 599 unrelated baseline files are unchanged.

Development failures involved explicit type/lambda inference, stable-arity arguments, cast/subtraction normalization and one new test needing its final match reduction. These were fixed without weakening statements or changing expected coefficients. The initial combined target failure is retained separately from the successful rerun. Two initial native output filenames collided with the timing wrapper's metadata filenames; both runs were repeated with distinct payload paths before byte comparison. Only the existing private-module warning and upstream Sage Algebras deprecation remain.

### Remaining work and next priority

Close the zero-remainder one-psi component, then identify all nine shifted matrix entries and prove complete support and strict decrease relative to the reconstructed plane degree. Finish finite-seed sufficiency, termination, soundness and uniqueness, then both blowup applications, every fixed genus-two suite and the complete descendant composition. Actual semisimple CohFT import, action laws, ordinary specialization, shared GKM regressions and the R8 research workflow remain required.

## 2026-10-03: Effective-remainder recursion through signed cotangent tails

**Status:** The complete genus-two point coefficient now has a proved recursion over the exact effective remainder, including every new rational tail created by cotangent pullback. Ordinary plane normalization forces the terminal genus-two component to consume zero remainder, so a one-degree shift uses degree-zero and degree-one rational complements. The original BP numerical requests and both existing coefficient certificates are preserved. Uniform closed matrix identification, complete equation support and genus-two reconstruction remain open. The goal stays active; milestone acceptance, applications, bounds and the mandatory class-valued GKM gate are unchanged.

### Scope and findings

Reviewed complete normalized coefficient support, signed point compression, ordered curve splittings, the plane terminal simplification and the native/Sage consumer. The baseline command `lake build AxiomaticGW.Surfaces.PlaneGenusTwoCoefficients AxiomaticGW.Surfaces.PointPullbackContraction` passed with 2738 jobs. All 417 preceding source pins matched; 607 existing files and the dirty-tree diff were snapshotted. The preceding user-facing turn was a status-only review and made no implementation progress; this turn revalidated the worktree and took the next available proof step.

- **High planned gap addressed:** The exploration restricted rational complements to total degree one without a corresponding recursive Lean reduction. Full-coordinate support and exact reindexing now justify that restriction through both original edges and signed new cotangent tails.
- **Medium implementation improvement:** The runtime splits the effective remainder instead of the entire source class. A degree-order guard prevents truncated subtraction from changing requests above the source degree.
- **High remaining gap:** Closed dimension-pruned point-placement sums and the full symbolic matrix are still unproved. The new restriction does not prove cancellation of source-degree unknowns, uniform pivots or well-founded reconstruction.

No mathematical defect was found in the reviewed pre-existing declarations. No public theorem statement, geometric input, numerical seed, global simp rule or instance was changed. The terminal-equality hypothesis in the generic evaluator is discharged by the existing coefficient implementation; it is not a new invariant oracle.

### Revisions and mathematical effect

[`WeightedCurveSplitting.lean`](../../AxiomaticGW/Coefficients/WeightedCurveSplitting.lean) proves both orientations of supported splitting translation using every effective coordinate. [`GenusTwoCoefficientSupport.lean`](../../AxiomaticGW/Surfaces/GenusTwoCoefficientSupport.lean) proves that complete normalized and signed point coefficients vanish unless the requested variable's full class is an effective part of the input.

[`GenusTwoRemainder.lean`](../../AxiomaticGW/Surfaces/GenusTwoRemainder.lean) recursively distributes that effective remainder. Its main-component recursion decreases the additional-point count and includes each signed cotangent tail. `remainderPointCoefficient_eq` identifies it with the entire original coefficient at the requested class plus the remainder, for all three coordinate models, arbitrary cotangent powers and finite marking counts.

[`PlaneGenusTwoRemainder.lean`](../../AxiomaticGW/Surfaces/PlaneGenusTwoRemainder.lean) proves the terminal plane remainder is zero, gives the two line splittings and identifies the guarded source-degree BP consumer with the old one. The native driver and the two existing kernel certificates now consume this implementation. The generic blowup path still retains its nonzero calibration corrections; no plane cancellation is asserted for blowups or localized equivariant theories.

Thirteen [regressions](../../AxiomaticGWTest/Surfaces/GenusTwoRemainder.lean) cover both separating orientations, degree-zero divisor correction, a nonzero signed new-tail coefficient `-3`, a nonzero blowup calibration correction `-1`, incomparable exceptional classes, zero remainder, higher ancestor tags, source-degree rejection and loops without genus-two vertices. These are coefficient checks, not new invariant values. The Sage report pins the four new proof modules and records the completed remainder boundary separately from the open matrix theorem.

### Validation

The [validation manifest](../../environments/genus-two-remainder-validation.json) records commands, source pins and proof boundaries.

- `lake build AxiomaticGWTest.Surfaces.GenusTwoRemainder genusTwoShifted AxiomaticGW` passed with 5577 jobs. `lake build` passed with 2846 jobs; `lake test` passed with 2924 jobs; `lake lint` passed.
- `lake env lean /tmp/gw_plane_split_axioms_20261003.lean`: all twenty queried results use only `propext`, `Classical.choice` and `Quot.sound`.
- Two native exports reproduce the unchanged ten-row, 3694-byte payload byte for byte, SHA256 `d540e18782b4a3194f61fc4e9f89ad52fed864028a6888a84fe10a4b6e8337e3`. The recorded durations are 3.849 and 2.446 seconds. This is runtime evidence, not a controlled comparison against the earlier implementation.
- Two fresh-cache, offline Sage 10.9 / admcycles 1.4 runs of `scripts/explore_genus_two_shifted.py` reproduce the report, with ten symbolic matches and seven actual admcycles pullbacks. The pinned environment's `python -B scripts/test_genus_two_shifted.py` passes all three methods and ten request/value corruptions.
- Whitespace, code-placeholder, local-file-link, source-preservation and GKM revision/source-pin checks pass. All 596 unrelated baseline files are unchanged.

Development failures involved explicit product projections, reducible coordinate inequalities, a swapped-pair membership rewrite, beta reduction of the terminal lambda and a test contradiction tactic. They were repaired without weakening statements or changing expected values. The fixture compiled successfully during a combined run whose new test initially failed; the corrected target run and full tests pass. Full tests retain the existing private-module warning in `AxiomaticGWTest/Basic.lean`; Sage retains its upstream Algebras deprecation. No new warning remains.

### Remaining work and next priority

Use the proved degree-one rational-complement recursion to derive the closed point-placement sums and identify all nine shifted matrix entries uniformly. Prove the complete canonical support, cancellation of source-degree variables and strict decrease relative to the reconstructed degree. Then finish finite-seed sufficiency, termination, soundness and uniqueness, both blowup applications and every genus-two suite. Actual semisimple CohFT import, reconstruction-action conditions, ordinary specialization, shared GKM regressions and the R8 research workflow remain required. R1/R3–R5/R7–R8 stay open.

## 2026-10-03: Uniform plane normalization and exact component-class pruning

**Status:** The complete ordinary plane normalizer is proved equal to its direct part at every full curve class. Canonical divisor-count and signed dimension formulas are proved, including degree zero. The coefficient evaluator now uses a proved component-class restriction, and both existing shifted coefficient certificates replay through it. Uniform identification of the shifted matrix, complete equation support and genus-two reconstruction remain open. The goal stays active; no application, bound, seed, geometric input, milestone acceptance, commit or push changes.

### Scope and findings

Reviewed the sparse first calibration, primary unit/string reduction, first-descendant divisor corrections, the full normalization and coefficient consumers, and the shifted native/Sage exchange. The targeted baseline passed, all 414 preceding pins matched, and 603 existing files were snapshotted. The preceding goal turn made progress by completing the signed-compression checkpoint. This review does not certify a geometric model or a class-valued GKM import.

- **High planned gap closed:** The symbolic plane calculation used vanishing of first-calibration corrections, but the complete Lean normalization had not yet been identified with that simplification. The new proof retains the original negative correction and kills each main primary-unit term using the existing reduction. It applies to the entire uncollected expression.
- **Medium integration improvement:** Exact component-class support now permits an early rejection before normalizing unrelated genus-two components. Equality theorems connect the component function, signed point contraction and BP wrapper to the full generic evaluator. No speedup is claimed from the recorded runs.
- **High remaining gap:** The uniform point-placement sums and their complete support are not yet identified with the symbolic matrix. Finite coefficient agreement does not prove solvability or well-founded reconstruction.

No mathematical defect was found in the reviewed pre-existing declarations. Public theorem statements are unchanged, and no global simp rule, instance, coercion, geometric assumption or numerical seed was added.

### Revisions and mathematical effect

[`PlaneNormalization.lean`](../../AxiomaticGW/Surfaces/PlaneNormalization.lean) proves that the first calibration outputs only the unit, so `normalizedTerms_plane_eq_direct` removes every calibration tail in the genus-at-least-two branch. `affineSubstitute_normalizedTerms_plane_eq` and `normalizedTerms_plane_support` extend this to complete expressions and exact curve-class support. The existing low-genus and higher-power branches are unchanged. This conclusion concerns ordinary plane normalization; it supplies no corresponding cancellation for localized equivariant theories or either blowup.

The same module proves the primary factor `d^h` in the absence of units, the hyperplane correction `h*d^(h-1)` with natural subtraction, and the absence of a divisor-product correction for a point descendant. Degree-zero and zero-count cases remain present without division. The signed dimension criteria are `n+1=3d+g` for primary points and `n+codim(b)+1=3d+g` for a first descendant of `b`. They remain arithmetic tests, with geometric query-domain checks unchanged.

[`PlaneGenusTwoCoefficients.lean`](../../AxiomaticGW/Surfaces/PlaneGenusTwoCoefficients.lean) rejects a genus-two component whose curve class differs from the requested variable, then uses the proved direct normalization. Its three equality theorems preserve every positive rational complement, node decoration and signed stable-curve pullback. The [native driver](../../scripts/GenusTwoShifted.lean) and the two existing [kernel coefficients](../../AxiomaticGW/Surfaces/Fixtures/GenusTwoShifted.lean) consume this implementation with their original requests and conclusions. No new invariant value is derived in this increment.

Eighteen [regressions](../../AxiomaticGWTest/Surfaces/PlaneNormalization.lean) cover public support/equality interfaces, a nonzero calibration unit row, repeated divisors, multiple units, degree-zero corrections, exact dimension criteria and a dimension-compatible query that is outside the geometric domain. The Sage report now pins the four normalization/compression sources and distinguishes their completed proofs from the still-open uniform symbolic matrix.

### Validation

The [validation manifest](../../environments/plane-normalization-validation.json) records exact commands, assumptions, source pins and development failures.

- `lake build AxiomaticGWTest.Surfaces.PlaneNormalization genusTwoShifted AxiomaticGW`: 5569 jobs, 70.772 seconds. `lake build`: 2842 jobs, 1.223 seconds. `lake test`: 2919 jobs, 35.531 seconds. `lake lint` passes in 10.145 seconds.
- `lake env lean /tmp/gw_plane_normalization_axioms_20261003.lean`: all seventeen queried results use only `propext`, `Classical.choice` and `Quot.sound`.
- Two native exports reproduce the same ten-row, 3694-byte payload exactly: SHA256 `d540e18782b4a3194f61fc4e9f89ad52fed864028a6888a84fe10a4b6e8337e3`. Recorded durations are 96.003 and 86.314 seconds; other validation overlapped, so these are not controlled performance comparisons.
- Two fresh-cache, offline `scripts/explore_genus_two_shifted.py` runs in Sage 10.9 / admcycles 1.4 reproduce the report exactly, with ten symbolic matches and seven actual admcycles comparisons. The same environment's `python -B scripts/test_genus_two_shifted.py` passes all three methods, including ten corrupted request/value cases.
- Final diff, whitespace, local-file-link, placeholder and source-preservation checks pass. All 592 unrelated baseline files and the five pinned GKM producer modules are unchanged.

Development errors concerned reducible matrix zeros, explicit list composition, a natural self-cast, decisions containing unreduced local parameters and two omitted target annotations in tests. A redundant tactic and a long line were removed. These repairs do not change mathematical statements. The final build has no new warnings; full tests retain the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`, and Sage retains its upstream Algebras deprecation.

### Remaining work and next priority

Use exact component-class support to rewrite shifted contractions as sums of rational complements of total degree one. Combine the proved component formulas with the signed point-placement counts, identify the full matrix uniformly, and prove cancellation of larger-degree unknowns and strict dependency decrease. Finite-seed sufficiency, termination, soundness, uniqueness, all three surfaces' genus-two descendant suites, actual semisimple CohFT import, ordinary specialization and R8 remain required. The R1/R3–R5/R7–R8 gates remain open.

## 2026-10-03: Signed point compression and two shifted plane coefficients

**Status:** Recursive signed point-marking compression is proved for arbitrary component values, original cotangent powers and any number of added primary points. Its BP and complete L24 consumers equal the full normalized coefficients. Two shifted plane entries have kernel replay, including a nonzero primary coefficient. Uniform identification of the symbolic matrix, complete dependency support and genus-two reconstruction remain open. The goal stays active; no application, benchmark, seed, geometric input, milestone acceptance, commit or push changes.

### Scope and findings

Reviewed decorated marking pullbacks, full-class surface contractions, component-genus bounds, coefficient normalization, the two relation consumers and their native/Sage comparisons. The targeted baseline passed and all 410 preceding pins matched a snapshot of 598 files. This is a focused coefficient and implementation audit, not a comprehensive review of geometric models or GKM semantics.

- **High planned gap addressed:** Enumerating every labelled signed graph placement was an obstacle to coefficient replay. Binomial placement counts now have a proof of equality with that complete expansion, including negative rational tails and node decorations.
- **High remaining proof gap:** Two nonzero entries do not identify the uniform shifted matrix or establish complete support. Cancellation of source-degree variables and strict decrease relative to the requested degree remain unproved.
- **Medium performance limitation:** Standalone kernel checks passed in 39.957 and 48.191 seconds, with peak child RSS 7866630144 and 6771212288 bytes. The integrated targeted build passed in 470.501 seconds. Numerical kernel replay still has a substantial cost; these development observations are not a controlled benchmark.

No defect was found in the reviewed pre-existing mathematical statements. Existing theorem signatures and conventions are preserved. No new geometric hypothesis, numerical seed, global simp rule, instance or coercion was added.

### Revisions and mathematical effect

[`PointPullbackContraction.lean`](../../AxiomaticGW/Surfaces/PointPullbackContraction.lean) distributes point counts through original separating edges using Pascal's identity. Its component recursion decreases the additional-point count even when a negative cotangent correction increases graph size. `contraction_eq` identifies the result with the original signed multiset expansion for arbitrary terminal values. The [component-genus lemmas](../../AxiomaticGW/Tautological/DecoratedGluingMarkingBounds.lean) prove exact preservation of the largest component genus.

[`GenusTwoPointCoefficients.lean`](../../AxiomaticGW/Surfaces/GenusTwoPointCoefficients.lean) uses normalized singleton coefficients on the unique genus-two component and the existing reconstructed constants on its rational complements. The BP and full L24 `pointCoefficient_eq_full` theorems in the [relation interface](../../AxiomaticGW/Surfaces/GenusTwoCoefficientRelations.lean) preserve every coefficient of the requested full equation. Graphs without a genus-two component contribute zero only after a proof.

The [shifted fixture](../../AxiomaticGW/Surfaces/Fixtures/GenusTwoShifted.lean) certifies coefficient `-18` on the degree-one hyperplane descendant in the source-degree-two PPP row, and coefficient `-36` on the degree-one primary variable in the HPP row. The latter sums the four checked contributions `-12, 0, 18, -42`. These are equation coefficients, not invariant values. Twelve [regression examples](../../AxiomaticGWTest/Surfaces/PointPullback.lean) include arbitrary-class API use, higher cotangent powers, node corrections, exceptional signs and rejection of incorrect coefficient claims. Formal probes with all component values one are explicitly distinguished from GW invariants.

### Validation

The [validation manifest](../../environments/point-pullback-validation.json) records exact commands, source pins, timings and assumptions.

- `lake build AxiomaticGWTest.Surfaces.PointPullback AxiomaticGW`: 2841 jobs. The unscoped heartbeat-option warning from that build was repaired by scoping it to each numerical theorem. The final `lake build` passes 2840 jobs in 103.315 seconds; `lake test` passes 2916 jobs in 112.242 seconds; `lake lint` passes in 11.598 seconds.
- `lake env lean /tmp/gw_shift_compression_axioms_20261003.lean`: all 22 queried results depend only on `propext`, `Classical.choice` and `Quot.sound`. A final module-doc heading correction was rechecked with `lake env lean AxiomaticGW/Surfaces/PointPullbackContraction.lean`; it changes no declaration or proof.
- The compressed native exporter reproduces all ten held rows byte for byte in 68.925 and 80.667 seconds. The unchanged 3694-byte payload has SHA256 `d540e18782b4a3194f61fc4e9f89ad52fed864028a6888a84fe10a4b6e8337e3`.
- Two fresh-cache runs of `scripts/explore_genus_two_shifted.py` with Sage 10.9 / admcycles 1.4 reproduce the comparison report exactly. All ten symbolic comparisons and seven actual admcycles pullbacks pass. `python -B scripts/test_genus_two_shifted.py` in that environment passes three methods, including ten request/coefficient corruptions. Shared BP data and lower-genus inputs remain identified.
- Final diff, whitespace, local-link, placeholder and source-preservation checks pass. All 586 unrelated baseline files and the five pinned GKM producer modules remain unchanged.

Development elaboration issues were repaired without changing statements: explicit marking imports, beta reduction before multiset congruence, weighted-sum matching, label composition, and an incorrect namespace qualifier. The integrated replay completed without interruption. The final build has no new warning; the test retains the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`. Sage retains its upstream Algebras deprecation.

### Remaining work and next priority

Prove plane first-calibration corrections vanish after primary-unit reduction, derive closed dimension-pruned formulas from the compressed recursion, and identify the shifted matrix uniformly. Prove complete canonical support, cancellation of larger-degree variables and strict decrease, then obtain finite-seed reconstruction, termination, soundness and uniqueness. Extend to both blowup monoids and arbitrary genus-two descendants, complete every fixed suite, and finish actual class-valued semisimple GKM import, action conditions, ordinary specialization and the R8 research workflow. The R1/R3–R5/R7–R8 gates remain open.

## 2026-10-03: Coefficients across curve classes and a shifted plane BP route

**Status:** General normalized coefficient extraction is proved for arbitrary full curve classes. The plane exploration finds a shifted-degree BP matrix with determinant `7776d`, compared with ten native rows and seven actual admcycles pullbacks. Its uniform coefficient formula, complete dependency support and numerical row replay are not yet Lean proofs. R7 and the full class-valued semisimple GKM gate remain open. The goal, fixed targets, benchmark bounds and finite seed inventory are unchanged; no commit or push was made.

### Scope and findings

Reviewed the existing leading evaluator, affine product rule, normalization tails, BP/L24 coefficient consumers, and the plane reconstruction discussion in Belorousski–Pandharipande Sections 3.2 and 3.5. The baseline targets passed, all 400 preceding source pins matched, and 587 existing files were snapshotted. This is a focused coefficient and reconstruction-route audit, not a comprehensive review of geometric models or the GKM producer.

- **High planned gap addressed:** Input-class extraction cannot see the positive rational complements needed by equations at a larger class. The new evaluator retains every ordered full-class split and all normalization corrections, with a theorem identifying its result with the complete normalized polynomial.
- **High remaining proof gap:** Mixed-point plane equations at degree `d+1` appear to determine the primary and first-descendant variables at degree `d`. Exact symbolic contraction gives a nonzero determinant for positive `d`, but finite agreement does not prove the uniform formula, cancellation of every larger-class variable, or sufficient support for induction.
- **Medium performance limitation:** Two whole-row kernel diagnostics were interrupted after expensive reduction. Smaller kernel regressions and universal correctness proofs pass. Signed point-marking compression is the next mathematical optimization; no numerical row is treated as certified because a native run succeeded.

No defect was found in the reviewed existing mathematical statements. No numerical seed, geometric hypothesis, global simp rule, instance or coercion was added.

### Revisions and mathematical effect

[`GenusTwoCoefficients.lean`](../../AxiomaticGW/Surfaces/GenusTwoCoefficients.lean) proves `coefficientEval_eq` for any requested variable and any full input curve class, preserving node powers, external powers, signed inverse metrics and positive-class complements. It evaluates a rational complement only after finding a nonzero genus-two coefficient. `coefficientEval_eq_zero_of_maxComponentGenus` proves vanishing for diagrams without a genus-two vertex, including diagrams with total genus two from loops or elliptic components.

The [runtime terms](../../AxiomaticGW/Surfaces/GenusTwoCoefficientTerms.lean) and [family proofs](../../AxiomaticGW/Surfaces/GenusTwoCoefficientRelations.lean) identify the BP and complete L24 extractions with their original normalized polynomials and recover the earlier input-class evaluator. Sixteen BP diagrams are skipped only in coefficient extraction, after the component-genus theorem; they remain in the full equations and constant terms. Existing definitions and theorem signatures are preserved. Nine [kernel regressions](../../AxiomaticGWTest/Surfaces/GenusTwoCoefficients.lean) cover arbitrary classes, both separating orientations, a positive rational complement, a negative calibration tail, distinct equal-energy exceptional classes, higher ancestor tags and an above-input query.

The [plane note](../mathematics/PlaneGenusTwoShifted.md) specifies the shifted requests and matrix. The [Sage explorer](../../scripts/explore_genus_two_shifted.py) derives its polynomial entries directly from dimension-selected point distributions and multinomial weights, retaining the negative one-psi pullback corrections. It does not interpolate finite degree values. Ten native rows agree; seven additionally agree with actual admcycles forgetful pullback and a separate incidence contraction. These comparisons share the held BP relation, plane conventions and lower-genus initial values, and do not independently prove geometric validity.

### Validation

The [validation manifest](../../environments/genus-two-shifted-validation.json) records commands, pins, assumptions, timings and interrupted diagnostics. Completed checks pass:

- `lake build AxiomaticGW.Surfaces.GenusTwoCoefficientRelations AxiomaticGWTest.Surfaces.GenusTwoCoefficients`: 2773 jobs; `lake build genusTwoShifted`: 5454 jobs. `lake build`: 2837 jobs; `lake test`: 2912 jobs; `lake lint`: passes. The full test retains the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.
- `lake env lean /tmp/gw_primary_route_axioms_20261003.lean`: all ten audited results use only `propext`, `Classical.choice` and `Quot.sound`.
- The native ten-row export completed in 131.098 seconds with peak child RSS 98140160 bytes. Two fresh-cache runs of `scripts/explore_genus_two_shifted.py` in Sage 10.9 / admcycles 1.4 reproduce the held report byte for byte, with online lookup disabled.
- The pinned Sage Python command `python -B scripts/test_genus_two_shifted.py` passes three methods, including nine altered request/encoding cases and a changed numerical coefficient. The explorer also detects omission of the signed pullback correction.
- Final diff, whitespace, local-link, placeholder and source-preservation checks pass. All 579 unrelated baseline files and the five pinned GKM producer modules remain unchanged.

The interrupted kernel diagnostics lasted 146.095 and 274.295 seconds, with peak child RSS 7219511296 and 8431992832 bytes. They supply no completed numerical proof. Initial elaboration, exact Sage-rational conversion and temporary-cache setup errors were repaired without changing mathematical statements or weakening acceptance.

### Remaining work and next priority

Prove signed point-marking compression and identify the shifted matrix uniformly with the actual BP equations. Prove complete canonical support, cancellation of larger-degree variables and strict decrease relative to the reconstructed degree. Then derive the plane recursion, termination, soundness and uniqueness from the unchanged seeds, and extend the audited argument to the full effective monoids of both blowups. Complete arbitrary genus-two descendants and every fixed benchmark; source degree five is allowed internally when reconstructing the degree-four plane suite. R1/R3–R5, actual semisimple CohFT import, applicable reconstruction-action conditions, ordinary specialization and R8 remain required.

## 2026-10-03: Direct decorated evaluation of genus-two leading matrices

**Status:** BP and complete L24 matrix entries now have executable decorated-gluing evaluators and equality proofs to the full normalized coefficients, for arbitrary full classes, added markings and cotangent powers. No positive-class lower-genus reconstruction is performed in this coefficient algorithm. Uniform solvability, the genus-two reconstruction theorem, all fixed suites and full class-valued GKM interoperability remain open. The goal stays active; the fixed targets, bounds, seeds and geometric inputs are unchanged. No commit or push was made.

### Scope and findings

Reviewed the existing affine substitution, genus-two monomial bounds, direct/full normalization coefficient theorem, decorated contraction and BP/L24 term formats. All 388 preceding source pins and the 575-file working-tree snapshot were checked before editing; the targeted baseline passed. This was a focused coefficient and runtime review, not a comprehensive geometric-model audit.

- **High planned gap closed:** Leading matrix search previously expanded positive-class lower-genus values that cannot affect the requested coefficient. The new proof isolates a genus-two factor carrying the input class and class-zero other factors. It includes the zero-class overlap correctly by summing the two product-rule contributions separately.
- **Medium development defect corrected:** The first new native driver imported the complete L24 proof assembly. A live process sample located eager initialization of unused genus-two psi-product source rows before `main`. That run was interrupted after 113.123 seconds, without producing a matrix. The new executable terms and proof consumers were separated; no existing source relation or public declaration was altered. Completed runs then evaluated twenty-five rows in 7.462 and 6.330 seconds with identical output. These observations concern development runs, not a controlled speedup benchmark against the full-equation task.
- **High remaining reconstruction gap:** Every one of the six new mixed-point BP requests has a zero canonical row. All nineteen previous projections agree, and the plane-line and F₁ fiber ranks remain 2/3 and 2/4. These displayed canonical submatrices do not prove full support, relation completeness or uniform rank. They establish that these six extra choices do not close the missing primary column.

No defect was found in the reviewed pre-existing mathematical statements. No numerical seed, geometric assumption, global simp rule, instance or coercion was introduced.

### Revisions and mathematical effect

[`AffineCoefficient.lean`](../../AxiomaticGW/Coefficients/AffineCoefficient.lean) computes singleton coefficients after the existing affine substitution and proves additivity, scaling, finite sums and a product rule. The product rule explicitly requires a constant monomial in each pair; nonlinear substitution is not asserted. [`GenusTwoLeading.lean`](../../AxiomaticGW/Surfaces/GenusTwoLeading.lean) derives this condition from component-genus bounds, proves lower-energy coefficient vanishing, and derives separating and nonseparating formulas. `leadingCoefficientEval_eq` identifies the recursive evaluator with the entire direct coefficient, including full curve coordinates, signed inverse metrics, node powers and arbitrary external powers.

[`GenusTwoLeadingTerms.lean`](../../AxiomaticGW/Surfaces/GenusTwoLeadingTerms.lean) supplies the complete BP/L24 runtime sums with their original coefficients and pullback multiplicities. [`GenusTwoLeadingRelations.lean`](../../AxiomaticGW/Surfaces/GenusTwoLeadingRelations.lean) proves equality with the complete normalized equations at the input class, so calibration tails remain in the equation while being absent from this matrix entry. Existing definitions and theorem signatures are unchanged. The root exports the proof interface; `lake build genusTwoLeading` builds the diagnostic executable through the term-only dependency path.

The [generated native driver](../../scripts/GenusTwoLeading.lean) includes every canonical primary/first-descendant column in the held nineteen requests and six additional BP requests. Its [9742-byte payload](../../environments/genus-two-leading-matrix-native.json) is checked against the earlier complete-equation report by the [Sage comparison](../../scripts/compare_genus_two_leading.py). The [matrix report](../../environments/genus-two-leading-matrix-exploration.json) records exact coefficients, ranks and absent columns. It reuses the relation data and existing normalization; no new independent geometric-CohFT or localization verification is claimed.

### Validation

The [validation manifest](../../environments/genus-two-leading-validation.json) records commands, pins, assumptions, development repairs and the interrupted startup run. The mathematical and integration checks pass:

- `lake build genusTwoLeading AxiomaticGWTest.Surfaces.GenusTwoLeading AxiomaticGW` passes. The [twelve Lean regressions](../../AxiomaticGWTest/Surfaces/GenusTwoLeading.lean) cover full-family interfaces, the zero split, both separating orientations, exceptional cup and inverse-metric signs, positive classes, loop genus, node/external powers, higher ancestor tags, equal-energy classes and the nonlinear boundary of affine substitution. `lake build`: 2834 jobs; `lake test`: 2908 jobs; `lake lint` passes.
- `lake env lean /tmp/gw_genus_two_leading_axioms_20261003.lean` audits twenty-two results; only `propext`, `Classical.choice` and `Quot.sound` occur.
- Complete native runs reproduce the payload exactly. Two fresh-cache Sage comparisons reproduce the matrix report. `python3 -B scripts/export_genus_two_leading.py --output scripts/GenusTwoLeading.lean --check` reproduces the native source. In the pinned Sage environment, `python -B scripts/test_genus_two_leading.py` passes three methods, including eight rejected request/coefficient corruptions.
- Placeholder/substitute-axiom, final-diff, whitespace, local-link and source-preservation checks pass. The GKM revision and five pinned producer modules remain unchanged.

Initial proof errors concerned simplification order, inferred component types and typed finite-sum binders; they were repaired without changing statements. The Python report test was corrected to compare JSON-normalized tuple/list representations, and the report was regenerated after a source-comment change updated its digest. Generated long-line warnings were removed. The remaining full-test warning is the pre-existing private-only `AxiomaticGWTest/Basic.lean` module.

### Next priority

Use the proved coefficient evaluator to audit sufficient equation families and reductions for the missing primary sector, including the plane-specific BP route and shifted exceptional classes in the surface recursions. Prove any required higher-cotangent elimination and well-founded measure before treating a finite matrix as reconstruction. Then complete finite-seed sufficiency, termination, uniqueness, arbitrary genus-two descendants and every fixed benchmark. The complete semisimple GKM bridge and remaining R1/R3–R5/R7–R8 obligations remain required.

## 2026-10-03: Normalized genus-two support and exact leading coefficients

**Status:** The full normalized BP/L24 families now retain affine genus-two support and effective full-class remainders, and their leading coefficients can be extracted without computing calibration tails. The decreasing remainder is preserved. This is a uniform prerequisite for reconstruction, not an invertibility theorem or completed R7. The goal, fixed targets, benchmark bounds, geometric obligations and full semisimple GKM completion gate remain unchanged. No numerical seed, commit or push was added.

### Scope and findings

Reviewed the original genus-two monomial bound, primary/first-descendant normalization, rational-tail energy theorem, affine substitution, exact coefficient API and their BP/L24 consumers. The two normalized-family baseline targets passed. All 382 preceding source pins matched the new 569-file snapshot.

- **High planned gap closed:** Support and strict energy decrease were proved for the ancestor equations but had not been transported through the complete descendant normalization. The new proofs preserve dimension compatibility, genus two and the full effective remainder for every uncollected term.
- **High remaining reconstruction gap:** Combining the currently sampled equations still does not determine every canonical unknown. The pilot includes absent columns rather than calculating rank only on variables appearing in a sample. Its plane-line matrix has a zero primary column and rank 2 of 3; the F₁ fiber matrix has rank 2 of 4. These statements concern the sampled rows before adding other relation families or initial constraints; they make no completeness claim about BP/L24.
- No defect was found in the reviewed pre-existing mathematical statements. No global simp rule, instance, coercion or substitute axiom was introduced.

### Revisions and mathematical effect

[`OnePsiSupport.lean`](../../AxiomaticGW/Surfaces/OnePsiSupport.lean) proves singleton support for the actual primary and first-descendant expressions. `directNormalizedTerms` exposes their normalization before positive rational-tail corrections. Its coefficients agree with the complete normalization at the input class, and more generally at any same-or-higher energy, with full curve classes still distinguished. This is a coefficient theorem; direct normalization is not asserted to be the full GW equation.

[`GenusTwoNormalizedSupport.lean`](../../AxiomaticGW/Surfaces/GenusTwoNormalizedSupport.lean) transports the original affine bound through substitution, proves the exact same-class/remainder decomposition under every valuation, and gives strict energy decrease for every variable in the remainder. `coefficient_normalized_eq_sameClass_direct` shows that an input-class coefficient depends only on original-class ancestors and their direct normalization. Both arbitrary-marking normalized BP and L24 families instantiate the bound. These results require no new geometric law, numerical value, recurrence or rank hypothesis, and preserve the old theorem statements.

The [eight API/kernel regressions](../../AxiomaticGWTest/Surfaces/GenusTwoNormalizedSupport.lean) exercise the complete family interfaces, a nonzero correction at twice the exceptional class, independent constants, the two distinct equal-energy exceptional classes, higher ancestor powers and class zero. In particular, the lower-class coefficient is minus one in the full normalization and zero in the direct expression, preventing the leading-coefficient optimization from being mistaken for a full-equation equality.

The [Sage pilot](../../scripts/explore_genus_two_leading.py) uses the exact previously verified BP/L24 payloads, the existing recursive reference normalizer and pinned GKM calibration. It compares nineteen leading extractions with the complete normalized equations and records eight exact matrices including every canonical column. Those shared sources are explicit; no new independent localization or geometric-CohFT verification is claimed.

### Validation

The [validation manifest](../../environments/genus-two-normalized-support-validation.json) records source pins, exact commands, assumptions and scope. Final checks pass:

- `lake build AxiomaticGWTest.Surfaces.GenusTwoNormalizedSupport`: 2766 jobs, eight examples. `lake build`: 2830 jobs, 6.791 seconds; `lake test`: 2903 jobs, 30.864 seconds; `lake lint`: 10.128 seconds.
- `lake env lean /tmp/gw_normalized_support_axioms_20261003.lean`: all nineteen audited results use only `propext`, `Classical.choice` and `Quot.sound`.
- Two fresh-cache runs of `scripts/explore_genus_two_leading.py` pass in 3.451 and 3.088 seconds and reproduce the [30257-byte report](../../environments/genus-two-leading-exploration.json), SHA256 `9289dba27c5670a28d77dc65a325dfbc3f480b432fdfcdcb5be9ec904ddccd2e`.
- Placeholder, final-diff, whitespace, local-link and source-preservation checks pass. All 563 unrelated baseline files and five pinned GKM producer modules are unchanged.

An initial proof used an unavailable singleton-injectivity name and two underconstrained component-query arguments. These were replaced by the public singleton equality lemma and explicit component queries, without changing statements. Two long-line warnings were removed. The final build has no new warning; the full test retains the existing private-module warning in `AxiomaticGWTest/Basic.lean`.

### Next priority

Derive a leading-coefficient evaluator directly from decorated gluing, avoiding positive-class lower-genus reconstruction when computing the matrix. Use it to select and prove uniform BP/L24 equation families that also determine the primary column and exceptional-class initial sectors. Then prove finite-seed sufficiency, termination and uniqueness, complete all genus-two descendants and fixed benchmarks, and finish the mandatory class-valued GKM bridge. No unresolved case is replaced by a new seed or a rank assumption.

## 2026-10-03: Complete L24 surface equations and first-descendant normalization

**Status:** The full L24 class relation now has a decorated GW contraction and an affine surface equation for arbitrary added markings and external ancestor powers. Its normalized form uses the same primary/first-descendant variables as BP. This closes the preceding surface-consumer gap; uniform reconstruction pivots, finite-seed sufficiency, the complete genus-two evaluator and full semisimple GKM interoperability remain open. The goal is active. No numerical seed, commit or push was added.

### Scope and findings

Reviewed the complete held L24 frame, decorated contraction and marking APIs, lower-genus reconstruction, affine substitution, existing rational-tail comparison, and the native/Sage exchange. The targeted baseline passed. All 359 preceding source pins matched the 546-file snapshot. This is a focused relation-consumer and implementation review, not a comprehensive geometric-model or GKM audit.

- **High planned gap closed:** Actual gluing expressions and checked graph isomorphisms now connect every held column to the numerical contraction. All 721 nonzero coefficients, including 703 nonprimitive terms, survive the passage to surface equations. Curve coordinates, node powers and signed forgetful corrections remain present.
- **Medium implementation defects corrected:** Native initialization repeated a costly BP coefficient conversion and initialized unused source-relation constructions. The original expression is now proved equal to one using the existing raw coefficient lookup; data and executable declarations were separated from their proof consumers without changing public names. Repeated lower-genus reconstruction is shared through a materialized cache with a universal equality theorem. A first function-only cache was rebuilt at every vertex by the generated code and was replaced. Incremental query-set collection is also proved equal to the original flattened collection.
- **High remaining obligation:** Affine support and smaller-class energy decrease do not prove that the same-class system is invertible. The complete plane degree-zero example normalizes to the known dilaton identity and supplies no additional numerical value. Finite matrix ranks are exploration evidence, not a uniform pivot theorem.

No defect was found in the reviewed pre-existing mathematical statements. Source relations, finite seeds, numerical normalizations and geometric hypotheses are preserved. No global simp rule, instance or coercion was added.

### Revisions and mathematical effect

[`L24Gluing.lean`](../../AxiomaticGW/Tautological/L24Gluing.lean) constructs all 815 held columns using 424 shared gluing expressions and 30 flag permutations. Lean verifies incidence, genus, labels and all decorations. [`L24GW.lean`](../../AxiomaticGW/Tautological/L24GW.lean) derives the complete arbitrary-marking equation from the existing class theorem and primitive realization laws. [`Surfaces/L24.lean`](../../AxiomaticGW/Surfaces/L24.lean) substitutes the proved genus-zero/one algorithms under their unchanged finite seeds. Each residual monomial is constant or one dimension-compatible genus-two ancestor with an effective full-class remainder.

[`GenusTwoNormalizedL24.lean`](../../AxiomaticGW/Surfaces/GenusTwoNormalizedL24.lean) applies the existing primary/first-power substitution, including the negative rational-tail correction. Its extra geometric input is the primitive cotangent comparison already used by normalized BP. Higher powers retain their ancestor interpretation. The [815-column plane fixture](../../AxiomaticGW/Surfaces/Fixtures/L24.lean) yields the complete residual equation $\langle\tau_1(1),\mathrm{pt}\rangle_{2,0}-3\langle\mathrm{pt}\rangle_{2,0}=0$. Its [normalized fixture](../../AxiomaticGW/Surfaces/Fixtures/GenusTwoNormalizedL24.lean) proves cancellation under every valuation, without assuming either invariant's value.

[`GenusTwoCachedTerms.lean`](../../AxiomaticGW/Surfaces/GenusTwoCachedTerms.lean) stores proved component expressions, with the original algorithm as the fallback for missing keys. `genusTwoTermsCached_eq` proves equality of the entire uncollected expression for any selected cache keys. The four held coordinate declarations moved verbatim to `Fixtures/L24Claims.lean`; the existing correction replay imports them and retains all assembly proofs. Both `L24Terms` modules preserve executable declarations and their public names. `L24Initial.bp_eq_original` proves the equivalent coefficient lookup. All five affected exporters reproduce the current files exactly.

### Validation

The [validation manifest](../../environments/surface-l24-validation.json) records exact commands, source pins, development failures, timings and proof boundaries. Final checks pass:

- `lake build`: 2828 jobs, 3.147 seconds with compiled dependencies; `lake test`: 2900 jobs, 36.180 seconds; `lake lint`: 11.340 seconds. Thirteen new Lean API examples cover the gluing, complete surface fixture, arbitrary cache keys and normalized interpretation.
- `python3 -B scripts/test_l24_gluing.py`, `python3 -B scripts/test_surface_l24_fixture.py`, `python3 -B scripts/test_l24_corrections.py` and `python3 -B scripts/test_l24_initial.py`: all fifteen test methods pass. The affected source pins, exact requests, complete column coverage and negative mathematical claims are checked. Five exporter reproduction commands pass. A fresh native 815-column export reproduces the held 22585-byte fixture exactly.
- The final nine-equation native export completes in 750.999 seconds with peak child RSS 183779328 bytes; all thirteen run pins are unchanged. Its 30635868-byte payload is byte-identical to the completed uncached and earlier materialized-cache runs. Their elapsed times were 1514.410 and 902.556 seconds. These are development observations, not a controlled benchmark.
- Two fresh-cache, offline runs of `scripts/explore_surface_l24.py` reproduce the [8723-byte report](../../environments/surface-l24-exploration.json) exactly. All nine complete equations agree with incidence-based Sage/admcycles contraction, and five deliberate corruptions are detected. Lower-genus numbers are shared Lean outputs; this comparison independently tests graph contraction, signed pullback and rational substitution, not the numerical genus-zero/one algorithm.
- `lake env lean /tmp/gw_surface_l24_axioms_final_20261003.lean`: all 21 audited results use only `propext`, `Classical.choice` and `Quot.sound`. Final placeholder, whitespace, local-link, diff and source-preservation checks pass. All 533 unrelated baseline files and five pinned GKM producer modules remain unchanged.

Early monolithic fixture checks and native runs were interrupted after profiling exposed excessive reduction, eager initialization or repeated work. Later columnwise kernel proofs and complete native runs passed. Intermediate elaboration and recursion-depth failures were repaired without weakening statements. The remaining warnings are the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean` and the upstream Sage Algebras deprecation.

### Remaining work and next priority

Prove the support and leading coefficients of the combined normalized BP/L24 equations, then uniform reconstruction pivots and finite-seed sufficiency. Complete arbitrary genus-two descendants, termination, uniqueness and every fixed suite for P², F₁ and Bl₂P². Original geometric validity, actual semisimple CohFT import, applicable reconstruction-action conditions and ordinary specialization remain required. The applications, energy bounds, finite seeds and R1/R3–R5/R7–R8 acceptance gates are unchanged.

## 2026-10-03: Complete conditional L24 class relation

**Status:** The complete 721-term L24 relation now has a Lean proof from the original source equations and primitive geometry. The initial BP expression is proved equal to the independently held initial coordinate row after realization. This closes the preceding comparison gap; it does not yet evaluate the full relation on the fixed surfaces. R7, all fixed benchmarks and full class-valued semisimple GKM compatibility remain open. The goal is active; no numerical seed, commit or push was added.

### Scope and findings

Reviewed the actual signed BP pullback, local component-dimension theorem, graph isomorphism checker, four external psi contributions, marking average, initial coordinates and final correction assembly. The baseline `lake build AxiomaticGW.Tautological.L24Assembly` passed, all 350 preceding pins matched, and 536 existing files were snapshotted. This was a focused review of the initial comparison and complete class equation; geometric models, the surface reconstruction and GKM class import were not comprehensively audited.

- **High planned proof gap closed:** The initial coordinate comparison now follows from actual graph operations and justified component-dimension vanishing. The 45 auxiliary graph classes cannot be discarded before averaging: 33 have nonzero unaveraged coefficients. The prescribed sixfold average cancels every auxiliary coordinate and recovers the unchanged 388-term initial row.
- **Medium verification issue addressed during development:** Elaborating four literal 306-entry record lists exceeded the default declaration budget. Local data-only heartbeat settings, typed list chunks and closed coordinate lemmas avoid repeated reduction. Graph hints and every coefficient equality remain kernel checked; no native decision proof is used.
- No concrete defect was found in the reviewed pre-existing mathematical statements. Existing source rows, geometric hypotheses, finite numerical seeds and the held final vector are preserved.

### Revisions and mathematical effect

[`L24InitialGraphs.lean`](../../AxiomaticGW/Tautological/L24InitialGraphs.lean) extends the original 815-column frame by 45 auxiliary graphs. Actual finite bijections check each graph and all six marking actions. [`L24InitialHints.lean`](../../AxiomaticGW/Tautological/L24InitialHints.lean) supplies 409 untrusted candidate keys; [`L24InitialCoverage.lean`](../../AxiomaticGW/Tautological/L24InitialCoverage.lean) checks incidence, vertex genera, kappa and every cotangent decoration for all retained terms. Missing keys and hash collisions have no authority to prove graph equality.

The [initial replay](../../AxiomaticGW/Tautological/Fixtures/L24InitialReplay.lean) checks four complete lists against the actual Lean `dimensionRecords` computation. The 120 BP assignments yield 306 signed pullback terms. Four psi contributions give 1,224 occurrences, with 18, 60, 60 and 60 dimension-zero markers. Repeated destinations and signed multiplicities remain present before consolidation. The original one-twelfth weight and sixfold average recover the held initial claim exactly.

[`L24InitialClass.expression_eq_initial`](../../AxiomaticGW/Tautological/L24InitialClass.lean) proves equality of realized classes using the existing component-dimension theorem. It does not claim equality in the free strata module before removing dimension-zero terms. `initial_vanishes` uses the same BP validity and primitive pullback, cotangent and label-compatibility hypotheses as the earlier expression theorem. [`L24Relation.realized_full`](../../AxiomaticGW/Tautological/L24Relation.lean) combines that result with all 71 previously checked corrections. It retains all 703 nonprimitive terms alongside the 18-term primitive projection. The original BP equation, four lower-arity genus-two psi rows, two derived rational psi rows and WDVV boundary geometry remain explicit inputs, supplied by their existing source theorems where applicable. No final-row vanishing, new source relation or invariant value is assumed.

The root module now reexports the complete relation; old public interfaces remain available. Assembly changes are documentation only. No new global simp rule, instance or coercion was introduced. The [exporter](../../scripts/export_l24_initial.py) checks seven held source pins and the exact native payload, then emits only candidate hints and records. It does not rewrite the original graph operations, auxiliary frame or final claim.

### Validation

The [validation manifest](../../environments/l24-initial-class-validation.json) records commands, timings, axiom dependencies and source preservation. Final checks pass:

- `lake build AxiomaticGW.Tautological.L24Relation`: 1868 jobs. `lake build AxiomaticGWTest.Tautological.L24Initial`: 1869 jobs, including five meaningful API examples.
- `lake build`: 2820 jobs, 3.362 seconds with compiled dependencies. `lake test`: 2887 jobs, 31.864 seconds. `lake lint`: 10.972 seconds. The only warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.
- `python3 -B scripts/export_l24_initial.py /tmp/gw_l24_corrections_native_bp_20261003.json --output-dir AxiomaticGW/Tautological --check`: exact reproduction. `python3 -B scripts/test_l24_initial.py`: four test methods pass in 12.118 seconds including a fresh native export. Seven kernel-proved inequalities reject lost negative terms, false pruning, nonzero pruning markers, wrong destinations, wrong signs, doubled normalization and omitted averaging permutations. Seven source-pin mutations, three native-payload mutations and duplicate JSON keys are rejected.
- `lake env lean /tmp/gw_l24_initial_axioms_20261003.lean`: all 22 audited declarations use only `propext`, `Classical.choice` and `Quot.sound`. Placeholder, whitespace, new-link and final-diff checks pass; all 528 unrelated baseline files and five pinned GKM producer sources are unchanged.

Initial proof drafts needed explicit finite-sum indices, concrete graph-check arguments, distinct multiset membership names and explicit unfolding of a local let. These elaboration repairs did not change mathematical statements. One combined coverage/replay build failed at the literal record budget after coverage compiled; later targeted, full build, test and lint checks passed. The immutable earlier diagnostic JSON and validation manifest retain their historical proof status. The new manifest records the completed comparison.

### Remaining work and next priority

Construct the full decorated GW contraction of this L24 class relation, preserving every node power, curve-class splitting and nonprimitive term. Use it to build the fixed-surface polynomial family and prove uniform reconstruction pivots. Complete finite-seed sufficiency, the remaining low-power/multi-marked genus-two sectors, termination, uniqueness, descendant composition and every energy-twelve benchmark for P², F₁ and Bl₂P². Original geometric validity and full semisimple GKM import, reconstruction-action conditions, applicability and ordinary comparison remain explicit obligations. No application, seed or acceptance gate is narrowed.

## 2026-10-03: Checked L24 correction contexts and complete coefficient assembly

**Status:** All 71 correction rows now have actual decorated graph contexts and offline kernel replay. Their complete 721-term coefficient sum and the independently held primitive target are checked. The initial BP expression has a conditional vanishing theorem, but its realized-class comparison with the saved initial coordinates remains open. R7, every fixed surface benchmark and full semisimple GKM interoperability remain required. This is a working-tree checkpoint; no numerical seed, commit or push was added.

### Scope and findings

Reviewed the existing square/product pullbacks, rational psi expansion, WDVV boundary geometry, BP normalization, raw graph realization and marking conventions. The baseline target passed, all 326 preceding source pins matched, and 511 existing files were snapshotted. The review is limited to this relation assembly and its proof boundary; geometric models, full surface reconstruction and the GKM producer have not been comprehensively reviewed.

- **High planned gap addressed:** The complete 29 high-power, 37 rational-psi and five WDVV corrections are tied to actual graph operations, retaining node branches and all decorations. Incoming coefficients are checked against those operations before the final weighted sum.
- **High remaining mathematical gap isolated:** The initial Sage vector is not an equality in the free strata module. Of 1,224 weighted BP pullback summands, 198 vanish by local component dimension. The retained terms also produce 45 auxiliary graph classes outside the correction frame that cancel. The diagnostic recovers the held 388-term initial row exactly, but that comparison still requires Lean replay at the level of realized classes.
- **Medium verification defects repaired:** Repeated table reduction made the first proof representations impractical. Balanced lookups, checked coefficient records, explicit graph bijections and expansion of finite weighted sums avoid that repetition without changing the statements. Negative tests now prove six explicit inequalities; a reduction failure or particular error message cannot pass as rejection evidence.

No concrete defect was found in the reviewed pre-existing statements. Existing definitions, source relations, geometric obligations and numerical seeds are unchanged.

### Revisions and mathematical effect

[`StrataOperation.lean`](../../AxiomaticGW/Tautological/StrataOperation.lean) gives typed label, attachment and cotangent contexts with a proved graph action and preservation of realized zero under their primitive compatibilities. [`GraphIsomorphismHint.lean`](../../AxiomaticGW/Tautological/GraphIsomorphismHint.lean) checks supplied finite bijections, incidence and all decorations. The coordinate replay and record helpers bind every retained source term to its actual image. [`RationalPsiRelation.lean`](../../AxiomaticGW/Tautological/RationalPsiRelation.lean) derives the genus-zero source rows from the existing universal-curve formula and component dimension.

The [815-column frame](../../AxiomaticGW/Tautological/L24Graphs.lean), six marking permutations and all 71 contexts have kernel coverage. The [four-part incoming replay](../../AxiomaticGW/Tautological/Fixtures/L24CorrectionsReplay.lean) verifies every row and the complete sum. [`L24Primitive.lean`](../../AxiomaticGW/Tautological/L24Primitive.lean) independently fixes the four published diagrams with coefficients 1, 3, -3, -3 before averaging. It proves the 18-column primitive projection and that every retained genus-two vertex has at most one cotangent factor; the other 703 terms remain in the full candidate. [`L24Assembly.lean`](../../AxiomaticGW/Tautological/L24Assembly.lean) proves the actual correction assembly and conditional preservation of realized zero.

[`L24Initial.lean`](../../AxiomaticGW/Tautological/L24Initial.lean) constructs all 120 original BP marking assignments, the signed pullback, weighted psi factor and prescribed average. Its vanishing follows from the original BP relation and primitive geometry. [`DecoratedComponentDimension.lean`](../../AxiomaticGW/Tautological/DecoratedComponentDimension.lean) proves local dimension vanishing, including existing node powers; [`CotangentDimensionReplay.lean`](../../AxiomaticGW/Tautological/CotangentDimensionReplay.lean) justifies pruning only after this class-level argument. Applying that API to the full BP row is the next step. No final L24 class vanishing is asserted.

The only new global instance decides the finite proposition `GraphIsomorphismHint.Valid`; there are no new global simp rules or coercions. The [mathematics-to-Lean map](../MathematicsToLean.md), roadmap and plan record this exact scope.

### Validation

The [validation manifest](../../environments/l24-corrections-validation.json) records commands, source hashes, axiom dependencies and repairs. Final checks pass:

- `lake build AxiomaticGW.Tautological.L24Assembly`: 1862 jobs. `lake build`: 2814 jobs. `lake test`: 2880 jobs, 22.635 seconds. `lake lint`: passes after documenting the three new graph-hint fields.
- `lake env lean AxiomaticGWTest/Tautological/L24Contexts.lean`: 13 API examples, including malformed bijections, node-branch and kappa distinctions, distinct marking permutations and local dimension cases that global codimension alone cannot detect.
- `python3 -B scripts/test_l24_corrections.py`: four methods pass, including six kernel-proved inequalities for corrupted coefficients or destinations, 15 schema/context mutations, duplicate-key rejection and reproducibility of all four generated modules. `python3 -B scripts/test_l24_normalization.py`: two methods and seven mutation cases pass.
- `python3 -B scripts/export_l24_corrections.py environments/l24-normalization-exploration.json --output AxiomaticGW/Tautological/Fixtures/L24CorrectionsReplay.lean --check` passes. A fresh-cache Sage/admcycles run reproduces the complete report byte for byte, SHA256 `227cd365a71aa1377c2b6c79c5a15b3217edbaf348cab6bcc8f4ab2c543cebe7`; online lookup is disabled.
- A fresh native decorated-pullback export matches its previous source pin. `scripts/audit_l24_initial.py` reproduces the [initial-row diagnostic](../../environments/l24-initial-dimension-audit.json), and a changed native payload is rejected.
- `lake env lean /tmp/gw_l24_corrections_axioms_20261003.lean`: all 35 audited results depend only on `propext`, `Classical.choice` and `Quot.sound`. Placeholder scans, `git diff --check`, incremental diff and local-link checks pass. All 504 unrelated baseline files and the five pinned GKM producer modules are unchanged.

Development failures in generated layouts, namespace qualification and rewrite transparency were repaired without weakening statements. The remaining warnings are the pre-existing private Basic test module and upstream Sage Algebras deprecation; the final linter passes.

### Remaining work and next priority

Replay the actual initial BP expression in an auxiliary frame retaining all 45 cancelling classes. Apply the proved local dimension theorem, prove the retained graph destinations, and check the exact cancellation before identifying `initialClaim`. Then compose original source geometry into the complete L24 class relation and its full-class GW equation. Uniform surface pivots, finite-seed sufficiency, termination, uniqueness, every fixed P²/F₁/Bl₂P² suite and full class-valued semisimple GKM compatibility remain open. No application, energy bound or completion gate has been narrowed.

## 2026-10-03: Certified genus-two psi pullbacks and a direct complete L24 candidate

**Status:** Both original genus-two psi relations now have proved signed pullbacks with arbitrary additional markings and full-class GW contraction equations. The three concrete higher-arity inputs to the L24 route have exact Sage comparison and offline Lean replay. A separate complete 721-term L24 candidate is reproducible and checked at the Python graph-operation level; its full class assembly still awaits Lean proof. R7, the research goal and full semisimple GKM compatibility remain open. No numerical seed, commit or push was added.

### Scope and findings

Reviewed the existing square/product source packages, decorated universal-curve expansion, raw graph realization and GW contraction APIs, and their composition for the L24 higher-power step. The 497-file baseline and all 313 preceding pins were checked before editing, and the targeted baseline build passed. This was a focused pullback and reconstruction-input review, not a comprehensive review of geometric models or the GKM producer.

- **High planned gap addressed:** The previous one- and two-marked relations were insufficient as explicit inputs on three-marked components. The new pullbacks preserve all negative rational-tail corrections, repeated placements and original node powers. Their validity follows from the original six Mbar(2,1) or ten Mbar(2,2) interior rows and already identified component rows, with primitive geometry. No higher-arity source vanishing is added.
- **High remaining proof boundary:** The paper's primitive L24 description is not a complete raw class equation. The new experiment keeps the 703 nonprimitive terms in addition to its 18 primitive terms. It uses no new interior FZ search, but its complete contextual derivation has not yet been connected to Lean.
- **Medium development defect corrected:** Native Sage constructors retained and mutated genus/kappa lists supplied by the proposed independent comparison helper. Copies at that boundary prevent changes to the held source graphs. Each native check now verifies that its inputs are unchanged, its output is one unit monomial, and its decorated incidence equals the independently constructed graph. This was a defect in the new experimental helper, not in a pre-existing formal statement.

No concrete defect was found in the reviewed pre-existing theorem statements. No declaration was weakened or renormalized. No foundational module, original certificate, seed, instance, coercion or global simp rule changed.

### Revisions and mathematical effect

[`CotangentCombination.lean`](../../AxiomaticGW/Tautological/CotangentCombination.lean) packages a finite rational multiset of existing decorated gluing expressions. `map_strata_pullback` and `pullback_vanishes` derive its actual iterated pullback from primitive cotangent, section and gluing laws. `gwContraction_eq_zero` supplies the entire signed metric contraction at any full curve class and external powers.

[`GenusTwoPsiForgetful.lean`](../../AxiomaticGW/Tautological/GenusTwoPsiForgetful.lean) proves that the signed square and product combinations are exactly the original independently held requests. In both namespaces, `realized_relation_with_markings_from_generators` derives arbitrary-marking class validity from the original sources; `gw_relation_with_markings` gives the full GW equation. All constructed terms keep codimension two. These are relation families, not a solved surface recursion or termination theorem.

[`CotangentReplay.lean`](../../AxiomaticGW/Tautological/CotangentReplay.lean) checks coverage by actual graph isomorphisms before identifying a coordinate vector with a formal sum. The default lookup value has no mathematical force without coverage. [`GenusTwoPsiPullbacks.lean`](../../AxiomaticGW/Tautological/GenusTwoPsiPullbacks.lean) holds the square on two and three markings and product on three markings. Their [incoming replay](../../AxiomaticGW/Tautological/Fixtures/GenusTwoPsiPullbacksReplay.lean) retains 23, 53 and 62 nonzero raw terms. Each leading coefficient is one; every other term has a boundary edge, no kappa and at most one psi factor. Old markings precede newly added markings.

The [direct L24 search](../../scripts/search_l24_normalization.py) starts with the complete BP pullback times the weighted psi combination, accounting for the original six-assignment normalization. It then applies 13 square and 16 product reductions, 37 rational psi reductions and five WDVV corrections. Its [full report](../../environments/l24-normalization-exploration.json) has 721 terms, including 27 with a genus-two vertex. All 1,516 raw substitutions agree with the native admcycles graph operation, and three intersection diagnostics vanish. The [offline Python regression](../../scripts/test_l24_normalization.py) rebuilds every correction row from the separately replayed psi coordinates and explicit rational/WDVV graph contexts and verifies the entire sum. Neither these diagnostics nor this Python check constitutes Lean certification of the L24 class equation.

### Validation

The [validation manifest](../../environments/genus-two-psi-pullbacks-validation.json) records commands, hashes, scope and repairs. Final validation passes:

- `lake build AxiomaticGWTest.Tautological.GenusTwoPsiPullbacks`: 1837 jobs, ten API examples; `lake build`: 2795 jobs, 2.613 seconds; `lake test`: 2860 jobs, 22.739 seconds; `lake lint`: 8.296 seconds.
- Fresh-cache runs of `scripts/search_genus_two_psi_pullbacks.py` reproduce the 13194-byte report, SHA256 `99b712144f5d6bec361f3927865c3592db614aa4fd47a2e8398795c596444232`. Fresh-cache L24 runs reproduce the 1554508-byte report, SHA256 `227cd365a71aa1377c2b6c79c5a15b3217edbaf348cab6bcc8f4ab2c543cebe7`. Online lookup is disabled by both scripts.
- `python3 -B scripts/export_genus_two_psi_pullbacks.py environments/genus-two-psi-pullbacks-exploration.json --output AxiomaticGW/Tautological/Fixtures/GenusTwoPsiPullbacksReplay.lean --check` passes.
- `python3 -B scripts/test_genus_two_psi_pullbacks.py`: three test methods pass in 53.144 seconds, including nine malformed/provenance mutations, duplicate-key rejection and five kernel-rejected altered mathematical claims. The Lean examples also reject accepting an absent graph through the lookup default. `python3 -B scripts/test_l24_normalization.py`: two methods pass, rebuilding the full candidate and rejecting seven altered operations or omitted corrections.
- `lake env lean /tmp/gw_psi_pullbacks_axioms_20261003.lean`: sixteen audited theorems use only `propext`, `Classical.choice` and `Quot.sound`. Placeholder/substitute-axiom scans, final-diff, whitespace, local-link and source-preservation checks pass. All 490 unrelated baseline files and five pinned GKM producer modules are unchanged.

Early label-decision case elimination, integer/rational coercion and graph-table reduction failures were repaired without changing statements. New linter warnings were removed. The remaining warnings are the pre-existing all-private Basic test module and the upstream Sage Algebras deprecation. The full target, build, test and lint succeeded after these repairs.

### Remaining work and next priority

Prove the actual contextual attachments and rational/WDVV corrections in the complete 721-term L24 derivation, tying the initial BP-derived vector and final raw class sum to the already proved geometry. Then derive the surface equations and uniform pivots, finite-seed sufficiency, termination and uniqueness. Higher-power surface evaluation, stable-map descendant composition, every fixed benchmark and full semisimple GKM CohFT interoperability remain required. The applications P², F₁ and Bl₂P², energy bound, fixed suites and geometric obligations are unchanged.

## 2026-10-03: Complete two-marked genus-two cotangent-product relation

**Status:** A claim-bound Sage certificate and offline Lean replay now give a complete $\psi_1\psi_2$ relation on $\overline M_{2,2}$, its actual boundary source maps and a full-curve-class GW ancestor consequence with arbitrary further powers at both markings. This is a higher-power ingredient for the $L_{2,4}$ route. R7, the complete research goal and full semisimple GKM compatibility remain open. No numerical seed was added; no commit or push was made.

### Scope and findings

Reviewed the original BP, decorated forgetful, external-psi, original component-source and raw contraction APIs; the [Wennink Sections 4, 7 and 8](https://arxiv.org/html/2210.04038); and the pinned admcycles original FZ coefficient and boundary-substitution routines. The targeted baseline build passed, all 304 prior source pins matched the 487-file snapshot, and no defect was found in the reviewed pre-existing statements. This is a focused relation and consumer review, not a comprehensive geometric-model or GKM audit.

- **High planned gap addressed:** A square at one marking does not supply the product at two different markings. The new independently held 38-column frame proves the complete product relation using ten identified original interior 3-spin rows and three separating images. Those three component rows are reused exactly from the existing BP source package.
- **High mathematical boundary preserved:** The boundary is not entirely lower genus. One of its 25 terms has a genus-two vertex, with coefficient three in raw normalization. `genusTwo_tail` proves that this vertex has one marking and psi on its node branch. The other 24 terms have component genus at most one. Omitting the same-genus term is rejected by replay.
- **Medium replay cost corrected:** The initial brute-force coordinate-inverse proof made the isolated core compile take 232.166 seconds. A proof using finite linear-combination maps and the exceptional coordinate gives the same inverse statement without enumerating the entire cubic coordinate check. The core's subsequent build reported 9.7 seconds. These are development observations, not a controlled performance benchmark.
- **High remaining obligation:** The ten original Mbar(2,2) interior vanishings are explicit new geometric obligations for this consumer. Their original parameters and coefficients are recorded; they are not inferred from the earlier BP geometry, a numerical oracle or intersection diagnostics. Primitive attachments derive the boundary-row vanishings rather than assuming the final product equation.

The full $L_{2,4}$ search found a complete 816-term candidate from the existing BP pullback times a psi combination and 89 boundary rows, with the independently transcribed 18-term primitive part. No new interior Mbar(2,4) row was needed in that experiment. This candidate is **Sage exploration only**, not a Lean-certified $L_{2,4}$ equation. Attempts to force every separate source block to be kappa-free were insufficient. The two-marked product was then isolated as a smaller reusable normalization input; no primitive-part identity was substituted for a full class identity. Historical reconstruction code was read as source, not executed or unpickled.

### Revisions and mathematical effect

[`GenusTwoPsiProduct.lean`](../../AxiomaticGW/Tautological/GenusTwoPsiProduct.lean) holds the graphs, the full request, original and monomial rows, invertible kappa-coordinate tables and decorated automorphism orders. Kernel arithmetic proves the 13-row combination. The coefficient-one leading graph is the actual external psi product, and the formal relation is proved nonzero before geometric vanishing is supplied.

[`GenusTwoPsiProductSources.lean`](../../AxiomaticGW/Tautological/GenusTwoPsiProductSources.lean) builds three actual attachments, checks every source-column image and derives their vanishings from the existing component rows and primitive relabelling/separating laws. `realized_psi_product_from_generators` then proves the complete class identity under the stated original interior validity and cotangent/fundamental compatibility.

[`GenusTwoPsiProductGluing.lean`](../../AxiomaticGW/Tautological/GenusTwoPsiProductGluing.lean) constructs and identifies all 25 raw decorated gluings. `gwAncestor_reduction_from_generators` integrates against arbitrary full curve classes and independent additional powers at the two markings. It retains signed inverse metrics, full splittings, every original node decoration and the one-marked genus-two contribution. It is an ancestor equation; a general surface evaluator, stable-map descendant composition and well-founded reconstruction are not claimed.

The [search](../../scripts/search_genus_two_psi_product.py), [exporter](../../scripts/export_genus_two_psi_product.py), [held report](../../environments/genus-two-psi-product-exploration.json), [incoming replay](../../AxiomaticGW/Tautological/Fixtures/GenusTwoPsiProductReplay.lean) and regressions provide a reproducible workflow. No pre-existing mathematical statement, seed, instance, coercion, global simp rule or producer module changed. The only pre-existing Lean edit adds the two public imports to the project root.

### Validation

The [validation manifest](../../environments/genus-two-psi-product-validation.json) records exact commands, hashes, development failures and scope. Final checks pass:

- `lake build AxiomaticGW.Tautological.GenusTwoPsiProductGluing AxiomaticGWTest.Tautological.GenusTwoPsiProduct`: 1826 jobs; `lake build`: 2790 jobs, 2.249 seconds; `lake test`: 2854 jobs, 29.994 seconds; `lake lint`: 8.489 seconds.
- Two fresh-cache offline Sage searches reproduce the 179364-byte report exactly, SHA256 `b22e8c432358044fec84188b96a5747cdf3ff14d4317686ebe6c661d62fe85b0`. Four complementary external-psi intersection diagnostics vanish; these are additional tests, not geometric proofs. `python3 -B scripts/export_genus_two_psi_product.py environments/genus-two-psi-product-exploration.json --output AxiomaticGW/Tautological/Fixtures/GenusTwoPsiProductReplay.lean --check` passes.
- `python3 -B scripts/test_genus_two_psi_product.py`: four test methods pass, including twelve schema/provenance mutations, eight kernel-rejected mathematical mutations and an accepted isomorphic loop-branch presentation. The mathematical mutations cover the wrong node branch, replacing the product by a square, omission of the genus-two tail, a changed original row, hidden automorphism division, a wrong decorated order, coherently erased kappa conversion and a self-consistent zero claim. Ten Lean API examples pass.
- `lake env lean /tmp/gw_product_axioms_20261003.lean`: fifteen audited results use only `propext`, `Classical.choice` and `Quot.sound`. Placeholder, substitute-axiom, whitespace, final-diff, local-link and source-preservation checks pass. All 480 unrelated baseline files and the five pinned GKM producer modules are unchanged.

Initial dependent-case, constructor-inference and test elaboration errors were repaired without changing the statements. One reproducibility attempt used the same path for its report and timing record; that local output was overwritten by the timing wrapper. The repeat used distinct paths and matched the held report. The final warnings are the pre-existing all-private `Basic` test module and the upstream Sage Algebras deprecation. No project-specific axiom, `sorryAx` or native proof decision was added.

### Remaining work and next priority

Use the complete two-marked product, one-marked square and rational cotangent relations to normalize the full BP-derived $L_{2,4}$ candidate, and prove every correction through the existing pullback and gluing laws. Then construct the surface consumer and prove uniform pivots, finite-seed sufficiency, termination and uniqueness. Arbitrary-marking higher-power reconstruction, stable-map descendants, every fixed numerical suite and full semisimple GKM CohFT import remain required. The target surfaces, energy bound, benchmark suites and R1/R3–R5/R7–R8 gates are unchanged.

## 2026-10-03: First-descendant BP normalization and two derived initial values

**Status:** Primary and one-power genus-two ancestor variables now reduce to the canonical stable-map point/first-descendant families, with the negative rational-tail comparison derived from the existing primitive geometry. The entire BP equation is preserved by this substitution. On the two-point blowup, the degree-zero primary point and the cross-exceptional first descendant are proved zero from the original source relations and unchanged finite seeds. This advances R7; the full recursion, all fixed suites and complete semisimple GKM CohFT interoperability remain open. The goal remains active. No commit or push was made.

### Scope and findings

Reviewed the surface primary/divisor, symmetric insertion, mixed cotangent, first-calibration and affine BP APIs; their new composition; the relevant [Wennink Sections 7–8](https://arxiv.org/html/2210.04038); and the pinned native GKM first-calibration comparison. Both targeted baselines passed. All 291 preceding source pins matched the 474-file working-tree snapshot. This is a focused normalization and consequence review, not a comprehensive review of geometric realizations or the GKM producer.

- **High planned gap addressed:** Divisor equations for stable-map descendants cannot simply be applied to ancestor variables. `SurfacePolynomialReduction.eval_onePsiTerms` solves the primitive mixed comparison for the ancestor, giving the negative sum over every positive tail and the reconstructed first-calibration matrix. `SurfacePolynomialReduction.eval_normalizedTerms` then applies the numerical descendant laws. Variable tags and full classes are retained.
- **Critical development integration defect corrected:** The first full build detected two new declarations duplicating the existing `SurfaceAncestorKey.descendantEval` API. The three existing genus-independent declarations were moved verbatim from `GenusZeroFullDescendants.lean` to `DescendantKeys.lean`, and publicly reimported. The duplicate definitions were removed. Existing names, statements, proofs and downstream access are unchanged; the final full build and genus-zero/one regression replays pass.
- **Medium comparison-coverage gap corrected:** In the initial small primitive-class equations the primary-reduced tail corrections vanish, so reversing the comparison sign was not detected. Additional twice-exceptional and mixed-class probes produce nonzero corrections and reject that mutation. This was a deficiency in the proposed test corpus, not a discovered defect in the geometric law.
- **High remaining obligation:** The finite normalized systems still leave coupled input-class unknowns. The plane-line sample has rank one with two unknowns; the F₁ fiber sample has rank two with three. These finite ranks do not decide the rank of the full BP family or prove a uniform reconstruction step.

No defect was found in the reviewed pre-existing mathematical statements. No global simp rule, instance, coercion, numerical oracle, substitute axiom or additional seed was introduced.

### Revisions and mathematical effect

[`FirstDescendantReduction.lean`](../../AxiomaticGW/Surfaces/FirstDescendantReduction.lean) extends primary reduction to degree zero for genus at least two, where all remaining arities are stable. String and dilaton remove unit insertions; divisor removes one primary occurrence at a time, with the classical cup correction. Its executable closed formula preserves multiplicities and exceptional squares $E_i^2=-\mathrm{pt}$, and never divides by a possibly zero curve pairing. Exact integer dimension filtering is proved sound. A dimension-compatible degree-zero point invariant remains a query until separately determined.

[`OnePsiComparison.lean`](../../AxiomaticGW/Surfaces/OnePsiComparison.lean) and [`OnePsiReduction.lean`](../../AxiomaticGW/Surfaces/OnePsiReduction.lean) compose this with the reconstructed first calibration and primitive cotangent law. Every positive tail has strictly smaller main energy. Higher powers stay tagged ancestors. [`AffineSubstitution.lean`](../../AxiomaticGW/Coefficients/AffineSubstitution.lean) preserves constant terms and requires a proof that the input monomials have cardinality at most one. [`GenusTwoNormalizedBP.lean`](../../AxiomaticGW/Surfaces/GenusTwoNormalizedBP.lean) uses the already proved support bound to derive the full normalized equation, for arbitrary added markings and external powers, without asserting that all resulting variables are solved.

The [held fixtures](../../AxiomaticGW/Surfaces/Fixtures/GenusTwoNormalizedBP.lean) kernel-check four small normalizations and one additional complete original BP expansion, with class $L_{12}$ and states $E_1,E_2,H$. Its normalized equation is

$$\frac1{240}-12\langle\mathrm{pt}\rangle_{2,0}-12\langle\tau_1(E_1)\rangle_{2,0}-12\langle\tau_1(E_2)\rangle_{2,0}+12\langle\tau_1(H)\rangle_{2,0}=0.$$

Substituting the existing genus-two divisor seeds, $-1/2880$ for each exceptional divisor and $-1/960$ for $H$, derives $\langle\mathrm{pt}\rangle_{2,0}=0$. The separately checked $E_2$ equation with three $E_1$ states derives $\langle\tau_1(E_1),\mathrm{pt}\rangle_{2,E_2}=0$. [`SurfaceGenusTwo.blowupTwo_initialValues`](../../AxiomaticGW/Surfaces/GenusTwoDerivedInitialValues.lean) proves both under the original BP/WDVV/Getzler/psi source validity, primitive GW and cotangent geometry, and unchanged finite seeds. Neither zero value is assumed, and no unproved blowdown identification extends these conclusions to another target.

### Verification

The [validation manifest](../../environments/surface-bp-normalized-validation.json) records commands, hashes, timings, failed development checks and scope. Final checks pass:

- `lake build`: 2786 jobs, 26.591 seconds; `lake test`: 2849 jobs, 60.128 seconds; `lake lint`: 8.970 seconds. All changed Lean modules, directly affected genus-zero/one descendants and GKM regression replays compile. Fifteen new kernel/API examples check degree-zero queries, repeated divisors, zero pairings, signed corrections, higher-power preservation and affine support.
- `lake build surfaceBPNormalized AxiomaticGW`: 5494 jobs. The final `.lake/build/bin/surfaceBPNormalized` run took 76.636 seconds and reproduced the prior 142911-byte payload exactly, SHA256 `1e02b8f07221e07a0c4f12e93936fb6173bbae31c116d87f22c2eb94c7de529f`.
- `/opt/homebrew/Caskroom/miniforge/base/envs/axiomatic-gw-sage/bin/python -B scripts/explore_normalized_surface_bp.py --ancestor-input /tmp/gw_surface_bp_payload_final_20261003.json --lean-input /tmp/gw_normalized_bp_payload_final_20261003.json --output /tmp/gw_normalized_bp_exploration_final_20261003.json` passed. Two fresh-cache offline runs reproduce the [27710-byte report](../../environments/surface-bp-normalized-exploration.json), SHA256 `b5b587e97e3a6c649b6c250de63b9f3fd49c82b2597fa3d0f5d8ce615c3b2505`: ten full equations, 85 individual substitutions, five additional probes and 45 collected normalized monomials. Three new normalization mutations and four original graph mutations are rejected.
- `lake env lean /tmp/gw_normalized_bp_axioms_20261003.lean` audits 27 important results, including the two derived values. All use only `propext`, `Classical.choice` and `Quot.sound`. Placeholder/substitute-axiom, final-diff, whitespace, documentation-link and source-preservation checks pass. Three moved declarations are byte-for-byte unchanged.

The original BP lower-genus numbers remain shared Lean outputs; the comparison independently redoes the admcycles contraction and recursive normalization, using previously checked native GKM first-calibration matrices. It is not an independent derivation of all GW numbers or an imported CohFT class. Original BP data, seed declarations, foundational rational terms, existing numerical tables and all five pinned GKM producer modules are preserved. All 465 unrelated baseline files are unchanged.

Intermediate elaboration repairs and one concurrent-build artifact race are recorded separately from the successful serial validation. The remaining warnings are the pre-existing all-private test module and upstream Sage Algebras deprecation. Peak host-reported build memory was about 6.53 GB; timings describe this checkout and finite corpus, not arbitrary marking counts or the full genus-two energy-twelve suite.

### Remaining work and next priority

Derive a complete class-level $L_{2,4}$ equation and its checked surface consumer, then prove uniform pivots for the coupled normalized system. The source's primitive-symbol identity alone is insufficient as a full relation. Complete the remaining low-power and multi-marked sectors, finite-seed sufficiency, well-founded recursion, uniqueness, stable-map descendant composition and every fixed numerical benchmark. Full class-valued semisimple GKM import, reconstruction-action conditions, geometric applicability and ordinary comparison remain required. The fixed targets, benchmark bounds and R1/R3–R5/R7–R8 acceptance gates are unchanged; R2 and conditional R6 acceptance are preserved.

## 2026-10-03: Affine surface BP equations and full-class dependency bounds

**Status:** The complete signed BP family now has an executable surface polynomial and a kernel theorem deriving its vanishing from the original geometric inputs and unchanged finite low-genus seeds. After dimension vanishing and genus-zero/one reconstruction, every term is constant or a single genus-two ancestor. Separating **all** input-class variables leaves strictly smaller energies. This advances R7 without accepting it, adding seeds or changing any fixed application, benchmark or GKM completion gate. No new genus-two invariant value or invertible recurrence is claimed. The goal remains active; no commit or push was made.

### Scope and findings

Reviewed the existing decorated contraction, rational-term, ancestor-key, dimension-reduction and low-genus reconstruction APIs, the full BP source and forgetful consumer, and [Wennink, Sections 7–8](https://arxiv.org/html/2210.04038). The targeted baseline build passed; all 282 preceding source pins matched a 464-file working-tree snapshot. This is a focused surface-specialization and support review, not a complete audit of all geometry or GKM code.

- **High planned gap addressed:** The complete relation previously had no surface polynomial closing its lower-genus components against the existing finite-seed algorithms. The new theorem composes precisely those existing proofs; it assumes no genus-two family, final recurrence or extra seed.
- **High remaining obligation isolated:** One nonzero coefficient is insufficient when several input-class genus-two unknowns remain. A proved full-class partition isolates that entire linear system. The ten sample equations are not square invertible systems: for example the plane-line sample has rank one with two input-class unknowns. This is evidence about these samples, not a proof that the full BP family is insufficient.
- **Medium runtime defect resolved in the consumer:** Native profiling located the initial stall in `paperNormalization`, whose lookup traverses the original hundred-column nested finite vector. The all-case attempt was stopped after 276 seconds without a payload, and a focused zero-class probe was stopped after 116 seconds. `rawPaperCoefficient_eq` checks a direct twenty-case lookup against the unchanged published coefficient times normalization. With that verified lookup, all ten cases completed in 69.397 seconds. Original graph tables, normalization definitions and theorem statements are preserved.
- No mathematical defect was found in the reviewed existing theorem statements. No global simp rule, instance, coercion, substitute axiom or native proof decision was added.

### Revisions and mathematical effect

[`DecoratedTermExpansion.lean`](../../AxiomaticGW/Surfaces/DecoratedTermExpansion.lean) extends the existing `RationalTerms` computation format to original node and leg decorations. `eval_surfaceDecoratedTerms` proves its algebraic meaning and zero decorations recover `surfaceTerms` exactly. The existing foundational term module is preserved byte for byte; a local bind-evaluation argument handles the signed graph sum in the new surface consumer.

[`GenusTwoTerms.lean`](../../AxiomaticGW/Surfaces/GenusTwoTerms.lean) executes signed dimension vanishing and the existing lower-genus algorithms. Residual keys retain genus, every effective coordinate, and the multiset of paired states/powers. `termsBound_decorated` bounds total residual genus and gives an effective remainder in the original curve class. `MonomialBound.affine` proves linearity in genus-two variables. `eval_split_by_class`, `sameClassTerms_dependencies` and `smallerClassTerms_dependencies` give an exact coupled system and strict anticanonical-energy decrease for its remainder. Degree-zero genus-two ancestors remain explicit until a proved reduction or audited seed determines them.

[`Surfaces/BelorousskiPandharipande.lean`](../../AxiomaticGW/Surfaces/BelorousskiPandharipande.lean) retains all twenty diagrams, six assignments, signed rational-tail corrections, full class splittings, signed inverse metrics and arbitrary upstairs powers. `eval_genusTwoTerms_eq_zero_from_geometry` discharges the lower-genus identifications using the original finite line/exceptional and elliptic-divisor seeds and named geometry. [`BelorousskiPandharipandeCoefficients.lean`](../../AxiomaticGW/Tautological/BelorousskiPandharipandeCoefficients.lean) supplies only the proved computational lookup. The [three small complete equations](../../AxiomaticGW/Surfaces/Fixtures/GenusTwoBP.lean) have claim-bound kernel coefficient replay for the plane, F₁ and the two-point blowup. They are equations in **ancestors**, not certified descendant values.

### Verification

The [validation manifest](../../environments/surface-bp-validation.json) records commands, timings, source hashes, development failures and limitations. Final checks passed:

- `lake build`: 2778 jobs; `lake test`: 2840 jobs, including eleven new API/kernel examples and three complete polynomial replays; `lake lint`.
- `lake build surfaceBP` and `.lake/build/bin/surfaceBP`: ten equations, a 2672962-byte payload, SHA256 `dddb622b1b3b8b2a5c15c8cf393b429dfd7d5d348b1b8a2198f9b87675cf44e3`.
- The Sage command `/opt/homebrew/Caskroom/miniforge/base/envs/axiomatic-gw-sage/bin/python -B scripts/explore_surface_bp.py --lean-input /tmp/gw_surface_bp_payload_fast_20261003.json --output /tmp/gw_bp_surface_sage_final1_payload_20261003.json` checked all ten symbolic contractions and their affine substitutions. The second run used `--output /tmp/gw_bp_surface_sage_final2_payload_20261003.json`; both complete commands are recorded in the manifest. Four deliberately incorrect variants are rejected: positive exceptional metric, missing marking assignments, omitted rational-tail corrections and collapse of full classes to energy.
- Two fresh-cache offline runs give the identical [6995-byte report](../../environments/surface-bp-exploration.json), SHA256 `744d94ab338f0d284b979b57d581038ffd34b5dc7961a27fd5b930816b7b28bc`. Lower-genus numbers are shared outputs of the already proved Lean algorithms; the external comparison independently checks contraction and substitution, not a second numerical derivation.
- Nineteen `#print axioms` audits use only `propext`, `Classical.choice` and `Quot.sound`. Original BP exporter `--check`, source-pin preservation, placeholder/substitute-axiom scan, final-diff, whitespace and local-link checks pass.

An initial full build was deliberately stopped after 620 seconds: a new helper in the foundational term module unnecessarily invalidated the expensive existing tables. That helper was removed, the module restored exactly, and the final full build rerun. The only retained warnings are the pre-existing all-private test module and upstream Sage Algebras deprecation. All 455 unrelated baseline files and all five pinned GKM producer modules are preserved. Native timing is for these small cases in the current checkout; arbitrary-marking performance and the energy-twelve genus-two suite were not tested or claimed.

### Remaining work and next priority

Reduce the coupled input-class ancestor variables using proved cotangent/divisor identities and the full $L_{2,4}$ equations where needed. Prove the resulting nonzero pivots and a well-founded recursion, audit genus-two seed sufficiency, then compose stable-map descendant reconstruction and run every fixed benchmark. All original geometric applicability obligations, full class-valued semisimple GKM input, reconstruction-action laws and ordinary comparison remain required. R1/R3–R5/R7–R8 remain open; R2 and the conditional R6 acceptance are unchanged.

## 2026-10-03: Decorated forgetful pullback and arbitrary-marking BP equations

**Status:** The complete BP equation now extends to any finite number of added markings and arbitrary upstairs ancestor powers, with the cotangent corrections at external and node flags derived in Lean. This advances R7 without accepting it or changing any fixed target, benchmark, seed inventory or GKM completion gate. No new numerical invariant, genus-two evaluator or imported CohFT class is claimed. The goal remains active; no commit or push was made.

### Scope and findings

Reviewed the existing raw gluing, universal-curve base-change, cotangent realization and BP consumer APIs, together with [Bae–Schmitt, Propositions 3.8–3.10](https://arxiv.org/pdf/2012.09887) and the pinned admcycles forgetful implementation. The baseline had 452 preserved files; all 271 preceding source pins matched and the targeted baseline build passed. This was a focused pullback and integration review.

- **High planned gap addressed:** The undecorated placement rule cannot pull back BP's component cotangent factors. The derived formula adds one negative rational tail per positive original power, with that power decreased by one at the main attaching flag. The coefficient is −1, independent of the exponent. Other component powers are retained.
- **Medium computation and normalization obligations resolved:** Explicit decisions on component-label equality make the finite graph expansion executable. Signed multisets preserve repetitions and multiply signs under iteration. The existing node bijections ensure that a new marking does not replace a gluing flag. Kernel proofs preserve total codimension and the component-genus bound.
- No pre-existing mathematical defect was found in the reviewed APIs. Four rational-tail declarations and `CotangentCompatible` were moved verbatim into shared modules so the new layer can use them without importing the genus-one certificate or the decorated numerical consumer. Existing names, signatures and downstream import access are preserved.

### Revisions and mathematical effect

[`RationalTailPullback.lean`](../../AxiomaticGW/Tautological/RationalTailPullback.lean) derives cotangent powers and arbitrary monomials from the existing one-psi comparison, actual raw tail identification, projection formula, cotangent restriction and the primitive section identity `TailForgetCompatible`. This new geometric input says that forgetting after attaching the three-point tail recovers the main projection. It assumes no decorated pullback formula, relation or numerical recurrence.

[`DecoratedGluingRealization.lean`](../../AxiomaticGW/Tautological/DecoratedGluingRealization.lean) identifies component-monomial evaluation with the existing graph realization. [`DecoratedGluingMarking.lean`](../../AxiomaticGW/Tautological/DecoratedGluingMarking.lean) constructs the signed outputs using the existing expression syntax and decorations. [`DecoratedGluingForgetful.lean`](../../AxiomaticGW/Tautological/DecoratedGluingForgetful.lean) proves their class meaning for any finite iteration from primitive gluing base change. [`DecoratedGluingMarkingBounds.lean`](../../AxiomaticGW/Tautological/DecoratedGluingMarkingBounds.lean) proves the graph bounds independently of cohomology.

[`BelorousskiPandharipandeForgetful.lean`](../../AxiomaticGW/Tautological/BelorousskiPandharipandeForgetful.lean) retains all twenty diagrams, six assignments, original raw coefficients, full curve splittings and arbitrary added-marking ancestor powers. `gw_forget_relation_from_generators` consumes the same accepted BP exchange and original source equations. The sixteen lower-genus terms stay in component genus at most one. Existing theorem statements and assumptions were not changed; the new universal-curve inputs are explicit. There is no new seed, substitute axiom or global simp/instance/coercion change.

### Verification

The [validation manifest](../../environments/decorated-forgetful-validation.json) records exact commands, hashes, timings, resource observations and limitations. Final checks passed:

- `lake build`: 2773 jobs; `lake test`: 2834 jobs, including eight new kernel/API regressions; `lake lint`.
- `lake build decoratedPullback`, then `.lake/build/bin/decoratedPullback`: actual native expansion of 252 cases, with 1,159 signed terms in a 235907-byte payload.
- `/opt/homebrew/Caskroom/miniforge/base/envs/axiomatic-gw-sage/bin/python -B scripts/explore_decorated_pullback.py`: every raw decorated-incidence comparison passed. The 250 raw-vector checks include the two full weighted BP equations, whose free supports have 118 and 315 coordinates. Four deliberately incorrect expansions were rejected. This uses no relation quotient or geometric zero oracle.
- Two fresh-cache offline Sage runs produced the identical [62642-byte report](../../environments/decorated-forgetful-exploration.json), SHA256 `86cf72f217babf9b3deefe3d3fad443de0032ffe78dcc90c0d68e34c67601699`. Native output is diagnostic evidence, separate from the general kernel proofs.
- Twenty-five `#print axioms` audits use only `propext`, `Classical.choice` and `Quot.sound`. The original BP exporter `--check`, source-pin and moved-API checks, placeholder scan, final-diff inspection, whitespace and local-link checks passed.

The only remaining warnings are the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean` and upstream Sage Algebras deprecation. All 441 unrelated baseline files and all five pinned GKM producer modules are preserved. The native benchmark covers one and two added markings; it is not an arbitrary-marking performance claim. The new Lean theorems have no such finite marking bound.

### Remaining work and next priority

Specialize the complete signed BP contractions to the fixed surface basis and prove nonzero leading coefficients and decreasing residual genus-two requests. The full $L_{2,4}$ equation, finite-seed sufficiency, termination, uniqueness, stable-map descendant composition and every fixed genus-two benchmark remain required. Kappa-decorated forgetting is outside this increment. Original geometric input validity, complete semisimple GKM CohFT import with its coefficient/descendant/ordinary comparisons, and R8 remain open. The existing conditional R6 acceptance and all other milestone gates are unchanged.

## 2026-10-03: Complete published BP certificate and decorated GW equation

**Status:** The full Belorousski–Pandharipande equation on Mbar(2,3) now has a reproducible Sage certificate, offline kernel replay, original component-gluing provenance and a GW contraction theorem. This is an R7 reconstruction input, conditional on original source-row validity and primitive geometry. No new genus-two numerical invariant, complete surface recursion or imported GKM CohFT class is claimed. The goal remains active; its targets, benchmark bounds, seed inventory and acceptance gates are unchanged. No commit or push was made.

### Scope and findings

Reviewed the twenty diagrams in [BP, Theorem 1, equation (4), page 4](https://arxiv.org/pdf/math/9803072), the original [3-spin source](https://arxiv.org/pdf/1303.1043), the relevant surface route in [Wennink, Sections 7–8](https://arxiv.org/html/2210.04038), pinned admcycles row generation and coordinate conversion, existing graph/gluing/realization APIs and the new complete consumer. All 441 baseline files were hashed and all 261 preceding source pins matched. The targeted baseline build passed. This is a focused certificate and equation review, not a comprehensive geometric verification.

- **High planned reconstruction gap addressed:** The previous one-point psi-square reduction did not supply the full three-marked BP equation needed by the surface route. The complete relation, including all lower-genus terms, is now transferred to actual decorated GW contractions.
- **Medium normalization obligations resolved:** The paper sums all six marking assignments, including repetitions. Raw graph coefficients require label-fixing automorphism divisors, including the exchange of two unmarked elliptic tails. The genus-two cotangent terms distinguish the specified node branch from an external marking. Each convention is encoded and kernel checked.
- **Medium diagnostic fragility repaired:** Lean could exhaust its pretty-printing budget while reporting a rejected large graph or coefficient expression. The emitter now reports concise check-failure messages. This fallback constructs no proof. Each corruption must also have a separately compiled counterexample, so a generic failure alone is not accepted as evidence of a mathematical defect. Diagnostic-branch lint exceptions are scoped to the generated proof declarations and justified by these negative tests.
- **Low development issues repaired:** Dependent finite indices, original component construction, conversion elaboration and a large generated structure required local proof/emitter corrections. Three incoming matrices are separate definitions to avoid code-generator recursion. No pre-existing mathematical defect was found in the reviewed APIs; no existing theorem statement changed.

### Revisions and mathematical effect

[`BelorousskiPandharipandeGraphs.lean`](../../AxiomaticGW/Tautological/BelorousskiPandharipandeGraphs.lean) holds 100 raw decorated columns, the twenty published diagrams, six actual marking permutations and the independently fixed full request with 46 nonzero coordinates. Graph isomorphisms, decorated automorphism orders, marking multiplicities and stack-to-raw conversion are proved. The request is nonzero in the free strata module.

[`BelorousskiPandharipandeSources.lean`](../../AxiomaticGW/Tautological/BelorousskiPandharipandeSources.lean) constructs seven actual separating attachments using the existing graph operations. Its 53 source columns cover Mbar(2,2), Mbar(0,4), Mbar(2,1), Mbar(1,1), Mbar(1,4), Mbar(1,2) and Mbar(1,3); the elliptic frame and rows are reused. [`BelorousskiPandharipande.lean`](../../AxiomaticGW/Tautological/BelorousskiPandharipande.lean) checks twenty selected symmetrized rows, exact witness arithmetic, both kappa coordinate conversions and all sixteen component pushforwards. Four original interior row vanishings and sixteen original component row vanishings imply the full relation through primitive gluing and relabelling laws. The source parameters are retained; the general geometric 3-spin construction is not formalized by this certificate.

[`BelorousskiPandharipandeGW.lean`](../../AxiomaticGW/Tautological/BelorousskiPandharipandeGW.lean) constructs every published decorated gluing and derives `gw_relation_from_generators` over any commutative rational algebra. Every full curve-class splitting, inverse-metric contraction, original node power and external ancestor power is retained. Sixteen terms have only genus-zero/one components; the first four retain the genus-two sector to be solved. There is no new seed, geometric axiom, assumed BP vanishing, assumed final numerical recurrence or global simp/instance/coercion change.

The [Sage search](../../scripts/search_belorousski_pandharipande.py), [strict exporter](../../scripts/export_belorousski_pandharipande.py) and [actual incoming replay](../../AxiomaticGW/Tautological/Fixtures/BelorousskiPandharipandeReplay.lean) bind source and target graphs, both coordinate systems, the complete request, coefficients and operation provenance. Sage does exploration only; the replay requires ordinary Python and Lean.

### Verification

The [validation manifest](../../environments/belorousski-pandharipande-validation.json) records exact commands, source hashes, timings, raw memory observations and unsuccessful development attempts. Final checks passed:

- `lake build`: 2766 jobs.
- `lake test`: 2826 jobs, including fifteen new normalization, node-placement, component-map and complete geometric-consumer regressions.
- `lake lint`.
- Thirty-one `#print axioms` audits: only `propext`, `Classical.choice` and `Quot.sound`.
- `python3 -B -m unittest discover -s scripts -p test_belorousski_pandharipande.py -v`: four tests; 22 schema/provenance corruptions rejected, fifteen complete corrupted exchanges rejected with independent kernel counterexamples, and an equivalent graph presentation accepted.
- `python3 -B scripts/export_belorousski_pandharipande.py environments/belorousski-pandharipande.json --output AxiomaticGW/Tautological/Fixtures/BelorousskiPandharipandeReplay.lean --check`.
- Source-pin, placeholder, final-diff, whitespace and local-documentation-link checks.

Three fresh-cache offline Sage runs produce the same 362520-byte [report](../../environments/belorousski-pandharipande.json), SHA256 `5868b2f3ef1e5a45e6175b6349566b72c778f4ab028ef941b43498fd0ee8d1bc`. The search reads the full 65-by-100 original matrix and checks the selected component replacements, both basis maps and exact witness. Fifteen complementary external-psi intersection tests vanish, but are diagnostics sharing the same mathematical foundations, not proofs of full class equality. The formal relation comes from the kernel certificate under the named original geometric inputs.

Only the existing private-module warning in `AxiomaticGWTest/Basic.lean` and upstream Sage Algebras deprecation remain. All 433 unrelated baseline files and all five pinned GKM producer modules are preserved. Timings use the current checkout and compiled dependencies; they are not a fresh-clone or arbitrary-class performance benchmark.

### Remaining work and next priority

Extend the complete BP equation to additional markings and the fixed surface basis, then derive and check the nonzero leading coefficients and degree decrease needed to solve low-power and multi-marked genus-two sectors. The full $L_{2,4}$ equation, finite-seed sufficiency, terminating numerical reconstruction, uniqueness, stable-map descendant composition and every fixed genus-two benchmark remain required. Wennink's primitive-part comparison modulo WDVV is not treated as an unqualified full class identity. Original geometric generator validity, target/seed applicability, complete semisimple GKM CohFT import, coefficient/descendant/ordinary comparisons and the R8 research workflow remain open.

## 2026-10-03: Decorated node contractions and genus-two one-point ancestors

**Status:** Every one-point genus-two ancestor of cotangent power at least two is now conditionally reconstructed for P², F₁ and Bl₂P², at every full effective class, using the existing finite low-genus seeds. The research goal stays active. R7 remains open; no fixed application, benchmark bound, seed inventory or GKM completion requirement changed. No commit or push was made.

### Scope and findings

Reviewed the existing gluing/ancestor contractions, the held marked psi-square relation, the signed surface inverse metric, full curve splittings and completed genus-zero/one evaluators. All 431 baseline files were hashed and all 252 preceding source pins matched. The targeted baseline passed; this was not a comprehensive review of the geometric theory.

- **Medium planned contraction gap resolved:** Original component cotangent powers could not be carried through the old undecorated evaluator. A decoration indexed by the existing expression now transports these powers to their actual external or node flags. The previous syntax and public APIs remain unchanged.
- **Medium numerical composition gap resolved in this sector:** The ten boundary terms now close against the proved lower-genus families. Their original component genera are at most one; no genus-two output is supplied as a seed or callback.
- **Medium validation cost isolated:** Direct kernel evaluation of the exceptional double-cover regression recomputed a large genus-one primary equation. Its proof now reuses the existing certified primary table through a local evaluation rule. Sequential checking bounds competing memory use. The numerical evaluator itself is unchanged; broad performance claims are not justified.
- **Low development issues repaired:** Dependent decoration transparency, explicit graph edge indices, function equality for added powers and a missing test namespace required local corrections. None changed the intended mathematics. Interrupted numerical probes and a bounded probe timeout are recorded separately from successful final checks.
- No mathematical defect was found in the reviewed existing graph, pairing or lower-genus laws. Their applicability to the geometric targets remains conditional.

### Revisions and mathematical effect

[`DecoratedGluing.lean`](../../AxiomaticGW/Tautological/DecoratedGluing.lean) attaches original component powers to the existing `GluingExpression`. Its zero-decoration theorem recovers the old graph. [`DecoratedGluingEvaluation.lean`](../../AxiomaticGW/Tautological/DecoratedGluingEvaluation.lean) derives the integral/contraction equality from primitive cotangent realization at original components and the existing gluing laws. External powers add to original powers. All full-class splittings, raw multiplicities and signed inverse-metric terms are retained.

[`GenusTwoPsiGluing.lean`](../../AxiomaticGW/Tautological/GenusTwoPsiGluing.lean) constructs all ten boundary terms, proves their equality to the held graph columns by kernel isomorphism checks, bounds component genus and derives the actual GW ancestor reduction. [`Surfaces/DecoratedGluingEvaluation.lean`](../../AxiomaticGW/Surfaces/DecoratedGluingEvaluation.lean) provides the executable contractions and their agreement with the existing pairing API. [`GenusTwoOnePointAncestors.lean`](../../AxiomaticGW/Surfaces/GenusTwoOnePointAncestors.lean) composes these with the complete lower-genus reconstruction. Its final theorem uses the actual accepted relation presentations, six original genus-two row vanishings, primitive realization/cotangent/gluing laws and exactly the existing finite low-genus seeds. The seventh row and every numerical dependency are derived.

No existing mathematical definition or theorem statement changed. There is no new geometric axiom, assumed numerical recurrence, global simp rule, instance or coercion. A reducible dependent decoration type is new; a benchmark evaluation rule is local to one test. These are stable-curve ancestors, not a completed genus-two stable-map descendant algorithm.

### Verification

The [validation manifest](../../environments/genus-two-one-point-ancestor-validation.json) records exact commands, source hashes, timings and raw memory observations. Final checks passed:

- `lake build`: 2761 jobs.
- `lake test`: 2820 jobs, including sixteen new public/semantic regressions and eleven exact numerical ancestor values.
- `lake lint`.
- Twenty-one `#print axioms` audits: only `propext`, `Classical.choice` and `Quot.sound`.
- `python3 -m unittest discover -s scripts -p test_gkm_genus_two_degree_zero.py -v`: three tests, including eight request/provenance corruptions and one coherent false zero.
- `python3 scripts/gkm_genus_two_degree_zero.py check environments/gkm-genus-two-degree-zero.json`.
- Source-pin, code-placeholder, final-diff, whitespace and local-documentation-link checks.

The pinned native GKM producer independently computes the three degree-zero descendant numbers 7/640, 7/720 and 49/5760. They agree with the proved ancestor constants. Two fresh offline runs produce the same 2978-byte [report](../../environments/gkm-genus-two-degree-zero.json). Exact equivariant fractions are retained and checked before ordinary comparison. This agreement is a diagnostic: it does not prove the geometric descendant–ancestor comparison or import a CohFT class. The computations share target conventions and intersection-theoretic foundations.

Only the existing private-module warning in `AxiomaticGWTest/Basic.lean` and upstream Sage Algebras deprecation remain. All 423 unrelated baseline files are preserved. The finite proof timings use the existing checkout and compiled dependencies, not a fresh clone or an arbitrary-class performance benchmark.

### Remaining work and next priority

Derive the missing low-power and multi-marked genus-two equations needed by the full BP/L_{2,4} surface route and mixed descendant reduction. Primary and first-power ancestors, all stable-map descendant sectors, every fixed genus-two numerical suite, seed sufficiency and uniqueness for the full genus-two theory remain open. Original relation validity, target/seed geometry, complete semisimple GKM CohFT import, descendant and ordinary comparisons, and the R8 research workflow remain required.

## 2026-10-03: First marked genus-two relation with checked elliptic gluing provenance

**Status:** The held Mbar(2,1) psi-square relation, actual Sage replay, class interpretation, higher one-marked powers and class-valued CohFT ancestor consequence are verified. This supplies an R7 input; it certifies no new genus-two surface number and changes no milestone acceptance, numerical seed, target, benchmark bound or GKM completion requirement. The research goal remains active. No commit or push was made.

### Scope and findings

Reviewed the current R7 route, Wennink Section 7.1/8.3, the installed admcycles original FZ generators and graph replacement, the existing genus-one relation, decorated graph syntax, external psi operation and primitive relabelling/separating realization laws. All 423 baseline files were hashed, the tracked diff and text snapshots were saved, and all 245 preceding source pins matched. The targeted baseline passed. This was a focused relation audit, not a review of all higher-genus geometry.

- **Medium planned relation gap resolved:** The existing unmarked genus-two frame could not identify an external psi square. The new frame has seventeen distinct codimension-two raw columns and a fixed nonzero request, with a seven-row exact witness.
- **Medium reconstruction gap remains:** `GluingExpression` and its ancestor evaluator construct undecorated gluings with zero node powers. The new relation needs node cotangent factors. Those older APIs are preserved; contracting the new decorated terms is the next step.
- **Low validation issues repaired:** Initial proof/formatting probes needed a direct rational contradiction, a noncomputable annotation, legal tactic line breaks and a shared CohFT coefficient/state universe. One negative diagnostic expanded a large graph proposition and exhausted pretty-printing heartbeats; a small automorphism table proved from the same enumerator now gives a direct checked comparison. An overlapping rebuild invalidated two early test imports; the final tests ran after the build and passed. A broad word scan found the English verb “admit” in an existing docstring, not a proof placeholder.
- No mathematical defect was found in the reviewed existing graph or realization laws. Their geometric applicability remains explicit.

### Revisions and mathematical effect

[`GenusTwoPsiSquare.lean`](../../AxiomaticGW/Tautological/GenusTwoPsiSquare.lean) holds six original full-stable 3-spin rows and one elliptic boundary row. `ellipticGluingColumn_eq`, `elliptic_row_gluing` and `elliptic_row_vanishes` prove that the latter is the actual raw gluing of the existing original genus-one row. Both kappa-coordinate conversions are checked and proved inverse on every rational vector. Kernel arithmetic expresses psi_1 squared as ten signed boundary terms; `boundary_reduces` proves every vertex has genus below two, kappa degree zero and at most one remaining cotangent factor. The fixed columns distinguish external and node psi, including which separating branch is decorated.

`realized_psi_square_from_generators` uses six original genus-two row vanishings, one original elliptic row vanishing, fundamental/cotangent normalization and primitive relabelling/separating compatibility. It derives the class identity without a supplied final numerical recurrence. `realized_psi_power` and `ancestor_reduction` give every higher one-marked power and its consequence for any supplied class-valued CohFT. No numerical seed, axiom, global simp rule, instance or coercion was added, and no existing Lean statement changed.

The [search](../../scripts/search_genus_two_psi_square.py) retains original generator parameters, actual gluing destinations, exact rational rows, both coordinate systems and source pins. The [exporter](../../scripts/export_genus_two_psi_square.py) binds the incoming data to the separate Lean frame. The [report](../../environments/genus-two-psi-square-exploration.json) is byte-identical across two fresh offline Sage runs. Its intersection-pairing zeros and psi_1^4 integral are diagnostics, not independent relation proofs. Decorated automorphism orders, rather than the underlying undecorated orders, are checked.

### Verification

The [validation manifest](../../environments/genus-two-psi-square-validation.json) records exact commands, hashes, timings and raw memory observations. Final checks passed:

- `lake build`: 2756 jobs.
- `lake test`: 2814 jobs, including twelve new semantic/consumer examples.
- `lake lint`.
- `python3 -m unittest discover -s scripts -p test_genus_two_psi_square.py -v`: seven tests, including eleven corruptions each independently refuted in Lean, a fresh positive replay and an accepted equivalent loop-branch presentation.
- Exporter `--check`, byte-identical fresh Sage regeneration and seventeen `#print axioms` audits. Every audited theorem uses only `propext`, `Classical.choice` and `Quot.sound`.
- Final diff/whitespace, source-placeholder and local documentation-link checks.

Only the existing `AxiomaticGWTest/Basic.lean` private-module warning and upstream Sage Algebras deprecation remain. All 415 unrelated baseline files are preserved. Performance observations concern this finite frame and the existing checkout, not a fresh clone or general reconstruction workload.

### Remaining work and next priority

Derive numerical contraction for the actual node-decorated boundary terms and compose it with the completed genus-zero/one reconstruction. Continue the full BP/L_{2,4} surface route, including all primary, one-descendant and few-marking benchmarks for P², F₁ and Bl₂P². Original relation validity, target and seed geometry, complete semisimple GKM CohFT import, descendant/ordinary comparisons and the R8 research release remain open. The present conditional class consequence is not a certified imported CohFT or a completed genus-two evaluator.

## 2026-10-03: Complete genus-one descendants and accept the conditional R6 numerical gate

**Status:** Genus-one ancestors and descendants now have executable reconstruction at every full effective class, finite marking set and cotangent power on P², F₁ and Bl₂P². The final soundness statements use the original geometric contracts and finite low-genus seeds. Positive-degree empty markings are included; auxiliary degree-zero empty requests are rejected. All 41 additional native GKM values pass kernel replay. Together with the preceding complete primary suites and genus-zero descendants, this accepts R6 for conditional numerical reconstruction. The full research goal remains active: geometric input validity, R1/R3–R5, the fixed genus-two applications and R8 remain incomplete. No commit or push was made.

### Scope and findings

Reviewed the existing genus-one psi expansion, raw loop normalization, full-class graph bounds, genus-zero ancestor evaluator, genus-one primary soundness, finite mixed reduction, calibration and arity adapter. Saved all 413 baseline file hashes and the tracked diff; all 234 preceding source pins matched. The targeted baseline passed. This is a focused extension and R6 acceptance audit, not a comprehensive repository or geometric-model review.

- **Medium planned reconstruction gap resolved:** Genus-one descendants still needed an elliptic ancestor family. The new evaluator decreases total psi degree, uses the already reconstructed rational family on genus-zero components and closes elliptic primaries with Getzler.
- **Medium planned integration gap resolved:** Genus-one unstable-arity evaluation still needed supplied stable values. Existing sorted occurrence transport and multilinear expansion now construct its callback from the new stable evaluator.
- **Low validation issues repaired:** Generated value vectors exceeded the line limit, and a consumer example contained an empty line within its declaration. The exporter and example were corrected; final checks introduce no new warnings.
- No mathematical defect was found in the reviewed existing primitive laws. Their geometric realization is still an explicit obligation.

### Revisions and mathematical effect

[`GenusOneAncestors.lean`](../../AxiomaticGW/Surfaces/GenusOneAncestors.lean) retains the original raw loop coefficient 1/24 and all separating-tail placements. `ancestorStep_congr` bounds every recursive elliptic dependency by strictly smaller total psi degree. `ancestorValueFuel_stable` proves sufficient-fuel independence, and `ancestorValue_unique` proves uniqueness for the derived triangular equations. `ancestorStep_eval` and `ancestorValue_eq_eval` identify the computation using the accepted psi relation and the original WDVV/Getzler geometry and seeds. No ancestor family remains as an input in the final theorem.

[`GenusOneDescendants.lean`](../../AxiomaticGW/Surfaces/GenusOneDescendants.lean) composes the mixed reduction with the reconstructed calibration and ancestors. Sorted finite marking transport and basis expansion reuse the existing genus-zero infrastructure. `stableValue_eq`, `value_eq` and `queryValue?_eq_checkedEval` prove all-arity determination on the original geometric domain. The [consumer regression](../../AxiomaticGWTest/Surfaces/GenusOneDescendants.lean) supplies all three actual exported relation presentations. No new numerical seed, geometric field, axiom, assumed final recurrence, global simp rule, instance or coercion was added. Existing Lean definitions and theorem statements are unchanged.

The [native explorer](../../scripts/gkm_genus_one_descendants.py) reuses the exact pinned transport with a new optional genus parameter whose default remains zero. Earlier three-point and all-arity genus-zero reports and replay are unchanged. The [held requests](../../AxiomaticGW/Surfaces/Fixtures/GenusOneDescendants.lean) and [incoming replay](../../AxiomaticGW/GKM/Fixtures/GenusOneDescendantReplay.lean) preserve every ordered state/power pair and full class. They certify ordinary values against the proved evaluator; the equivariant fraction and specialization preflight remains exact Python verification, and geometric localization or CohFT-class import is not inferred from agreement.

### Validation and R6 acceptance

The [manifest](../../environments/genus-one-descendant-validation.json) records exact commands, outcomes, source hashes, axiom audits, resources and the requirement-by-requirement R6 evidence.

- `lake build`: passed, 2754 jobs.
- `lake test`: passed, 2811 jobs, including twelve new examples. The only Lean warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.
- `lake lint`: passed.
- `python3 -m unittest discover -s scripts -p 'test_gkm_*descendants.py' -v`: all 17 tests passed. The five new tests include a fresh positive replay and six coherent false claims, each with a separate kernel counterexample. The twelve prior tests also pass.
- Two fresh-cache Sage 10.9/admcycles 1.4 runs are byte-identical for all 41 requests: 14 plane, 12 one-blowup and 15 two-blowup cases, at arities 0–4. All 34 nonzero values are fractional; fourteen are negative. Producer revision and all five source hashes are unchanged, and online lookup is disabled. The existing Sage `Algebras` deprecation warning persists.
- `python3 scripts/gkm_genus_one_descendants.py replay environments/gkm-genus-one-descendants.json --output AxiomaticGW/GKM/Fixtures/GenusOneDescendantReplay.lean --check`: passed.
- `lake env lean /tmp/gw_genus_one_desc_axioms_20261003.lean`: all 24 new audited public theorems use only standard Lean axioms.
- The touched Lean sources contain no placeholders, project axioms, unsafe code, unchecked native decision or implementation override. Final source, theorem hypotheses, query-domain handling, documentation, local links and whitespace were checked; unrelated baseline files are preserved.

R6 now has the required general evaluators, decreasing measures, solved-coefficient proofs, finite-seed determination and all 506 positive-class primary benchmarks in each of genera zero and one through energy twelve. The previously certified auxiliary rows remain excluded from geometric lookup. The native comparisons use a separate numerical implementation while sharing target conventions, geometric normalizations and intersection-theoretic foundations; they are labelled accordingly. R6 acceptance is conditional on the named geometric inputs and does not accept the upstream general interoperability gates.

### Remaining risks and next priority

The next mathematical priority is the marked genus-two relation/reconstruction step, using the completed lower-genus engine. Audit the original Belorousski–Pandharipande and surface-specific relation route before encoding the needed marked graph frames and a decreasing genus-two reduction; the existing unmarked genus-two certificate alone does not determine the required descendants. Preserve the fixed targets, primary energy-twelve bound, one-descendant suite and all higher-power few-marking cases. Geometric realization, genus-two finite seed sufficiency, full class-valued semisimple CohFT import, action laws, primary deformation and the shared release workflow remain required. The total recursive evaluators provide no broad performance guarantee for large arbitrary queries.

## 2026-10-03: Complete genus-zero ancestors and all-arity descendants

**Status:** Genus-zero ancestors and descendants are now reconstructed at every effective class, finite arity and cotangent power on P², F₁ and Bl₂P². The final soundness theorems use the original finite line/exceptional seeds and explicit geometric inputs. Positive-degree unstable arities are included, and the original geometric-domain rejection is preserved. All 34 additional native GKM values pass kernel replay. Genus-one descendants, genus two and the complete semisimple CohFT bridge remain open; R6 and the full goal are active. No commit or push was made.

### Scope and findings

Reviewed the existing arbitrary-marking psi expansion, full-class gluing evaluation, finite mixed reduction, primary reconstruction, basis expansion and unstable-arity adapter. Saved all 400 baseline file hashes and the tracked diff; all 221 preceding source pins matched. The targeted baseline passed. This is a focused extension, not a comprehensive repository review or geometric-model construction.

- **Medium planned reconstruction gap resolved:** The mixed reduction still needed terminal ancestor values at marking counts above three. A total genus-zero ancestor evaluator now reduces every component's total psi degree and closes at the existing primary reconstruction.
- **Medium planned integration gap resolved:** The unstable-arity adapter required arbitrary-state stable callbacks. Sorted occurrence transport and multilinear expansion now construct them from that evaluator.
- **High replay defect found and fixed during development:** Canonical sorting initially ran in the compiled runtime but failed kernel reduction. The final exposed structural insertion sort is proved equal to mathlib's public sorting API, retaining the same state-power pairs and multiplicities. No unchecked native decision replaces kernel replay.
- **Low validation issues repaired:** Added a missing public definition docstring and removed a test's incorrect assumption about the wording of Lean's negative kernel-decision diagnostic. The positive replay control and separate mathematical counterexamples remain mandatory.
- No mathematical defect was found in the reviewed existing primitive GW laws. Their geometric realization remains an explicit obligation.

### Revisions and mathematical effect

[`AncestorMarkings.lean`](../../AxiomaticGW/Surfaces/AncestorMarkings.lean) gives computable symmetric marking frames. [`GluingDegree.lean`](../../AxiomaticGW/Surfaces/GluingDegree.lean) proves genus and psi-degree bounds for every terminal component of the existing gluing evaluator. [`GenusZeroAncestors.lean`](../../AxiomaticGW/Surfaces/GenusZeroAncestors.lean) selects a positive power, applies the original geometric boundary expansion and recurses with a strictly smaller total. `ancestorValueFuel_stable` proves sufficient-fuel independence, and `ancestorValue_eq_eval` discharges the primary terminal family from the original WDVV contract and finite seeds.

[`GenusZeroDescendants.lean`](../../AxiomaticGW/Surfaces/GenusZeroDescendants.lean) composes that family with the finite mixed reduction. [`GenusZeroFullDescendants.lean`](../../AxiomaticGW/Surfaces/GenusZeroFullDescendants.lean) supplies arbitrary states to the existing anticanonical adapter. `value_eq` identifies every numerical genus-zero query, including the auxiliary convention, and `queryValue?_eq_checkedEval` gives the geometric query boundary. Determination follows from equality with the theory-independent executable value. No new numerical seed, geometric field, assumed recurrence, axiom, global simp rule, instance or coercion was added. Existing Lean definitions and theorem signatures are unchanged.

The [native exporter](../../scripts/gkm_genus_zero_descendants.py) reuses the existing exact pinned transport with explicitly parameterized request families. The earlier three-point API and saved replay are preserved. The [new held requests](../../AxiomaticGW/Surfaces/Fixtures/GenusZeroDescendants.lean) cover arities 0, 1, 2, 4, 5 and 6. [Incoming replay](../../AxiomaticGW/GKM/Fixtures/GenusZeroDescendantReplay.lean) binds each value to its actual full curve class and ordered insertion data. Both mathematical paths share the target conventions and geometric normalizations; ordinary agreement does not certify localization geometry or import a CohFT class.

### Validation

The [manifest](../../environments/genus-zero-descendant-validation.json) records exact commands, outcomes, logs, source hashes and resource observations, including repaired development failures.

- `lake build`: passed, 2752 jobs.
- `lake test`: passed, 2805 jobs, including nine new regression examples. The only Lean warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.
- `lake lint`: passed.
- `python3 -m unittest discover -s scripts -p 'test_gkm_*descendants.py' -v`: all 12 tests passed. The new suite has a fresh positive replay and four coherent false claims, each with a separate kernel counterexample; the seven existing three-point tests also pass.
- Fresh-cache Sage 10.9/admcycles 1.4 reports are byte-identical for all 34 requests: 12 plane, 10 one-blowup and 12 two-blowup cases, including 32 nonzero, ten negative and one fractional value. Producer revision and all five source hashes remain unchanged; online lookup is disabled. The existing Sage `Algebras` deprecation warning persists.
- `python3 scripts/gkm_genus_zero_descendants.py replay environments/gkm-genus-zero-descendants.json --output AxiomaticGW/GKM/Fixtures/GenusZeroDescendantReplay.lean --check`: passed.
- `lake env lean /tmp/gw_ancestor_engine_axioms_20261003.lean`: all 48 audited public theorems use only standard Lean axioms; the structural-sort equalities require none.
- The touched Lean files have no placeholders, project axioms, unsafe code, native decision or implementation override. Final whitespace, documentation links and preservation checks are recorded in the manifest. Nine baseline files changed and thirteen files were added including the manifest; all 391 other baseline files are preserved.

### Remaining risks and next priority

The geometric psi, virtual-intersection and realization packages remain hypotheses, not constructed moduli spaces. Arbitrary genus-zero queries terminate, but large marking counts and degrees can still be expensive; this increment is not a general performance guarantee. Next close total genus-one ancestors using the accepted one-point loop relation and the existing primary reconstruction, then compose with the mixed reduction and arity adapter. The fixed genus-two suites, higher-genus seed sufficiency, full symplecticity, primary deformation, actual semisimple CohFT/reconstruction-action import and shared release corpus remain required. Targets and benchmark bounds are unchanged.

## 2026-10-03: Finite mixed reduction and complete three-point rational descendants

**Status:** Every curve-stable query now has a finite exact ancestor expression, in any genus. For genus zero with three markings, the expression closes against the existing primary reconstruction, giving every class and all descendant powers on P², F₁ and Bl₂P² without an invariant-value callback. All 27 held native GKM values pass kernel replay. R6 and the full research goal remain active and incomplete. No commit or push was made.

### Scope and findings

Reviewed the mixed cotangent step, simultaneous relabelling, the actual calibration identification, surface basis coordinates, symmetric ancestor keys, rational term evaluation, primary reconstruction and native GKM integration. Saved all 389 baseline file hashes and the tracked diff; all 210 preceding validation pins matched. The targeted baseline passed. This was a focused extension, not a comprehensive audit of the repository or geometric inputs.

- **Medium planned integration gap resolved:** The one-step mixed formula had no executable finite elimination of all descendant markings. Nested structural recursion now produces the ancestor expression, with an interpretation theorem and explicit partial-traversal condition.
- **Medium planned numerical gap resolved:** Stable three-point descendants still needed a supplied stable-value callback. Vanishing of positive ancestor powers on the three-point rational curve closes this sector against the proved primary evaluator.
- **Medium interoperability gap resolved:** This descendant sector lacked claim-bound native comparison. The new suite binds all 27 incoming values to their full curves, ordered powers and state labels.
- No correctness defect was found in the reviewed existing GW laws. Geometric realization and the larger reconstruction programme remain open.

### Revisions and mathematical effect

[`MixedComparison.lean`](../../AxiomaticGW/GW/Descendants/MixedComparison.lean) derives `mixed_step_at` at any selected finite marking by transporting both cotangent families and all states. [`MixedAncestorReduction.lean`](../../AxiomaticGW/Surfaces/MixedAncestorReduction.lean) expands the actual calibration state in the existing surface basis, clears each selected descendant power, and iterates over an explicit marking list. `SurfaceQuery.ancestorTerms` traverses all markings. `eval_ancestorTerms` discharges every calibration coefficient with the existing finite-seed theorem. The output uses existing ancestor keys, and remains an ancestor expression until those values are reconstructed.

[`ThreePointDescendants.lean`](../../AxiomaticGW/Surfaces/ThreePointDescendants.lean) uses three-point rational curve dimension vanishing for every nonprimary terminal ancestor. `threePointValue_eq` identifies the resulting computable rational number with the actual descendant invariant at every class and power. Its final inputs are the existing original WDVV/finite-seed and primitive virtual-intersection contracts. No additional seed, geometric field, substitute axiom or assumed final recurrence was added. Existing definitions and public theorem statements are unchanged. No global simp lemma, instance or coercion was added.

The [native explorer/exporter](../../scripts/gkm_three_point_descendants.py) calls GKM integration independently of the Lean recurrence and retains exact equivariant fractions. The [held requests](../../AxiomaticGW/Surfaces/Fixtures/ThreePointDescendants.lean) cover degree zero, multiple descendant markings, permutation, negative values, exceptional covers and equal-energy distinct classes. [Kernel replay](../../AxiomaticGW/GKM/Fixtures/ThreePointDescendantReplay.lean) checks all incoming ordinary values and coverage. Numeric agreement and exact Python fraction checks do not prove localization geometry or import a CohFT class.

### Validation

The [manifest](../../environments/mixed-ancestor-reduction-validation.json) pins all sources and records exact commands, logs, resource measurements, failed development probes and final outcomes.

- `lake build`: passed, 2747 jobs.
- `lake test`: passed, 2796 jobs, including eight new regression examples. The sole warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.
- `lake lint`: passed.
- `python3 scripts/test_gkm_three_point_descendants.py`: seven tests passed, including a fresh positive kernel control and rejection of three coherent false claims, each supported by a separate kernel counterexample.
- Fresh-cache Sage 10.9/admcycles 1.4 exploration from the producer checkout and package paths gave byte-identical 27-case reports. Producer revision and all pinned source hashes remained unchanged; online lookup was disabled. Sage retained its existing `Algebras` deprecation warning.
- `python3 scripts/gkm_three_point_descendants.py replay environments/gkm-three-point-descendants.json --output AxiomaticGW/GKM/Fixtures/ThreePointDescendantReplay.lean --check`: passed.
- `lake env lean /tmp/gw_descendant_engine_axioms_20261003.lean`: all 18 new public theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
- Touched Lean sources contain no placeholders, project axioms, unsafe code, native decision procedure, or implementation override. The final task diff and whitespace were checked; all unrelated baseline files are preserved.

### Remaining risks and next priority

General ancestor evaluation is still missing, even though the genus-zero and genus-one cotangent contraction equations are available. Next derive a total evaluator from those equations at arbitrary marking count, with a proved decrease for every component dependency, then compose it with the finite mixed reduction and unstable-arity adapter. The fixed genus-two suites, seed sufficiency, geometric realization, complete semisimple CohFT import, full symplecticity, primary deformation and shared release corpus remain required. The application list and benchmark bounds are unchanged.

## 2026-10-03: Mixed cotangent comparison and complete calibration recursion

**Status:** Primitive virtual intersection laws now derive the actual mixed descendant–ancestor step. Its three-point rational specialization and the original divisor equation give a terminating matrix reconstruction of every calibration coefficient on P², F₁ and Bl₂P² from the existing finite genus-zero seeds. Thirty native GKM higher-coefficient requests agree, and all 582 incoming ordinary entries pass kernel replay. General descendant evaluation, genus two, geometric realization and full semisimple CohFT import remain open. R6 and the research goal remain active; no commit or push was made.

### Scope reviewed and findings

Reviewed the existing numerical extension, stable-map descendant classes, ancestor multiplication, stabilization carrier, two-point calibration, virtual dimension, full divisor law, surface first coefficient and native GKM numerical interface. Saved the tracked diff and all 377 baseline file hashes; all 198 preceding validation pins matched. The targeted baseline compiled. This was a focused extension, not a comprehensive repository or geometric-moduli audit.

- **Medium integration gap resolved:** Stored main boundary maps and residual data did not derive the mixed cotangent formula. Optional raw intersection and fiber-product boundary inputs now state the primitive cotangent, diagonal and stabilization laws. Lean derives both actual numerical factors and the mixed comparison.
- **Medium reconstruction gap resolved:** Higher calibration coefficients previously needed supplied stable genus-zero descendants. The new divisor-based recursion reduces every coefficient to the already reconstructed first coefficient and classical cup multiplication.
- **Medium interoperability gap resolved:** Higher calibration powers had no native comparison bound to full classes, powers and actual incoming entries. Thirty fixed requests now have exact preflight and offline kernel replay.
- No defect was found in the reviewed original primitive GW laws. Geometric instantiation of the new inputs remains an explicit obligation.

### Revisions and mathematical effect

[`Geometry/StableMapIntersection.lean`](../../AxiomaticGW/Geometry/StableMapIntersection.lean) defines mixed classes from the existing descendant family and ancestor monomials. It proves the two endpoints, relabelling and raw-integral interpretation. `StableMapIntersection` realizes the original numerical family, including positive-degree two-point maps. `StableMapStabilization` supplies pullback, virtual pushforward, projection and proper integration, identifying the existing pushed descendant classes.

[`Geometry/RationalTailComparison.lean`](../../AxiomaticGW/Geometry/RationalTailComparison.lean) gives the boundary its own fiber-product cohomology algebra. Evaluation and cotangent pullbacks, stabilization compatibility, a virtual diagonal law on arbitrary component classes, and a cotangent cycle law tested against arbitrary ambient classes imply `integrated_tail` and `mixed_step`. The main factor is the existing mixed invariant, and the tail inserts the actual calibration state. All ancestor powers stay on the main component. Zero class has no positive tails. Main energy and the three relevant descendant-power measures strictly decrease. The mathematical mechanism is [Kontsevich–Manin, Theorem 1.2, equation (4)](https://arxiv.org/html/alg-geom/9708024); the [M8 note](../mathematics/M08DescendantsAndAncestors.md#9-mixed-comparison-from-primitive-virtual-intersection-laws) records the precise conventions.

[`GW/Descendants/CalibrationRecursion.lean`](../../AxiomaticGW/GW/Descendants/CalibrationRecursion.lean) uses three-point rational ancestor vanishing and the original divisor equation to derive the higher-coefficient recurrence. [`Surfaces/CalibrationRecursion.lean`](../../AxiomaticGW/Surfaces/CalibrationRecursion.lean) identifies every primary main factor with the classical anticanonical cup operator at zero class, or energy times the first coefficient at positive class. `reconstructedCalibrationMatrix` divides only by positive effective energy and recurses on inverse-loop power. `reconstructedCalibrationMatrix_eq` discharges the first-coefficient identification with the original WDVV reconstruction and finite line/exceptional seeds. It proves agreement with the actual GW operator at every power and full class; no stable-descendant callback, higher coefficient, extra seed or solved recurrence is an input.

The [native explorer and exporter](../../scripts/gkm_calibration_recursion.py) preserve the pinned producer, exact equivariant fractions, signed inverse metric, full curve classes and power conventions. The [held requests](../../AxiomaticGW/Surfaces/Fixtures/HigherCalibration.lean) include all ten nonzero first-coefficient classes at powers two and three, the remaining plane-line powers and first vanishing power, a conic, and double exceptional classes. The [incoming replay](../../AxiomaticGW/GKM/Fixtures/HigherCalibrationReplay.lean) checks all 582 ordinary entries against the derived algorithm, plus basis bijectivity, indices and held coverage. Exact equivariant multiplication and regular specialization are supplemental Python evidence; no geometric localization theorem or imported CohFT class follows from these checks.

Existing definitions and theorem signatures are unchanged. New theorems consume explicit optional geometric intersection inputs. The original GW laws, finite seeds, target list and benchmark bounds are preserved. No placeholder, substitute axiom, new global simp lemma, coercion or typeclass instance was introduced. Root imports, the plan, input ledger, mathematical map and GKM workflow now document this scope.

### Validation

- `lake build AxiomaticGW.GW.Descendants.TwoPointCalibration AxiomaticGW.Tautological.PsiBoundaryExpansion` passed the baseline, 2,631 jobs.
- `lake build AxiomaticGWTest.GW.MixedComparison AxiomaticGWTest.Surfaces.CalibrationRecursion` passed with 2,681 jobs and 14 regression examples, compiling all new proof modules. Tests cover both mixed endpoints, label transport, a genus-two main ancestor exponent, zero-class tails, strict decrease, ordered matrix products, negative descendants, conics and exceptional multiple covers.
- `lake build` passed, 2,744 jobs. `lake test` passed through job 2,789. `lake lint` passed. The only Lean warning was the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.
- `lake env lean /tmp/gw_mixed_axioms_20261003.lean` audited all 40 new public theorems; dependencies are only `propext`, `Classical.choice` and `Quot.sound`.
- `python3 scripts/test_gkm_calibration_recursion.py -v` passed all seven tests. A fresh positive control compiles; three coherent false reports pass arithmetic preflight and fail kernel replay. Separate kernel proofs establish counterexamples for the jointly zeroed matrix, swapped loop powers, and exchanged equal-energy exceptional classes. The original test's assumption about Lean's diagnostic wording was repaired; no mathematical claim was weakened.
- Two native runs using the pinned Sage interpreter passed all thirty requests with fresh caches and online admcycles lookup disabled. The replay and reproducibility checks, exact command lines, source hashes and resource observations are recorded in the [validation manifest](../../environments/mixed-descendant-comparison-validation.json). Native execution emitted only the previously observed Sage deprecation warning.

The final incremental diff, documentation links, placeholder/axiom scan and preservation audit are recorded in that manifest. Eight baseline files changed and twelve were added, including the manifest; all 369 unrelated baseline files remain byte-identical. Producer sources were not modified. Intermediate elaboration failures and repaired validation-script issues are listed separately from the successful final checks.

### Remaining risks and next priority

The raw intersection and boundary structures express geometric hypotheses; no stable-map moduli space or virtual cycle is constructed. The mixed step and calibration are now proved, but a total stable descendant evaluator, its combined termination and uniqueness proof, genus-two reconstruction, full symplecticity, primary deformation and actual semisimple CohFT-class/reconstruction-action import remain required. Next assemble the mixed step with the existing ancestor equations and finite seeds into stable numerical descendant reconstruction, preserving full classes and zero-degree terms. The fixed targets and research benchmarks are unchanged.

## 2026-10-03: Two-point calibration and complete first-coefficient GKM replay

**Status:** Actual two-point descendants now construct the zero-primary-deformation calibration. Its first coefficient is determined at every full curve class on P², F₁ and Bl₂P² by the existing primary reconstruction and finite seeds. Native GKM agrees on the entire potentially nonzero positive-class sector, and the incoming ordinary matrices pass kernel replay. Stable descendant reconstruction, the mixed stable-map comparison, genus two and full CohFT import remain open. R6 and the research goal remain active. No commit or push was made.

### Scope reviewed and findings

Reviewed the perfect pairing and transport, actual numerical two-point family and unstable conventions, stored stabilization operators, divisor-based arity reduction, primary reconstruction, signed surface coordinates and the native GKM producer's numerical interface. The normalization was checked against [Givental, §5](https://arxiv.org/html/math/0108100). Saved the tracked diff and hashes of all 366 baseline files; all 180 preceding source pins matched. The targeted baseline compiled successfully.

- **Medium integration gap resolved:** The existing calibration carrier did not construct its operators from numerical GW values. Perfect duality now constructs them, fixes the one-step shift between inverse-loop and descendant power, and proves sewing, transport and uniqueness. The full constant-term normalization excludes spurious positive-class constant terms.
- **Medium numerical bridge gap resolved:** Native GKM had no complete calibration-matrix comparison with the reconstructed surfaces. The entire first coefficient now has independently held values, finite coverage and replay of actual incoming ordinary entries.
- **Remaining geometric gap:** The stored main boundary maps, weights and residual identity are still supplied. Identifying the paired tail values does not derive that geometry or a mixed descendant--ancestor formula.
- No mathematical defect was found in the reviewed original primitive GW laws. This extension is not a comprehensive audit of geometric moduli models or of the repository.

### Revisions and mathematical effect

[`Linear/TwoPointOperator.lean`](../../AxiomaticGW/Linear/TwoPointOperator.lean) raises the first, attaching-node index of a two-point multilinear form using the existing perfect pairing. It proves the paired characterization, uniqueness, canonical copairing contraction and conjugation under state-space transport.

[`GW/Descendants/TwoPointCalibration.lean`](../../AxiomaticGW/GW/Descendants/TwoPointCalibration.lean) constructs coefficients satisfying `eta(x, S_(m+1,beta) y) = <x,tau_m(y)>_(0,beta)`. The zero-power, zero-class coefficient is identity; all other zero-power coefficients and all positive-power zero-class coefficients vanish. Primary relabelling proves first-coefficient self-adjointness. The optional paired-value property `TwoPointCompatible` uniquely identifies an existing stored calibration with this actual numerical construction. Substitution in the existing tail sum leaves the main boundary maps and residual geometry as inputs. No full symplectic identity or primary-deformation dependence is inferred.

[`Surfaces/TwoPointCalibration.lean`](../../AxiomaticGW/Surfaces/TwoPointCalibration.lean) uses the established unstable-arity adapter to compute matrices from stable genus-zero descendants. Matrix rows are output coordinates and retain the negative exceptional inverse-metric weights. The dimension rule proves vanishing above inverse-loop power `energy + 2`; stable values determine every coefficient without a separate infinite tail seed family. `firstCalibrationMatrix_eq` derives the primary first coefficient using the unchanged original WDVV contract and finite line/exceptional seeds.

[`FirstCalibration.lean`](../../AxiomaticGW/Surfaces/Fixtures/FirstCalibration.lean) checks every matrix through energy three, including class zero, then uses uniform primary dimension vanishing at higher energy. There are ten nonzero matrices across the three targets: line, exceptional, ruling and strict-line classes. The result is not limited to the energy-twelve benchmark window. The [M8 note](../mathematics/M08DescendantsAndAncestors.md#8-actual-two-point-operators-at-zero-primary-deformation) records the full sparse actions and their conventions.

The [native explorer](../../scripts/explore_gkm_first_calibration.py) calls the pinned producer with fresh temporary caches and online admcycles lookup disabled. Its [report](../../environments/gkm-first-calibration-comparison.json) retains all 25 positive full classes through energy three, 564 matrix entries, fifteen zero matrices and 27 nonzero entries. It records exact equivariant correlators, raised operators and ordinary values. The [exporter](../../scripts/export_gkm_first_calibration.py) independently checks inverse-metric multiplication and regular specialization over exact Python fractions. The [Lean replay](../../AxiomaticGW/GKM/Fixtures/FirstCalibrationReplay.lean) checks actual incoming ordinary entries, labels, full classes, power indices and complete coverage against the held surface values. Equivariant arithmetic for these new matrices is supplemental Python evidence, not a new Lean localization or specialization proof. Both methods share target conventions and geometric normalizations; the comparison does not independently prove those foundations or import a CohFT class.

Existing definitions, theorem statements, geometric laws, seeds and benchmark bounds are unchanged. The new paired identification is an explicit optional geometric condition, not a supplied final numerical recurrence. No placeholder, substitute axiom, global simp rule or typeclass instance was added. Root imports and the plan, mathematical map, input ledger and GKM workflow now document the new boundary.

### Validation

- `lake build AxiomaticGW.GW.Descendants.Stabilization AxiomaticGW.GW.Descendants.FullPotential AxiomaticGW.Surfaces.DescendantStabilization` passed the baseline with 2,572 jobs.
- `lake build AxiomaticGWTest.Surfaces.TwoPointCalibration` passed with 2,676 jobs and all 19 examples, compiling all five new proof modules. Regressions cover exceptional signs, equal-energy full classes, inverse-loop indexing, zero-class conventions, high-energy vanishing, imported matrices and geometric consumers.
- `lake build` passed with 2,738 jobs; `lake test` passed through job 2,781; `lake lint` passed. The sole Lean warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.
- `lake env lean /tmp/gw_calibration_axioms_20261003.lean` audited all 41 new public theorems. Every dependency is among `propext`, `Classical.choice` and `Quot.sound`.
- `python3 scripts/test_gkm_first_calibration.py -v` passed all seven tests. Two separately compiled coherent false fixtures pass arithmetic preflight and fail kernel replay: a jointly zeroed correlator/operator/claim and swapped equal-energy exceptional curve labels.
- `python3 scripts/export_gkm_first_calibration.py environments/gkm-first-calibration-comparison.json --output AxiomaticGW/GKM/Fixtures/FirstCalibrationReplay.lean --check` passed. Fresh native runs using the pinned Sage interpreter produce byte-identical reports; only the existing Sage deprecation warning appears. Exact commands and resource observations are in the [validation manifest](../../environments/two-point-calibration-validation.json).

The final incremental diff, source pins, local documentation links and placeholder scan were checked. Eight baseline files changed and eleven files were added, including the validation manifest; all 358 unrelated baseline files remain byte-identical. Intermediate elaboration failures and a repaired temporary validation-path collision are recorded separately. No producer source was modified.

**Follow-up:** The [mixed comparison and complete calibration recursion](#2026-10-03-mixed-cotangent-comparison-and-complete-calibration-recursion) above now derive the actual main/tail factors and all calibration powers from primitive geometric inputs and the original finite genus-zero seeds. The historical scope below records the boundary at this earlier increment.

### Remaining risks and next priority

The numerical interpretation retains the original geometric laws and finite seeds. Higher calibration powers depend on stable genus-zero descendants; the new finite support theorem does not compute them. The next priority is to derive the mixed stable-map cotangent comparison and identify its main boundary factors, then construct stable numerical descendant recursion and finite seed sufficiency. Full symplecticity, nonzero primary deformation, actual semisimple CohFT-class or reconstruction-action import, ordinary comparison of those classes, and every remaining genus-two application stay required. The fixed targets and bounds are unchanged.

## 2026-10-03: Certified genus-one psi relation and low-genus ancestor equations

**Status:** An exact Sage/admcycles certificate now supplies the genus-one base cotangent relation. Iterating primitive stable-curve forgetting derives genus-zero and genus-one ancestor lowering equations with arbitrarily many added markings and arbitrary remaining ancestor powers. Stable-map descendant comparison, a total descendant evaluator and finite descendant determination remain open. R6 and the full research goal remain active. No commit or push was made.

### Scope reviewed and findings

Reviewed the existing psi classes and forgetting formula, raw gluing expressions, marking pullback, ancestor contraction, decorated-graph acceptance and stable-map stabilization interfaces. The targeted baseline build passed; hashes and the tracked diff were saved for all 357 baseline files, and all 172 preceding source pins matched.

- **Medium certificate gap resolved:** The exploratory genus-one psi row witness had no replay tied to independently fixed graph semantics, original generator rows and the exact requested equation. The new acceptance proof binds all three columns, their decorations, raw normalization, rows and request.
- **Medium integration gap resolved:** `PsiForgetFormula.boundaryTail` had no identification with an explicit raw gluing expression. The new optional `PsiBoundaryExpansion.TailCompatible` states that primitive class-level identification. Induction then derives the arbitrary-marking psi expansion and its integrated ancestor equation.
- **Low generated-documentation defect resolved:** Lint found missing definition docstrings, and the subsequent build exposed the generated file's incomplete header. Both are fixed in the exporter and regenerated source.
- No mathematical defect was found in the reviewed original forgetting or gluing laws. This is not a verification of geometric moduli models or of a complete stable-map descendant algorithm.

### Revisions and mathematical effect

[`GenusOnePsi.lean`](../../AxiomaticGW/Tautological/GenusOnePsi.lean) fixes the raw columns κ₁, ψ₁ and the self-gluing pushforward of the three-point rational fundamental class. It proves distinctness, codimension, the loop automorphism count two and the actual external-psi interpretation. The original full-stable 3-spin rows are `(102, −30, −3)` and `(30, 42, −3)`; their combination with coefficients `−5/864, 17/864` gives `(0, 1, −1/24)`. Acceptance consumes the incoming presentation, while geometric vanishing of the original rows remains explicit. The coefficient `1/24` belongs to raw gluing; `1/12` belongs to the normalized irreducible boundary divisor. The conventions are checked against [Getzler, §4](https://arxiv.org/html/math/9801003) and the [3-spin relation source](https://arxiv.org/abs/1303.1043).

[`PsiBoundaryExpansion.lean`](../../AxiomaticGW/Tautological/PsiBoundaryExpansion.lean) constructs the primitive rational tail with explicit old/new labels. Successive marking pullbacks retain graph multiplicities. The genus-zero base vanishes by the existing cohomological dimension bound; genus one uses the accepted finite certificate. Every term has one edge. `genusZero_ancestor_eq_contractions` and `genusOne_ancestor_eq_contractions` integrate these derived identities against the actual GW class and remaining ancestor monomial, then apply the established graph contraction theorem with every full curve-class splitting retained.

The new `TailCompatible` hypothesis identifies a **stable-curve** forgetting divisor with raw gluing; it does not identify the separate stable-map tail coefficients. Existing public definitions, theorem statements, seeds and benchmark bounds are unchanged. The new theorems still require the named primitive gluing/forgetting and strata compatibility laws, and genus one requires geometric validity of its two original rows. No final numerical recurrence, placeholder, substitute axiom, global simp rule or global typeclass instance is added. No new GW benchmark number or total numerical descendant evaluator is claimed.

The [search script](../../scripts/search_genus_one_psi.py) recomputes the original admcycles generator rows with fresh temporary caches and online lookup disabled. The [exporter](../../scripts/export_genus_one_psi.py) emits actual incoming decorated graphs and kernel isomorphism proofs against the held frame. The [replay fixture](../../AxiomaticGW/Tautological/Fixtures/GenusOnePsiReplay.lean) runs without Sage or network access; provenance digests are not proof of geometry. The root exports, M8 notes, input ledger, research plan and Sage workflow document this boundary.

### Validation

- `lake build AxiomaticGW.Tautological.LegPsiRealization AxiomaticGW.Tautological.GluingForgetful AxiomaticGW.GW.Descendants.Stabilization` passed the baseline with 2,620 jobs.
- `lake build AxiomaticGW.Tautological.GenusOnePsi`, `lake build AxiomaticGW.Tautological.Fixtures.GenusOnePsiReplay` and `lake build AxiomaticGW.Tautological.PsiBoundaryExpansion` passed. The final generated documentation is also compiled by the full build.
- `lake build AxiomaticGWTest.Tautological.PsiBoundaryExpansion` passed with 1,816 jobs and all 15 regression examples: graph labels and incidence, expansion multiplicities, raw normalization, rejection of a jointly altered zero claim, arbitrary-marking consumers and the dimension-derived genus-zero base.
- `lake build` passed with 2,733 jobs; `lake test` passed through job 2,775; `lake lint` passed. The only test warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.
- `python3 scripts/test_genus_one_psi.py -v` passed all nine tests, including seven separately compiled corrupted fixtures. They reject the wrong raw factor, altered decoration, generator row, witness, column scaling, automorphism count and a jointly zeroed claim.
- `python3 scripts/export_genus_one_psi.py environments/genus-one-psi-exploration.json --output AxiomaticGW/Tautological/Fixtures/GenusOnePsiReplay.lean --check` passed. Two fresh-cache runs of `scripts/search_genus_one_psi.py` under the pinned Sage environment produced byte-identical reports. An upstream Sage deprecation warning is recorded separately.
- `lake env lean /tmp/gw_psi_axioms_20261003.lean` audited all 32 new public proof declarations. Dependencies are only `propext`, `Classical.choice` and `Quot.sound`.

The [validation manifest](../../environments/low-genus-psi-validation.json) records exact commands, the final lint result, source pins, corrected development failures, incremental diff and preservation checks. Eight baseline files were revised and nine files added, including that manifest; all 349 unrelated baseline files remain byte-identical.

### Remaining risks and next priority

Class-level geometric row validity and gluing compatibility are explicit obligations. The equations lower ancestor powers but do not yet provide a terminating numeric evaluator, a finite descendant seed theorem or stable-map descendant comparison. Next identify the existing stable-map tail coefficients and maps with actual lower-point GW factors, and derive the descendant comparison and stable recursion from those primitive laws. Genus-two tables and fixed descendant suites, geometric applicability and mandatory full semisimple GKM/CohFT compatibility remain open. P², F₁ and Bl₂P² and all benchmark bounds remain fixed.

## 2026-10-03: Derived divisor action and terminating descendant arity reduction

**Status:** Stable descendant values now determine all unstable numerical values on P², F₁ and Bl₂P², with an executable reduction and proofs of termination, soundness and uniqueness. The abstract divisor correction is proved to equal surface cup multiplication. Stable descendants are still required as input; this step adds no GW benchmark values and does not complete R6. The research goal remains active. No commit or push was made.

### Scope reviewed and findings

Reviewed the existing stable and full string/divisor equations, numerical unstable extension, surface target identification, classical cubic, pairing contraction, primary query domain and rational-tail comparison interface. The directly relevant baseline build passed. Saved hashes and the tracked diff for all 352 baseline files; all 167 preceding source pins matched.

- **Medium integration gap resolved:** The abstract divisor action was not connected to surface cup multiplication. Evaluating the same degree-zero four-point invariant by string and divisor fixes its pairing with every state. The existing classical cubic and perfectness then determine the action, without an extra compatibility hypothesis.
- **Medium reconstruction gap resolved:** The supplied unstable numerical family had no terminating reduction to stable values or associated uniqueness theorem. Positive anticanonical degree now permits this reduction at every nonzero full class.
- **Low documentation issue resolved:** The input ledger listed divisor-action compatibility as a separate outstanding obligation. It now records the derivation and retains divisor--curve pairing compatibility as a geometric input.
- No mathematical defect was found in the reviewed original string/divisor or classical-cubic statements. Stable-map geometric existence and stable descendant reconstruction were outside this completed increment.

### Revisions and mathematical effect

[`GW/Descendants/DivisorAction.lean`](../../AxiomaticGW/GW/Descendants/DivisorAction.lean) proves the primary unit normalization, the paired divisor-action identity and uniqueness of that action. [`Surfaces/DescendantDivisor.lean`](../../AxiomaticGW/Surfaces/DescendantDivisor.lean) extends the existing classical cubic from basis multisets to arbitrary linear states using multilinearity and proves `SurfaceTheoryIdentification.divisorAction_eq_mul`.

[`Surfaces/DescendantStabilization.lean`](../../AxiomaticGW/Surfaces/DescendantStabilization.lean) derives the solved anticanonical divisor equation. Adding its primary insertion lowers the curve-stability deficit, while each correction lowers a positive psi power. Their sum is a sufficient recursion bound. `stabilizedValue_eq_invariant` proves the executable adapter correct when its stable-value callback is correct; `invariant_eq_of_stable_eq` and `numerical_extension_unique` prove numerical determination at all arities. The low-level fuel helper has an exhausted branch, proved unreachable under the bound used by `stabilizedValue`. Its arbitrary low-fuel outputs are not claimed to be invariants.

`stabilizedQuery?_eq_checkedEval` preserves the existing geometric-domain rule, including positive-degree unstable requests and rejection of auxiliary degree-zero unstable requests. Genus and the full curve class never change. The existing definitions, public theorem statements, finite seeds, geometric hypotheses and target bounds are unchanged. No new global simp rule, instance, substitute axiom or assumed reconstruction recurrence is added. The root library exports the new adapter; the [mathematics-to-Lean map](../MathematicsToLean.md#m8-descendants-and-ancestor-comparison), M8, input ledger and plan record its exact boundary.

### Validation

- `lake build AxiomaticGW.Surfaces.DegreeZero AxiomaticGW.GW.Descendants.Stabilization AxiomaticGWTest.GW.Exceptional` passed the baseline with 2,573 jobs.
- `lake build AxiomaticGWTest.Surfaces.DescendantStabilization` passed with 2,568 jobs, compiling all three new proof modules and all 17 regression examples without new warnings. It checks exceptional intersection signs, high psi powers, every unstable arity, stable genus-two passthrough, the query domain and public semantic consumers. Synthetic callback outputs test execution only and are explicitly not geometric GW values.
- `lake build` passed with 2,730 jobs; `lake test` passed through job 2,771; `lake lint` passed. The only final warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.
- `lake env lean /tmp/gw_descendant_axioms_20261003.lean` audited all 18 new public theorems. Every dependency is among `propext`, `Classical.choice`, and `Quot.sound`.
- `git diff --check`, the touched-source placeholder scan and local documentation file-link checks passed. The incremental patch preserves all 345 unrelated baseline files byte for byte. Seven baseline files changed and five files were added, including the validation manifest.

The [validation manifest](../../environments/surface-descendant-stabilization-validation.json) records source pins, exact commands, resource observations, corrected intermediate elaboration failures and preservation checks. No new Sage, admcycles or GKM numerical run was needed for these deductions from existing Lean laws.

### Remaining risks and next priority

The stable callback remains a reconstruction obligation; this is neither a finite descendant seed theorem nor existence of a full numerical model. The current rational-tail comparison interface still contains tail coefficients and maps requiring identification with actual lower-point GW factors. The next priority is to certify the low-genus cotangent relations and establish that identification, then derive stable descendant recursion from primitive geometric laws. Genus-two tables and descendant suites, geometric applicability, and the full semisimple GKM/CohFT contract remain open. The fixed applications and benchmark bounds are unchanged.

## 2026-10-03: Complete genus-one primary benchmark certificates

**Status:** The complete energy-twelve primary point suite in genus one is kernel checked on P², F₁ and Bl₂P², retaining all 506 positive-class queries and three auxiliary zero-class entries. This completes the primary numerical subset of R6. Descendants, genus two and the full semisimple GKM/CohFT contract remain required; R6 and the research goal remain incomplete. No commit or push was made.

### Scope reviewed and findings

Reviewed the original ordered Getzler marking expansion, its genus-one support and pivot proofs, scalar primary and degree-zero reductions, original geometric inputs and seeds, genus-zero finite certificates, the full-class benchmark contract, and Chaudhuri–Das formula (3.1). The baseline targeted reconstruction and certificate build passed. The 334-file baseline and tracked diff were saved; all 150 preceding source pins matched.

- **Medium execution gap resolved:** Ordered marking placements and repeated labelled contractions were impractical for bounded replay. Exact binomial compression, graph-dimension selection, summed marking-orbit weights and direct coordinate tuples now compute the same equation. The right component is evaluated first to discard zero products before evaluating a nested left component.
- **Medium numerical gate resolved:** A joint bounded checker validates the rational inputs and every elliptic equation, with exact class coverage. Its proof retains genus-zero terms at the original energy and decreases only elliptic energy.
- No mathematical defect was found in the reviewed original geometric-input contract, pivot or primary reconstruction statements. Geometric-model existence and imported CohFT-class validity were outside this scoped extension.

### Revisions and mathematical effect

[`PointExpansion.lean`](../../AxiomaticGW/Surfaces/PointExpansion.lean) proves binomial compression including nonseparating gluing for every valuation in a rational algebra. [`GenusOneCompactStep.lean`](../../AxiomaticGW/Surfaces/GenusOneCompactStep.lean) connects it to the original remainder and bounds rational dependencies. [`GenusOneScalar.lean`](../../AxiomaticGW/Surfaces/GenusOneScalar.lean) proves scalar replay with separate rational and elliptic candidates and the original signed degree-zero constants.

[`CurveSum.lean`](../../AxiomaticGW/Surfaces/CurveSum.lean) proves complete literal-tuple enumeration. [`GenusOneDimension.lean`](../../AxiomaticGW/Surfaces/GenusOneDimension.lean) derives dimension vanishing from the actual graph edge count and solves the unique possible point distribution with its full binomial weight. Negative required counts remain integers until checked, and the parallel-edge graph counts both nodes. [`GenusOneSymmetry.lean`](../../AxiomaticGW/Surfaces/GenusOneSymmetry.lean) proves that the original 33 labelled contractions group into seven representatives when every external label is H, with weights −9, 12, 3, −6, −1/2, −1/8 and 3/4. Separate kernel proofs of the seven intermediate contractions avoid repeated reduction of a large combined rational expression.

[`GenusOneCertificate.lean`](../../AxiomaticGW/Surfaces/GenusOneCertificate.lean) proves soundness of joint genus-zero/genus-one finite replay and held claims. The generated tables check every equation and exact coverage; [`GenusOneBenchmarks.lean`](../../AxiomaticGW/Surfaces/GenusOneBenchmarks.lean) provides a shared lookup and geometric consumer. Unsupported energies and auxiliary zero classes return `none`. The existing definitions, theorem statements, geometric hypotheses, finite seeds and application bounds are unchanged. No global simp rule, typeclass instance, substitute axiom or assumed recurrence is added.

The [candidate generator](../../scripts/export_surface_genus_one_tables.py) separately transcribes [Chaudhuri–Das (3.1)](https://arxiv.org/html/1901.00839v2#S3), using four anticanonical divisors. Lean contracts the original four-H request. Both use Getzler's relation, the same rational inputs and geometric base values; the comparison does not independently validate those shared foundations. Published anchors were fixed before acceptance: plane cubic/quartic values 1 and 225, F₁ value 240 for 5H−3E, and Bl₂P² value 20 for 5H−3E₁−2E₂. A separate [intermediate-contraction helper](../../scripts/surface_genus_one_contractions.py) uses the pinned admcycles graph incidences and the candidate tables to emit smaller proof steps. Each number is checked against Lean’s own gluing expression before exact arithmetic assembles the row. The [frozen manifest](../../environments/surface-genus-one-primary-tables.json) retains 33 nonzero positive answers, 473 zero positive answers and three auxiliary zeros. Of the zero answers, 34 have nonzero individual graph contributions whose exact cancellation is checked.

### Validation and resources

- `lake build AxiomaticGW.Surfaces.Fixtures.GenusOnePlaneTable`, `lake build AxiomaticGW.Surfaces.Fixtures.GenusOneF1Table`, and `lake build AxiomaticGW.Surfaces.Fixtures.GenusOneBl2Table` passed, each with 2,683 jobs. All 3,514 intermediate equalities and 509 row equations were checked by Lean’s kernel.
- `lake build AxiomaticGW.Surfaces.GenusOneBenchmarks` passed with 2,689 jobs; `lake build AxiomaticGWTest.Surfaces.GenusOneCertificate` passed with 2,692 jobs and all 21 examples.
- `lake build` passed with 2,727 jobs; `lake test` passed through job 2,767; `lake lint` passed. The sole warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.
- `python3 scripts/export_surface_genus_one_tables.py --check` passed; `python3 scripts/test_surface_genus_one_tables.py -v` passed all six tests.
- `lake env lean /tmp/gw_genus_one_certificate_axioms_20261003.lean` audited 33 core, table and public-consumer declarations: every dependency is among `propext`, `Classical.choice`, and `Quot.sound`. `lake env lean /tmp/gw_genus_one_readme_20261003.lean` compiled the exact documented examples and returned 225, 240, 20, and `none`.
- The validation manifest additionally records successful scratch checks for the next descendant step and the five genus-two query shapes. These do not certify the future reconstruction or expected genus-two values.

Cold two-point-blowup replay was costly: Lake reported 5,762 seconds; the command wrapper recorded 4,373.189 seconds and a child high-water value of 5,980,487,680 bytes. Both timer observations are retained without treating them as a controlled performance comparison.

The 21 [Lean regressions](../../AxiomaticGWTest/Surfaces/GenusOneCertificate.lean) test published values, full-class distinctions at equal energy, altered seeds and candidates, missing/extra classes, bounds, same-energy rational terms, signed degree-zero sectors, dimension pruning, parallel edges, lookup domains and geometric use of both actual Sage-exported relation presentations. Six Python tests check reproducibility, complete request counts, published values, blowup comparisons, exceptional-label symmetry and signed binomial boundaries. Native exploratory evaluations are recorded separately and are not treated as proofs.

Development experiments included interrupted large raw, grouped and selected-distribution checks. Parallel replay caused memory pressure; final heavy table runs are sequential. An experimental proof-producing `decide_cbv` run was interrupted and supplies no accepted theorem. Failed intermediate proof elaborations were repaired before final validation. The two-point-blowup fixture contains 3,157 intermediate contraction proofs and 455 row proofs in one compiler unit, so its cold replay remains expensive. The bounded lookup reads the saved values after acceptance. Timings and child memory records are observational, including startup/imports; they do not constitute controlled speed comparisons. See the [validation manifest](../../environments/surface-genus-one-certificate-validation.json) for successful commands, development attempts, axiom audits and preservation checks.

Five [published genus-two descendant comparison cases](../../environments/surface-genus-two-published-anchors.json) from [Wennink, §8.4](https://arxiv.org/html/2210.04038) are frozen for later R7 checks. They specify full effective coordinates, stable-map psi powers and all point insertions; Lean scratch proofs check dimension, positive class, energy and membership in the existing bound. The expected values remain uncertified and are not new seeds. No genus-two acceptance is claimed.

### Remaining risks and next priority

Numerical interpretation remains conditional on the original GW, strata/gluing/forgetting, grading, string/divisor and seed inputs. Arbitrary descendants, genus-two reconstruction and its fixed suites, geometric input validity, actual semisimple CohFT import, R-matrix/translation conditions and ordinary specialization remain open.
The primary regression consumers use the existing checked Sage exports, and this turn adds no new GKM numerical comparison.

A separate preliminary Sage search, with online lookup disabled, found exact row-span witnesses for ψ₁ on M̄₀,₄ and ψ₁ = raw-loop/24 on M̄₁,₁. Lean scratch checks verified both rational row identities and derived the genus-zero three-point vanishing and four-point boundary formula from the existing dimension and forgetful laws. These are preparation for [Getzler’s descendant formulas](https://arxiv.org/html/math/9801003); a follow-up scratch prototype uses the existing semantic kappa, external-psi and nonseparating constructors to hold the genus-one frame, checks the witness and rejects coefficient 1/12. It derives the psi interpretation only under primitive fundamental/psi compatibility and explicit source-row vanishing. A separate Sage run checks that the three named columns have the standard coordinate vectors. Promoting these frames, certifying graph correspondence, geometric relation provenance and stable-map interpretation remain required. The validation manifest retains the exploratory data and exact successful commands.

A further scratch check derives the solved anticanonical divisor equation from the existing all-arity divisor law, proves its positive-class coefficient nonzero, and checks the total-psi and arity-deficit decreases and three signed cup products. It still leaves the abstract divisor action to be identified with those products. No complete descendant reconstruction theorem is claimed from these probes.

Next derive terminating genus-zero and genus-one descendant reductions from the cotangent, boundary and stable-map comparison inputs. The scoped interface review identified two concrete obligations: identify the descendant divisor action with the actual cup product, and identify the supplied rational-tail factors with lower-complexity GW invariants. The current residual comparison alone does not supply a reconstruction formula. The fixed genus-two applications and mandatory full GKM/CohFT compatibility are preserved.

## 2026-10-03: Primary genus-one reconstruction from the existing finite seeds

**Status:** All three fixed surfaces now have a terminating primary genus-one evaluator, uniform nonzero pivot, derived initial sector, and soundness and uniqueness proofs. Arbitrary full effective classes and primary basis multisets are included. The full genus-one numerical benchmark tables, descendant reductions, genus two and required GKM/CohFT gates remain open, so R6 and the research goal are incomplete. No commit or push was made.

### Scope reviewed and findings

Reviewed the original 33 Getzler gluing expressions and requested normalization, signed full-class contractions, primary and degree-zero reductions, ordered marking placements, existing exceptional and strict-line certificates, genus-zero reconstruction and its finite seeds. The baseline `lake build AxiomaticGWTest.Surfaces.LowDegree AxiomaticGWTest.Surfaces.GenusZeroCertificate` passed with 2,674 jobs. All 142 preceding source pins matched the 325-file baseline, and the existing tracked diff was saved before editing.

- **Medium missing reconstruction argument resolved:** Equal energy does not force an elliptic dependency. The actual 2L four-hyperplane equation contains a genus-zero singleton with coefficient −5 at the original energy. New support proofs track total component genus as well as the full curve sum. Genus-zero values use the existing evaluator, and only genus-one calls recurse by strictly smaller energy.
- **Medium missing pivot and seed-sufficiency arguments resolved:** The entire four-hyperplane family has coefficient −9 at energy at least two. The complete initial sector follows from the existing exceptional and strict-line deductions, so no infinite seed family or guessed nonvanishing hypothesis is needed.
- **Medium execution limitation remains:** The current genus-one evaluator constructs all original ordered marking placements. Its theorem-level termination does not certify practical bounded replay. The energy-twelve genus-one numerical gate remains open pending compression and finite certificates.
- No mathematical defect was found in the reviewed existing geometric-input contract or genus-zero public statements. Geometric-model existence and imported CohFT classes were not verified in this scoped extension.

### Revisions and mathematical effect

[`GenusOneSupport.lean`](../../AxiomaticGW/Surfaces/GenusOneSupport.lean) proves homogeneous full-class support and a bound on the sum of component genera. [`GenusOnePivot.lean`](../../AxiomaticGW/Surfaces/GenusOnePivot.lean) proves equality of the extreme-splitting coefficient evaluator to the original raw coefficient. Rational components and self-gluing branches cannot contribute an elliptic singleton.

[`GenusOneMarkings.lean`](../../AxiomaticGW/Surfaces/GenusOneMarkings.lean) proves that every added marking kills a primary class-zero constant in genus at most one, including loop graphs. Induction over the original ordered placements therefore shifts only the positive elliptic vertex in a leading term. [`GenusOneUniform.lean`](../../AxiomaticGW/Surfaces/GenusOneUniform.lean) computes the coefficient of four hyperplanes with energy minus two added points: only the three labelled two-tail graphs contribute, each with requested weight −3. All seven graph types and the original normalization are retained.

[`GenusOneStep.lean`](../../AxiomaticGW/Surfaces/GenusOneStep.lean) isolates the exact coefficient in the original accepted Getzler equation. [`GenusOneRecursion.lean`](../../AxiomaticGW/Surfaces/GenusOneRecursion.lean) defines `pointValue`, proves termination by elliptic energy, removes the guard on actual support and proves uniqueness with genus-zero reconstruction fixed. [`GenusOneReconstruction.lean`](../../AxiomaticGW/Surfaces/GenusOneReconstruction.lean) proves `initialValue_eq_eval`, `pointValue_eq_eval` and `primaryValue_eq_eval` under the original named geometric laws and only the existing line, exceptional and degree-zero elliptic divisor seeds. It includes degree-zero primary values and explicitly keeps the empty zero-class point value auxiliary.

The original genus-zero APIs, theorem statements, geometric assumptions and finite seed inventory are unchanged. The sole new instance decides the explicit `energy ≤ 1` initial predicate, following the existing genus-zero API; no global simp rule, substitute axiom, numerical oracle or assumed recurrence is introduced. The new support properties extend to genus at most one without replacing the existing genus-zero representation. The [API map](../MathematicsToLean.md) and [input ledger](../mathematics/SurfaceReconstructionInputs.md) record the exact boundary.

### Validation and resources

- `lake build AxiomaticGW.Surfaces.GenusOneReconstruction`: passed, 2,672 jobs; every new module was also compiled incrementally.
- `lake build AxiomaticGWTest.Surfaces.GenusOneReconstruction`: passed; the final warning-free version was rebuilt in the full test run below.
- `lake build`: passed, 2,716 jobs.
- `lake test`: passed, 2,755 jobs. The sole final warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.
- `lake lint`: passed.
- `lake env lean /tmp/gw_genus_one_axioms_20261003.lean`: all 20 audited declarations use only `propext`, `Classical.choice` and `Quot.sound`.
- `git diff --check`, new-file whitespace/placeholder checks, documentation links, source pins and preservation checks are recorded in the [validation manifest](../../environments/surface-genus-one-reconstruction-validation.json).

The 15 [regression examples](../../AxiomaticGWTest/Surfaces/GenusOneReconstruction.lean) cover the unbounded coefficient theorem, energy-twelve classes, equal-energy distinct coordinates, the actual −5 rational coefficient in 2L, elliptic-pivot filtering, exclusion of two elliptic component variables, incorrect marking count, zero class, every initial exceptional/strict-line generator, degree-zero divisor signs, the geometric query domain and both original Sage-exported presentations. Direct kernel computation of the recursive branches gives N₁(H;pt³)=0 on P² and N₁(F;pt²)=0 on F₁. These two values test execution, not completion of the required bounded tables.

Development-only proof probes failed before repairs to bound inference, the explicit shifted-marking hypothesis and finite flag-map normalization. One recursive simp combination was removed. Two temporary heartbeat-limit documentation warnings were fixed before the final full test run. These attempts are separated from successful validation in the manifest; none is reported as a successful proof. Reported timings include startup/imports, and Lake timings and wrapper timings are recorded without treating them as controlled performance ratios.

Exactly six existing files were intentionally updated and nine files added, including the validation manifest. All 319 unrelated baseline files remain unchanged. The fixed applications, energy and descendant bounds, Sage/admcycles requirement and mandatory full GKM/CohFT compatibility contract are preserved.

### Remaining risks and next priority

Geometric interpretation remains conditional on the original GW, strata/gluing/forgetting, grading, string/divisor and seed inputs. Primary determination is now proved in genera zero and one; efficient genus-one bounded certificates, arbitrary descendants, genus two, geometric model validity, actual semisimple CohFT import, R-matrix/translation conditions and ordinary specialization are unfinished.

Next prove a compact genus-one marking-distribution evaluator equal to the complete Getzler polynomial, retain the same-energy genus-zero contributions, and use saved intermediate values to certify every required genus-one primary benchmark through energy twelve. R6 remains open until its descendant and numerical gates are met; the full research goal remains active.

## 2026-10-03: Complete genus-zero primary benchmark certificates

**Status:** The fixed positive-class genus-zero primary suite through energy twelve is kernel checked on all three targets: 4 plane, 48 F₁ and 454 two-point-blowup queries. Three auxiliary zero-class entries are checked separately and excluded from geometric lookup. The original geometric inputs and finite genus-zero seeds are unchanged. R1 and R3–R8 remain incomplete; genus-one/two reconstruction, descendants and the required GKM/CohFT gates remain open. No commit or push was made.

### Scope reviewed and findings

Reviewed the existing compact WDVV evaluator, signed primary and degree-zero reduction, complete bounded class enumeration, strict-energy support, geometric soundness, the fixed primary benchmark contract, archived Kontsevich–Manin formula (5.18), and three existing native GKM primary cases. The baseline compression regression target passed. All 131 preceding source pins matched; the complete tracked diff and a 314-file hash snapshot were saved before editing.

- **Medium execution gap resolved:** Recomputing nested tables and reducing one monolithic certificate caused expensive kernel reduction and memory pressure. Saved intermediate values now receive separate row proofs. The scalar evaluator avoids intermediate polynomial construction, skips proved zero products, and sums directly over first splitting components using injectivity of the original pair map.
- **Medium coverage cost resolved:** Direct equality of large function-valued finite sets was impractical for the largest table. Coverage now follows from strict adjacent ordering of integer keys, inclusion in the original bounded set and equality of finite cardinalities. No zero-valued class is dropped.
- **Medium numerical gate resolved:** Every required positive-class genus-zero primary query through energy twelve has a checked exact answer and a geometric consumer. Higher-genus and descendant gates are not implied by this subset.
- No mathematical correctness defect was found in the reviewed original support, pivot or soundness statements. This is a scoped reconstruction review, not verification of geometric moduli models or imported CohFT classes.

### Revisions and mathematical effect

[`GenusZeroScalar.lean`](../../AxiomaticGW/Surfaces/GenusZeroScalar.lean) proves equality of direct scalar evaluation to the full compact graph polynomial for every candidate valuation by full curve class. Its vertex formula preserves the signed dimension equation, divisor products and the classical cubic. Graph induction preserves node labels, inverse-metric signs, all class splittings and binomial marking multiplicities. The small energy-three profile keeps the original computation. All prior reconstruction and cached-table APIs are preserved.

[`GenusZeroCertificate.lean`](../../AxiomaticGW/Surfaces/GenusZeroCertificate.lean) checks each initial value or selected original WDVV equation. Exact enumeration and strict energy decrease prove `checkBoundedValues_sound` by induction. `checkPointClaim` binds the target, positive full class, bound and claimed rational answer; its checked-query theorem retains the original geometric laws, WDVV presentation and genus-zero seeds. No recurrence assumption, extra seed, placeholder, substitute axiom, global simp rule or typeclass instance was introduced.

The [frozen manifest](../../environments/surface-genus-zero-primary-tables.json) contains 509 rows, with all zero answers retained. The generated [plane](../../AxiomaticGW/Surfaces/Fixtures/GenusZeroPlaneTable.lean), [F₁](../../AxiomaticGW/Surfaces/Fixtures/GenusZeroF1Table.lean) and [two-point-blowup](../../AxiomaticGW/Surfaces/Fixtures/GenusZeroBl2Table.lean) modules prove complete coverage, every row equation and agreement with the original evaluator. [`GenusZeroBenchmarks.lean`](../../AxiomaticGW/Surfaces/GenusZeroBenchmarks.lean) supplies a common bounded lookup and its soundness/geometric theorems. Unsupported and auxiliary requests return `none`.

The [candidate generator](../../scripts/export_surface_genus_zero_tables.py) is a separate exact implementation of published formula (5.18) at energy at least four. It does not reuse the Lean or prior Python graph evaluator. Both mathematical routes use WDVV; the low-energy normalizations and derived base cases are shared and explicitly labelled. Lean still verifies the noninitial energy-three equations, so those comparison values are not new trusted seeds. The three GKM comparisons test existing numerical normalizations and conventions only.

The 18 new Lean regression examples cover altered seeds/answers, omitted and extra classes, bounds, same-energy full-class distinctions, the classical negative exceptional pairing, public lookup domains, and actual Sage WDVV replay in plane and blowup geometric deductions. In particular, the eleven-point values are 640 for 5H−3E on F₁ and 18132 for 5H−2E₁−E₂ on the two-point blowup. The README provides executable lookups and a proof example.

### Validation and resources

- `lake build AxiomaticGW.Surfaces.GenusZeroBenchmarks`: passed, 2,667 jobs. All three complete fixture certificates are accepted; the largest fixture replay reported 800 seconds in Lake. The subsequent public-interface repair rebuilt successfully using those accepted fixtures.
- `lake build AxiomaticGWTest.Surfaces.GenusZeroCertificate`: passed, 2,669 jobs, including all 18 new examples.
- `lake build`: passed, 2,709 jobs.
- `lake test`: passed, 2,747 jobs. The sole warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.
- `lake lint`: passed.
- `lake env lean /tmp/gw_table_certificate_axioms_20261003.lean`: all 25 audited declarations use only `propext`, `Classical.choice` and `Quot.sound`.
- `lake env lean /tmp/gw_table_certificate_readme_20261003.lean`: the exact README example passed, returning `some 620`, `some 640`, `some 18132`, and `none`, and checking its proof example.
- `python3 scripts/export_surface_genus_zero_tables.py --check`: all four frozen outputs match.
- `python3 scripts/test_surface_genus_zero_tables.py -v`: all ten tests passed, including the three existing GKM comparisons.
- `git diff --check`, changed-file whitespace and placeholder scans, local documentation links, source pins and the baseline preservation audit passed as recorded in the validation manifest.

The [validation manifest](../../environments/surface-genus-zero-certificate-validation.json) separates successful final replay from native exploration, failed development probes and explicitly interrupted resource experiments. The isolated native complete checks returned true for both blowup tables, but those outputs were not used as proofs. Early monolithic reductions, direct coverage comparisons and the superseded splitting evaluator were stopped without claiming complete blowup acceptance. Resource figures distinguish host-wide memory observations from the reported per-child high-water value; timings include startup and imports and are not controlled speed ratios. The first complete row replay reached the final 455-row assembly but failed its default recursion-depth limit. A local limit of 4096 fixed that proof; an isolated assembly check with explicit row hypotheses passed before the full replay was repeated.

Exactly six existing files were intentionally revised and eleven files added, including the validation manifest. All 308 unrelated files in the 314-file baseline remain byte-for-byte unchanged. The final incremental diff excludes only the self-referential validation manifest; its hash, source pins and preservation evidence are recorded there.

### Remaining risks and next priority

The numerical answers remain conditional on the existing geometric GW, gluing/forgetting, grading, divisor and seed inputs when interpreted as actual invariants. Arbitrary descendants, genus-one/two reconstruction, geometric-model validity and all outstanding class-level GKM/R-matrix/ordinary-specialization gates remain open. The fixed surfaces, all benchmark bounds and the full research goal are unchanged and active.

Next prove genus-one support and a nonzero solved coefficient for the selected Getzler family, derive its complete low-energy sector from the existing finite seeds, and establish termination and soundness before filling its fixed tables. This genus-zero numerical gate does not complete R6 or the research goal.

## 2026-10-03: Binomial marking compression and the plane quartic benchmark

**Status:** The bounded genus-zero table now evaluates a proved binomial compression of the original marked WDVV polynomial. The complete positive-class plane primary genus-zero subset through energy twelve is kernel checked: degrees one through four give 1, 1, 12, 620. Its coverage and conditional geometric interpretation are proved. R1 and R3--R8 remain incomplete; the full blowup and higher-genus suites, descendants and required GKM/CohFT integration remain obligations. No commit or push was made.

### Scope reviewed and findings

Reviewed ordered marking placement, the node-label bijections, symmetric primary keys, full-class contractions, strict-energy remainder support, uniform pivot coefficients, bounded-table execution, and the plane benchmark specification. All 125 source pins from the preceding validation record matched; `lake build AxiomaticGWTest.Surfaces.GenusZeroReconstruction` passed the baseline with 2,661 jobs. The 307-file working-tree snapshot and full tracked diff were saved before editing.

- **Medium performance gap addressed:** The original equation enumerated every ordered placement. For a two-vertex WDVV channel with n additional points, the new computation uses n+1 distributions, weighted by binomial coefficients, rather than 2^n placements. Full curve splits and signed node contractions are unchanged.
- **Medium remaining performance limitation:** Direct kernel evaluation of larger blowup tables is still expensive. A valid regression attempt containing several energy-five-through-nine computations was stopped without an accepted result. Native outputs are recorded separately, and those large computations are not claimed as kernel-certified benchmarks.
- **Low documentation correction:** Current descriptions no longer say the bounded evaluator expands every ordered marking placement. Historical validation records and their then-open gates are retained.
- No mathematical correctness defect was found in the reviewed existing support, pivot or soundness statements. Their public signatures and geometric assumptions are preserved.

### Implementation and mathematical effect

[`GenusZeroExpansion.lean`](../../AxiomaticGW/Surfaces/GenusZeroExpansion.lean) appends points to the original insertion multiset and proves the one-marking identity using Pascal's formula and explicit node-label transport. Induction proves equality to the complete original expansion for every genus-zero gluing expression, point count and valuation in any commutative rational algebra. The WDVV corollary therefore preserves the whole polynomial, including zero-class contributions and all multiplicities.

[`GenusZeroCompactStep.lean`](../../AxiomaticGW/Surfaces/GenusZeroCompactStep.lean) evaluates that expression with a strict-energy guard. The leading singleton evaluates to zero; the existing support theorem proves that every remaining valuation is unchanged. The uniform denominator uses its existing coefficient-one theorem, and the energy-three request is preserved. [`GenusZeroTable.lean`](../../AxiomaticGW/Surfaces/GenusZeroTable.lean) now calls this compact step, with the same table-comparison and geometric soundness statements. No seed, recurrence hypothesis or geometric law was added.

[`PlaneQuartic.lean`](../../AxiomaticGW/Surfaces/Fixtures/PlaneQuartic.lean) kernel-checks the entire eight-point-marked HHptpt request against `N₄ - 33 N₁N₃ - 224 N₂²`. [`PlanePrimaryBenchmarks.lean`](../../AxiomaticGW/Surfaces/PlanePrimaryBenchmarks.lean) proves the four values, exhaustive positive-class coverage through energy twelve, and their interpretation under the existing geometric laws and original accepted WDVV certificate, with only the plane line seed. The [frozen query manifest](../../environments/plane-primary-genus-zero-benchmarks.json) records independently published expected values from the archived Kontsevich--Manin source, section 5.2. Its recursion is not assumed in these proofs.

Seven new regression examples reject a changed quartic coefficient and a changed marking request, preserve equal-energy full-class distinctions on both blowups, check the geometric query domain, and consume the actual Sage-exported WDVV presentation to deduce the quartic invariant. The [API map](../MathematicsToLean.md) records the public declarations.

### Validation and preserved work

- `lake build AxiomaticGWTest.Surfaces.GenusZeroCompression`: passed, 2,665 jobs.
- `lake build`: passed, 2,703 jobs.
- `lake test`: passed, 2,740 jobs. The sole warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.
- `lake lint`: passed.
- `lake env lean /tmp/gw_compact_axioms_20261003.lean`: all 15 audited declarations use only standard Lean axioms; no project-specific or placeholder axiom occurs.
- `git diff --check`, new-file whitespace and placeholder scans, query/source-manifest consistency, documentation links, and preservation checks: passed as recorded in the [validation manifest](../../environments/surface-genus-zero-compression-validation.json).

The separate quartic kernel probe succeeded in 6.110 seconds including Lean startup/imports, while its native probe returned 620 in 5.705 seconds. These concurrent runs are observations, not a controlled speed benchmark. A native bounded two-point-blowup table returned 12, 0, 12, 0, 1 for classes (3,3,3), (9,0,0), (2,2,3), (1,1,3), (1,2,3), respectively, in 14.842 seconds including startup. These larger outputs remain exploratory. Two development regression runs were explicitly cancelled with exit 130: the first while correcting the query-domain API name, and the second because direct large-table kernel evaluation was still running. Final focused regressions and the full suite passed afterward.

Exactly seven existing files were intentionally revised and seven files added; all 300 unrelated baseline files remain unchanged. The fixed application targets, benchmark bounds, Sage/admcycles integration and GKM completion contract are unchanged. The full research goal remains active.

### Next priority

Build compact certificates for saved intermediate values, so the kernel can check bounded blowup equations without repeatedly evaluating whole tables. Complete the fixed genus-zero F₁ and two-point-blowup suites through energy twelve against independently audited expected values, then extend reconstruction to genus one. The plane subset does not complete R6 or the full research goal.

## 2026-10-03: Primary genus-zero reconstruction and certified bounded tables

**Status:** Primary genus-zero reconstruction now has a terminating evaluator, a complete derivation of its initial sector, and proofs of soundness and determination from the existing line and exceptional seeds for all three fixed surfaces. Arbitrary primary basis multisets, degree-zero classical values and positive-degree unstable arities are included. A bounded-table implementation is proved equivalent and reuses lower-class values. R1 and R3--R8 remain incomplete: descendants, higher genera, the complete numerical benchmark corpus and the remaining GKM gates are unchanged obligations. No commit or push was made.

### Scope reviewed and findings

Reviewed the full-class support and nonvanishing proofs, original WDVV numerical consumer, finite line/exceptional seeds, ruling/L deductions, existing double-class vanishings, and primary/degree-zero reductions. The preceding turn made verified progress. Its 121 source pins matched the current tree; the baseline `lake build AxiomaticGWTest.Surfaces.GenusZeroUniform` passed 2,657 jobs. The diff and hashes of all 302 tracked/untracked files were saved before editing.

- **High reconstruction gap resolved for primary genus zero:** The selected requests now form a total energy-decreasing computation, with complete low-energy coverage and a geometric soundness theorem. The uniqueness proof's equations are discharged from the original checked relation, rather than accepted as a recurrence input.
- **Medium dependency improvement:** Four exact WDVV identities prove the required double-exceptional and double-strict-line genus-zero vanishings directly. The new consumer therefore needs only the genus-zero line and exceptional seeds; the earlier Getzler-based proofs remain intact.
- **Medium computation improvement:** The bounded table reuses earlier values, preserves every curve coordinate and proves that all dependencies lie within the previous bound. The full marked remainder still expands exponentially, and large closed kernel replay remains a practical gap.
- No semantic defect was found in the inspected existing declarations. The scope is the primary genus-zero reconstruction path, not a comprehensive review or construction of geometric GW/CohFT models.

### Revisions and mathematical effect

[`RationalTerms.eval_congr`](../../AxiomaticGW/Coefficients/RationalTerms.lean) proves that evaluation depends only on variables occurring in the actual terms. [`GenusZeroRecursion.lean`](../../AxiomaticGW/Surfaces/GenusZeroRecursion.lean) defines the initial sector as energy at most two together with the line seed, and fixes the original WDVV request, exact coefficient and remainder for every remaining class. `pointValue` terminates by anticanonical energy. A guard makes its valuation total, while the support theorem proves the guard's zero branch is never used in the actual remainder. `eq_pointValue_of_equations` proves uniqueness by energy induction. `primaryValue` applies the existing classical, signed-divisor and dimension reductions at arbitrary marking multiplicity.

[`GenusZeroReconstruction.lean`](../../AxiomaticGW/Surfaces/GenusZeroReconstruction.lean) proves the initial table using exhaustive full-coordinate enumeration, the existing ruling/L deductions and four additional checked WDVV identities. The `H,H,Eᵢ,Eᵢ` request at `2Eᵢ` and `H,H,E₁,E₂` at `2L` each equal four times the requested singleton. `initialValue_eq_eval`, `pointValue_eq_eval` and `primaryValue_eq_eval` then identify the computations with the supplied theory under its existing geometric laws, original WDVV certificate, target identification and genus-zero seeds. The auxiliary empty query at zero curve class retains its zero convention.

[`GenusZeroTable.lean`](../../AxiomaticGW/Surfaces/GenusZeroTable.lean) constructs one complete table per energy layer. `tableLookup_pointTable` proves correctness for every class inside any bound; strict decrease guarantees every lower-class lookup is covered. The cached point and primary interfaces have both algorithm-comparison and geometric soundness theorems.

No existing mathematical definition or theorem statement changed. The new direct vanishing route reduces the hypotheses needed by this consumer; it does not replace earlier APIs. No seed, assumed recurrence, placeholder, substitute axiom, global simp rule or coercion was introduced. The sole new instance is the canonical decidability of the explicit finite-sector predicate. The complete descendant and higher-genus seed-sufficiency claims remain open.

### Validation and numerical evidence

The [nineteen regression examples and cubic computation](../../AxiomaticGWTest/Surfaces/GenusZeroReconstruction.lean) cover every initial-value branch, noninitial energy-three recursion, equal-energy classes with different values, signed divisor factors, unit and dimension vanishing, degree-zero normalization, bounded-table lookup and a public geometric consumer. Kernel replay proves the plane cubic value twelve and derives the actual eight-point invariant from the original WDVV certificate and plane line seed.

```bash
lake build AxiomaticGWTest.Surfaces.GenusZeroReconstruction
lake build
lake test
lake lint
lake env lean /tmp/gw_reconstruction_axioms_20261003.lean
python3 scripts/test_surface_equations.py
git diff --check
```

The targeted build passed 2,661 jobs, the final full build passed 2,699 jobs, and the test run passed 2,735 jobs. Lint and all fourteen Python regressions passed. All 22 audited declarations use only standard Lean axioms. The only warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`. Local proof-development issues involving definition equation names, closed decidability goals and a runtime-probe IO annotation were repaired before the successful checks.

A separate native cached calculation returned the plane quartic candidate 620 in 9.485 seconds including Lean startup/imports. Its internal IO timer reported zero because closed pure computation can occur before that timer; that number is not used as performance evidence. Two earlier combined execution/kernel-replay probes were explicitly stopped with exit 130, with no accepted quartic replay. Thus the native result is exploratory evidence, while twelve is the new kernel-checked plane benchmark. The [validation manifest](../../environments/surface-genus-zero-reconstruction-validation.json) records the successful commands, stopped probes, source hashes, axiom audit and preservation of unrelated work.

### Remaining risks and next priority

The full marking expansion and large closed kernel reductions remain performance concerns, and the complete energy-twelve corpus has not passed kernel replay. Next, prove a compact remainder computation preserving the original placement multiplicities, then complete the fixed primary genus-zero tables and their claim-bound replay before extending the reduction to genus one. Arbitrary descendants, genus-two reconstruction, geometric input validity, shared research benchmarks and all remaining class-level GKM/R-matrix/ordinary-comparison obligations remain open. The full goal stays active.

## 2026-10-02: A uniform genus-zero pivot and certified point-marking computation

**Status:** The original `H,H,pt,pt` WDVV request now has proved leading coefficient one on all three fixed surfaces at every energy at least four, with energy minus four added points. Exhaustive kernel checks supply nonzero coefficients for every energy-three class on F₁ and Bl₂P²; the plane's energy-three class is its line seed. The numerical step retains its original geometric inputs and certificate. Total reconstruction and finite-seed sufficiency remain open. R1 and R3--R8 remain incomplete, and the fixed applications, benchmarks and GKM completion gate are unchanged. No commit or push was made.

### Scope reviewed and findings

Reviewed the exact coefficient algebra, degree-zero primary vertices, ordered marking placements, their full-class interpretation, and the WDVV reconstruction step. The baseline `lake build AxiomaticGWTest.Surfaces.GenusZeroPivot` passed 2,653 jobs. All 118 source pins of the preceding validation record matched before editing; the existing diff and hashes of 298 tracked/untracked files were saved.

- **High proof gap resolved for the selected family:** Nonvanishing is proved for all classes above the finite initial sector, without a bound or a hyperplane-intersection hypothesis. The two F₁ and ten Bl₂P² energy-three classes are covered exhaustively using the proved complete bounded enumerator.
- **Medium computation gap resolved for leading coefficients:** A dimension shift on the original three graphs replaces exponential point-marking enumeration. The complete remainder polynomial still uses the existing expansion.
- **Low documentation issue fixed:** An earlier F₁ regression's negative coefficient comes from classical exceptional self-intersection, not directly from the exceptional inverse metric. Only its comment changed.
- No semantic defect was found in the existing declarations inspected. This scoped review does not establish a geometric surface GW model or a total reconstruction algorithm.

### Revisions and mathematical effect

[`RationalTerms.coefficient_mul_zero`](../../AxiomaticGW/Coefficients/RationalTerms.lean) proves the constant coefficient of a product comes from its two constant coefficients. [`GenusZeroMarkings.lean`](../../AxiomaticGW/Surfaces/GenusZeroMarkings.lean) uses it to prove that every additional-marking placement on a degree-zero primary tree has zero constant contribution. Induction through the original ordered placement list then puts all new points on the positive-class vertex of each linear contribution. `WDVV.pointMarkedCoefficient_eq` identifies the compact computation with the singleton coefficient of the original complete request, preserving node labels, signed contractions and multiplicities.

[`GenusZeroUniform.lean`](../../AxiomaticGW/Surfaces/GenusZeroUniform.lean) evaluates the `H,H,pt,pt` family. The classical `H,H,1` vertex contributes one, its paired positive-class vertex has only point insertions, and the crossed channel contributes zero. The dimension equation gives exactly energy minus four added points. `WDVV.primaryTerms_reconstruction_coefficient` proves coefficient one for the full expansion; `WDVV.primary_point_eq_reconstruction` combines this with the original numerical step. The selected energy-three divisor profiles have separate exhaustive nonzero proofs, and `plane_energy_three_eq_line` identifies the plane base class.

No existing definition or theorem statement changed. No new geometric law, recurrence assumption, seed, axiom, global simp rule, instance or coercion was introduced. These are unconditional coefficient identities and a numerical deduction under the existing named geometric hypotheses. The conic regression rechecks an existing value; no new numerical benchmark value is claimed.

### Validation

The [fourteen regression examples](../../AxiomaticGWTest/Surfaces/GenusZeroUniform.lean) cover nonvacuous marking vanishing, agreement with the earlier evaluator, zero hyperplane intersection, the energy-twelve boundary, all energy-three branches, a missing-marking failure and the conic deduction from the existing line seed. A plane degree-100 case computes coefficient one with 296 added points and separately certifies equality to the original expansion without enumerating its placements.

```bash
lake build AxiomaticGWTest.Surfaces.GenusZeroUniform
lake build
lake test
lake lint
lake env lean /tmp/gw_uniform_axioms_20261002.lean
python3 scripts/test_surface_equations.py
git diff --check
```

The targeted build passed 2,657 jobs, the full build passed 2,696 jobs, and the test run passed 2,731 jobs. Lint and all fourteen Python regressions passed. All twenty audited theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. The only warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`. The [validation manifest](../../environments/surface-genus-zero-uniform-validation.json) records commands, source hashes, axiom results and preservation of unrelated working-tree changes. Local proof-development failures were repaired before successful validation; no failed attempt is counted as a passing check.

### Remaining risks and next priority

The full remainder still enumerates marking placements, and the finite energy-one/two results have not yet been assembled into a total evaluator. Next, combine those results, the energy-three coefficients, the uniform step and strict decrease into a well-founded genus-zero point-invariant computation; prove soundness and uniqueness from the existing finite seeds. Efficient remainder evaluation, arbitrary descendant reduction, genus-one/two reconstruction, every fixed benchmark, geometric input validity and the remaining class-level GKM/R-matrix/ordinary-comparison gates remain open.

## 2026-10-02: Uniform genus-zero coefficient extraction through degree-zero components

**Status:** The leading coefficient of every positive-class primary genus-zero graph can now be computed using only the two extreme curve-class splits, with a proof of equality to the complete original expansion. The WDVV consumer preserves every original channel and marking placement. Uniform nonvanishing for the selected request families and total invariant reconstruction remain open. R1 and R3--R8 remain incomplete; the fixed surface applications, genus-two benchmarks and GKM completion gate are unchanged. No commit or push was made.

### Scope reviewed and findings

Reviewed the rational-term coefficient representation, complete primary graph expansion, full-class support proof, dimension and divisor reductions, classical cubic and arbitrary-marking WDVV request. The baseline `lake build AxiomaticGWTest.Surfaces.GenusZeroStep` passed (2,654 jobs). The existing diff and hashes of 295 tracked/untracked files were saved before editing.

- **High proof gap partially resolved:** The coefficient is now reduced uniformly to its two degree-zero-component contributions. This proves extraction and an executable shortcut, but not the proposed nonzero formulas for all selected classes and marking counts.
- **Medium computation gap resolved for class splitting:** The new coefficient evaluator avoids enumerating every effective splitting of the positive class. It retains the original additional-marking enumeration, so the exponential placement cost remains.
- **Low documentation issue fixed:** The malformed module heading in `GenusZeroSupport.lean` was corrected. Its definitions and proofs were unchanged.
- No semantic defect was found in the existing declarations inspected. This is a scoped review of the primary genus-zero coefficient path, not a comprehensive review or construction of a geometric GW model.

### Revisions and mathematical effect

[`RationalTerms.lean`](../../AxiomaticGW/Coefficients/RationalTerms.lean) now proves coefficient compatibility with terms, addition, finite/list sums, scaling and singleton extraction from products. The product formula retains empty/singleton factors, cancellation and repeated-variable multiplicities.

[`GenusZeroPivot.lean`](../../AxiomaticGW/Surfaces/GenusZeroPivot.lean) derives zero coefficients for monomials with the wrong full curve class. In particular a positive-class component has no constant term. `pointCoefficient_separating` therefore retains precisely the ordered splits `(0, beta)` and `(beta, 0)`, with the original signed inverse metric. Elementary components give their dimension-checked signed divisor product or classical cubic. A degree-zero primary vertex with arity other than three contributes zero; consequently a two-vertex placement with more than three flags on both vertices contributes no leading coefficient.

`pointCoefficientEval_eq` proves the recursive coefficient computation equal to the complete graph expansion for every positive class, without an energy or marking bound. `WDVV.primaryPointCoefficient_eq` ties this computation to the original held WDVV request and all its marking multiplicities. The explicit genus proof rules out nonseparating expressions. This algorithm computes coefficients, not GW invariant values, and introduces no geometric hypothesis, recurrence assertion, seed, axiom, global simp rule, instance or coercion. No prior mathematical definition or theorem statement changed, and no new numerical benchmark value is claimed.

### Validation

The [eleven regression examples](../../AxiomaticGWTest/Surfaces/GenusZeroPivot.lean) check cancelled/nonlinear terms, distinct equal-energy exceptional coordinates, four-point degree-zero vanishing, placements on both vertices, a three-vertex tree, and exact original-request coefficients on P², F₁ and Bl₂P². Negative checks cover a zero exceptional coordinate and a missing point marking. The original-request coefficient checks use `decide +kernel` after the proved extraction identity.

```bash
lake build AxiomaticGWTest.Surfaces.GenusZeroPivot
lake build
lake test
lake lint
lake env lean /tmp/gw_pivot_axioms_20261002.lean
python3 scripts/test_surface_equations.py
git diff --check
```

The targeted build passed 2,653 jobs, the full build passed 2,694 jobs, and the test run passed 2,728 jobs. Lint and all fourteen Python regressions passed. All 22 audited theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. The only warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`. The [validation manifest](../../environments/surface-genus-zero-pivot-validation.json) records exact commands, source hashes, axiom results and preservation of unrelated working-tree changes. Local proof-development errors in conditional simplification, indexed constructor patterns and `StableArity` decidability were repaired before successful validation; no failed attempt is counted as a passing check.

### Remaining risks and next priority

The coefficient equality is unconditional algebra for the fixed surface representations; the existing equation in actual invariants still requires its named geometric laws, realizations, target identification and seed validity. The new evaluator has a proved extraction contract at positive classes, not a uniform nonzero result. Symmetric marking enumeration, the total genus-zero invariant evaluator, finite-seed sufficiency and uniqueness, genus-one/two reconstruction, descendant comparison, and all remaining class-level GKM and R-matrix obligations are open.

Next, use the arity-three vanishing theorem to prove the multiplicity of the surviving additional-marking placements and derive the proposed uniform pivot formulas for each surface and boundary branch. Then combine nonvanishing with the established strict decrease and audited low-energy cases to construct and certify the invariant recursion.

## 2026-10-02: Uniform genus-zero support and a checked decreasing reconstruction step

**Status:** Strict decrease of all residual primary genus-zero WDVV queries is now proved for arbitrary curve classes, basis labels and marking counts. The numerical step is derived from the original checked relation whenever its exact pivot is proved nonzero. Uniform nonvanishing and a complete recursive evaluator remain open. R1 and R3--R8 remain incomplete; the goal, fixed applications, benchmarks and GKM completion gate are unchanged. No commit or push was made.

### Scope reviewed and findings

Reviewed the exact rational-term representation, primary and degree-zero substitutions, signed dimension condition, positive full-class monoid, graph evaluator, arbitrary-marking WDVV bridge and previous 493-case exploration. The baseline `lake build AxiomaticGWTest.Surfaces.WDVVBaseCases` passed (2,657 jobs), and the pre-existing diff and hashes of 291 files were saved.

- **High proof gap resolved:** The previous decrease evidence was a bounded computational probe. The new proof establishes full curve-class homogeneity of every surviving monomial and derives strict decrease uniformly for primary genus zero.
- **High reconstruction gap partially resolved:** Exact singleton isolation and a sound division step are now proved. Nonzero pivots for a complete request family, executable recursion, seed sufficiency and global uniqueness still require proof; these are not assumed complete because finite examples work.
- No new semantic defect was found in the reviewed existing definitions or statements. The review is limited to this reconstruction path. A new filter docstring was tightened to make clear that strict decrease requires homogeneous point support; an arbitrary term list does not have that property.

### Revisions and mathematical effect

[`GenusZeroSupport.lean`](../../AxiomaticGW/Surfaces/GenusZeroSupport.lean) first derives the residual point count from the signed dimension equation. A nonzero primary coefficient excludes unit insertions, so a positive genus-zero component has exactly energy minus one points. Induction through the existing gluing evaluator then proves that each surviving monomial contains only these positive-class point queries, with full component classes summing to the original class. Genus zero excludes nonseparating gluings. Degree-zero components become constants through the existing reduction.

Positivity of energy shows that a variable at the original energy forces the monomial to be exactly the requested singleton. This excludes nonlinear leading occurrences and distinct equal-energy curve classes. The executable `lowerTerms` filter removes all occurrences of that singleton, and `wdvv_lowerTerms_dependencies` proves that each remaining query has strictly smaller positive energy. The result applies without a marking or energy bound and without any geometric hypothesis or numerical value.

The added `RationalTerms.eval_isolate_singleton` theorem in [`RationalTerms.lean`](../../AxiomaticGW/Coefficients/RationalTerms.lean) proves exact decomposition into the collected singleton coefficient and filtered remainder, for every commutative rational algebra. [`GenusZeroStep.lean`](../../AxiomaticGW/Surfaces/GenusZeroStep.lean) uses that identity and the original incoming WDVV presentation to prove `WDVV.primary_point_eq` under the existing geometric laws. Its denominator is computed from the complete graph request; the caller must prove that exact number nonzero. It consumes no final recurrence assertion, new seed, or elliptic seed.

No prior definition or theorem statement changed, and no global simp rule, instance, coercion or axiom was added. The full curve coordinates and positive-degree unstable arities are preserved. The earlier finite exploration remains evidence for the proposed pivots; its decrease component now has a separate uniform Lean proof. This step adds no new numerical benchmark value.

### Validation

Targeted production and regression builds passed:

```bash
lake build AxiomaticGW.Surfaces.GenusZeroStep
lake build AxiomaticGWTest.Surfaces.GenusZeroStep
```

The [regression module](../../AxiomaticGWTest/Surfaces/GenusZeroStep.lean) contains four examples and two exact coefficient/remainder checks. It rejects replacing E₁ with equal-energy E₂, excludes a squared leading variable, preserves the F₁ exceptional zero-point query, and recovers the plane conic value through the new division step using the original certificate and unchanged line seed. The final validation commands and outcomes are recorded in the [manifest](../../environments/surface-genus-zero-support-validation.json):

```bash
lake build
lake test
lake lint
lake env lean /tmp/gw_order_axioms_20261002.lean
python3 scripts/test_surface_equations.py
git diff --check
```

The full build passed 2,693 jobs, tests passed 2,726 jobs, lint passed, and all fourteen existing Python regressions passed. The sixteen audited public theorems use only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`, or a subset). The only warning was the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`. The full test run also recompiled the support module and its consumers after the filter-docstring correction.

Initial local proof attempts needed matching simplification in an induction hypothesis, explicit singleton membership conversion, elementary additive identities in place of an unavailable tactic, and an explicit energy calculation in the conic consumer. These were corrected before the successful targeted builds, and temporary diagnostic traces were removed. No failed attempt is counted as successful validation.

### Remaining risks and next priority

The support theorem covers primary genus zero; it does not claim descendant or higher-genus decrease. The numerical theorem retains geometric realization, GW law and target-identification hypotheses. A nonzero proof is required for each computed pivot, so the theorem does not by itself give a total reconstruction algorithm. All fixed numerical tables, genus-one/two recursion, arbitrary descendant comparison, geometric seed validity and sufficiency, and remaining GKM/CohFT/R-matrix gates retain their stated obligations.

Next, prove the proposed uniform pivot formulas for the three fixed targets and their boundary cases, then use the established strict decrease to construct the recursive evaluator and prove soundness and uniqueness from the finite audited base cases. Efficient symmetric marking enumeration remains necessary for the research-scale benchmark suites.

## 2026-10-02: Arbitrary-marking WDVV and the remaining low-energy surface base cases

**Status:** The original WDVV certificate now gives equations with arbitrary additional markings and ancestor powers. Nine further conditional numerical values are derived, including the plane conic and the separate generator L=H−E₁−E₂. The finite seed package is unchanged. R1 and R3--R8 remain incomplete; the fixed targets, energy-twelve and genus-two benchmarks, and GKM completion gate are unchanged. The goal remains active. No commit or push was made.

### Scope reviewed and findings

Reviewed the original WDVV frame and boundary-class semantics, primitive forgetting/gluing laws, genus-zero component reductions, finite seed list, and the full-class surface graph evaluator. The baseline `lake build AxiomaticGWTest.Surfaces.Exceptional` passed (2,649 jobs). The existing diff and hashes of 277 tracked/untracked files were saved before editing.

- **High integration gap resolved:** The checked WDVV-to-GW path previously stopped at four external markings. The new bridge derives every additional-marking placement from the existing primitive laws and retains the original three-column, two-row certificate.
- **High reconstruction gap resolved for the finite base cases:** L was distinct from the indexed Eᵢ classes and its normalization could not be assumed as another seed. Five blowup WDVV requests now derive the ruling and L normalizations from the existing line/Eᵢ seeds. Three Getzler requests in 2L then settle its genus-one base case.
- **Medium hypothesis issue avoided in the new API:** Genus-zero WDVV reduction does not require genus-one divisor seeds. Two additional semantics lemmas prove this directly by the genera of the components; the existing general-genus interface remains unchanged.
- No new semantic defect was found in the scoped existing definitions and theorem statements. This is not a comprehensive review or a construction of geometric surface GW theories.

### Revisions and mathematical effect

[`WDVVForgetful.lean`](../../AxiomaticGW/Tautological/WDVVForgetful.lean) identifies the original columns with explicit gluing expressions, proves the placement count 3·2ⁿ, and derives the arbitrary-marking ancestor equation from boundary equality and primitive forgetting/gluing compatibility. The additional genus-zero lemmas in [`TermExpansion.lean`](../../AxiomaticGW/Surfaces/TermExpansion.lean) interpret reduced component terms without elliptic seeds. [`Surfaces/WDVV.lean`](../../AxiomaticGW/Surfaces/WDVV.lean) transfers the original incoming relation and an exact complete term comparison to an equation in the supplied theory's invariants.

The [blowup fixtures](../../AxiomaticGW/Surfaces/Fixtures/BlowupWDVV.lean), [plane conic fixture and consumer](../../AxiomaticGW/Surfaces/PlaneGenusZero.lean), and [strict-line Getzler fixtures](../../AxiomaticGW/Surfaces/Fixtures/StrictLineGetzler.lean) check nine complete requests with `decide +kernel`. The conic request includes all placements of two additional points and retains the squared line variable.

The [blowup consumer](../../AxiomaticGW/Surfaces/BlowupGenusZero.lean) gives N₀(F;1)=1 on F₁ and N₀(L;0)=N₀(E₁+L;1)=N₀(E₂+L;1)=1, N₀(E₁+E₂;1)=0 on the two-point blowup. The plane consumer gives N₀(2H;5)=1. The [strict-line consumer](../../AxiomaticGW/Surfaces/StrictLine.lean) gives N₀(2L;1)=N₁(2L;2)=N₁(L;1)=0. The last argument counts repeated primary point insertions. These are nine numerical deductions under explicit geometric laws and existing seeds, not nine new seed assumptions.

No prior definition, theorem statement, normalization, finite seed, global simp lemma, instance, or coercion changed. The WDVV path uses the same exact full classes and inverse metric as the existing Getzler path. Arbitrary nonzero powers remain ancestors unless a separately proved reduction applies; no descendant comparison is silently introduced.

The [Sage script](../../scripts/explore_wdvv_base_cases.py) and [report](../../environments/surface-wdvv-base-cases.json) record 652 uncollected contributions, 19 final monomials and the exact base-case linear systems. Only the existing seeds are substituted; the derived L normalization then enters the strict-line system, whose determinant is 1026. The exporter now permits an explicitly requested three-column frame while preserving its 33-column default and byte-identical old export.

The [companion finite exploration](../../scripts/explore_wdvv_pivots.py) checks all 493 selected genus-zero requests of energy three through twelve, excluding the plane line seed: three plane, 45 F₁ and 445 Bl₂P² classes. The [report](../../environments/surface-wdvv-pivot-exploration.json) verifies a nonzero proposed leading coefficient and that every residual variable is a positive, strictly lower-energy genus-zero point query. These shared-source symbolic checks compute no GW table and do not prove a uniform recursion. Energy-one/two cases remain separate finite deductions.

### Validation

Targeted builds compiled every new production module. The final validation commands were:

```bash
lake build
lake test
lake lint
lake env lean /tmp/gw_wdvv_axioms_20261002.lean
/opt/homebrew/Caskroom/miniforge/base/envs/axiomatic-gw-sage/bin/python scripts/explore_wdvv_base_cases.py --output environments/surface-wdvv-base-cases.json
python3 scripts/explore_wdvv_pivots.py --energy-bound 12 --output environments/surface-wdvv-pivot-exploration.json
python3 scripts/test_surface_equations.py
git diff --check
```

The full build passed 2,691 jobs, tests passed 2,723 jobs, and lint passed. Eight new Lean regression examples check marking incidence/multiplicity, original-certificate consumption, changed-marking rejection, repeated-variable preservation, and numerical consumers with the unchanged seeds. All fourteen Python regressions passed. The 22 audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`. The only warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.

Initial local proof attempts exposed a natural-cast simplification, the orientation of natural-number zero-sum lemmas, explicit surface constructor qualification, and a nested label-lambda syntax error. These were repaired before the successful builds. A new line-length warning was also fixed. A multi-file documentation patch failed its context check without changing files; the final patch was reapplied against the saved baseline. Failed development attempts are not counted as validation. The [manifest](../../environments/surface-wdvv-validation.json) records exact commands, standard-axiom results, source pins and preservation checks.

### Remaining risks and next priority

The numerical conclusions remain conditional on geometric realization, primitive GW and forgetting laws, target identification, and seed validity. A uniform coefficient-isolation theorem, a well-founded reduction order, finite-seed sufficiency, arbitrary descendant comparison, genus-two reconstruction and the remaining GKM/CohFT/R-matrix gates are unproved. The finite energy-twelve probe supplies evidence for a possible genus-zero recursion only; it does not meet the numerical benchmark gate.

Next, prove the uniform genus-zero leading coefficient and strict decrease of every residual query, using these finite base cases. Then connect the resulting recursion to genus-one reduction while retaining the separate genus-two and class-level GKM obligations. The finite eliminations using higher-energy classes must be incorporated as base-case proofs rather than assumed recursive steps.

## 2026-10-02: Exceptional genus-one base cases from checked Getzler equations

**Status:** The exceptional energy-one genus-one values and two double-class values are now deduced for E on F₁ and E₁,E₂ on the two-point blowup. R1 and R3--R8 remain incomplete. The fixed applications, benchmark bounds, and required GKM compatibility are unchanged; the goal remains active. No commit or push was made.

### Scope reviewed and findings

Reviewed the full-class primary reduction and degree-zero rules, finite surface seeds, Getzler graph requests and checked term evaluator, existing numerical consumers, and the surface reconstruction route. Before editing, the baseline `lake build AxiomaticGWTest.Surfaces.LowDegree` passed (2,650 jobs), and the existing diff and hashes of 271 tracked/untracked files were saved.

- **High reconstruction gap resolved for the indexed exceptional classes:** The previous blowup equations retained the genus-one one-point values in class Eᵢ. The current finite seed list supplies N₀(Eᵢ;0)=1, but did not supply or prove those genus-one values. Three additional Getzler requests in class 2Eᵢ now determine them without extending the seed list.
- Exact Sage exploration found that 45 dimension-compatible energy-one basis multisets, including the separate class L on the two-point blowup, give zero equations directly. This finite diagnostic motivated using class 2Eᵢ; it does not prove a limitation on all relations or descendants.
- No new semantic defect was found in the scoped existing definitions or theorem statements. This work does not review the entire development or construct geometric surface theories.

### Revisions and mathematical effect

[`ExceptionalGetzler.lean`](../../AxiomaticGW/Surfaces/Fixtures/ExceptionalGetzler.lean) checks HHHH, HEᵢEᵢEᵢ and HHEᵢEᵢ in class 2Eᵢ with zero powers and no added markings. Each of the nine selected requests is compared directly to the complete 33-column Lean evaluator using `decide +kernel`. The candidate terms retain every full curve coordinate and signed metric contribution.

Writing x=N₀(Eᵢ;0)N₁(Eᵢ;1), y=N₀(2Eᵢ;1), z=N₁(2Eᵢ;2), the three checked equations are −9z=0, −3y/2=0, and 3x−y/6+3z=0. The last argument counts repeated primary point insertions. [`Exceptional.lean`](../../AxiomaticGW/Surfaces/Exceptional.lean) first proves y=z=0 and then uses the existing exceptional seed to prove N₁(Eᵢ;1)=0. The original checked Getzler presentation and the existing geometric laws and finite elliptic divisor seeds supply the equation semantics. Compatibility at zero added markings is derived from the source compatibility rather than requested again.

These are three uniform theorem statements instantiated at the three indexed exceptional divisors, giving nine conditional numerical values. No existing definition, theorem statement, normalization, or seed value changed. No new axiom, final recurrence assumption, global simp lemma, instance, or coercion was added. The index does not include L=H−E₁−E₂.

The existing Python expansion helper now accepts four validated external basis labels, preserving its old HHHH default and byte-identical old export. [`explore_exceptional_getzler.py`](../../scripts/explore_exceptional_getzler.py) uses the pinned admcycles-derived frame, exact component rules, and Sage rational matrices. The [report](../../environments/surface-exceptional-exploration.json) records 21 surviving uncollected contributions and the common rank-three coefficient matrix with determinant −81/2. These shared-source diagnostics are separate from Lean acceptance and geometric applicability.

### Validation

The following commands passed:

```bash
lake build AxiomaticGW.Surfaces.Fixtures.ExceptionalGetzler
lake build AxiomaticGW.Surfaces.Exceptional
lake build AxiomaticGWTest.Surfaces.Exceptional
lake build
lake test
lake lint
lake env lean /tmp/gw_exceptional_axioms_20261002.lean
/opt/homebrew/Caskroom/miniforge/base/envs/axiomatic-gw-sage/bin/python scripts/explore_exceptional_getzler.py --output environments/surface-exceptional-exploration.json
python3 scripts/test_surface_equations.py
git diff --check
```

The complete nine-request fixture compiled in 63 seconds; the numerical consumer in 1.1 seconds. The full build passed 2,684 jobs and tests passed 2,714 jobs. Three Lean regression examples check sign rejection, distinct equal-energy classes, and actual consumption of the original Getzler presentation with the unchanged finite seed package. All eleven Python regressions passed, including byte reproduction of the previous four-request export and new label-validation checks. The six new principal theorems use only `propext`, `Classical.choice`, and `Quot.sound`. The only warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.

An initial Sage probe could not write the user cache; the final script uses a temporary writable cache. A scratch proof initially lacked an explicit list type and was corrected. An accidentally overlapping dependent build was explicitly interrupted before running the final build sequentially. These development attempts are not recorded as successful validation. The [validation manifest](../../environments/surface-exceptional-validation.json) records commands, source pins, baseline preservation, and the remaining scope.

### Remaining risks and next priority

The conclusions remain conditional on the named geometric realization, GW laws, target identification, and finite seeds. This step does not prove geometric existence, seed validity or general sufficiency, arbitrary exceptional multiples, the L-class values, descendant comparison, a well-founded reconstruction, or any genus-two or remaining GKM completion gate. Earlier historical entries retain their then-current limitations.

Next, derive a uniform genus-zero/genus-one reduction and its well-founded order, using these proved exceptional base cases and addressing L explicitly. Any same-genus step that uses a higher-energy class must be accounted for in that order; the finite three-equation elimination here does not establish termination for arbitrary queries.

## 2026-10-02: Checked surface equations and first numerical deductions

**Status:** Four complete reduced Getzler equations now have kernel certificates bound to independently held graph requests. Two singleton equations give conditional numerical surface values. R1 and R3--R8 remain incomplete; the three fixed applications, benchmark bounds and required GKM compatibility remain part of the active goal. No commit or push was made.

### Scope reviewed and findings

Reviewed the executable surface gluing evaluator, both primary-reduction stages, query and residual-variable equality, exact polynomial interpretation, fixed Getzler requests, exporter and numerical consumers. The baseline `lake build AxiomaticGWTest.Surfaces.DegreeZero` passed (2,645 jobs); the pre-existing diff and hashes of 261 tracked/untracked files were saved before editing.

- **High integration gap resolved:** Earlier finite component and collection checks did not bind the final candidate equations to the complete Lean graph evaluator. The new sound term expansion and exact column certificates supply that connection for all four fixed requests.
- **Medium computational defect fixed:** Derived query equality and generic sum-tag equality transported decisions through extensional equality of curve functions. Native evaluation succeeded while kernel reduction became stuck. Fieldwise decisions now avoid that transport, including for actual splitting-generated classes. Query data, mathematical equality and the existing public instance name are preserved.
- **Medium replay cost addressed:** Direct whole-equation comparison and an initial whole-multiset witness caused repeated reduction of long expansions. Those two owned runs were explicitly interrupted to change the checker. The final proof checks each of the 33 original columns separately, then uses finite-sum congruence and exact coefficient comparison. The certificate module compiles in about two minutes with dependencies cached. This does not establish research-scale performance for arbitrary markings or energy bounds.
- No additional semantic defect was found in the scoped existing mathematical APIs. This is not a comprehensive review or construction of geometric GW theories or GKM CohFT inputs.

### Revisions and mathematical effect

`Coefficients/RationalTerms.lean` represents executable coefficient/monomial multisets and interprets them in the existing `MvPolynomial` ring. Repeated variables, repeated contributions, cancellation and both sides of the monomial support are retained. `eval_eq_of_equivalent` proves the finite check sound for every valuation in every commutative rational algebra.

`Surfaces/TermExpansion.lean` follows the existing graph evaluator, with all ordered full-class splits and signed inverse-metric states. It executes the established dimension and primary reductions at terminal components. `polynomial_primaryTerms` proves equality with the previous reduced polynomial; `exchange_checkedPrimaryTerms_eq_zero` combines the exact term certificate with the original incoming Getzler presentation and its existing geometric hypotheses.

The held requests in `Surfaces/Fixtures/GetzlerFrames.lean` specify the target, full curve class, marking count, states and powers independently of candidate coefficients. The exporter combines the pinned Sage result with proposed uncollected contributions. `GetzlerReplay.lean` checks all **132 original-column expansions** and **four complete coefficient comparisons** in the kernel. Their 16/34/72/3 uncollected contributions yield 1/4/8/1 terms. The independently archived unreduced sparse polynomials remain exploratory: these certificates prove the complete reduced equations directly.

`Surfaces/LowDegree.lean` uses the two singleton equations, each with coefficient −9, to prove:

| Target and full class | Genus and primary insertions | Deduced value |
| --- | --- | --- |
| $\mathbb P^2$, $H$ | Genus one, three points | $0$ |
| $\mathrm{Bl}_{p,q}\mathbb P^2$, $E_1+E_2$ | Genus one, two points | $0$ |

These are deductions from the existing geometric laws and finite elliptic divisor seeds. No final recurrence, additional seed, numerical oracle, substitute axiom or geometric existence assumption was disguised as a proved result. Existing theorem statements and normalizations are unchanged. The new canonical coefficient-check decision and specialized residual-tag equality are tested alongside the repaired query equality. No global simp lemma or coercion was added. Two root imports expose the new API, and the mathematical map, input ledger, plan and research workflow describe its scope.

### Validation

The following commands passed:

```bash
lake build AxiomaticGW.Surfaces.LowDegree
lake build
lake test
lake lint
lake build AxiomaticGWTest.Surfaces.TermExpansion AxiomaticGWTest.Surfaces.LowDegree
lake env lean /tmp/gw_surface_terms_axioms_20261002.lean
lake env lean environments/surface-primary-reduction-replay.lean
lake env lean environments/surface-degree-zero-replay.lean
python3 scripts/test_surface_equations.py
git diff --check
```

The targeted/full/test builds cover 2,651/2,682/2,711 jobs. Fourteen new Lean regressions cover signs, multiplicities, cancellation, missing/extra terms, nonliteral curve representatives, equal-energy distinct classes, retained nonzero powers and both numerical consumers using the original Getzler replay and existing finite seed package. Eight Python regressions check reproducibility, full coordinates, exact rationals, rejection of altered labels/powers/tags and agreement with the Sage coefficients. The Python comparison shares the graph frame and component rules with the earlier exploration; it is arithmetic consistency evidence. All 31 audited declarations, including every accepted equation and both numerical theorems, use only `propext`, `Classical.choice` and `Quot.sound`.

Generated-line and option-scope warnings were corrected in the exporter. The sole final warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`. The [validation manifest](../../environments/surface-term-expansion-validation.json) records exact commands, outcomes, hashes, axiom query, baseline preservation and replay scope. Placeholder, whitespace and final-diff checks pass. The completed finite replay requires neither Sage nor network access.

### Remaining scope and next priority

Prove uniform genus-one coefficient isolation and a decreasing recurrence, with a justified treatment of exceptional energy-one and equal-plane-degree branches. The other two checked line equations still contain residual unknowns. Finite seed sufficiency, arbitrary descendant reduction, genus-two reconstruction and the remaining numerical suites are open. Actual GKM CohFT/reconstruction-action input, geometric and descendant--ancestor comparison, R/translation conditions when used, and ordinary specialization remain required completion gates.

## 2026-10-02: Degree-zero primary surface reduction

**Status:** Primary degree-zero components in genera zero and one now reduce uniformly in the marking multiplicities, and the resulting substitution preserves the checked Getzler equation. R1 and R3--R8 remain incomplete. All three fixed targets, benchmark bounds, and mandatory GKM compatibility are unchanged. The goal remains active; no commit or push was made.

### Scope reviewed and findings

Reviewed the existing primary multiset evaluator, signed dimension vanishing, full string/divisor laws and their exceptional corrections, surface grading/product/metric, finite elliptic divisor seeds, and the polynomial/Getzler consumer. The baseline `lake build AxiomaticGWTest.Surfaces.PolynomialReduction` passed (2,643 jobs). The pre-existing diff and hashes of 254 tracked/untracked files were saved before editing.

- **Medium integration gap resolved:** Degree-zero primary components remained unevaluated after positive-class reduction. The new theorems cover arbitrary multiplicities, including the existing auxiliary unstable zeros.
- **Low input-ledger overstatement corrected:** A separate classical cubic normalization is unnecessary for these surface basis queries. String, grading, and the identified metric already imply it. The geometric laws and identifications themselves remain inputs.
- No semantic defect was found in the scoped existing APIs. No existing definition, theorem statement, or normalization was changed. This is not a comprehensive review of the geometric theories or GKM CohFT inputs.

### Revisions and mathematical effect

`Surfaces/DegreeZero.lean` proves `SurfacePrimary.eval_genus_zero_zero` and `eval_genus_one_zero`. At genus zero, a unit gives the three-point metric correction and a unit-free multiset vanishes by dimension. At genus one, string/divisor/dimension reduction leaves only the existing hyperplane and exceptional single-divisor seeds. No new seed or cubic assumption is introduced.

`Surfaces/DegreeZeroPolynomial.lean` supplies an executable constant lookup and the sound simultaneous substitution theorem `aeval_reduceDegreeZero_reduce`. `exchange_primarySurfacePolynomial_eq_zero` consumes the unchanged incoming Getzler presentation. The lookup distinguishes a known zero from an inapplicable rule; nonzero powers, higher genera, and numerical query variables retain their semantics. Two root imports expose the API. No global simp lemma, instance, placeholder, or substitute axiom was added.

### Validation

All final commands passed:

```bash
lake build AxiomaticGWTest.Surfaces.DegreeZero
lake build
lake test
lake lint
lake env lean environments/surface-degree-zero-replay.lean
lake env lean /tmp/gw_degree_zero_axioms_20261002.lean
git diff --check
```

The targeted/full/test builds completed 2,645/2,677/2,704 jobs. Twelve focused regressions cover classical and exceptional signs, elliptic seeds, repeated markings, rule boundaries, arbitrary multiplicities, and the original checked Getzler consumer using the existing finite seed package. All 22 audited public declarations use only `propext`, `Classical.choice`, and `Quot.sound`. The only final warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`. Draft elaboration errors were repaired before release.

The pinned Sage 10.9/admcycles 1.4 command passed:

```bash
/opt/homebrew/Caskroom/miniforge/base/envs/axiomatic-gw-sage/bin/python scripts/explore_surface_degree_zero.py \
  --output environments/surface-degree-zero-exploration.json \
  --lean-replay environments/surface-degree-zero-replay.lean
```

The [complete report](../../environments/surface-degree-zero-exploration.json) reduces the three line cases from 13/23/40 to 1/4/8 terms, and E₁+E₂ from two to one, retaining leading elliptic coefficient −9 in every case. The [offline replay](../../environments/surface-degree-zero-replay.lean) checks all 66 distinct component rules with `decide +kernel` and all four complete rational collection identities by `ring`, for arbitrary residual-variable values. An independent `fractions.Fraction` calculation multiplies actual scalar/divisor/point coordinates to verify the constants and all 14 collected monomials, full total-class conservation, and residual point-query dimensions.

These checks certify this substitution and collection stage. They do not certify the earlier independent raw sparse graph expansion or establish numerical GW values. The [validation manifest](../../environments/surface-degree-zero-validation.json) records exact source/replay/log hashes, commands, axiom output, independent arithmetic, and remaining gates. Placeholder and final-diff scans pass; pre-existing work is preserved.

### Remaining scope and next priority

Certify the sparse graph expansion and isolate the genus-one coefficient uniformly, proving that every residual term decreases in the chosen order, including exceptional and equal-plane-degree branches. Four observed nonzero coefficients do not prove a general recurrence. Finite-seed sufficiency, numerical benchmarks, higher-power descendant comparison, genus-two reconstruction, actual GKM CohFT/reconstruction-action import, and ordinary specialization remain required.

## 2026-10-02: Primary surface reduction and polynomial substitution

**Status:** Dimension vanishing and positive-class primary string/divisor reduction now preserve the checked Getzler polynomial equation. R1 and R3--R8 remain incomplete; the fixed three targets, benchmark bounds, and mandatory GKM compatibility are unchanged. The full goal remains active, with no commit or push.

### Scope reviewed and findings

Reviewed the full numerical string/divisor laws and their degree-zero corrections, primary ancestor/descendant identification, signed dimension laws, surface intersection conventions, multiset occurrence semantics, and the existing Getzler polynomial consumer. The baseline `lake build AxiomaticGWTest.Surfaces.AncestorPolynomial` passed (2,640 jobs). The full pre-existing diff and hashes of 247 tracked/untracked files were saved before editing.

- **Medium integration gap resolved:** The collected equation had no proved substitution reducing primary surface components to their point invariants. The new reduction is derived from the existing laws for arbitrary multiplicities and arities, including positive-degree unstable residuals.
- **Geometric input made explicit:** `SurfaceTheoryIdentification` intentionally did not identify the divisor law's coefficients. `DivisorPairingCompatible` now names exactly that previously documented intersection comparison. It contains no GW recurrence. All cotangent powers are zero in this reduction, so no divisor-action identification is needed.
- **No semantic defect found in the scoped existing APIs.** The foundational change adds a signed ancestor vanishing theorem; no existing definition, theorem signature, normalization, or hypothesis was altered. The geometric surface theories and GKM CohFT data were not comprehensively reviewed or constructed.

### Revisions and mathematical effect

`Surfaces/PrimaryReduction.lean` proves `SurfacePrimary.eval_reduced`: at nonzero full curve class, a primary multiset equals the product of its signed divisor intersections times the point invariant with the original point multiplicity; a unit contributes zero. Its proof removes non-point occurrences by multiset induction and uses the existing full numerical invariant. It retains exceptional minus signs and the zero-, one-, and two-marking positive-degree sectors.

`GromovWittenTheory.ancestorInvariant_eq_zero_of_virtual_dimension_ne` includes negative expected output degrees. `Surfaces/PolynomialReduction.lean` uses it in executable dimension and primary checks. `reduceVariable` returns either zero or an exact coefficient and residual variable. `aeval_reduce` proves simultaneous substitution for any ancestor polynomial; `exchange_reducedSurfacePolynomial_eq_zero` consumes the original incoming Getzler certificate. Residual ancestors and numerical point queries have distinct tags. Degree-zero ancestors and nonzero powers remain explicit. No seed, substitute axiom, assumed final recurrence, or global simp lemma was added. Two canonical decidability instances serve the new finite checks. The polynomial carrier remains mathlib's noncomputable `MvPolynomial`; the individual reduction data are executable.

### Validation

All final commands passed:

```bash
lake build AxiomaticGWTest.Surfaces.PolynomialReduction
lake build
lake test
lake lint
lake env lean environments/surface-primary-reduction-replay.lean
lake env lean /tmp/gw_surface_reduction_axioms_20261002.lean
git diff --check
```

The targeted/full/test builds completed 2,643/2,675/2,701 jobs. Thirteen focused regression examples cover repeated insertions, signed exceptional products, equal-energy distinct classes, zero divisor intersections, unit vanishing, negative output degree, retained degree-zero and nonzero-power ancestors, unstable point queries, and the genuine arbitrary-marking Getzler replay consumer. All 34 audited public declarations and instances use only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`, or none). The only final warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`. Draft proof/export elaboration errors were corrected; the final replay log is empty and exits zero.

The pinned Sage command passed:

```bash
/opt/homebrew/Caskroom/miniforge/base/envs/axiomatic-gw-sage/bin/python scripts/explore_surface_reduction.py \
  --output /tmp/surface-primary-reduction-exploration.json \
  --lean-replay /tmp/surface-primary-reduction-replay.lean
```

It checks the archived polynomial hashes and reduces the P²/F₁/Bl₂P² line cases from 251/1,388/6,550 to 13/23/40 monomials. E₁+E₂ reduces from 853 to two. The [complete report](../../environments/surface-primary-reduction-exploration.json) retains all 78 residual monomials and their exact coefficients. All 1,570 distinct component substitutions are archived as [kernel replay](../../environments/surface-primary-reduction-replay.lean) and compile without Sage or network access. An independent `fractions.Fraction` computation using signed lattice coordinates agrees with every reduced polynomial and checks preservation of the full total class. These finite checks certify agreement of component reduction rules; they do not certify the independent raw graph expansion or turn the reduced equations into numerical GW answers.

The [validation manifest](../../environments/surface-primary-reduction-validation.json) records source/log hashes, commands, the axiom query, exact replay pin, independent arithmetic check, and remaining gates. Placeholder and final-diff scans pass. Pre-existing work is preserved.

### Remaining scope and next priority

Reduce degree-zero primary components symbolically to the justified classical cubic and elliptic seed data, then isolate the genus-one pivot and prove that every remaining term decreases in the chosen order, including exceptional and equal-plane-degree branches. No numerical benchmark, finite-seed sufficiency theorem, or complete recursion is proved here. Descendant comparison, efficient symmetric enumeration, genus-two reconstruction, actual GKM CohFT/reconstruction-action import and ordinary specialization remain required.

## 2026-10-02: Surface Getzler polynomials and symmetric component variables

**Status:** The Getzler equation now has an explicit finite surface evaluator and a polynomial interpretation in actual component ancestors. Full curve classes and insertion multiplicities are retained. R1 and R3--R8 remain incomplete; all three fixed applications, numerical benchmarks, and mandatory GKM completion gates are unchanged. No commit or push was made.

### Scope reviewed and findings

Reviewed the arbitrary-marking Getzler consumer, recursive gluing/ancestor contractions, canonical copairing, surface Frobenius algebra, finite class-splitting algorithm, and state/descendant query data. The unchanged baseline `lake build AxiomaticGWTest.Tautological.GetzlerForgetful` passed (1,823 jobs). The full existing diff and hashes of all 236 tracked/untracked files were saved before editing. [Wennink, Section 8.2](https://arxiv.org/pdf/2210.04038) was checked for the genus-one leading-term strategy; its approximate relations are not introduced as recurrence assumptions.

- **High integration gap resolved:** The surface equation still used an abstract copairing and uncollected component expressions. The new evaluator derives explicit signed basis sums, and the polynomial variables canonically collect equal insertion multisets with a proof of their GW interpretation.
- **Medium performance limitation isolated:** Raw full-equation kernel reduction for all three one-marking line probes ran for over ten minutes and was explicitly interrupted (tool exit 130). Those cases remain Sage/native execution evidence, not claimed kernel numeral proofs. The smaller coefficient probe and the general interpretation theorem are kernel-checked. No claim of efficient direct symmetric enumeration is made.
- **No semantic defect found in the scoped existing interfaces.** Existing public definitions and theorem statements are unchanged. This was not a comprehensive review of the geometric GW inputs or of the producer's CohFT classes.

### Revisions and mathematical effect

- `Surfaces/Contraction.lean` proves the actual copairing is `1 ⊗ pt + pt ⊗ 1 + H ⊗ H - ∑ Eᵢ ⊗ Eᵢ`, then derives explicit separating and nonseparating contraction formulas. Query labels retain ordered dual partners and negative exceptional inverse weights.
- `Surfaces/GluingEvaluation.lean` defines `GluingExpression.surfaceEval` with terminal component values, exact signed node sums, and all ordered full-class splittings. `surfaceEval_eq_gwAncestorContraction` proves equality to the existing contraction when the terminals are the supplied theory's actual ancestors. Only its metric identification with the surface algebra is needed. Algebra homomorphisms commute with this evaluator, and the existing incoming Getzler replay implies its explicit equation.
- `Surfaces/AncestorPolynomial.lean` introduces stable component keys containing genus, full class, and a multiset of paired basis labels/powers. The multiset occurrence type keeps repeated markings separate; `eval_ofLabels` proves interpretation by the existing simultaneous relabelling law. The standard `MvPolynomial` collects component monomials; `exchange_surfacePolynomial_eq_zero` transfers the unchanged checked presentation under the existing geometric inputs.

Three public imports expose the modules. One canonical `DecidableEq` instance for the new component keys compares data without dependent proof transports; a regression tests a nontrivial multiset permutation. No global simp lemma, geometric law, seed, substitute axiom, or final recurrence was added. The rational callback evaluator is executable. The mathlib polynomial carrier and the choice of occurrence bijection used in its semantic proof are noncomputable; an optimized executable sparse-polynomial exchange remains future work.

### Validation

All final commands passed:

```bash
lake build AxiomaticGWTest.Surfaces.AncestorPolynomial
lake build
lake test
lake lint
lake env lean /tmp/gw_surface_polynomial_axioms_20261002.lean
git diff --check
```

The targeted build completed 2,640 jobs, the full build 2,673 jobs, and tests 2,698 jobs. All 36 audited definitions, structures, instances, and theorems use only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`, or none). Eight regression examples check the three surface loop contractions, all nine E₁+E₂ component assignments, simultaneous state/power permutation, rejection of mismatched powers and equal-energy/different full classes, repeated insertion multiplicity, the -9 elliptic coefficient probe, and the actual frozen Getzler replay for arbitrary marking counts and powers. Concrete numeral checks use `decide +kernel`, not native proof reduction. The only final warning remains the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`. Initial draft errors and the three missing field docstrings reported by lint were corrected before the final checks.

The independent Sage command passed in the pinned environment:

```bash
/opt/homebrew/Caskroom/miniforge/base/envs/axiomatic-gw-sage/bin/python scripts/explore_surface_getzler.py \
  --polynomials-dir environments/surface-getzler-polynomials
```

It expands the frozen admcycles frame by actual vertex incidence, all curve assignments, and the surface inverse metric. For the P²/F₁/Bl₂P² line cases it collects 2,313/11,824/53,825 raw terms into 251/1,388/6,550 component monomials. The formal classical-tail substitution gives `-9 * elliptic` in all three cases and in E₁+E₂. Native execution via `lake env lean --run /tmp/gw_surface_native_probes_20261002.lean` independently returns -9 for each line case. These computations are formal probes, not numerical GW values. The native source and output are archived in the validation manifest; its millisecond prints are not a timing benchmark. Sage initially attempted a read-only home cache; the script was corrected to use temporary caches and the final run succeeded without escalation.

The [exploration report](../../environments/surface-getzler-exploration.json) pins its input and script and links the complete compressed sparse polynomials, with hashes of both compressed and uncompressed content. The [validation manifest](../../environments/surface-polynomial-validation.json) records source/log hashes, native source, command outcomes, the axiom audit, and remaining gates. Final scans found no placeholders or unintended long lines in the four new Lean files. The final diff was reviewed against the saved baseline, preserving all pre-existing work.

### Remaining scope and next priority

The general nonzero solved coefficient has not yet been isolated, the remaining terms are not yet proved lower in a well-founded order, and no numerical invariant or benchmark has been solved by this step. Classify and reduce the collected polynomial using the proved dimension rules and justified classical/divisor identities, then prove the genus-one pivot and decrease uniformly, including equal-plane-degree and exceptional branches. Direct symmetric generation must replace raw exponential marking enumeration before large benchmarks. Finite seed sufficiency, descendant comparison, genus-two relations/reconstruction, actual GKM CohFT and reconstruction-action import, ordinary specialization, and the fixed release suites remain required. The full goal stays active.

## 2026-10-02: Getzler pullback for arbitrary markings

**Status:** The checked Getzler ancestor equation now supports every finite number of additional markings. Its graph expansion, multiplicities, and cohomological realization are derived from primitive universal-curve/gluing base change. R1 and R3--R8 remain incomplete; the three fixed surfaces, full benchmark suites, and mandatory GKM compatibility are unchanged. The work remains uncommitted.

### Scope reviewed and findings

Reviewed the gluing-expression and ancestor evaluation APIs, existing forgetful/relabel/gluing pullbacks, raw separating and nonseparating Gysin laws, the marked Getzler replay, and the prior pinned Sage exploration. The baseline `lake build AxiomaticGWTest.Tautological.GetzlerAncestors` passed (1,819 jobs). The tracked diff and hashes of all 230 existing tracked/untracked files were saved before editing.

- **High integration gap resolved:** The four-marking equation had no proved graph expansion after forgetting extra markings. The new construction and induction now cover arbitrary finite additions, preserving the original certificate and full curve classes.
- **Necessary geometric input isolated:** The existing commuting pullback laws do not state how forgetful pullback interacts with a gluing pushforward. `GluingForgetfulCompatibility` names exactly the two elementary base-change laws used here, independently of any GW family or relation. The source is [Bae--Schmitt, Proposition 3.8 and Corollary 3.9](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/chow-rings-of-stacks-of-prestable-curves-i/196BE8335EA2020E7F0A75CE198B2CCE). Their geometric validity remains an explicit obligation.
- **No semantic defect found in the scoped existing interfaces.** Existing definitions and theorem signatures are preserved. The only addition to an existing foundational module is `optionSumEquivRight`, constructed from the existing left-label transport and sum swaps. No moduli-space or surface model was constructed or reviewed comprehensively.

### Revisions and mathematical effect

- `Tautological/GluingMarking.lean` adds one marking at each component through the existing gluing syntax, with explicit transports keeping old node flags distinct from the new external label. Lists retain repeated graph classes. Iteration supports `ExtraMarkings n S` for arbitrary `n`; `ExtraMarkings.finEquiv` numbers old markings first and appends new markings in their order of addition.
- The construction preserves vertex count, edge count, and stratum codimension. `length_addMarkings` proves the exact term count `vertexCount ^ n`. Genus and stability are enforced by the existing expression indices and the derived stability theorem.
- `CohFT/GluingForgetful.lean` records primitive base change for separating and nonseparating raw pushforwards. The separating law adds both component contributions, including coincident outputs; the nonseparating law uses the inverse of the existing three-label permutation. No graph relation, GW class family, or final recurrence is a field.
- `Tautological/GluingForgetful.lean` evaluates an expression as a cohomology class and identifies it with the existing realization under `Compatible`. `sum_classValue_addMarking`, its iteration, and `sum_map_stratum_addMarkings` derive the actual forgetful graph formula. Only source and finite output-expression realization compatibility is required. Integration against an arbitrary class upstairs is a further linear consequence.
- `Tautological/GetzlerForgetful.lean` proves `exchange_ancestor_with_markings_eq_zero` from the unchanged decoded certificate, named Getzler relation, primitive geometry, and supplied GW theory. Arbitrary ancestor monomials are inserted after the undecorated pullback; the theorem does not assume a decorated pullback shortcut. Zero additional markings recover the existing channel. `sum_length_addMarkings` proves the general count `25 * 3^n + 8 * 2^n`.

Four public imports expose the new modules. One canonical `Fintype` instance for iterated optional labels was added and tested for variable arity and empty/finite label types. No global simp lemma, placeholder, substitute axiom, or artificial GW hypothesis was introduced. Existing mathematical statements and assumptions were not changed; the new extended theorem explicitly requires the independently justified base-change input.

### Validation

All final commands passed:

```bash
lake build AxiomaticGWTest.Tautological.GetzlerForgetful
lake build
lake test
lake lint
lake env lean /tmp/gw_getzler_forgetful_axioms_20261002.lean
git diff --check
```

The targeted build completed 1,823 jobs, the full build 2,670 jobs, and tests 2,694 jobs. All 34 audited public definitions, properties/projections, and theorems use only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`, or none). The five new Lean files pass placeholder/substitute-axiom and 100-character line scans. The only test warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.

Eleven regressions cover the 91- and 257-term counts, all vertex assignments of one and two added markings in every original column, all retained genera/node incidences/external labels, coefficient two for coincident placements on a symmetric genus-two graph, rejection of the wrong node permutation, canonical finite-label inference and exchange numbering, and consumption of the actual frozen Sage replay for arbitrary `n`, powers, and the full class E₁+E₂. The two full-incidence checks use a local two-million-heartbeat limit to reduce the 91 and 257 graphs in the kernel; no native proof bypass is used.

The earlier Sage report was rechecked against its unchanged input and script pins; Sage was not rerun in this implementation step. Its raw counts and symmetry example agree with the new Lean regressions, while the earlier decorated psi countercheck still bounds the scope of the construction. The [validation manifest](../../environments/getzler-forgetful-validation.json) records command logs, source pins, axiom evidence, and remaining inputs. The final diff and new files were reviewed, and unrelated pre-existing work was preserved.

### Remaining scope and next priority

This supplies conditional ancestor equations, not a solved or numerical GW reconstruction. General decorated forgetting and common-refinement products, genus-two relation provenance, finite seed sufficiency, stable-map descendant comparison, actual GKM CohFT/reconstruction input, ordinary specialization, and every fixed numerical benchmark remain open. Geometric applicability of the named Getzler and Gysin/base-change laws is not inferred from the formal graph computation.

The raw placement list grows exponentially; concrete graph regressions cover one and two added markings, not benchmark-scale evaluation. Next, collect symmetric marking contributions and derive the genus-one reduction from the expanded equation, proving the solved coefficient and decrease of every recursive call and connecting the recursion to the finite audited seeds. This is the next R6 gate, rather than assuming a numerical recurrence as input.

## 2026-10-02: Getzler ancestor contractions and forgetful exploration

**Status:** The checked Getzler equation now evaluates all 33 marked columns as full-class component ancestor contractions, with arbitrary powers at the four external markings. The primary theorem is recovered at zero powers. R1 and R3--R8 remain incomplete; the fixed surfaces, all benchmarks, and mandatory GKM compatibility are unchanged. No commit or push was made.

### Scope reviewed and findings

Reviewed the existing `PsiClasses` pullback laws, primary gluing-expression evaluation, Getzler certificate consumers, and their regression uses. The baseline `lake build AxiomaticGWTest.Tautological.GetzlerGW` passed (1,816 jobs). The pre-existing working-tree diff was saved before editing and unrelated changes were preserved.

- **High integration gap resolved:** Arbitrary external ancestor insertions were already available in Getzler graph integrals, but their component contractions were not derived. The new proof transports powers with the actual marking bijections and restricts them to the correct component, with zero powers at newly glued nodes.
- **No semantic defect found in the scoped existing interfaces.** No existing theorem was weakened, no geometric hypothesis was strengthened, and no public API was replaced. This was not a comprehensive review of the foundations or surface models.
- The next forgetful construction must retain vertex multiplicities and distinguish undecorated graphs from decorated pullbacks. The Sage checks below verify both requirements, including cases that would reject an overly broad vertex-only rule.

### Revisions and mathematical effect

- `CohFT/PsiGluing.lean` derives separating and nonseparating monomial pullbacks and marking transport from the existing individual psi laws. The component exponent functions explicitly assign zero at node flags.
- `Tautological/GluingAncestors.lean` defines the actual ancestor graph integral and its recursive component contraction. `gwAncestorIntegral_eq_contraction` proves equality by structural induction, using the unchanged `Compatible` predicate, primitive projection/integration laws, GW gluing, and the derived monomial formulas. Every ordered effective splitting of the full class is retained. The two zero-power theorems recover the existing primary API.
- `Tautological/GetzlerAncestors.lean` derives `integrate_column_ancestor`, `certificate_ancestor_eq_zero`, and `exchange_ancestor_eq_zero`. They use the unchanged 33 columns, original row, held request, decoded certificate, named geometric Getzler input, and normalized-cycle identification.
- The public root imports and the mathematics map, plan, roadmap, input ledger, and environment guide now describe this exact scope. No global simp lemma or instance was added.

These are stable-curve ancestor equations, conditional on the existing geometric inputs. They neither construct geometric surface GW theories nor supply numerical seed values or stable-map descendant comparison.

### Validation

All commands passed:

```bash
lake build AxiomaticGWTest.Tautological.GetzlerAncestors
lake build
lake test
lake lint
lake env lean /tmp/gw_getzler_ancestors_axioms_20261002.lean
/opt/homebrew/Caskroom/miniforge/base/envs/axiomatic-gw-sage/bin/python scripts/explore_getzler_forgetful.py
git diff --check
```

The targeted build completed 1,819 jobs, the full build 2,666 jobs, and tests 2,689 jobs. All 20 audited new declarations use only `propext`, `Classical.choice`, `Quot.sound`, or no axioms. The four new Lean files pass placeholder/substitute-axiom and 100-character line scans. The only Lean test warning remains the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`; Sage emits its upstream category deprecation warning.

Eight regressions check asymmetric left/right powers, both zero self-gluing powers, covariant versus inverse marking transport, transport in an actual recursive expression, agreement with all primary channels at zero powers, and consumption of the frozen Sage replay in the full class E₁+E₂ with arbitrary powers. These test semantics and theorem integration, not numerical GW values. The [ancestor validation manifest](../../environments/getzler-ancestors-validation.json) records commands, source pins, the axiom audit, and remaining hypotheses. The final tracked diff was compared with the saved pre-edit diff, and the new files were reviewed directly.

### Exploration of additional markings

The new `scripts/explore_getzler_forgetful.py` rebuilds graph incidence independently from the held Getzler candidate. In Sage 10.9/admcycles 1.4, placing each new marking at every vertex agrees exactly with `forgetful_pullback` in raw degree-two coordinates, before passing to a tautological quotient. One additional marking gives **91** distinct terms; two give **257**. The original row coefficients, held request, and witness `-1/4` are preserved. Both expanded vectors remain nonzero in the free strata space. Online lookup is disabled and caches are temporary.

A symmetric genus-two graph with two elliptic vertices gives one raw output graph with coefficient **two**, showing why coincident vertex placements must not be deduplicated. A psi-class countercheck gives the negative rational-tail correction, showing why the undecorated rule does not directly handle decorated pullbacks. The [exploration report](../../environments/getzler-forgetful-exploration.json) pins the script, input, and producer sources. It is computational exploration evidence, not a Lean certificate or proof of relation vanishing.

The geometric source reviewed for the next step is [Bae--Schmitt, Proposition 3.8 and Corollary 3.9](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/chow-rings-of-stacks-of-prestable-curves-i/196BE8335EA2020E7F0A75CE198B2CCE). The pullback formula sums over vertices with component pullbacks; it uses raw gluing pushforwards. The installed admcycles implementation was also inspected, including its separate psi/kappa correction terms.

### Remaining scope and next priority

Additional markings are not yet implemented in Lean. General decorated forgetting/products, genus-two relation provenance, actual GKM CohFT/reconstruction input, ordinary specialization, stable-map descendant comparison, finite seed sufficiency, and terminating/unique reconstruction for every fixed benchmark remain open.

Next, construct the undecorated additional-marking operation in the existing gluing-expression/graph representation, preserving repeated vertex placements and external labels. Prove its realization from primitive forgetful/gluing base-change laws, then lift the checked Getzler equation and use it in the genus-one reduction argument. External ancestor monomials can be inserted after this pullback; pulling back a decorated relation itself requires the separate correction formulas.

## 2026-10-02: Getzler graph constructions and primary GW contractions

**Status:** All 33 marked Getzler columns now have explicit elementary gluing constructions and a proved primary graph-to-GW contraction chain. The accepted Sage presentation yields the corresponding conditional full-class GW equation. R1 and R3--R8 remain incomplete; the three fixed targets, all benchmarks, and mandatory GKM compatibility are unchanged. No commit or push was made.

### Scope reviewed and findings

Reviewed the existing marked Getzler frame and integral consumer, raw separating/nonseparating and relabelling operations, their realization compatibility laws, and the full-class GW boundary contraction theorems. The unchanged Getzler baseline passed `lake build AxiomaticGW.Tautological.GetzlerRealization AxiomaticGWTest.Tautological.GetzlerReplay` (1,799 jobs).

- **High integration gap resolved:** The earlier Getzler consumer concluded with 33 graph integrals. It supplied no theorem identifying those integrals with iterated component contractions. The correction adds explicit constructions and proves that identification from the existing primitive laws; it does not assume the final GW equation.
- **No semantic defect found in the scoped existing interfaces.** Their raw-pushforward normalization and complete curve-class splitting are preserved. This was not a comprehensive review of the cohomology/GW foundations or geometric surface models.
- The unfinished validation manifest from the preceding Getzler work was completed by checking its recorded logs, 36-case report, 97-declaration axiom audit, and byte-reproduction hashes. Those historical search/regression jobs were not rerun in this follow-up.

### Revisions and mathematical effect

- `GluingExpression.lean` records finite compositions of stable fundamental components, actual marking bijections, separating gluing, and self-gluing. It constructs the existing finite graph and quotient stratum and proves the genus index correct. No new graph quotient or competing geometric definition is introduced.
- `GluingEvaluation.lean` defines the exact recursive contraction expression. Every separating step sums over `D.splittings beta`; every self-gluing retains `beta`. `Compatible` contains fundamental normalization and the existing raw graph-map laws only along the supplied expression, independently of any GW theory. `gwIntegral_eq_contraction` proves soundness by structural induction using the existing Gysin/integration and GW gluing theorems.
- `GetzlerGluing.lean` constructs all seven representative graphs and 33 explicit marking bijections. Kernel isomorphism proofs identify every expression with its held column. Loops and parallel edges use different source-node incidences, and no additional automorphism or orbit factor is inserted.
- `GetzlerGW.lean` proves `GetzlerGraphs.integrate_column_gw`, `certificate_gw_eq_zero`, and `exchange_gw_eq_zero`. These retain the exact original request and its normalization, the named geometric Getzler input, and normalized-cycle identification. The actual decoded Sage presentation is used in the test consumer.

Four public imports expose the new modules. No existing mathematical statement or assumption was changed, and no global simp lemma or instance was added. The contraction is an exact expression in supplied component invariants; it is not yet a numerical reconstruction algorithm or a source of surface seed values.

### Validation

All final commands passed:

```bash
lake build AxiomaticGWTest.Tautological.GetzlerGW
lake build
lake test
lake lint
lake env lean /tmp/gw_getzler_gw_axioms_20261002.lean
git diff --check
```

The targeted test build completed 1,816 jobs, the full build 2,663 jobs, and the test build 2,685 jobs. All 32 audited new declarations use only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`, or none). The five new Lean files pass placeholder/substitute-axiom and 100-character line scans. The only test warning remains the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`.

Six regressions check a valid but wrong loop-and-tail construction, its rejection in the parallel-edge slot, a wrong external marking, all nine three-component assignments of E₁+E₂ including zero factors, their equality with the actual effective-class sums, and consumption of the frozen Sage replay in that full class. They test graph incidence and theorem integration, not numerical surface GW values. The [validation manifest](../../environments/getzler-gw-validation.json) records commands, source hashes, the axiom audit, and the precise remaining hypotheses. The final diff was reviewed against the saved pre-edit working-tree diff; unrelated changes were preserved.

### Remaining scope and next priority

The primary equation has four external markings. External ancestor powers, arbitrary additional markings, stable-map descendant comparison, geometric applicability, finite seed sufficiency, and the terminating/unique reconstruction remain open. General products/forgetting and genus-two relation provenance, actual GKM CohFT or semisimple reconstruction input, ordinary specialization, and the complete fixed benchmark release are still required. The existing constant targets are not promoted to geometric Gysin models.

Next, extend the proved Getzler evaluation to the extra markings and ancestor decorations required by the reconstruction plan, retaining exact node/marking multiplicities. Use that equation to derive the genus-one reduction and prove the complexity decrease, rather than assuming a numerical recurrence.

## 2026-10-02: Explicit Getzler replay and acceptance of R2 computation

**Status:** The seven normalized Getzler cycles, marked claim-bound replay, and conditional integral consumer are implemented and verified. R2's finite-computation gate is accepted after the coherent 68-case native run and its completion audit. R1 and R3--R8 remain incomplete; the fixed applications, benchmark bounds, and mandatory GKM compatibility are unchanged. The work remains uncommitted.

### Scope reviewed and findings

Reviewed `Getzler.lean`, the new `GetzlerGraphs.lean` and `GetzlerRealization.lean`, the exact exporter and generated replay, finite graph/curve computation, the native corpus runner, and R2--R5 acceptance requirements. The normalization review used [Getzler, Section 1, Proposition 1.6 and Theorem 1.8](https://arxiv.org/pdf/alg-geom/9612004) and the pinned admcycles constructors and raw-coordinate APIs.

- **High integration gap resolved:** `GetzlerStrataEncoding` previously required all seven cycles as supplied data. `GetzlerGraphs.encoding` constructs them from 33 distinct marked raw graphs, with checked genus, codimension, complete S4 orbits, orbit sizes, and inverse graph-automorphism factors.
- **Critical draft build failures resolved:** `graph_automorphismCount` attempted a rewrite after its conditional had already reduced. The integral consumer lacked the public integration-map import. The corrections preserve the mathematical statements and use the existing APIs; the resumed targeted build initially failed, and the final targeted/full builds pass.
- The source-stack stabilizer and graph automorphism order are different quantities. Tree terms have raw factor one; loop and parallel-edge terms have factor one-half. No new semantic defect was found in the scoped existing graph or weighted-curve definitions.
- The native corpus process returned terminal success. Its earlier “running” record was updated from observed tool completion and verified artifacts, without merging output from different executable/source versions.

### Revisions and mathematical effect

`GetzlerGraphs.lean` proves that the expanded raw row equals the pre-existing seven-cycle relation. The independently held consequence isolates delta23; Sage finds the exact row witness `-1/4`. The original row and held consequence are both nonzero in the free strata module. No existing public definition, theorem statement, or geometric assumption was changed; no new global simp lemma or instance was added.

The exporter emits actual incoming graphs and proves their equality to the fixed marked columns. It checks named-cycle slots, orbifold/raw factors, the original relation, held request, and exact witness. `GetzlerRealization.lean` derives integrated identities from the named `GetzlerRelationGeometry` input and identification of its cycles with the explicit graph sums. Actual GW classes with arbitrary external ancestor powers are supported as insertions. This does not yet evaluate those graph integrals as iterated GW contractions.

The fresh-cache Sage search reproduces the seven-cycle published intersection matrix with rank six and the frozen candidate report byte for byte. That comparison is a normalization diagnostic, not a geometric proof in Lean. Ordinary Python regenerates the frozen Lean replay byte for byte.

### R2 acceptance evidence

| Requirement | Evidence inspected |
| --- | --- |
| Executable bounded curve sets and all full-class splittings | `WeightedCurveClass.mem_bounded`, `bounded_eq`, `mem_splittings`, `splittings_eq`; surface regressions include exceptional coordinates, all eight ordered line splittings on the two-point blowup, and counts 5/49/455 through energy twelve |
| Complete finite graph isomorphisms and automorphism multiplicities | `isoEquivCandidates`, `isomorphic?_eq_true_iff`, `automorphismCount_eq_card`, and presentation invariance; regressions include loop branch exchanges and repeated/asymmetric decorations |
| Exact bounded decorated-stratum enumeration | `TautologicalStratum.mem_boundedStrata` proves equivalence with the codimension bound for arbitrary genus and finite labels |
| Every initial runtime case | One coherent run covers exactly 68 stable triples with genus at most two, at most six markings, and bounds zero through three; child and tool exit codes are zero |
| Provenance and consistency | All eight project source hashes and the native executable match; coverage, uniqueness, monotonicity, and six existing kernel-fixture counts pass |

The largest case has 39,109 bounded formal strata. The runner recorded 8,601.484 seconds using `LEAN_STACK_SIZE_KB=2097152`. The [manifest](../../environments/graph-corpus-native-osx-arm64.json), JSON-lines output, and diagnostics are archived in `environments/`; `scripts/verify_graph_corpus.py --verify-executable` checks the accepted evidence. Native counts remain supplemental execution evidence, distinct from kernel numeral proofs and geometric cohomology dimensions. Target-to-geometry identification belongs to R1.

### Validation

All final checks passed:

```bash
lake build AxiomaticGW.Tautological.GetzlerRealization AxiomaticGWTest.Tautological.GetzlerReplay
lake build
lake test
lake lint
lake env lean /tmp/gw_getzler_axioms_20261002.lean
python3 scripts/test_getzler_certificate.py
python3 scripts/verify_graph_corpus.py --verify-executable
/opt/homebrew/Caskroom/miniforge/base/envs/axiomatic-gw-sage/bin/python scripts/search_getzler_certificate.py
python3 scripts/export_getzler_certificate.py environments/getzler-candidate-osx-arm64.json
git diff --check
```

The full build completed 2,659 jobs; tests completed 2,680 jobs. The only Lean warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`. Sage retains its upstream category deprecation warning. The 36 exchange cases comprise four accepted presentations, fourteen kernel rejections, and eighteen parser rejections. All 97 audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`. The new Lean files contain no placeholders, substitute axioms, or native proof bypass. [Getzler validation](../../environments/getzler-validation.json) records source pins and detailed evidence.

### Remaining scope and next priority

The geometric Getzler theorem, normalized-cycle identification, proper Gysin/graph-realization data, and target applicability remain explicit inputs. General strata products and node excess, forgetting, the required genus-two relation families and operation provenance, geometric seed sufficiency, actual GKM CohFT/reconstruction data, descendant--ancestor comparison, termination/uniqueness, and the full fixed numerical suites remain open.

Next, express the seven representative Getzler graphs as compositions of the existing elementary gluings and label transports. Derive their actual full-curve-class GW contractions from primitive class gluing and push-pull laws, then use that concrete equation in the genus-one reconstruction argument.

## 2026-10-02: R3/R4/R5 marked WDVV replay and GW interpretation

**Status:** External label transport, the explicit four-point raw boundary frame, Sage witness search, offline claim-bound replay, and conditional full-class GW evaluation are implemented and verified. R1--R8 remain unaccepted as complete; the fixed surfaces and benchmark bounds are unchanged. This work remains uncommitted.

### Scope reviewed and findings

Reviewed the existing stable-graph relabelling, finite graph isomorphisms, rational certificate semantics, fundamental strata, separating Gysin/realization laws, GW ancestor convolution, and earlier WDVV restriction-map theorem. The baseline `lake build AxiomaticGW.Tautological.RelabelRealization AxiomaticGW.Tautological.SeparatingRealization AxiomaticGW.GW.SmallQuantumProduct` passed (1,800 jobs). The unfinished WDVV draft failed its closed arithmetic `decide` proof; this critical build defect was repaired through the existing checker equality theorem and explicit finite rational arithmetic, preserving its statement.

The high-severity integration gap was the absence of a checked marked graph vector and a geometric route from that vector to GW evaluation. `GenusZeroGeometry.mbarZeroFourBoundary` equates restriction maps; it does not by itself equate the raw pushforward classes without additional duality. The new consumer records that class equality separately, rather than silently inferring it or assuming the final GW recurrence. The unmarked genus-two replay fixture could not test external label corruption; the marked fixture now does.

### Revisions and mathematical effect

- `Tautological/Relabel.lean` reuses the existing stable-graph relabelling for finite presentations, transports incidence and psi powers together, preserves all internal decorations and automorphism orders, and descends through graph isomorphism classes to a degree-preserving rational linear map.
- `RelabelRealization.lean` extends primitive basis naturality to all rational combinations, preserves the realization kernel, and derives integrated CohFT/GW state reindexing with the full curve class unchanged.
- `WDVV.lean` fixes the three distinct raw partitions `01|23`, `02|13`, `03|12`, their automorphism order one, rows `(1,-1,0)` and `(0,1,-1)`, and the independently held request `(1,0,-1)`. Kernel arithmetic checks the searched witness `(1,1)`; the requested formal expression is proved nonzero before imposing geometric relations.
- `WDVVRealization.lean` identifies each column with the corresponding raw boundary point class. `BoundaryClassesEqual` states [Keel, Section 4, Theorem 1, Part I(2)](https://www.math.colostate.edu/~renzo/teaching/Moduli16/keel.pdf) as a named geometric property with no GW family or final recurrence in its definition. Fundamental normalization, raw graph-map composition, relabelling, and proper push-pull/integration derive original row vanishing and the accepted GW convolution equation. `gw_channel_zero_eq_two` is a consequence of this certificate chain.
- Three project-owned scripts search in pinned Sage/admcycles, emit actual incoming graph data and Lean proof replay, and test corruptions offline. The version-one frame fixes genus, locus, labels, raw factors, generator references, original rows, and the requested expression. JSON parsing remains outside the mathematical trust boundary; graph stability, genus, semantic column equality, and exact witness arithmetic are kernel obligations.

Four public imports expose these modules. Existing theorem signatures and geometric conventions are preserved; no existing theorem was weakened. No placeholder, substitute axiom, new global simp lemma, or global instance was introduced. The generic coefficient interface remains suitable for a supplied GKM theory with its required grading/ordinary comparison; no GKM CohFT class or semisimple reconstruction action is imported here.

### Validation

All final commands returned zero:

```bash
lake build AxiomaticGWTest.Tautological.WDVV
lake build
lake test
lake lint
lake env lean /tmp/gw_wdvv_axioms_20261002.lean
python3 scripts/test_wdvv_certificate.py
/opt/homebrew/Caskroom/miniforge/base/envs/axiomatic-gw-sage/bin/python scripts/search_wdvv_certificate.py
python3 scripts/export_wdvv_certificate.py environments/wdvv-candidate-osx-arm64.json
git diff --check
```

The six reviewed Lean files pass the placeholder/substitute-axiom and global-state scans and the 100-character line check. All **80 audited declarations**, including incoming graph validation, semantic equality, and replay acceptance, depend only on standard Lean axioms. The existing private-module warning in `AxiomaticGWTest/Basic.lean` remains; no new Lean warnings were introduced. Sage emits an upstream category deprecation warning.

The **30 offline exchange cases** comprise three accepted replays (baseline, vertex exchange, branch exchange), ten kernel rejections, and seventeen parser rejections. Changed partitions and a different valid kappa column fail the held semantic slots. Other cases alter raw factors, rows, claims, witnesses, graph genus/incidence/powers, locus, relation references, label conversion, tool pins, exact number encodings, or JSON shape. Fresh Sage generation and ordinary Python export reproduce the frozen report and Lean replay byte for byte.

The Lean regressions check all external incidences and component state orders, graph distinctness and degree, rational coefficients, asymmetric decorations, transport back across label types, empty-label loop behavior, and incoming replay consumption. The actual marked graph-to-GW chain is tested on `E₁+E₂`, retaining both distinct exceptional classes, their two ordered splits, and both zero factors. These tests instantiate the interface under named geometric inputs; they do not compute surface GW numbers.

[`environments/wdvv-validation.json`](../../environments/wdvv-validation.json) records command outputs and hashes, source pins, scope, and the axiom audit. [`wdvv-certificate-regressions.json`](../../environments/wdvv-certificate-regressions.json) records the exchange cases; the [environment guide](../references/AdmcyclesEnvironment.md#marked-four-point-wdvv-replay) documents regeneration and offline replay. The older separating validation manifest is retained as historical evidence for its original source pins.

### Remaining obligations and next priority

The raw boundary class equality, geometric Gysin/graph realization, target applicability, and genuine stable-map descendant comparison remain explicit obligations. This consumer has four external markings; arbitrary-background WDVV, common-refinement products and node excess, forgetting, normalized Getzler/genus-two graph encodings and provenance, finite seed sufficiency, reconstruction termination/uniqueness, actual GKM CohFT import, and the complete benchmark/research release remain open.

The next relation priority is the seven explicit normalized Getzler graph cycles and their marked claim-bound replay, so the genus-one reconstruction route can consume concrete graph data rather than a supplied cycle oracle. Continue the existing full graph corpus through its owned live handle and accept it only after terminal exit, complete coverage, and source-pin validation; no partial run is promoted to completion.

## 2026-10-02: R3/R5 separating gluing and full-class boundary equations

**Status:** Separating graph gluing, linear product integration, and conditional CohFT/GW ancestor boundary evaluation and certificate transfer are implemented and verified. R1--R8 remain unaccepted as complete. The three fixed surfaces and every benchmark bound are unchanged. The implementation remains uncommitted.

### Scope, findings, and revisions

The targeted review covers the two component flag sets, incidence and stability, genus and decoration conventions, graph isomorphisms and rational strata, existing separating pullbacks and CohFT/GW gluing, ancestor integration, realization composition, and exact row witnesses. Existing public structures and statements were preserved. This is not a comprehensive repository review.

- **High implementation gap addressed:** `Tautological/SeparatingGluing.lean` joins two independently stable graphs at their `none` markings. A vertex flag bijection proves stability; connectedness and the spanning-tree bound justify the genus calculation. Component genera add, and codimension is the sum plus one. Retained markings, kappa and old half-edge decorations survive; source node powers move to the ordered branches of the new last edge. Independent component isomorphisms extend, giving quotient and rational bilinear maps.
- **High integration gap addressed:** The existing algebra-homomorphism scalarization lemma could not express ordinary linear integration. `Linear/SeparatingContraction.lean` proves contraction through two linear functionals with arbitrary module targets. The existing lemma and its API are unchanged. `CohFT/SeparatingPushforward.lean` defines tensor integration from the factor integrals and derives boundary contraction from optional primitive proper Gysin, projection, and integration laws. Neither factor integral is assumed multiplicative.
- `GW/SeparatingBoundary.lean` derives the finite convolution over every ordered splitting of the complete curve class, including zero factors. Source cotangent monomials give the existing component ancestor invariants, with both node powers retained. No final numerical recurrence is a hypothesis.
- `Tautological/SeparatingRealization.lean` extends primitive basis-level graph-map composition bilinearly, preserves the realization kernel of either component, and transfers checked original row witnesses to expanded integrated glued equations. Its normalized fundamental theorem derives the complete graph-to-GW ancestor chain from the primitive cotangent laws. The graph operation is independent of certificate semantics; the CohFT layer does not import GW. No global simp lemma, instance, coercion, or notation was added.

### Mathematical effect and regressions

Raw ordered pushforward multiplies the two source coefficients and sums coincident output columns. Gluing can create component-exchange automorphisms; no automorphism divisor is inserted. This matches the [admcycles separable-boundary pushforward convention](https://modulispaces.gitlab.io/admcycles/tautological_ring.html#admcycles.tautological_ring.TautologicalRing.separable_boundary_divisor), audited on 2026-10-02.

Component dimension vanishing does not generally become target dimension vanishing: two codimension-one columns on `Mbar(0,3)` glue with a genus-two fundamental component to distinct codimension-two graphs below the target dimension five. The tests prove that the output columns are distinct. Their integrated vanishing is derived through geometric composition and the original checked certificate, rather than cancellation of identical graphs or a target dimension test. Certificates are tested in both component positions.

`AxiomaticGWTest/Tautological/Separating.lean` has seventeen examples and eight private supporting theorems. They check empty retained label sets, automorphism orders two and eight, symmetry breaking by decorations, preserved marking/kappa/internal powers, signed rational coefficient multiplication and merging, isomorphism transport, both certificate transfers, and the full graph-to-ancestor chain. The latter retains all four splittings of `E₁+E₂`, including both ordered exceptional pairs and both zero factors, despite equal exceptional energies. Arbitrary retained and node powers remain parameters. Kernel reduction checks all 96 automorphism candidates in the two-loop fixtures using a documented local heartbeat budget.

A genuine rank-two Frobenius-derived CohFT gives the nonzero source ancestor contraction **7057**. A separate example proves that the product counit is nonmultiplicative, and a negative fixture excludes the degree-zero constant target with its usual integration as a separating Gysin model. The constant model is used only for the source ancestors; these fixtures do not compute surface GW values or provide a geometric boundary model.

Draft checks exposed stable-arity decidability, finite-index elaboration, noncomputable kappa syntax, scalar rewrite order, and tensor/finite-sum evaluation. These proof errors were repaired without weakening the statements, changing any normalization, or introducing artificial hypotheses. Proper Gysin, cotangent, graph-map composition, and original relation validity remain explicit geometric inputs.

### Validation and remaining obligations

The production baseline passed `lake build AxiomaticGW.Linear.Contraction AxiomaticGW.CohFT.Ancestors AxiomaticGW.GW.Basic` (1,706 jobs). The existing draft separating regression failed before revision; the final targeted check passes. All five production modules and their consumer compiled incrementally. Final checks passed:

```bash
lake build AxiomaticGWTest.Tautological.Separating
lake build
lake test
lake lint
lake env lean /tmp/gw_separating_axioms_20261002.lean
git diff --check
```

The targeted/full builds completed 2,653 jobs; the test suite completed 2,671. Only the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean` remained. All sixty-one new public declarations were audited and depend only on `propext`, `Classical.choice`, and `Quot.sound`. The source/test scan found no placeholders, substitute axioms or native proof bypasses; all six new Lean files have no trailing whitespace and lines at most 100 characters. [The validation manifest](../../environments/separating-validation.json) records exact commands, log digests, twenty-six source pins, the declaration audit, fixture scope and remaining obligations. The targeted final patch and untracked sources were inspected, preserving existing work.

The owned native graph-corpus handle was confirmed live, still with 67 of 68 coherent records. Its executable and all eight pinned project dependencies were reverified unchanged. `environments/graph-corpus-native-attempts.json` records the observation; the partial corpus is not accepted as a completed R2 gate.

**Next priority:** Encode the selected reconstruction relation vectors and complete the common-refinement/node excess and forgetful corrections consumed by their derivations. Elementary gluing does not yet prove general graph splitting or stable-map descendant comparison. Geometric surface identification, finite-seed sufficiency, terminating and unique reconstruction, actual GKM CohFT/reconstruction-action import, and all fixed surface numerical benchmarks remain required.

## 2026-10-02: R3/R5 nonseparating gluing and boundary equations

**Status:** The nonseparating graph operation and its conditional CohFT/GW boundary evaluation and certificate transfer are implemented and verified. R1--R8 remain unaccepted as complete; the fixed targets and benchmark bounds are unchanged. The implementation remains uncommitted.

### Scope, findings, and revisions

The targeted review covers graph incidence, vertex stability, genus and decoration conventions, isomorphisms and rational strata, primitive stable-curve pullbacks and integration, the existing class-valued CohFT/GW nonseparating axioms, ancestor evaluation, and exact row witnesses. Existing public structures and statements were preserved; this is not a comprehensive repository review.

- **High implementation gap partly addressed:** `Tautological/NonseparatingGluing.lean` constructs the new last edge from `none` and `some none`. A bijection of vertex flags proves stability, including loops. Connectedness is retained; the spanning-tree bound justifies the natural-subtraction genus calculation. Genus and codimension increase by one; kappa, retained markings, and old internal decorations survive, and the two node powers move onto their ordered branches. The operation transports isomorphisms, descends to the quotient, and acts linearly with degree and dimension-relation preservation.
- **High interpretation gap partly addressed:** `CohFT/NonseparatingPushforward.lean` supplies optional geometric degree, relabelling, branch-swap, projection, and integration laws. These primitive laws and the existing CohFT gluing axiom prove the integrated inverse-metric contraction. `GW/NonseparatingBoundary.lean` proves the class-resolved version and identifies source monomials with the existing ancestor invariant. No final recurrence is an input.
- `Tautological/NonseparatingRealization.lean` states basis-level raw graph-map composition, extends it to arbitrary rational combinations, proves kernel preservation and integrated pull-push, and transfers checked original row witnesses into expanded glued equations. The combinatorial operation does not depend on certificate semantics; the CohFT layer does not import GW. No global simp lemma, instance, coercion, or notation was added.

### Mathematical effect and regressions

The source's node labels cease to be external labels. Consequently, output graph symmetries may increase and distinct source strata can coincide. The operation retains each raw coefficient and sums coincident output columns; it does not divide by an automorphism order. This agrees with the [admcycles raw irreducible-boundary pushforward convention](https://modulispaces.gitlab.io/admcycles/tautological_ring.html#admcycles.tautological_ring.TautologicalRing.irreducible_boundary_divisor).

`AxiomaticGWTest/Tautological/Nonseparating.lean` has fifteen examples and three substantive quotient lemmas. They cover loops, parallel edges in genus two, unequal node powers, retained labels and kappa/internal decorations, changed automorphism orders, noninjectivity, raw coefficient merging, dimension relations, the full graph-to-GW ancestor chain, and an exact two-column certificate using original dimension vanishing. The certificate's output columns are proved distinct, excluding cancellation of identical graph classes as the reason the equation passes. A two-dimensional Frobenius-derived CohFT gives the nonzero ancestor contraction **5**. A negative fixture proves that the degree-zero constant target with its usual nonzero three-point integration cannot carry these geometric Gysin laws; it is not used as a fake boundary model. None of these fixtures computes a surface GW value.

Draft checks exposed public/private module visibility, finite-index and coercion elaboration, noncomputable kappa syntax, and exact vector normalization. These were repaired without weakening statements or changing graph conventions. The optional geometric inputs remain explicit, and existing assumptions were not strengthened.

### Validation and remaining obligations

The relevant baseline passed `lake build AxiomaticGW.Tautological.GraphBounds AxiomaticGW.CohFT.Ancestors AxiomaticGW.GW.Basic` (1,781 jobs). Incremental checks compiled all four new production files and their consumer. Final checks passed:

```bash
lake build AxiomaticGWTest.Tautological.Nonseparating
lake build
lake test
lake lint
lake env lean /tmp/gw_nonseparating_axioms_20261002.lean
git diff --check
```

The targeted/full builds completed 2,648 jobs and the test suite completed 2,665. Only the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean` remained. The twenty-six declaration axiom audit found only `propext`, `Classical.choice`, and `Quot.sound`. Source/test scans found no placeholders or native proof bypasses. [The validation manifest](../../environments/nonseparating-validation.json) records exact commands, log digests, source pins, the axiom audit, and fixture scope. The final patch was inspected, including untracked sources, and existing work was preserved.

The native graph-corpus handle remains live with 67 of 68 coherent records; its binary and eight pinned project dependencies are unchanged. The observation is recorded in `environments/graph-corpus-native-attempts.json`, not promoted to a completed R2 gate.

**Next priority:** Construct separating graph gluing and derive its boundary evaluation with every effective-class splitting and inverse-metric contraction. Then complete graph-map composition, common-refinement/node excess and forgetful corrections needed by the selected relations. General graph splitting, geometric relation validity, stable-map descendant comparison, seed sufficiency and termination, actual GKM CohFT import, and all fixed surface reconstruction applications remain open.

## 2026-10-02: R3/R5 external psi operations and integrated equations

**Status:** External psi graph multiplication and its conditional realization and numerical evaluation are implemented and verified. R1--R8 remain unaccepted as complete. All three surface applications, benchmark bounds, and the active research objective are unchanged. No implementation commit has been created.

### Scope, findings, and revisions

The review covers the existing decorated-graph isomorphisms and raw gluing-pushforward convention, the free strata module and degree subspaces, `StrataRealization`, exact relation witnesses, and the stable-curve psi, integration, and CohFT ancestor interfaces. Existing graph definitions, realization and CohFT structures, theorem statements, and normalizations were preserved. This is not a comprehensive review of the repository.

- **High implementation gap addressed:** The graph syntax had external powers but no verified operation multiplying arbitrary stratum combinations by their monomials. `Tautological/LegPsi.lean` implements `addLegPsi`, the full isomorphism bijection, unchanged automorphism counts, quotient well-definedness and injectivity, exponent composition, codimension addition, and the rational linear action `mulLegPsi`. It proves preservation of homogeneous and dimension-relation subspaces. Internal decorations, graph incidence, marking labels, and raw coefficients are retained.
- **High interpretation gap partially addressed:** A graded linear realization alone does not identify these graph powers with actual cotangent classes. `LegPsiRealization.lean` states only the primitive single-marking compatibility law and derives arbitrary powers and several markings by natural and finitely-supported induction. The law is expressed using delta values, so it does not depend on a choice of decidable equality. The compatibility itself remains a geometric input.
- `integrateAgainst` composes the existing realization, cohomology multiplication, and integration. `certificate_mulLegPsi_eq_zero` derives the multiplied integrated equation from the checked original row witness and original cohomological row vanishing. No multiplied equation or final GW recurrence is supplied as an assumption. `integrateAgainst_fundamental` identifies normalized fundamental evaluation with the existing full class-valued CohFT ancestor.
- The graph operation depends on graph syntax, isomorphism enumeration, the free strata module, and mathlib's linear-combination API. Its certificate consumer is kept in the realization extension, avoiding a dependency from the combinatorial operation on certificate semantics. No global simp lemma, instance, coercion, or notation was added.

### Mathematical effect and regressions

The additions prove formal graph operations and conditional stable-curve interpretation for arbitrary finite label types and marking powers. They do not change existing assumptions or prove common-refinement multiplication, graph gluing/forgetting, geometric relation validity, general graph splitting, or stable-map descendant comparison.

`AxiomaticGWTest/Tautological/LegPsi.lean` contains twelve public-API examples plus a negative fixed-label lemma. They cover loop flips, broken decoration stabilizers, internal branch exchange, equal-codimension powers at different labels, empty labels, rational coefficients and signs, and codimension. A constructed normalized constant realization has integrated value six. Its actual Frobenius-derived full CohFT gives the nonzero three-point ancestor **30** for inputs `(2,3,5)`, while positive cotangent powers vanish through the existing classes. An exact row witness then proves a multiplied integrated equation using original dimension-relation vanishing. These are interface fixtures, not surface GW values.

Draft checks exposed dependent quotient rewriting, accidental transitive imports, opaque finite-index normalization, and a decidable-equality mismatch in the preliminary single-factor predicate. They were corrected with the quotient map, explicit imports and finite range proofs, public vector identities, and the equality-independent primitive law. No graph convention, requested numerical value, or existing mathematical statement was weakened.

### Validation

The following commands passed:

```bash
lake build AxiomaticGW.Tautological.GraphIsomorphisms \
  AxiomaticGW.Tautological.StrataRealization AxiomaticGW.CohFT.Ancestors
lake build AxiomaticGW.Tautological.LegPsi
lake build AxiomaticGW.Tautological.LegPsiRealization
lake build AxiomaticGWTest.Tautological.LegPsi
lake build
lake test
lake lint
lake env lean /tmp/gw_leg_psi_axioms_20261002.lean
git diff --check
```

The final build completed **2,644 jobs**; tests completed **2,660 jobs**; lint passed. The only warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`. The axiom audit of **24 declarations** reports only `propext`, `Classical.choice`, and `Quot.sound`. `environments/leg-psi-validation.json` records exact commands, outcomes, source hashes, and the declaration audit. The new source and tests contain no placeholders, declared substitute axioms, or `native_decide`. The final diff and source-bound records were inspected.

The pending GKM Euler-coherence test and lint checks also completed successfully, and both curve-certificate reports were refreshed from the actual 24-case regression output and eleven-declaration audit. Their baseline remains the frozen 17,848-byte proof. Prior state-certificate source pins and the candidate input bundle remain unchanged.

### Remaining obligations and next priority

The owned coherent 68-case native corpus was confirmed live in session **30672**, with **67 complete records** at the latest verified wait. The largest case remains in progress; no run was restarted or accepted from partial output. All eight pinned native-driver project dependencies and the executable are unchanged by this work.

The next mathematical priority is graph gluing/forgetting and its realization and splitting laws, including the node excess factors, automorphism coefficients, and marking multiplicities needed by the selected reconstruction relations. Then the checked relations must be transferred to genuine curve-resolved GW descendant equations. Actual GKM CohFT class or reconstruction-action input, equivariant grading and ordinary comparison, geometric surface identification, finite-seed sufficiency, terminating recursions, and every fixed benchmark remain required. External psi interpretation is progress toward R3/R5, not acceptance of either full gate.

## 2026-10-02: R4 full GKM curve and invariant-edge replay

**Status:** The new curve certificate, three surface replays, public examples, command-line regressions, and final build/test/lint checks are verified. R1--R8 remain unaccepted as complete. The applications, benchmark bounds, and active goal are unchanged; no implementation commit has been created.

### Scope, findings, and mathematical effect

This review covers the existing `SurfaceTarget` coordinate, intersection, and first-Chern APIs, the candidate bundle's curve/fan/edge fields, and their new kernel replay. It preserves the existing surface definitions, state certificates, graph enumerator, and numerical GW laws. It is not a comprehensive mathematical review of the project.

- **High integration gap addressed:** Curve and invariant-edge fields previously had supplemental Python checks only. `GKM/CurveConventionCertificate.lean` now binds acceptance to independently held `Fixtures/CurveFrames.lean` requests. `Fixtures/CurveReplay.lean` proves all twelve edge conventions and all twenty-six symbolic divisor-intersection traces for X0--X2.
- Acceptance checks rays, cone labels, unordered tangent pairs and their duality, full lattice matrices, positive energy weights, generator walls, the wall bijection and complete fan adjacency, oriented tangent signs, full curve classes, normal branches, signed degrees, and character transitions. The localization traces agree with the existing signed divisor-intersection API. Geometric localization remains a separate input.
- **High consistency gap repaired before completion:** The initial new certificate checked the state and fan separately without explicitly connecting their Euler factors and Chern sums. `state_euler` and `state_tangentSum` now prove that the held state request uses exactly the product and sum of the same two fan characters. The generated proofs establish both identities at every fixed point; an additional regression proves non-acceptance of a doubled state Euler request.
- `transport_correct`, `transport_injective`, `transport_add`, and `energy_correct` hold for arbitrary effective classes. `edge_firstChern` uses the existing actual divisor pairing; `intersection_trace` uses accepted state-space tables; `intersections_specialize` proves regular ordinary values of complete sums. No existing theorem statement, hypothesis, basis order, or normalization changed.
- **Medium encoding risk prevented:** The exporter emits finite labels as constructors with range proofs, avoiding the modular interpretation of an out-of-range Lean numeral. The Python preflight already rejects invalid labels; these new proofs also expose the range obligation in the replay.
- Regression examples exhibit equal energy but distinct transported E1/E2 classes. Five Lean examples prove non-acceptance of an exceptional-class swap, wrong normal degree, reversed weight without endpoint exchange, zero curve matrix, and incoherent state Euler request. These are stronger evidence than merely failing to reuse an existing proof.
- Draft compilation exposed finite-index normalization and opaque predicate decision-synthesis failures. Explicit finite-sum coordinate proofs, controlled scalar simplification, and unfolding only the finite adjacency predicates fixed them without changing the requested mathematics. The generated proof budget is scoped and documented. Final formatting warnings were repaired in the generator, with no linter suppression.

### Validation

The following commands passed:

```bash
lake build AxiomaticGW.Surfaces.CurveClasses AxiomaticGW.GKM.Fixtures.SurfaceFrames
lake build AxiomaticGW.GKM.Fixtures.CurveFrames
lake build AxiomaticGWTest.GKM.CurveReplay
lake build
lake test
lake lint
python3 scripts/check_gkm_inputs.py environments/gkm-inputs-osx-arm64.json
python3 scripts/test_gkm_curve_certificate.py
lake env lean /tmp/gw_gkm_curve_certificate_axioms_20261002.lean
PYTHONPYCACHEPREFIX=/tmp/gw-gkm-certificate-cache python3 -m py_compile \
  scripts/export_gkm_curve_certificate.py scripts/test_gkm_curve_certificate.py
git diff --check
```

The final build completed **2,642 jobs** without warnings; tests completed **2,657 jobs**, with only the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`; lint passed. The final exporter suite passes **24 cases**: four accepted presentation variants, fourteen controlled export rejections, and six kernel claim-binding rejections. `environments/gkm-curve-certificate-regressions.json` records exact source/proof hashes and measurements. The default frozen proof is **17,848 bytes**, SHA256 `8ad5340f75c63df113332df14fadac3a2b1a34454532ec76764b9305fa3f7b26`; standalone replay took about **22 seconds**. These are target-data replay timings, not GW reconstruction timings.

The axiom audit of **eleven declarations**, including all three acceptance proofs, reports only `propext`, `Classical.choice`, and `Quot.sound`; `environments/gkm-curve-certificate-axioms.json` pins the sources. Placeholder, declared-axiom, and `native_decide` scans of the new modules, tests, and scripts found no matches. The prior state-certificate source hashes and the 308,271-byte GKM candidate bundle remain unchanged. The final diff and manifests were inspected.

### R2 runtime follow-up and remaining priorities

The owned large-stack retry is now terminal and produced the complete record `(2,6,3,count=39109,elapsed_ms=10252351)`. The resource timing wrapper returned one after reporting `sysctl kern.clockrate: Operation not permitted`; the original child's exit was not recorded separately. A controlled small case reproduced this instrumentation failure: the direct driver returned zero, while the timing wrapper returned one for the same valid output. The current executable and all eight native-driver project dependencies match the largest-case pin.

The earlier 67-case corpus has a different `GraphEnumeration.lean` source pin. These runs were therefore not silently merged into a passed current-source corpus. A fresh coherent 68-case run uses the pinned executable directly, the same large stack, and a wrapper that records the child's exit and validates the exact range, uniqueness, count monotonicity, small fixtures, and unchanged source/executable hashes. Its manifest is `/tmp/gw_graph_corpus_current_20261002_manifest.json`; session **30672** was confirmed live after dispatch. `environments/graph-corpus-native-attempts.json` preserves the observed results and provenance. This is supplemental native execution, not a kernel proof of the counts. R2 remains open pending that run and its other acceptance obligations.

Next, construct checked graph-operation interpretation and relation-to-GW equations, and provide actual CohFT classes or a specified reconstruction action with its comparison hypotheses. Stable-map localization graphs, covering and automorphism factors, stabilization, descendant--ancestor comparison, ordinary specialization of full classes, equivariant grading, geometric surface identification, finite-seed sufficiency, and R6/R7 reconstruction and all fixed benchmarks remain required. The target-data certificates do not supply those results.

## 2026-10-02: R4 exact GKM state certificates and regular specialization

**Status:** The classical state certificate implementation, kernel replay for X0--X2, and final build/test/lint and command-line regression checks are verified. R1--R8 remain unaccepted as complete. The applications, energy bounds, and active research goal are unchanged; no implementation commit has been created.

### Scope, findings, and revisions

This review covers `GKM/EquivariantCoefficients.lean`, `GKM/StateSpaceCertificate.lean`, the three fixed surface requests and generated replay, their Python exporter and regressions, and the narrow surface coordinate API used by the ordinary comparison. Existing numerical GW laws and reconstruction interfaces were not revised. This is not a comprehensive review of the repository.

- **High integration gap addressed:** The exact Python state tables previously had no claim-bound kernel replay. `Accepts request tables` now checks the independently held restrictions, Euler factors, tangent sums, unit index, and ordinary surface algebra. Each exported denominator has a separate nonvanishing proof. The replay proves both basis inverses, weighted metric/inverse formulas, all products, the unit and Chern coordinates, and regular ordinary comparisons.
- **High semantic correction in draft data:** The two-point blowup's last two draft Euler factors and tangent sums had incorrect signs. The failed replay exposed them. Recomputing the dual fan characters gives factors `(-x)*y` and `(-y)*(y-x)` and sums `y-x` and `-x`. The fixed request was corrected; ordinary surface products, basis order, and curve conventions were preserved.
- **Medium exporter limitation repaired:** A hardcoded nonvanishing sample could fail on a valid polynomial denominator. The exporter now searches a finite degree-bounded grid when necessary and emits an exact Lean evaluation witness. Evaluations certify only nonvanishing; symbolic identities are proved by field and ring arithmetic.
- **Medium replay robustness defect repaired:** A valid regular representative with denominator `1+x-y` exposed a second failure when denominator clearing changed its polynomial form. The exporter transports the proved nonvanishing fact through an exact ring identity rather than relying on literal expression matching. Default fixture generation remains byte-identical.
- **High remaining integration gap identified:** The certified localized plane pairing of `H` and `pt` is nonzero (`-y`). Their ordinary degrees sum to three, so they cannot satisfy the existing dimension-two `GradedStateSpace.pairing_vanishes` over an ungraded coefficient field. A regression exhibits this boundary. Bare CohFT transport is sound; a full GW import still needs ordinary specialization of classes or explicit equivariant coefficient grading. No existing grading law was weakened.
- The coefficient domain is the genuine fraction field of rational polynomials in two independent characters. `Specializes.unique` proves representative independence. `not_specializes_inverse` excludes ordinary values for individual Euler poles; complete expressions may specialize after cancellation. No whole-field evaluation at zero is postulated.
- `SurfaceCohomology.one_coordinates` and `firstChernDivisor_val` expose existing coordinates without changing definitions or theorem hypotheses. They avoid dependence on private surface instances in generated arithmetic proofs. The larger proof budget is scoped to the three finite acceptance declarations.

### Mathematical effect and concrete use

`Fixtures/SurfaceFrames.lean` computes ordinary tables from the existing rational surface algebra. `Fixtures/SurfaceReplay.lean` checks **216 product coefficients, 50 metric entries, and 50 inverse-metric entries** across the three targets. Its proofs construct the actual state equivalences and connect the tables to the existing perfect pairing and transported bilinear product. The root library imports the frozen replay.

The new Lean regression examples use those actual pairings and products: the plane hyperplane metric specializes to one, exceptional self-intersection to minus one, and the two distinct exceptional classes have zero mixed point coefficient. A fixed-point Euler reciprocal has no ordinary specialization. These are classical algebra results, not numerical GW invariants or imported CohFT classes.

The public exporter can replay the whole fixed bundle or selected targets, and reports only candidate proof emission until Lean compilation succeeds. The command-line suite includes equivalent rational representatives, a regular denominator that vanishes at the initial sample, controlled export failures, and kernel rejection of attempts to reuse proofs against altered tables or requests. Digests remain reproducibility metadata.

### Validation

Completed successfully:

```bash
lake build AxiomaticGW.GKM.StateSpaceCertificate AxiomaticGW.GKM.Fixtures.SurfaceFrames
lake build AxiomaticGWTest.GKM.EquivariantCoefficients
lake env lean /tmp/gw_surface_replay_candidate_v5.lean
lake env lean AxiomaticGWTest/GKM/SurfaceReplay.lean
lake build
lake test
lake lint
python3 scripts/check_gkm_inputs.py environments/gkm-inputs-osx-arm64.json
python3 scripts/test_gkm_inputs.py
python3 scripts/test_gkm_certificate.py
lake env lean /tmp/gw_gkm_regular_denominator_variant_final.lean
lake env lean /tmp/gw_gkm_state_certificate_axioms_20261002.lean
PYTHONPYCACHEPREFIX=/tmp/gw-gkm-certificate-cache python3 -m py_compile \
  scripts/export_gkm_certificate.py scripts/test_gkm_certificate.py
git diff --check
```

All listed commands passed. The final build completed **2,639 jobs**, tests **2,653 jobs**, and lint passed. The only warning is the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`. The input suite passes **34 cases** and the new state-certificate suite passes **18 cases**, recorded in `environments/gkm-state-certificate-regressions.json`. Its baseline matches the frozen public module exactly: **123,248 bytes**, about **179 seconds** for standalone proof checking in this run. The two selected-target equivalent-representation replays took about **28 seconds** each. Generation took less than a second; these timings do not measure Sage exploration or GW reconstruction.

Earlier draft proof runs exposed vector/finite-index and denominator-normalization failures; they were corrected without changing the claimed equalities. A library build also exposed an unscoped proof budget and failures in the new explicit examples, now corrected. The valid nonconstant-denominator regression first failed in denominator clearing; the corrected conversion replays successfully. Its final formatting revision was independently replayed without warnings and is recorded separately in the regression report.

The audit of **18 key declarations**, including all three acceptance theorems, reports only `propext`, `Classical.choice`, and `Quot.sound`; source hashes are recorded in `environments/gkm-state-certificate-axioms.json`. Placeholder, declared-axiom, and `native_decide` scans of the GKM modules, their tests, the two touched surface modules, and the new scripts found no matches. The final diff and whitespace checks were inspected.

### Remaining obligations and next priority

The exact state proofs do not certify curve/edge conventions, localization-graph stabilization, numerical query values, quantum multiplication, CohFT classes, or an R-matrix/translation action. Equivariant coefficient grading and ordinary specialization of the full classes remain required before applying GW dimension laws. The geometric surface identification and finite-seed sufficiency remain explicit R1 obligations. The full graph runtime gate and R3 relation operations remain open; the owned `(2,6,3)` retry was still live at the final check, with no terminal result, and was not restarted. The next research bridge is checked graph/operation interpretation and relation-to-GW equations, together with actual class-valued or reconstruction-action input and its ordinary comparison. R6/R7 still require terminating reconstruction, uniqueness, and every fixed numerical benchmark.

## 2026-10-02: R4 fixed-frame replay and initial GKM/CohFT bridge

**Status:** The fixed-frame certificate prototype, GKM candidate exporter/checker, and algebraic full CohFT transport are implemented. R1--R8 remain unaccepted as complete; no reconstructed positive-degree genus-two table or geometric surface theory is claimed. No implementation commit has been created. The fixed applications, benchmark bounds, and active goal are unchanged.

### Scope, findings, and revisions

The review covers the fixed genus-two relation frame, certificate exporter/replay, graph normalization proof API, the five pinned GKM producer modules, `GKM/FixedPointAlgebra.lean`, the new pairing/CohFT/matrix transport modules, and the GKM candidate scripts and regression fixtures. It is not a comprehensive review of the whole formalization. `notes/MathematicsToLean.md`, `notes/references/AdmcyclesEnvironment.md`, and `notes/references/GKMExchange.md` map the declarations and trust boundaries.

- **High input-validation defect repaired:** The earlier GKM arithmetic checker accepted exchanging an E1 edge for E2 at unchanged energy. This was reproduced against the preserved earlier script with a freshly computed digest. The revised checker binds the fan, toric divisor lifts, every divisor intersection, complete curve coordinates, edge orientations, normal branches, and normal degrees. The equal-energy corruption is now rejected; equivalent rational representatives and reversed edge orientations are accepted.
- **High integration gap addressed:** There was no state-space transport constructor for a full CohFT. `SymmetricPerfectPairing.comap` derives the new perfect metric, and `map_copairing_comap` proves the inverse-tensor correspondence. Two-slot, nonseparating, and separating contraction invariance then construct `CohFT.comap` with proved flat-unit and gluing laws and class-valued round-trip equality. An actual CohFT is required as input; numerical integrals cannot populate its class fields.
- `StateSpaceTransport.basisEquiv` uses checked inverse restriction matrices; its metric theorem identifies the actual pairing, and both transported metric products equal the identity. Multiplication is transported as a bilinear map, with associativity, commutativity, its transported unit, and Frobenius invariance. No pointwise ring instance is substituted for the basis product.
- **Validation defect repaired:** The pre-existing fixed-point inverse-metric regression did not compile because its explicit normalization omitted the final vector projection. Its statement and Euler factors are unchanged. New mixed-basis fixtures test nonzero off-diagonal metric, non-pointwise coefficient multiplication, unit transport, normalized three-point classes, and a full class round trip.
- The R4 prototype binds all eight raw genus-two codimension-two columns, seven exact rows, both kappa tables, and the independently held request. Direct field/arithmetic proofs are proved equivalent to Boolean acceptance and give formal-span membership. Evaluation vanishing still requires named vanishing hypotheses for every supplied row. Kernel-replayed graph branch exchanges are accepted without using unchecked native arithmetic. The semantic candidate/reference API preserves the production graph-search algorithm.

### Export and mathematical effect

The producer is pinned at `a09c6625b280312721c5e0f2f915791781339aa5`; its source hashes were verified before and after generation, and its checkout was not modified. Two fresh-cache Sage 10.9/admcycles 1.4 runs produced identical `environments/gkm-inputs-osx-arm64.json`, SHA256 `062a32a9919fa5ddf806c353f5bb56256ca5dca31d170c246b9bfa39c3b11376`. The initial data cover the three fixed surfaces, their full effective coordinates, symbolic basis/product/metric/Chern/edge data, and nine query regressions, including a nonzero genus-two degree-zero descendant on every target.

The stdlib checker verifies exact identities using independent sparse polynomial arithmetic over `Fraction`. Its numerical reference values are held independently fixed; its outputs remain candidate-data validation, not Lean certificates or geometric comparisons. The GKM/admcycles Hodge dependency is shared and explicitly recorded. No producer redistribution license was found, and no producer code is vendored.

Existing theorem statements and numerical normalizations are preserved. New conditional transport theorems derive every coherence law from existing mathematical structures; no desired GW recurrence, relation validity, or invariant value is inserted as a substitute axiom. The fixed-point algebra is classical and localized; neither it nor a numerical table determines the quantum product or full CohFT.

### Validation

The following completed successfully:

```bash
lake build AxiomaticGW.Linear.PairingTransport AxiomaticGW.CohFT.Transport
lake build AxiomaticGW.GKM.StateSpaceTransport
lake build AxiomaticGWTest.GKM.FixedPointAlgebra
lake build AxiomaticGWTest.GKM.StateSpaceTransport
lake build
lake test
lake lint
python3 scripts/check_gkm_inputs.py environments/gkm-inputs-osx-arm64.json
python3 scripts/test_gkm_inputs.py
python3 scripts/test_admcycles_certificate.py
lake env lean /tmp/gw_gkm_and_replay_axioms_20261002.lean
git diff --check
```

The full build completed 2,635 jobs and tests 2,647 jobs. Lint passed after adding 24 missing graph/decorations docstrings in the existing genus-two fixture; stripping docstrings and blank lines confirmed identical declaration text. The only warning was the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`. The GKM command-line suite passes **34 cases**; admcycles exporter/replay passes **23 cases** without Sage. The audit of **21 key declarations** reports only `propext`, `Classical.choice`, and `Quot.sound`, recorded with source hashes in `environments/gkm-and-replay-axioms.json`. Placeholder, declared-axiom, and `native_decide` scans of the touched mathematical and replay modules found no matches.

### R2 runtime follow-up and remaining obligations

The earlier full native corpus run is terminal: **67 of 68 cases**, then a stack overflow at `(g,n,d)=(2,6,3)`. Completed records were rechecked for uniqueness and the exact fixed range. The last three successful counts were 10,743 at `(2,5,3)`, 3,404 at `(0,6,3)`, and 15,523 at `(1,6,3)`; the first and last took about fourteen and seventeen minutes respectively. These are runtime diagnostics, not kernel numeral proofs.

A new owned run of the same largest case started with `LEAN_STACK_SIZE_KB=2097152`, current executable/source hashes in `/tmp/gw_graph_g2n6d3_stack2gb_manifest.json`, output in `/tmp/gw_graph_g2n6d3_stack2gb.jsonl`, and diagnostics in `/tmp/gw_graph_g2n6d3_stack2gb.log`. A one-second process sample confirmed deep repeated runtime application frames; it did not establish a precise root cause. A live single-case retry is not acceptance of the full corpus. Assess its terminal result and improve enumeration as needed before accepting R2.

The next bridge priority is claim-bound Lean replay of the exact equivariant tables, with denominator nonvanishing and complete-sum regularity/specialization. Actual CohFT class/reconstruction-action export, R-matrix conditions when used, geometric comparison, descendant--ancestor transfer, relation-operation provenance, WDVV/Getzler replay, and the full shared corpus remain open. R1's seed-sufficiency/geometric audit and R6/R7's terminating reconstruction, uniqueness, and all numerical applications are still required.

## 2026-10-02: R2 runtime caches and corpus driver

**Status:** The revised graph implementation, regression tests, and native driver are verified. The full 68-case execution gate remains open. No implementation commit has been created; the overall R0--R8 goal remains active.

### Scope, findings, and revisions

The review covers `DecoratedStableGraph.lean`, `GraphBounds.lean`, `GraphEnumeration.lean`, `GraphIsomorphisms.lean`, graph regressions, `scripts/GraphCorpus.lean`, and its Lake target. It also inspects the installed admcycles graph encoding and `Graphtodecstratum`/`FZ_coeff` conversion paths; the [integration note](../references/AdmcyclesEnvironment.md#graph-coordinate-conventions-audited-on-2026-10-02) records that scope.

- **Medium runtime defects repaired:** Repeated fibre counting and repeated reconstruction of exponent/kappa data dominated bounded enumeration. `CountedLegAssignment` now materializes leg counts with a proof of their exact compatibility; `requiredLegs` and `meets_requiredLegs_iff` preserve the original stability condition. Exponent tuples are materialized as vectors before coordinate lookup, and each decoded vertex's kappa monomial is materialized once.
- **Medium proof-interface defect repaired:** Membership-indexed candidate subtypes made cached-search equalities unusable for rewriting downstream finite images. `validCandidates` instead carries the existing semantic `Candidate.Valid` predicate. Its direct evaluation equality restores kernel `decide` proofs of the numerical fixtures. No native answer is inserted into a theorem.
- Summed stability proves `vertexCount + 2 ≤ 2 * totalGenus + card S`, permitting early rejection of impossible vertex counts. Presentation-independent vertex/edge counts justify disjoint size groups. A proved external-leg relation key partitions duplicate searches before full decorated isomorphism checks; key collisions would only merge search groups, not remove strata.
- The native driver enumerates the fixed 68-case range, with smaller bounds first, and reports exact counts plus elapsed milliseconds. New regressions cover the forced single vertex at genus zero with three markings and the empty unmarked genus-one corpus.

No new semantic defect was found in the reviewed stable-graph definitions. The genus, codimension, label, branch, and raw gluing conventions are unchanged. `mem_boundedStrata` retains its statement and arbitrary finite-label generality. The new global simp lemmas are only the canonical `vertexCount_mk` and `edgeCount_mk` projections, exercised by the downstream graph tests. Native corpus counts are formal syntax counts, not geometric dimensions or reconstructed invariants.

### Validation

The final source revision passed:

```bash
lake build AxiomaticGWTest.Tautological.GraphEnumeration AxiomaticGWTest.Tautological.GraphIsomorphisms graphCorpus
lake build graphCorpus
lake build
lake test
lake lint
lake env lean /tmp/gw_graph_runtime_axioms.lean
git diff --check
```

The targeted build completed 2,926 jobs; the driver rebuild after reordering its cases completed 2,924 jobs. The full build completed 2,629 jobs, and tests completed 2,637 jobs. Lint passed. The only Lean warning was the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`. All seventeen audited results, including cached stability, direct-search equalities, quotient invariants, exact decoration round-trip, grouping equality, completeness, and decorated isomorphism correctness, depend only on `propext`, `Classical.choice`, and `Quot.sound`. Placeholder, declared-axiom, `native_decide`, and unrestricted-simplifier scans of the touched graph area returned no matches.

The earlier native implementation completed 39 of 68 cases and was stopped after its replacement was verified. A fresh run of the cached implementation has completed **64 of 68 cases** at this checkpoint, including all 51 cases with bounds zero through two. Completed records were checked for uniqueness, the exact fixed range, nonnegative counts/times, monotonic counts across bounds, and agreement with the existing kernel fixtures. The unmarked genus-two counts through bounds zero, one, two, and three are respectively `1, 4, 12, 36`; only the previously recorded small fixtures are kernel numeral proofs.

The genus-one five-marking bound-three case has count `4208`: an earlier version took `142685` ms; cached runs took `65929` and `50725` ms. These are individual diagnostic runs with differing concurrent load, not a controlled speed estimate. The full run is stored temporarily in `/tmp/gw_graph_corpus_counted.jsonl`, with progress in `/tmp/gw_graph_corpus_counted.log` and source/executable hashes in `/tmp/gw_graph_corpus_counted_source.json`. Its executable SHA256 is `a1ca2f4d44c9e77477a73cdc40c555236e31f038968ac9f8128eb15c62b323df`. An unfinished temporary log is not a release artifact or acceptance evidence for missing cases.

### Remaining risk and next priority

At this checkpoint the four remaining cases were genus two with five markings and all three genera with six markings, each at bound three. **Follow-up:** that run ended after 67 cases with a stack overflow in the final case; the newer entry above records the changed-stack experiment and fixed-frame certificate work. R1's geometric identifications, finite-seed sufficiency, and historical comparison environment remain open. The caches and smoke test do not themselves implement R3's geometric operations or complete R4's general exchange.

## 2026-10-01: R2 bounded formal-stratum enumeration

**Status:** The bounded enumerator and its soundness and completeness proofs are implemented and verified. R2 remains incomplete because execution and performance of its full initial test range have not been established. No implementation commit has been created.

### Scope, findings, and mathematical effect

The review covers `GraphBounds.lean`, `GraphEnumeration.lean`, `GraphIsomorphisms.lean`, their public imports, and graph regression tests. The existing stable-graph and decorated-stratum definitions are preserved.

- **High integration gap resolved:** The earlier finite computation layer had no bounded decorated-graph enumerator or completeness theorem. `GraphBounds` proves the spanning-tree bound and finite decoration bounds. `boundedStrata` now enumerates exactly the existing quotient classes with codimension at most the supplied bound, for arbitrary genus and finite external labels. Encoding and decoding preserve the entire graph presentation and its decorations.
- **Medium performance issues addressed:** Fixed-size raw candidates are constructed with injective maps and disjoint unions, avoiding duplicate comparisons between disjoint incidence/genus groups. Boolean isomorphism checks test leg and vertex compatibility before edge/branch permutations and stop at the first witness. The existing correctness statements and full automorphism enumeration are unchanged.
- The raw syntax deliberately retains decorations above geometric dimension. For example, genus zero with three markings has five formal strata through codimension one. These counts do not claim a Chow or cohomology basis, geometric nonvanishing, or independence modulo relations. No semantic defect was found in the scoped existing graph definitions.

### Verification

The final revision passed:

```bash
lake build AxiomaticGW.Tautological.GraphEnumeration AxiomaticGWTest.Tautological.GraphEnumeration
lake build
lake test
lake lint
lake env lean /tmp/gw_graph_enumeration_axioms.lean
git diff --check
```

The targeted build completed 1,469 jobs, the full build 2,629 jobs, and tests 2,637 jobs. Lint passed. The only Lean warning was the pre-existing private-module warning in `AxiomaticGWTest/Basic.lean`. The temporary axiom audit checked the vertex bound, exact decoration round-trip, `mem_boundedStrata`, and decorated isomorphism checker; all depend only on `propext`, `Classical.choice`, and `Quot.sound`. The touched graph area contains no placeholders, declared axioms, or `native_decide`.

Kernel-checked fixtures cover the unstable empty corpus, labelled genus-zero four-point boundaries and psi classes, positive kappa weights, genus-one one-point strata, and the unmarked genus-two corpus through codimension two. The latter has twelve formal strata in total, including eight of codimension two, agreeing in count with the installed admcycles fixture. Count agreement alone is not a checked coordinate correspondence or a geometric certificate.

### Remaining risk and next gate

A diagnostic using the earlier implementation completed cases through genus zero, five markings, codimension two, but was stopped while computing codimension three after the candidate construction was optimized. This partial run is not acceptance evidence for the full planned range $g\leq2$, $n\leq6$, codimension at most three. Establish practical execution of that range next, then bind concrete graph coordinates and normalization witnesses to certificate exchange. Geometric vanishing and relation proofs remain separate obligations. The overall R0--R8 goal remains active.

## 2026-10-01: R1/R2 partial surface and finite-computation implementation

**Status:** The delivered algebra, query, and finite-computation modules are verified; R1 and R2 remain incomplete. No implementation commit has been created for this revision.

### Scope and delivered API

The review covers the four `Surfaces` modules, `WeightedCurveClass.lean`, `GraphIsomorphisms.lean`, and their regression tests. The [declaration map](../MathematicsToLean.md#r1r2-fixed-surfaces-and-executable-finite-data) and [geometric-input ledger](../mathematics/SurfaceReconstructionInputs.md) separate the proved algebra from the remaining geometric obligations.

- `SurfaceCohomology` constructs the cup-product ring, perfect trace pairing, basis, and multiplicative grading. `SurfaceTarget` fixes the three targets and their complete curve coordinates. `divisorPairing_firstChernDivisor` identifies the algebraic Chern pairing with curve energy; the elliptic parameters are $(3+r)/24$ and $-\int D c_1/24$.
- `SurfaceQuery` uses actual basis states and the existing numerical invariant. Signed dimension checks imply vanishing under `SurfaceTheoryIdentification`. **Medium boundary issue resolved:** `checkedEval` rejects degree-zero curve-unstable requests, while retaining positive-degree unstable arities. `SurfaceSeed.SeedValues` states exactly 4, 7, and 10 finite initial-value obligations for the three targets; it supplies no reconstruction oracle.
- `WeightedCurveClass.bounded` and `splittings` are executable and proved equal to the abstract `EffectiveCurveMonoid` sets. Graph isomorphism enumeration is equivalent to the existing isomorphism types; automorphism counts are invariant under changing presentation, and a successful check implies equality in the existing stratum quotient.

No further mathematical defect was found in the scoped review of the target formulas and source-listed seeds. Existing stable laws and graph syntax remain unchanged. The additions prove algebra and finite computation, not a geometric surface GW theory or the sufficiency of the seed list.

### Verification

Final integration passed:

```bash
lake build
lake test
lake lint
git diff --check
```

The build completed 2,587 jobs and the tests 2,594 jobs, with only the pre-existing `AxiomaticGWTest/Basic.lean` private-module warning. Lint and whitespace checks passed. Audited key results depend only on the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.

Kernel-checked fixtures verify negative exceptional self-intersections, distinct equal-energy classes, all eight ordered splittings of the two-point blowup's line class, and bounded-class counts $5,49,455$ through energy twelve. Graph tests cover loop branch swaps, repeated decorations, kappa monomials, fixed external labels, and automorphism counts. Query tests check the signed dimension and geometric domain, including the positive-degree two-point line and unmarked exceptional seeds. These are finite regressions, not reconstructed GW tables.

### Remaining risk and next gate

R1 still requires the geometric target and seed identifications, a complete seed-sufficiency audit, and the historical reference environment. The exploration environment is now installed: native macOS arm64 Sage 10.9, admcycles 1.4, and Python 3.12.14. Its conda and pip inputs are hash-pinned, dependency checks pass, and two fresh-cache exact smoke runs produced identical output. The [Sage/admcycles note](../references/AdmcyclesEnvironment.md) records commands, scope, and the remaining upstream deprecation warning. The [R2 follow-up](#2026-10-01-r2-bounded-formal-stratum-enumeration) supplies enumeration and completeness of bounded formal strata; execution of the full initial test range remains open. These are the next gates before verified strata operations and certificate exchange; numerical reconstruction remains R6/R7 work.

## 2026-10-01: R0 numerical unstable sectors and exceptional equations

**Status:** Implemented and verified within the numerical-interface and finite-boundary-fixture scope. No implementation commit has been created for this revision.

### Scope reviewed

The review covers `GW/Descendants/Equations.lean`, `FullPotential.lean`, the stable descendant and integration interfaces, their public regression examples, and [R0 of the reconstruction plan](GWReconstructionPlan.md#r0-correct-normalization-and-unstable-sectors). The genus-one exceptional signs were checked against [Tseng, Theorem 1.1, equations (1.3)--(1.4)](https://arxiv.org/pdf/0912.3580). The declaration map is [M9 in the mathematics-to-Lean map](../MathematicsToLean.md#m9-potentials-and-equations).

### Findings and revisions

- **Critical:** The previous unstable string law omitted the degree-zero three-point metric correction and contradicted normalized three-point integration. Degree-zero unstable correlators now use zero conventions, and `stringCorrection` carries the metric exactly at genus zero, degree zero, two remaining markings, and zero cotangent powers.
- **Critical:** The previous unstable dilaton law forced the exceptional genus-one point value to zero. It also truncated the negative genus-zero coefficients. `dilatonCoefficient` is signed, and `dilatonCorrection` supplies a target-dependent scalar only at genus one, degree zero, and no remaining markings.
- **High:** The supplied unstable numerical family had no relabelling or dimension compatibility. The revised package requires both and exposes `invariantMap`, `invariant_relabel`, and `invariant_eq_zero_of_degree_ne` for the full family. Stable values remain the existing integrated descendant classes.
- The separate `FullDescendantDivisorLaw` records unstable-base divisor recurrences and derives a global equation using the unchanged stable divisor law. Its corrections use the actual integrated genus-zero primary cubic and an explicit genus-one linear functional, without assuming that an arbitrary divisor action is cup product.

### Mathematical effect and migration

The stable string, dilaton, and divisor statements are unchanged. The false all-arity string/dilaton statements have been corrected rather than preserved. `UnstableDescendantConventions` constructors now supply `unstable_zero`, relabelling, dimension compatibility, and `genusOneDilaton`. `zeroPoint_zero` and `onePoint_zero` are derived lemmas; the retained `twoPoint_zero` name now concludes zero instead of the metric. The calibration identity is separate and unchanged.

For a geometric smooth projective target, the genus-one inputs have values $+\chi(X)/24$ and $-\frac1{24}\int_X D\,c_{\dim X-1}(TX)$. Their geometric interpretation remains a hypothesis to be supplied by a target model. In particular the point constant $1/24$ is not universal. The positive sign follows Tseng and point normalization; [Wennink's Lemma 4.10](https://arxiv.org/pdf/2210.04038) prints a conflicting negative dilaton sign.

### Verification

The following commands have passed:

```bash
lake build AxiomaticGW.GW.Descendants.Exceptional
lake build AxiomaticGW.GW.Descendants.FullPotential
lake build AxiomaticGW.GW.Descendants.FullDivisor
lake env lean AxiomaticGWTest/GW/Exceptional.lean
lake build
lake test
lake lint
git diff --check
```

The R0 integration build completed 2,579 jobs, and `lake test` completed 2,582 jobs with only the pre-existing `AxiomaticGWTest/Basic.lean` private-module warning. Lint and whitespace checks passed. Direct boundary-test elaboration reported no warnings. The divisor correction and global equation axiom audits reported only standard Lean axioms.

The finite numerical fixtures test normalized genus-zero three-point value one, positive genus-one point value $1/24$, all genus-zero zero/one/two-marking transitions, genus-one zero-marking transitions, the signed positive-degree chain $1,-2,2,0$, exceptional support, and swapped metric labels. Distinct scalar fixtures $3/24,4/24,5/24$ test parameter dependence for the planned surfaces; their geometric identifications belong to R1.

### Remaining risk and next gate

These fixtures verify the exceptional equations against explicit finite data. They do not construct an all-genus geometric point model or a positive-degree surface theory. R1's target algebra and geometric-input/finite-seed audit and R2's finite computation work have started without complete-stage acceptance. Full numerical reconstruction models remain R6/R7 work.

## 2026-07-18: Decorated tautological strata and Getzler relation layer

**Status:** Implemented for combinatorial syntax, formal relation quotients, realization factoring, and low-genus arithmetic; the geometric product and relation proofs remain open.

### Scope reviewed

The review covered the existing `StableGraph`, `StableCurveCohomology`, tautological-class, ancestor, and point-target APIs; every new declaration and its public imports; and the conventions in Getzler's arXiv TeX source and the `admcycles` TeX manual. The source audit fixed the raw decorated-stratum convention $[\Gamma,\alpha]=(\xi_\Gamma)_*\alpha$ without division by $|\operatorname{Aut}(\Gamma)|$, the node self-intersection factor $-\psi_h-\psi_{h'}$, the low-genus values, and the exact Getzler coefficient vector. No SageMath or `admcycles` package was installed.

### Findings and revisions

- **High:** The first graph-isomorphism draft preserved an artificial ordering of the two branches of each edge. `StableGraphCode.Iso` now carries an independent `Fin 2` equivalence for every edge, and decorated isomorphisms transport internal psi powers through that branch equivalence. A regression example identifies loop strata whose sole psi decoration lies on opposite presentations of the same branch.
- **Medium:** The abstract cohomology API had no universe-small basis syntax for general decorated stable graphs or a checked path from formal relations to a geometric target. The new layer defines decorated graph isomorphism classes, codimension, one-vertex strata, `StrataModule`, homogeneous and dimension-relation submodules, known-relation quotients, `StrataRealization`, and the kernel condition that factors a realization through a quotient.
- **Medium:** Calling the free module a tautological ring before implementing common refinements and excess intersection would overstate the construction. `CertifiedStrataProduct` is therefore a proof-carrying contract with explicit grading, commutativity, associativity, and unit fields; no global multiplication or ring instance is installed.
- **Medium:** Getzler's named cycles use an orbifold normalization that is not identical to the raw gluing-pushforward convention. `GetzlerStrataEncoding` requires an explicit normalized codimension-two cycle for each of the seven names, and `GetzlerRelationGeometry` keeps geometric validity separate from formal quotient vanishing.
- **Low:** The point-target layer lacked an executable genus-zero reference formula. `PointTarget.genusZeroPsiValue` now implements the standard multinomial value and verifies the first three closed cases with explicit finite reductions; `GenusZeroPsiFormula` is the separate certificate linking those values to abstract integration.

### Mathematical effect

No existing theorem statement or assumption changed. The new quotient proves only that supplied relation generators vanish formally. It does not prove that those relations hold in cohomology or generate the full tautological ideal. The exact Getzler linear combination is available to downstream theorems, while its normalized graph encoding and geometric proof remain visible obligations.

### Delivered API

- `StableGraphCode`, `StableGraphCode.Iso`, `DecoratedStableGraph`, `DecoratedStableGraph.Iso`, and `TautologicalStratum`.
- `TautologicalStratum.oneVertex`, `TautologicalStratum.fundamental`, and their genus and codimension theorems.
- `StrataModule`, `StrataModule.degree`, `dimensionRelations`, `KnownRelationsQuotient`, `CertifiedStrataProduct`, `ProductIdeal`, `StrataRealization.dimensionRelations_le_kernel`, and `StrataRealization.factor`.
- `GetzlerStratum`, `GetzlerStrataEncoding`, its exact relation and known quotient, `GetzlerRelationGeometry`, and the realization-kernel factorization theorem.
- `PointTarget.genusZeroPsiValue`, the initial arithmetic checks, and `PointTarget.GenusZeroPsiFormula`.

### Verification

The final validation passed:

```bash
lake build
lake test
lake lint
git diff --check
rg --pcre2 -n '\b(?:simp|simpa|simp_all)(?! only)(?:\s|\[|$)' AxiomaticGW AxiomaticGWTest -g '*.lean'
rg -n '\b(sorry|admit)\b|^\s*(axiom|unsafe|opaque)\b|sorryAx|admitAx' AxiomaticGW AxiomaticGWTest
```

`lake build` completed 2,577 jobs, `lake test` completed 2,578 jobs, and `lake lint` passed. The test command emitted only the pre-existing private-module warning for `AxiomaticGWTest/Basic.lean`. The explicit-simplifier and placeholder/axiom scans returned no matches, and `git diff --check` passed. `#print axioms` for the graph genus theorem, realization factorization, Getzler quotient vanishing, and the genus-zero arithmetic check reported only `propext`, `Classical.choice`, and `Quot.sound`.

### Remaining risk and next gate

The principal remaining risk is mathematical rather than syntactic: a native finite enumeration of common refinements and excess factors has not constructed `CertifiedStrataProduct`; the seven normalized Getzler cycles are not yet expanded into decorated stable graphs; and no `StrataRealization` has been constructed from an actual Chow or cohomology theory of $\overline{\mathcal M}_{g,S}$. The next priority is the explicit low-genus graph encoding for `Mbar(0,4)`, `Mbar(1,1)`, and the seven Getzler cycles, followed by a checked low-genus product table. SageMath/`admcycles` may later serve as an external oracle, but the Lean kernel must check the resulting certificates.

## 2026-07-18: Literature-based mathematical-note revision

**Status:** Implemented and locally verified.

### Scope reviewed

The review covered the ten numbered mathematical notes, the point-target note, the project-wide mathematical overview, the mathematics-to-Lean map, and the current roadmap descriptions. Formulas and terminology were checked directly in the project-local arXiv TeX sources: Kontsevich--Manin for GW classes, inverse-metric splitting, grading, unit, divisor, quantum multiplication, and WDVV; Dumitrescu for the oriented two-dimensional TFT/Frobenius-algebra correspondence; Givental for descendants, ancestors, the two-point calibration, symplecticity, total potentials, and Fock-space qualifications; and Mulase--Safnuk for psi-class intersections and the DVV/Virasoro normalization.

### Findings and revisions

- **Medium:** The geometric-realization notes wrote a pushed-forward virtual homology or Chow class as though it were already a cohomology class. They now define the pushed-forward class first and apply Poincare duality explicitly when available.
- **Medium:** Several central constructions were described narratively without the formulas needed to determine their meaning. The notes now define copairing contraction, separating and nonseparating inverse-metric sums, the TFT handle operator, stable-graph gluing, the stable-curve and stable-map cotangent-line corrections, the exact GW output codimension, fixed-class and Novikov quantum products, WDVV, the $S$-operator and its symplectic identity, and the stable string, dilaton, and descendant divisor equations.
- **Low:** Phrases such as “the tensor inserted at a node,” “wrong ordinary dimension,” and schematic boundary corrections obscured the mathematical maps and hypotheses. These were replaced by basis-independent definitions, explicit source and target classes, and stated implementation limits.
- No critical or high-severity defect was found. The source ledger now records which topics were checked in each TeX archive, and the roadmap, overview, and mathematics-to-Lean map use the same current terminology.

### Mathematical effect

No Lean definition, theorem statement, proof, assumption, instance, coercion, or public API changed. The documentation now distinguishes homology from cohomology, stable-map descendants from stable-curve ancestors, coefficient families from completed tensor products, and supplied comparison carriers from geometric theorems. These are corrections and clarifications of the described mathematics, not changes to the formalized propositions.

### Verification

The revision passed:

```bash
lake build
lake test
lake lint
git diff --check
rg -n '\b(sorry|admit)\b|^\s*(axiom|unsafe|opaque)\b|sorryAx|admitAx' AxiomaticGW AxiomaticGWTest
```

The full build completed 2,570 jobs. `lake test` passed with only the pre-existing private-module warning for `AxiomaticGWTest/Basic.lean`, and library lint passed. The source scan returned no matches. Stateful audits of every changed Markdown file found no manually wrapped prose paragraphs, unbalanced or attached display-math delimiters, stale renamed anchors, or broken tracked local links.

### Remaining risk and next gate

The literature audit checks the mathematical exposition and its agreement with the current Lean interfaces; it does not construct or verify the missing geometric hypotheses. The principal remaining risk is still the realization of stable-curve and stable-map geometry: graph pullbacks, tautological push-pull identities, rational-tail factorization, virtual classes, refined diagonal pullback, and the comparison packages are represented abstractly. The next priority is a concrete geometric instance of one of those optional packages, with the stabilization comparison as the most direct target.

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

**Follow-up (2026-10-01):** The R0 audit found that the original full-potential string/dilaton extension had incorrect exceptional equations despite passing the checks above. The R0 revision corrects their statements and adds explicit numerical normalization fixtures; see the verified scope in the [R0 entry](#2026-10-01-r0-numerical-unstable-sectors-and-exceptional-equations).

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

**Follow-up:** The separate stable-graph carrier, arbitrary-background genus-zero WDVV, rational-tail comparison data, and full-potential extension were implemented in `9a3d625`. Decorated stable-graph syntax, formal relation quotients, the named Getzler generator, and low-genus psi values were added in the later tautological-strata revision; the native product, geometric relation proofs, other geometric limitations, and mixed-completion limitations still apply.

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

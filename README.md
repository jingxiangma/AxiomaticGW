# AxiomaticGW

Lean formalization of the algebraic foundations of axiomatic Gromov--Witten theory.

The repository is the home of the full project, developed in verified layers. The Frobenius/TFT and full CohFT foundations are implemented, as are the axiomatic GW interfaces for tautological ancestors, positive effective curve classes, beta-resolved primary classes, Novikov coefficients, small and big quantum products, stable graphs, decorated tautological-stratum syntax and relation quotients, stable-map descendants, rational-tail descendant--ancestor comparison data, stable and explicitly extended descendant potentials, Laurent total free energies, and an algebraic output carrier for future virtual geometry.

> **Project status:** active, research-stage development. Conditional reconstruction now covers arbitrary finite descendants in genera zero through two on all three fixed surfaces. The genus-zero/one primary suites through energy twelve and the full fixed plane genus-two suites have checked certificates; the blowup genus-two numerical suites and full semisimple CohFT interoperability remain incomplete. Optional packages expose stable-graph pullbacks, arbitrary-background genus-zero WDVV and big-quantum-product associativity, rational-tail descendant--ancestor factorization with its two-point calibration, and a proof-carrying interface for a future common-refinement strata product. The R0 numerical-extension repair is implemented and verified: it separates auxiliary zero conventions from exceptional string/dilaton/divisor terms and preserves the existing stable laws. The free strata module includes the seven normalized Getzler cycles as 33 explicit labelled graphs, the exact relation vector, and a formal known-relations quotient, but no geometric proof of that relation or all-genus product enumeration is claimed. Concrete stable-curve and stable-map moduli, virtual classes, and proofs that geometric theories instantiate the abstract packages remain future work.

> **Scope:** Stable-curve targets are abstract even graded cohomology algebras and are not assumed finite free. Novikov completion is therefore coefficientwise for cohomology-valued classes; numerical coefficients and the finite-free state space carry the completed convolution operations.

The research command accepts JSON or Sage input and exports a Lean theorem for the geometric value under the stated hypotheses. The worked genus-two plane quartic with thirteen point insertions gives $27$. On the two blowups, all 292 energy-one few-marking requests have checked reconstructions and full equivariant comparisons. The canonical tables reach energy three on $F_1$ and energy one on the two-point blowup. The guide also shows how to search for and certify a relation using admcycles. [Research query guide](notes/references/ResearchQueries.md) · [Energy-one comparison](AxiomaticGW/GKM/Fixtures/GenusTwoEnergyOneReplay.lean) · [Energy-three table](AxiomaticGW/Surfaces/Fixtures/F1PlaneLineL24Replay.lean)

## Project progress

The genus-two exceptional examples distinguish the full two-character function from its ordinary value. On the primitive curve $E_1$ of the two-point blowup, $\langle\tau_3(E_1)\rangle^T_{2,E_1}=(x+y)/240$ in the signed fixed-locus calculation and the ordinary value is zero. In class $2E_1$ the reconstructed ordinary value is $3/320$, which the pinned producer also returns as a constant equivariant function. The worked queries include the exact inputs and offline replay commands. [Exceptional examples](notes/references/ResearchQueries.md#genus-two-descendants-on-a-doubled-exceptional-curve)

The [mathematics-to-Lean map](notes/MathematicsToLean.md) connects the mathematical notes to source modules and principal declarations. The [implementation progress record](notes/milestones/ImplementationProgress.md) provides dated milestone scope, verification evidence, implementation commits, deferred work, and the next development gate. The [roadmap](notes/milestones/AxiomaticGWRoadmap.md) remains the source of truth for current milestone status and ordering.

The [GW reconstruction plan](notes/milestones/GWReconstructionPlan.md) fixes the first research applications as genus-two reconstruction for $\mathbb P^2$, $\mathbb F_1$, and $\mathrm{Bl}_{p,q}\mathbb P^2$, with Sage/admcycles used for exploration and Lean for certificate checking. R0 is complete within its numerical-interface and finite-fixture scope. R1 has verified target algebra and query/finite-seed interfaces, with geometric identification still open and conditional finite-seed sufficiency supplied by the reconstruction theorems below. R2 is accepted for executable curve/graph computation, completeness proofs, and the full initial native graph corpus. Sage 10.9 and admcycles 1.4 are installed with hash-pinned inputs. A fixed unmarked genus-two relation exporter now produces claim-bound, kernel-checked formal-span proofs and passes 23 replay regressions without Sage. General relation provenance, geometric identifications, outstanding numerical certificates and the complete research workflow remain open. Later progress paragraphs below supersede the then-open gates of earlier steps.

The goal also requires [compatibility with `gkm_localization`](notes/milestones/GWReconstructionPlan.md#gkm-and-semisimple-cohft-exchange-contract) for semisimple CohFT inputs. The [initial GKM bridge](notes/references/GKMExchange.md) exports exact target data and nine numerical regressions for all three surfaces, with 34 candidate-input checks. Lean constructs the fixed-point Frobenius algebra, proves full CohFT transport, and replays claim-bound certificates for the classical state tables, full curve coordinates, and all invariant-edge conventions, including regular ordinary comparisons. Imported CohFT classes, geometric comparison, stable-map localization-graph derivations, and certification of numerical GW queries remain open. The application targets and benchmark bounds remain fixed.

The marked four-point WDVV frame now has three explicit, distinct raw boundary graphs, a Sage-searched two-row witness, and offline Lean replay with 30 exchange regressions. Its GW evaluation is derived from named geometric boundary-class equality and primitive push-pull/realization laws, preserving all labels and full curve-class splittings. This provides a checked relation-to-GW path; full descendant reconstruction, general relation provenance, and class-level GKM import remain open.

The seven normalized Getzler cycles now have a fixed 33-column graph frame, checked marking orbits and automorphism factors, and a Sage-searched consequence isolating $\delta_{2,3}$. Offline replay passes 36 exchange tests. Every column now has an explicit gluing expression, and its GW integral with arbitrary external ancestor powers is proved equal to the corresponding iterated full-class contraction. Powers follow their marking bijections; new node powers are zero. The final replay theorem uses the named geometric Getzler relation, normalized-cycle identification, primitive realization/Gysin laws, and the existing cotangent pullbacks. The same checked relation now extends to any finite number of additional markings: primitive universal-curve/gluing base change derives every raw placement, including its multiplicity. Ancestor powers are inserted after that pullback. Stable-map descendant comparison and genus-two reconstruction remain open.

Surface primary reduction now handles arbitrary insertion multiplicities, including the genus-zero and genus-one degree-zero sectors. Four reduced Getzler equations are checked directly against Lean's complete graph evaluator, using exact rational terms and the Sage-generated candidates. Under the documented geometric laws and finite seeds, this proves the genus-one plane line invariant with three points and the genus-one two-point invariant of $E_1+E_2$ on the two-point blowup are zero. The general primary genus-one reconstruction below extends these finite deductions; genus-two reconstruction, descendants and the higher-genus benchmark suites remain open; see the [numerical theorems](AxiomaticGW/Surfaces/LowDegree.lean).

Three additional Getzler requests in class $2E_i$ now give [exceptional-class deductions](AxiomaticGW/Surfaces/Exceptional.lean) for $E$ on $\mathbb F_1$ and $E_1,E_2$ on the two-point blowup: $N_0(2E_i;\mathrm{pt})=N_1(2E_i;\mathrm{pt}^2)=N_1(E_i;\mathrm{pt})=0$. All nine graph identities are checked in Lean. The last deduction uses the existing seed $N_0(E_i)=1$; the seed list is unchanged.

The original checked WDVV relation now supports [arbitrary additional markings and ancestor powers](AxiomaticGW/Tautological/WDVVForgetful.lean). Its genus-zero surface consumer needs no elliptic seeds. Exact graph certificates give the [plane conic value](AxiomaticGW/Surfaces/PlaneGenusZero.lean) $N_0(2H;\mathrm{pt}^5)=1$, the [blowup ruling and strict-line values](AxiomaticGW/Surfaces/BlowupGenusZero.lean), and the [genus-one base case for $L=H-E_1-E_2$](AxiomaticGW/Surfaces/StrictLine.lean). These nine further numerical deductions use the existing finite seeds and explicit geometric laws. Arbitrary descendants, genus-two reconstruction and applications, and the remaining GKM gates are still open; see the [validation record](environments/surface-wdvv-validation.json).

For primary genus-zero equations, [full curve-class support](AxiomaticGW/Surfaces/GenusZeroSupport.lean) now proves that the requested singleton is the only possible same-energy term. Every variable left after removing it has strictly lower positive energy, for arbitrary classes, labels and marking counts. The [reconstruction-step theorem](AxiomaticGW/Surfaces/GenusZeroStep.lean) derives the value from the original checked WDVV relation whenever its exact leading coefficient is proved nonzero.

The [genus-zero coefficient evaluator](AxiomaticGW/Surfaces/GenusZeroPivot.lean) computes that leading coefficient using only the two splits with a degree-zero component. The [point-marking proof](AxiomaticGW/Surfaces/GenusZeroMarkings.lean) further computes it on the original three WDVV graphs, without enumerating the added-marking placements: degree-zero primary vertices vanish after receiving an extra marking. Equality to the complete expansion preserves the signed inverse metric and all original multiplicities.

The [uniform reconstruction step](AxiomaticGW/Surfaces/GenusZeroUniform.lean) proves that the `H,H,pt,pt` request with energy minus four added points has leading coefficient exactly one on all three surfaces whenever the energy is at least four. Exhaustive kernel checks cover every energy-three class on F₁ and the two-point blowup; the plane's energy-three class is its existing line seed. These proofs add no geometric assumption or seed; see the [validation record](environments/surface-genus-zero-uniform-validation.json).

The [terminating genus-zero evaluator](AxiomaticGW/Surfaces/GenusZeroRecursion.lean) now computes point invariants and arbitrary primary basis multisets on all three surfaces. Its [soundness theorem](AxiomaticGW/Surfaces/GenusZeroReconstruction.lean) derives the complete initial sector from the original WDVV relation and only the existing line and exceptional seeds, then proves agreement with every supplied surface theory satisfying the stated geometric laws. This establishes finite-seed sufficiency and uniqueness for primary genus zero, including degree zero and positive-degree unstable arities. The [bounded-table implementation](AxiomaticGW/Surfaces/GenusZeroTable.lean) reuses lower-class values and is proved equal to that evaluator at every class within the bound. The [compressed evaluator](AxiomaticGW/Surfaces/GenusZeroExpansion.lean) now replaces ordered point placements by binomially weighted distributions, with a universal equality proof to the full original expression. The complete [plane primary genus-zero suite](AxiomaticGW/Surfaces/PlanePrimaryBenchmarks.lean) through energy twelve is kernel checked: degrees one through four give 1, 1, 12, 620. The finite certificates below now complete the positive-class genus-zero primary subset on all three targets. Arbitrary descendants, genus-two reconstruction and the remaining GKM gates stay open; see the [reconstruction record](environments/surface-genus-zero-reconstruction-validation.json) and [compression record](environments/surface-genus-zero-compression-validation.json).

The [finite certificate checker](AxiomaticGW/Surfaces/GenusZeroCertificate.lean) now accepts all 506 positive-class genus-zero point queries through energy twelve: 4 on P², 48 on F₁, and 454 on the two-point blowup. All zero answers and three additional auxiliary zero-class entries are checked. Exact coverage, each selected WDVV equation, and equality to the terminating evaluator are proved in Lean. Candidate values are generated by a separate implementation of Kontsevich–Manin formula (5.18); both methods share WDVV and the low-energy normalizations, as recorded in the [full query manifest](environments/surface-genus-zero-primary-tables.json).

For certified bounded lookups:

```lean
import AxiomaticGW.Surfaces.GenusZeroBenchmarks
open AxiomaticGW SurfaceGenusZero

#eval pointBenchmark? .plane ![4]             -- some 620
#eval pointBenchmark? .hirzebruchOne ![2, 5]   -- some 640
#eval pointBenchmark? .blowupTwo ![3, 4, 5]    -- some 18132
#eval pointBenchmark? .plane ![5]             -- none: beyond the certified bound

example : pointValue .blowupTwo ![3, 4, 5] = 18132 := by
  rw [← pointBenchmarkValues_eq .blowupTwo ![3, 4, 5] (by decide +kernel)]
  decide +kernel
```

The blowup coordinates are `(E,F)` and `(E₁,E₂,L)`: these two examples represent 5H−3E and 5H−2E₁−E₂, each with eleven point insertions. `pointBenchmark?_sound` binds every returned answer to its full positive class and the proved evaluator. `pointBenchmark_checkedEval` connects it to the supplied GW invariant under the original WDVV certificate, geometric laws and finite genus-zero seeds. The [regressions](AxiomaticGWTest/Surfaces/GenusZeroCertificate.lean) consume the actual Sage-exported WDVV presentation. Three existing GKM numerical cases also agree; this does not certify imported CohFT classes.

Regenerate candidates with `python3 scripts/export_surface_genus_zero_tables.py`, check reproducibility with `--check`, and replay offline with `lake build AxiomaticGW.Surfaces.GenusZeroBenchmarks`. Sage and network access are unnecessary for replay. The [validation record](environments/surface-genus-zero-certificate-validation.json) records resources, independent-code limits, rejected claims and unchanged geometric assumptions. The genus-one extension below completes its primary numerical subset as well; genus-two reconstruction, descendants and the required GKM/CohFT integration remain open.

[Primary genus-one reconstruction](AxiomaticGW/Surfaces/GenusOneReconstruction.lean) now has termination, soundness and uniqueness proofs for all three surfaces, at arbitrary full class and primary marking multiplicity. The four-hyperplane Getzler family with energy minus two additional points has leading coefficient exactly −9 whenever energy is at least two. Genus-zero dependencies may have the original energy; every remaining genus-one dependency has strictly smaller energy. The entire energy-at-most-one initial sector follows from the existing WDVV/Getzler certificates and finite line, exceptional and degree-zero elliptic seeds. No recurrence or extra seed is assumed. This establishes primary genus-one determination under the named geometric inputs; see the [theorem validation record](environments/surface-genus-one-reconstruction-validation.json).

The [joint certificate checker](AxiomaticGW/Surfaces/GenusOneCertificate.lean) now verifies all 506 positive-class genus-one point queries through energy twelve, retaining all 473 zero answers and three additional auxiliary zero-class entries. It reuses the certified genus-zero tables, preserves rational terms at the original energy, and proves equality to the original elliptic evaluator. Binomial compression includes self-gluing, dimension pruning selects the unique admissible point counts, and a proved symmetry reduction sums the original 33 labelled weights into seven contractions. The geometric laws, finite seeds and target bounds are unchanged.

```lean
import AxiomaticGW.Surfaces.GenusOneBenchmarks
open AxiomaticGW SurfaceGenusOne

#eval pointBenchmark? .plane ![4]             -- some 225
#eval pointBenchmark? .hirzebruchOne ![2, 5]   -- some 240
#eval pointBenchmark? .blowupTwo ![2, 3, 5]    -- some 20
#eval pointBenchmark? .plane ![5]             -- none: beyond the certified bound

example : pointValue .plane ![4] = 225 := by
  rw [← pointBenchmarkValues_eq .plane ![4] (by decide +kernel)]
  decide +kernel
```

The blowup examples represent 5H−3E with twelve points and 5H−3E₁−2E₂ with ten points. The [frozen manifest](environments/surface-genus-one-primary-tables.json) uses a separate implementation of [Chaudhuri–Das (3.1)](https://arxiv.org/html/1901.00839v2#S3), with published plane and blowup anchors. It shares Getzler's relation, rational inputs and geometric base values with the proof path; this is not independent verification of those foundations. The [regressions](AxiomaticGWTest/Surfaces/GenusOneCertificate.lean) consume both actual Sage-exported relation presentations.

Regenerate with `python3 scripts/export_surface_genus_one_tables.py`, check reproducibility with `--check`, and replay offline with `lake build AxiomaticGW.Surfaces.GenusOneBenchmarks`. The [validation record](environments/surface-genus-one-certificate-validation.json) records complete coverage, kernel checks, rejected corrupt claims and axiom audits. The descendant extensions below complete the conditional numerical part of R6. Genus two, geometric input validity and the mandatory GKM/CohFT integration remain open.

The [descendant arity adapter](AxiomaticGW/Surfaces/DescendantStabilization.lean) now reduces every positive-degree curve-unstable request to supplied stable descendant values, with a computed termination bound, soundness and uniqueness proofs. The abstract divisor correction is proved to be surface cup multiplication from the existing string/divisor laws and classical cubic. Full curve classes and the geometric query domain are preserved. This adapter adds no numerical seeds; its genus-zero and genus-one callbacks are now supplied by the reconstructions below. See the [adapter validation record](environments/surface-descendant-stabilization-validation.json).

The [low-genus psi expansion](AxiomaticGW/Tautological/PsiBoundaryExpansion.lean) now derives genus-zero and genus-one ancestor equations for arbitrary added markings and arbitrary remaining psi powers. Genus zero starts from three-point dimension vanishing; genus one consumes a [Sage-generated certificate](AxiomaticGW/Tautological/Fixtures/GenusOnePsiReplay.lean) for the raw one-point loop coefficient 1/24. Primitive forgetting and gluing laws give the boundary expansion and full-class GW contractions. Geometric row validity and identification of the primitive tail divisor are explicit inputs. A complete numerical descendant evaluator remains open; see the [validation record](environments/low-genus-psi-validation.json) and the mixed comparison below.

The [two-point calibration](AxiomaticGW/GW/Descendants/TwoPointCalibration.lean) is constructed from actual numerical descendants by raising the node index. Its complete first coefficient is reconstructed from the existing finite genus-zero seeds on all three surfaces, with native GKM agreement on all 564 entries through energy three. The [mixed comparison](AxiomaticGW/Geometry/RationalTailComparison.lean) now derives the actual main/tail formula from primitive virtual cotangent, diagonal and stabilization laws. These remain explicit geometric inputs.

The [calibration recursion](AxiomaticGW/Surfaces/CalibrationRecursion.lean) now computes every inverse-loop power and full curve class from that first coefficient and classical cup multiplication, with a Lean soundness proof and no stable-descendant callback. Native GKM agrees on [30 higher-coefficient requests](AxiomaticGW/GKM/Fixtures/HigherCalibrationReplay.lean), including a conic and multiple exceptional classes; all 582 incoming ordinary entries are kernel checked. The subsequent genus-one construction supplies its stable descendants. Full symplecticity, primary deformation, genus two and imported semisimple CohFT classes remain open. See the [workflow](notes/references/GKMExchange.md#higher-calibration-recursion) and [validation record](environments/mixed-descendant-comparison-validation.json).

The [finite mixed reduction](AxiomaticGW/Surfaces/MixedAncestorReduction.lean) now turns every curve-stable descendant query into exact rational terms in the existing ancestor variables, in any genus. It preserves all ancestor powers and full classes, and uses the proved calibration recursion. The [three-marked genus-zero evaluator](AxiomaticGW/Surfaces/ThreePointDescendants.lean) closes this reduction using ancestor vanishing on the three-point rational curve and the existing primary reconstruction. It computes every class and descendant power on all three surfaces from the same finite seeds, with conditional geometric soundness and no value callback. All [27 native GKM cases](AxiomaticGW/GKM/Fixtures/ThreePointDescendantReplay.lean) pass kernel replay. This three-point sector is extended to all genus-zero arities below; see its [validation record](environments/mixed-ancestor-reduction-validation.json).

The [total genus-zero ancestor evaluator](AxiomaticGW/Surfaces/GenusZeroAncestors.lean) now lowers a positive cotangent power through the original geometric psi expansion. Every component has strictly smaller total psi degree, so the recursion terminates at the existing primary reconstruction. [Stable descendant reconstruction](AxiomaticGW/Surfaces/GenusZeroDescendants.lean) composes this with the finite mixed reduction. The [all-arity evaluator](AxiomaticGW/Surfaces/GenusZeroFullDescendants.lean) supplies arbitrary states to the existing stabilization adapter, covering every full effective class and descendant power on P², F₁ and Bl₂P², including positive-degree zero-, one- and two-marked queries. `SurfaceGenusZero.queryValue?_eq_checkedEval` proves soundness on the original geometric domain; zero-class unstable requests are rejected. The finite seeds and explicit geometric assumptions are unchanged. All [34 additional native GKM values](AxiomaticGW/GKM/Fixtures/GenusZeroDescendantReplay.lean) pass kernel replay. The following extension supplies genus-one descendants; genus two and the full semisimple CohFT bridge remain required; see the [validation record](environments/genus-zero-descendant-validation.json).

The [genus-one ancestor evaluator](AxiomaticGW/Surfaces/GenusOneAncestors.lean) now closes the elliptic family by decreasing total psi degree in the original raw loop/tail expansion. Rational components use the proved genus-zero family; elliptic primaries use the original Getzler reconstruction. Termination, sufficient-fuel independence and uniqueness are proved. The [full descendant evaluator](AxiomaticGW/Surfaces/GenusOneDescendants.lean) composes the mixed reduction, reconstructed calibration and anticanonical stabilization, with no new seed or supplied invariant family. Its final soundness theorem consumes the original geometric inputs and all three accepted relation presentations. All [41 additional native GKM claims](AxiomaticGW/GKM/Fixtures/GenusOneDescendantReplay.lean) pass kernel replay, including $\langle\tau_5(\mathrm{pt})\rangle_{1,2H}^{\mathbb P^2}=1/32$ and $\langle\tau_2(E)\rangle_{1,2E}^{\mathbb F_1}=-1/16$. The [validation and R6 audit](environments/genus-one-descendant-validation.json) records the conditional genus-zero/one reconstruction gate. Genus two, geometric input validity and full semisimple CohFT compatibility remain required.

The first [marked genus-two cotangent relation](AxiomaticGW/Tautological/GenusTwoPsiSquare.lean) now expresses $\psi_1^2$ on $\overline M_{2,1}$ as ten lower-genus boundary terms, with every node cotangent decoration retained. Its [Sage replay](AxiomaticGW/Tautological/Fixtures/GenusTwoPsiSquareReplay.lean) binds seventeen graph columns, six original 3-spin rows, one derived elliptic gluing row, both kappa-coordinate tables and the exact requested expression. Primitive realization laws give the class identity, higher one-marked powers and an ancestor reduction for any supplied class-valued CohFT. The [node-cotangent contraction](AxiomaticGW/Tautological/DecoratedGluingEvaluation.lean) now evaluates those terms from their actual decorated gluings. The [one-point surface evaluator](AxiomaticGW/Surfaces/GenusTwoOnePointAncestors.lean) computes every full class and power $2+k$ on all three targets, with soundness proved from the existing finite low-genus seeds and named geometric inputs. No genus-two value is supplied as a seed. These are stable-curve ancestors; primary and first-power sectors, multiple markings and stable-map descendants remain open. The [new audit](environments/genus-two-one-point-ancestor-validation.json) records the exact scope and numerical regressions; all fixed applications, benchmark bounds and full GKM requirements are unchanged.

The [two-marked cotangent-product relation](AxiomaticGW/Tautological/GenusTwoPsiProduct.lean) now expresses $\psi_1\psi_2$ on $\overline M_{2,2}$ as a complete 25-term boundary. Twenty-four terms have only genus-zero/one components. The remaining term is three times a rational tail carrying both markings, with psi on its one-marked genus-two component. [Source geometry](AxiomaticGW/Tautological/GenusTwoPsiProductSources.lean) derives the three boundary rows from existing component generators; ten explicitly identified original interior 3-spin vanishings on $\overline M_{2,2}$ remain geometric inputs. The [GW consumer](AxiomaticGW/Tautological/GenusTwoPsiProductGluing.lean) retains full classes, node powers and arbitrary further powers at both markings. This supplies a higher-power relation needed by the $L_{2,4}$ route, not a completed surface solver or new numerical seed. See the [audit](environments/genus-two-psi-product-validation.json).

The [genus-two psi pullbacks](AxiomaticGW/Tautological/GenusTwoPsiForgetful.lean) derive both complete relations with any number of added markings from their original geometric sources. Three [concrete pullbacks](AxiomaticGW/Tautological/Fixtures/GenusTwoPsiPullbacksReplay.lean), with 23, 53 and 62 nonzero terms, agree with Sage and have offline kernel replay. Every nonleading term is a kappa-free boundary with at most one psi factor. These inputs, rational psi relations and five WDVV corrections now feed the complete conditional L24 class equation below. The seeds and research completion gates are unchanged. See the [pullback audit](environments/genus-two-psi-pullbacks-validation.json).

The [complete L24 class relation](AxiomaticGW/Tautological/L24Relation.lean) now follows from the original BP and lower-arity source equations and explicit primitive geometry. Its [initial BP comparison](AxiomaticGW/Tautological/L24InitialClass.lean) checks all 306 signed pullback terms, proves the 198 local dimension vanishings across four psi contributions and cancels all 45 auxiliary graph classes after averaging. The unchanged 71 corrections give the full 721-term equation, retaining the 703 nonprimitive terms. The [GW extension](AxiomaticGW/Tautological/L24GW.lean) now derives its full decorated contraction with arbitrary added markings and ancestor powers. The [surface equations](AxiomaticGW/Surfaces/L24.lean) use the proved genus-zero/one algorithms and retain the remaining genus-two variables in an affine system. Their [first-descendant normalization](AxiomaticGW/Surfaces/GenusTwoNormalizedL24.lean) uses the same variables and signed rational-tail correction as normalized BP; higher powers retain their ancestor interpretation. The remaining blowup equations and dependency support, complete genus-two reconstruction and the full semisimple GKM bridge remain required. See the [class audit](environments/l24-initial-class-validation.json) and [surface validation](environments/surface-l24-validation.json).

The [published Belorousski–Pandharipande relation](AxiomaticGW/Tautological/BelorousskiPandharipande.lean) on $\overline M_{2,3}$ now has a complete Sage certificate and [offline Lean replay](AxiomaticGW/Tautological/Fixtures/BelorousskiPandharipandeReplay.lean). All twenty diagrams, six marking assignments including repetitions, graph automorphism factors and both kappa coordinate systems are checked. Four original interior 3-spin rows and sixteen actual separating pushforwards derive the relation under explicit source-row validity and primitive realization laws. The [GW equation](AxiomaticGW/Tautological/BelorousskiPandharipandeGW.lean) retains every full curve-class splitting, original node cotangent factor and external ancestor power. The [signed decorated forgetful extension](AxiomaticGW/Tautological/BelorousskiPandharipandeForgetful.lean) now derives the equation with any finite number of added markings and arbitrary upstairs ancestor powers. It includes the rational-tail corrections at cotangent-decorated node branches. Every output preserves codimension and the bound on component genus. The [new validation record](environments/decorated-forgetful-validation.json) includes exact raw-coordinate comparisons of 1,159 computed terms in 252 cases with Sage/admcycles. Nonzero surface pivots, the $L_{2,4}$ equation and complete genus-two numerical reconstruction remain open; no new numerical invariant is claimed.

The [surface BP expansion](AxiomaticGW/Surfaces/BelorousskiPandharipande.lean) now produces exact affine equations in genus-two ancestors on all three fixed targets, for any added-marking count and external powers. Dimension vanishing and the existing finite-seed algorithms remove lower-genus variables. Kernel proofs preserve full curve classes and show strict energy decrease after **all** input-class unknowns are separated. Three complete small equations have [offline kernel replay](AxiomaticGW/Surfaces/Fixtures/GenusTwoBP.lean); ten equations agree with independent Sage/admcycles contractions. These equations remain coupled: the plane-line sample has rank one with two input-class unknowns. They are progress toward reconstruction, not new invariant values or a proved invertible recursion. See the [validation record](environments/surface-bp-validation.json).

[First-power normalization](AxiomaticGW/Surfaces/OnePsiReduction.lean) now converts primary and one-power genus-two ancestors to stable-map point/first-descendant families, with the proved negative rational-tail correction and signed divisor cup products. The complete BP equations retain that interpretation under [affine substitution](AxiomaticGW/Surfaces/GenusTwoNormalizedBP.lean). On the two-point blowup, [two initial values](AxiomaticGW/Surfaces/GenusTwoDerivedInitialValues.lean) are derived from the original geometry and unchanged finite seeds: the degree-zero primary point and the cross-exceptional invariant $\langle\tau_1(E_1),\mathrm{pt}\rangle_{2,E_2}$ both vanish. Ten normalized equations and nonzero-tail probes agree with Sage/admcycles and the pinned native GKM calibration matrices. General genus-two recursion, all fixed suites and full semisimple CohFT interoperability remain open; see the [normalization audit](environments/surface-bp-normalized-validation.json).

The [normalized support and coefficient theorems](AxiomaticGW/Surfaces/GenusTwoNormalizedSupport.lean) now preserve affine genus-two support, dimension compatibility and effective full-class remainders through the ancestor comparison. After separating every input-class unknown, all other variable dependencies strictly decrease energy. Exact leading coefficients can be computed using only original-class ancestors and direct primary/first-descendant normalization; the smaller-class calibration corrections remain in the complete equation. The [nineteen-equation pilot](environments/genus-two-leading-exploration.json) includes every canonical primary/first-descendant column, even absent ones. Its sampled plane-line and F₁ fiber systems have ranks 2/3 and 2/4 respectively. These finite systems do not prove uniform reconstruction; see the [support audit](environments/genus-two-normalized-support-validation.json).

The [genus-two leading evaluator](AxiomaticGW/Surfaces/GenusTwoLeading.lean) now computes a matrix entry directly along decorated gluings, using only class-zero constants on the other components. Its [equality theorems](AxiomaticGW/Surfaces/GenusTwoLeadingRelations.lean) identify every BP/L24 entry with the full normalized equation at the requested full class, including class zero and arbitrary marking and cotangent powers. The [native diagnostic](scripts/GenusTwoLeading.lean) evaluates twenty-five rows in 7.462 seconds on the recorded run. All nineteen prior full-equation projections agree; six additional mixed-point BP rows have zero canonical coefficients and leave the sampled ranks unchanged. This is a proved coefficient algorithm and finite search evidence. Subsequent results below supply conditional finite-seed reconstruction; the full GKM gate remains open. See the [validation record](environments/genus-two-leading-validation.json).

The [general coefficient extension](AxiomaticGW/Surfaces/GenusTwoCoefficientRelations.lean) now handles smaller full curve classes as well, retaining positive-class rational components and calibration tails. The [plane BP audit](notes/mathematics/PlaneGenusTwoShifted.md) finds an exact symbolic shifted-degree matrix with determinant `7776d`, compared with ten native rows and seven admcycles pullbacks. Recursive signed point compression is now proved, and two shifted matrix entries have kernel replay, including the previously missing primary contribution. Plane calibration-tail cancellation, exact component-class support and canonical divisor-count formulas are now proved uniformly; the plane coefficient shortcut is proved equal to the full evaluator. The full signed point contraction now has a proved recursion over the exact effective remainder, including every new cotangent tail. On the ordinary plane, a one-degree shift uses only degree-zero and degree-one rational complements; the final genus-two component consumes no remainder. Primary rational point placements now have closed binomial formulas, and the complete one-psi plane component at remainder one has proved coefficients `-choose(n,2)` and `-n`, with zero unit contribution. The zero-remainder one-psi component is now proved equal to its canonical terminal expression minus the linear classical unit correction, with an explicit normalization independent of insertion sorting. The complete `PPP` row is now proved uniformly as `(0, -18, 18d)` for every positive degree, including its equality with the full normalized BP equation and its canonical support at a one-degree remainder. The mixed rational-complement formulas now retain the classical two-hyperplane branch. Source-degree cancellation is proved in all three mixed rows, including the cancellation of two individually nonzero `HHP` diagrams. Every nonzero genus-two coefficient has degree strictly below the equation degree. The complete `HPP` row is now proved as `(-36, 12-36d, 36d²)`, with exact canonical support and strict degree decrease after removing its three canonical variables. The complete `HHP` row is now proved as `(-108d, -27d²+27d+12, 27d³+9d²)`, with its full canonical support. The matrix extracted from the original three equations has determinant `7776d` for every positive `d`, an executable rational solver, and unique solutions for every supplied right-hand side. Every noncanonical variable with a nonzero coefficient in any row has strictly smaller degree. Coefficient collection now removes cancelled dependencies before recursion. The retained remainder has proved strict degree decrease, its evaluation gives the exact matrix right-hand side with the constant sign preserved, and the solved canonical step follows from the original BP geometry and finite low-genus seeds. Every retained dependency is now proved to be one of the three canonical families at a strictly smaller degree. A terminating recursion reconstructs all three families from the existing finite seeds, with uniqueness from the original BP equations and soundness for the actual plane theory under the named geometric inputs. The initial primary entry is derived from the source-degree-one HPP equation. Kernel replay now proves its complete lower-genus constant is `1/80`, giving the initial triple `(0, -1/960, 0)` without another seed. Scalar remainder evaluation and a claim-bound finite-table checker are proved equivalent to the original recursion. Kernel replay certifies the primary and both first-descendant plane line values as zero, including their exact-query comparison with the pinned GKM producer. Certified lower-genus support now extends to degree five for the shifted quartic equations. The complete twelve-query plane candidate calculation through degree four now matches the held published table, including the quartic triple `(27,42,25/4)`. All scalar kernel certificates and the complete twelve-query table are now accepted; the replay follow-up below records their validation. The geometric claim theorem composes accepted query certificates with the original named geometric inputs and the same three seeds. No additional numerical seed is assumed. Both genus-two blowup reconstructions, the fixed numerical suites and full class-valued GKM interoperability remain open; the following extension supplies arbitrary plane descendants. The [canonical reconstruction theorem](AxiomaticGW/Surfaces/PlaneGenusTwoReconstruction.lean) and [latest validation](environments/genus-two-plane-reconstruction-validation.json) record the proved scope and remaining computational work.

The cubic and quartic scalar certificates and all twelve full canonical requests through degree four now pass kernel checking. [Marking-state symmetry](AxiomaticGW/Surfaces/PlaneGenusTwoScalarSymmetry.lean) permits arithmetic reuse only for equal transported states, retaining all six marking occurrences. [Direct nonprimary coefficients](AxiomaticGW/Surfaces/PlaneGenusTwoFirstCoefficients.lean) prove that primary cotangent-tail corrections cannot contribute to a requested positive-power variable when the main component has total psi degree at most one. The optimized evaluator is proved equal to the original and retains its fallback elsewhere. The quartic triple is `(27, 42, 25/4)`. The [bounded lookup](AxiomaticGW/Surfaces/PlaneGenusTwoBenchmarks.lean) checks the complete incoming query, proves coverage of every positive plane class through energy twelve, and returns an accepted full-query claim. The [replay validation](environments/genus-two-plane-scalar-replay-validation.json) records the complete certificates and rejected component forgeries. The fixed applications, numerical bounds, seeds and full semisimple GKM completion gate are unchanged.

Use the certified finite suite directly from the public library:

```lean
import AxiomaticGW
open AxiomaticGW SurfaceGenusTwo

#eval planeCanonicalBenchmark? (SurfaceQuery.points .plane 2 ![4] 13) -- some 27
#eval planeCanonicalBenchmark? (SurfaceQuery.points .plane 2 ![5] 16) -- none
```

`planeCanonicalBenchmark?_sound` supplies the full-query certificate consumed by `planeCheckCanonicalClaim_checkedEval_from_geometry`. The latter retains the original geometric inputs and the same three seeds. An unsupported lookup is distinct from a certified zero.

The [plane low-psi evaluator](AxiomaticGW/Surfaces/PlaneGenusTwoLowPsi.lean) now reconstructs every finite genus-two insertion list with total psi degree at most one from the original three canonical families. Its ordered query interface preserves all state/power occurrences, and its geometric interpretation uses the unchanged inputs and seeds. For higher powers, the [square/product reduction](AxiomaticGW/Surfaces/GenusTwoPsiReduction.lean) now isolates the leading monomial after any number of added markings. Every remaining term has a boundary edge, so each residual genus-two dependency has strictly smaller total psi degree. The complete signed equations follow from the original geometric generators. The [marking selection and terminating ancestor recursion](AxiomaticGW/Surfaces/GenusTwoAncestors.lean) are now implemented, with independence of sufficient fuel and uniqueness relative to the low-psi terminal family. The [plane descendant consumer](AxiomaticGW/Surfaces/PlaneGenusTwoDescendants.lean) now composes this recursion with the original geometric inputs, the proved low-psi evaluator and reconstructed calibration. Its ordered query theorem identifies every finite genus-two plane descendant, including degree zero and empty markings, from exactly the existing three seeds. Accepted canonical tables can replace ancestor terminal values throughout their degree range. The remaining few-marking certificates, both blowups and full GKM/release gates remain open. See the [validation record](environments/genus-two-plane-descendant-validation.json).

The [degree-zero descendant comparison](AxiomaticGW/GW/Descendants/DegreeZeroComparison.lean) now proves equality with ancestors for every finite stable marking set using the absence of positive rational tails. The [surface consumer](AxiomaticGW/Surfaces/GenusTwoDegreeZeroDescendants.lean) and [GKM replay](AxiomaticGW/GKM/Fixtures/GenusTwoDegreeZeroReplay.lean) certify the nonzero shared genus-two query `tau_2(1)` at class zero on all three targets: `7/640`, `7/720` and `49/5760`. The interpretation uses the original finite low-genus seeds and geometric inputs, with no new genus-two seed. The positive-degree blowup reconstructions and actual class-valued GKM/CohFT bridge remain open; see the [validation](environments/genus-two-degree-zero-descendant-validation.json).

The [plane few-marking frame](AxiomaticGW/Surfaces/PlaneGenusTwoFewMarkings.lean) proves complete coverage of all 48 required ordered queries. Their original descendant values now all have [kernel replay](AxiomaticGW/GKM/Fixtures/PlaneGenusTwoFewMarkingsReplay.lean), agreeing with the pinned native GKM candidates. Exact incoming query/value binding and coherent false-value rejection also pass. The certificates interpret ordinary invariants under the original geometric inputs and seeds; they do not certify localization geometry or import CohFT classes.

[Shared ancestor certificates](AxiomaticGW/Surfaces/GenusTwoAncestorCertificate.lean) now certify all 39 full ancestor keys and all 539 original boundary terms used by the 48 plane requests. The [component replay](AxiomaticGW/GKM/Fixtures/PlaneGenusTwoComponentsReplay.lean) checks 291 distinct lower-genus values. Partial caches preserve the original square/product equations and the elliptic component recursion, with the original algorithm retained at omitted keys. All ancestor rows, complete descendant expansions, arithmetic and final query acceptance now pass. The [validation record](environments/genus-two-plane-component-replay-validation.json) records the accepted scope, rejected forgeries, source pins and measured resource costs. Both genus-two blowup reconstructions and the full semisimple CohFT/release gates remain open.

The [few-marking lookup](AxiomaticGW/Surfaces/PlaneGenusTwoFewMarkingBenchmarks.lean) is available from `import AxiomaticGW`:

```lean
open AxiomaticGW SurfaceGenusTwo

#eval planeFewMarkingBenchmark?
  ⟨2, ![1], [⟨.point, 1⟩, ⟨.point, 1⟩]⟩ -- some (1 / 144)
```

`planeFewMarkingBenchmark?_sound` identifies each returned value with the original descendant algorithm. `planeFewMarkingBenchmark?_domain` proves exact coverage of the fixed suite; an outside request returns no answer, rather than a certified zero.

The [full few-marking request domain](AxiomaticGW/Surfaces/GenusTwoFewMarkings.lean) now has a completeness theorem for all three surfaces. Its [held manifest](environments/genus-two-few-markings-requests.json) fixes 48 plane, 656 one-blowup and 4,495 two-blowup ordered requests before numerical answers are supplied. Original reconstruction currently covers 48 plane, 263 one-blowup and 1,235 two-blowup requests. At energy two on the two-point blowup, all 630 requests have native field values and 520 also have original reconstruction witnesses. [Original witness counts](AxiomaticGW/GKM/Fixtures/BlowupPositivePlaneEnergyTwoBenchmark.lean) · [630 native references](AxiomaticGW/GKM/Fixtures/BlowupTwoEnergyTwoNativeCoverage.lean)

The [blowup canonical families](AxiomaticGW/Surfaces/GenusTwoCanonicalQueries.lean) have full-class normalization support. A named [exceptional point evaluation hypothesis](AxiomaticGW/Surfaces/ExceptionalEvaluationSupport.lean) gives their positive exceptional zero boundary and helps derive the [F₁ class-zero primary point](AxiomaticGW/Surfaces/GenusTwoExceptionalInitialValues.lean) from the original BP geometry and existing divisor seed. Its geometric applicability remains explicit in the [input ledger](notes/mathematics/SurfaceReconstructionInputs.md).

The [uniform shifted H pivot](AxiomaticGW/Surfaces/GenusTwoBlowupHContributions.lean) is now −1 at every positive-energy full class. The exact 27-term genus-two coefficient reduces to two original contributions of −1/2. [Subcritical source-column vanishing](AxiomaticGW/Surfaces/GenusTwoBlowupHSupport.lean) and [equal-measure cancellation](AxiomaticGW/Surfaces/GenusTwoBlowupHCoupling.lean) prove that every nonzero H coefficient in the full normalized row is at the requested class or strictly earlier in the established reconstruction order. Distinct exceptional classes and negative signed multiplicities remain separate.

The [BP HHH coefficients](AxiomaticGW/Surfaces/GenusTwoBlowupPCoefficients.lean) are $18,-18d,0$ for H/P/K at positive energy; the P pivot requires positive plane degree. [Same-class primary N vanishing](AxiomaticGW/Surfaces/GenusTwoBlowupPPrimary.lean) and [nonprimary support](AxiomaticGW/Surfaces/GenusTwoBlowupPSupport.lean) now exclude different-class nonprimary columns of equal plane degree and force every surviving K column to smaller plane degree. [Complete P-row support](AxiomaticGW/Surfaces/GenusTwoBlowupPPrimarySupport.lean) now proves that every surviving primary column strictly lowers plane degree and every surviving canonical column is its own P variable or earlier in the reconstruction order. The proof derives exceptional rational point-tail vanishing from the existing genus-zero reconstruction and retains the generator seed one. These identities add no seed or geometric hypothesis. The canonical reconstruction below now supplies the remaining primary N equation and the combined recursion; both blowup numerical suites remain open.

The [complete primary BP/L24 closure](AxiomaticGW/Surfaces/GenusTwoCanonicalRelations.lean) now proves that every surviving variable is a canonical descendant at a full effective subclass; no unresolved ancestor callback remains. The [solved P row](AxiomaticGW/Surfaces/GenusTwoBlowupPRow.lean) collects cancellations, removes its own column and proves every remaining dependency is earlier. At positive plane degree it computes the remainder divided by $18d$, with uniqueness relative to earlier values. This is one derived row; the combined reconstruction and its conditional geometric interpretation are supplied below.

The [complete H support](AxiomaticGW/Surfaces/GenusTwoBlowupHOtherFamilies.lean) now excludes every same-plane primary, point-descendant and exceptional-descendant column from the original shifted L24 row. Its [solved H step](AxiomaticGW/Surfaces/GenusTwoBlowupHRow.lean) is the collected remainder, with uniqueness and agreement between different exceptional shifts when the original equations hold. The [exceptional BP coefficients](AxiomaticGW/Surfaces/GenusTwoBlowupKCoefficients.lean) give a uniform K_i pivot $-18$, signed P coefficient $18\alpha_i$, and zero other same-class K_j coefficients. The [solved K step](AxiomaticGW/Surfaces/GenusTwoBlowupKRow.lean) is the remainder divided by $18$, valid at every positive-energy full class, including zero plane degree and negative signed multiplicities. Both remainders use only earlier canonical values. No new seed, geometric law or assumed recurrence is introduced. The primary N row and combined finite-seed reconstruction are now supplied below.

The [complete primary N row](AxiomaticGW/Surfaces/GenusTwoBlowupNRelation.lean) combines the original BP rows at $\beta+E_i$ as $(3d/2)EHH-EEH+(d/2)EEE-HHH/3$. Its [uniform coefficient proof](AxiomaticGW/Surfaces/GenusTwoBlowupNCoefficients.lean) gives pivot $6d$; [complete support](AxiomaticGW/Surfaces/GenusTwoBlowupNCanonicalSupport.lean) proves every other surviving canonical state is earlier, including all same-plane exceptional-column cancellations. Negative and zero signed multiplicities are retained. The [canonical recursion](AxiomaticGW/Surfaces/GenusTwoBlowupRecursion.lean) terminates in the proved order of plane degree, family rank and energy, satisfies its original selected equations at positive plane degree, and is unique among their solutions with the same finite boundary data. [Primitive geometric soundness](AxiomaticGW/Surfaces/GenusTwoBlowupReconstruction.lean) derives the needed equations from the original relation sources, finite seeds and named geometric compatibilities; class-zero primary N is derived without an extra seed.

[All finite blowup descendants](AxiomaticGW/Surfaces/GenusTwoBlowupDescendants.lean) now reduce to that canonical table, with the full signed ancestor calibration retained at every effective subclass. The [final geometric consumer](AxiomaticGW/Surfaces/GenusTwoBlowupDescendantReconstruction.lean) covers arbitrary finite markings, cohomology states and descendant powers, including class zero and empty markings, using the original geometric inputs. Together with the plane algorithm, this closes the conditional genus-two reconstruction theorem for all three fixed targets. Release still requires the remaining positive-degree blowup entries through energy twelve, the uncovered few-marking requests, the geometric semisimple GKM comparison and offline corpus replay. R7 remains partially accepted. The new [validation record](environments/genus-two-blowup-reconstruction-validation.json) distinguishes proved reconstruction from numerical execution and geometric realization.


The [Sage/admcycles environment guide](notes/references/AdmcyclesEnvironment.md) provides the tested native macOS arm64 package lock, activation commands, and an exact genus-two relation smoke test. Sage is an optional exploration dependency; the Lean build does not require it.

The native graph benchmark runs the proved bounded enumerator over the 68 stable cases with genus at most two, at most six labelled markings, and codimension bounds zero through three:

```bash
LEAN_STACK_SIZE_KB=2097152 lake exe graphCorpus
lake exe graphCorpus --single 2 0 2
python3 scripts/verify_graph_corpus.py
```

Smaller bounds run first. Counts and elapsed milliseconds are emitted as JSON lines on stdout, with progress on stderr. These are formal-stratum counts, not cohomology dimensions or GW invariants. The completed coherent run covers all 68 cases and reports 39,109 bounded formal strata at genus two, six markings, bound three. Its [archived corpus](environments/graph-corpus-native-osx-arm64.jsonl) and [manifest](environments/graph-corpus-native-osx-arm64.json) passed source/hash, coverage, monotonicity, and six kernel-fixture comparisons. The large stack setting above was used for this run. Earlier failed attempts remain recorded separately.

## Getting started

Install Lean with [elan](https://github.com/leanprover/elan), clone the repository, and run:

```bash
lake exe cache get
lake build
lake test
```

The project pins Lean and mathlib to `v4.32.0`. Import the current public API with:

```lean
import AxiomaticGW
```

Run `lake lint` before submitting changes. CI performs the build, test, and lint steps on every pull request to `main`.

## Final scope

The endpoint is an **all-genus axiomatic Gromov--Witten theory**, resolved by curve class and equipped with the complete descendant package. In particular, the final theory is intended to support

- primary GW classes for every stable `(g, S)` and every effective curve class;
- separating and nonseparating gluing, the flat unit, grading, virtual dimension, effectivity, and the divisor axiom;
- descendant insertions indexed by arbitrary powers of stable-map `psi`-classes;
- ancestor insertions using stable-curve `psi`-classes, together with the descendant--ancestor comparison;
- a beta-preserving Novikov completion over a positive locally finite effective curve-class monoid;
- all-genus descendant and ancestor genus potentials and total free energies;
- string, dilaton, divisor, splitting, genus-reduction, and tautological relations whenever the required abstract geometric operations are present.

A bare CohFT already contains all stable genera. The genus-zero API is only a derived restriction used to prove associativity and WDVV. Descendants are not fields of the minimal CohFT structure: they require `psi`-classes, pushforwards, integration, and projection formulas. Moreover, stable-map descendants and stable-curve ancestors are kept distinct.

## Architecture

The intended dependency direction is

```text
Mathlib -> Linear -> Frobenius -> TFT
              \                    \
               -> Combinatorics -> CohFT -> GW -> Geometry
               -> Coefficients ------------/
```

The implemented source layout is:

```text
AxiomaticGW/
  Linear/
    PerfectPairing.lean
    Copairing.lean
    Contraction.lean
    SeparatingContraction.lean # contraction through linear component integrals
    PairingTransport.lean      # perfect metrics and contractions under state equivalence

  Frobenius/
    Basic.lean
    Constructions.lean
    Coalgebra.lean
    Examples.lean

  TFT/
    FiniteProduct.lean
    Correlator.lean
    Sewing.lean
    Basic.lean
    Frobenius.lean
    Classification.lean
    Examples.lean

  Combinatorics/
    StableArity.lean
    StableGraph.lean            # finite stable graphs and optional graph pullbacks

  Coefficients/
    EffectiveCurveClass.lean
    WeightedCurveClass.lean    # executable bounded classes and complete splittings
    Novikov.lean
    GenusExpansion.lean
    DescendantVariables.lean

  CohFT/
    Topological.lean           # implemented scalar-valued stable theory
    StableCurve.lean           # implemented abstract even-cohomology targets
    Basic.lean                 # implemented full all-genus CohFT
    Transport.lean             # class-valued state transport with proved gluing laws
    Constant.lean              # implemented degree-zero model and conversion
    GenusZero.lean             # implemented genus-zero restriction
    Frobenius.lean             # implemented extraction, WDVV, associativity
    TopologicalPart.lean       # implemented degree-zero scalarization
    Classification.lean       # implemented stable-arity Frobenius round trip
    Tautological.lean          # psi, integration, pushforward, kappa
    Ancestors.lean             # stable-curve ancestor correlators
    PsiGluing.lean            # derived cotangent monomial gluing laws
    GluingForgetful.lean      # primitive universal-curve/gluing base-change laws
    NonseparatingPushforward.lean # primitive Gysin laws and derived boundary contraction
    SeparatingPushforward.lean # product integration and ordered boundary contraction

  GW/
    Basic.lean                 # beta-resolved, full all-genus primary theory
    SmallQuantumProduct.lean   # derived small WDVV and associativity
    Constant.lean              # beta-zero reference model
    BigQuantumProduct.lean     # big product, genus-zero WDVV, and primary potential
    NonseparatingBoundary.lean # class-preserving boundary and ancestor contraction
    SeparatingBoundary.lean   # complete effective-class splitting and ancestors
    Descendants/
      Basic.lean               # stable-map descendant classes
      Comparison.lean          # descendant--ancestor residual decomposition
      Stabilization.lean       # rational tails, calibration, quantized comparison
      Equations.lean           # string, dilaton, divisor law package
      Exceptional.lean         # signed dilaton coefficient and exceptional terms
      Potentials.lean          # invariant-defined descendant/ancestor series
      FullPotential.lean       # coherent numerical extension and corrected equations
      FullDivisor.lean         # optional all-arity divisor equation and exceptions

  PointTarget/
    Descendants.lean           # stable-curve intersections and DVV hypothesis

  GKM/
    CurveConventionCertificate.lean # full class, fan, and invariant-edge acceptance
    EquivariantCoefficients.lean # exact fraction field and regular specialization
    FixedPointAlgebra.lean     # actual localization trace and inverse Euler metric
    StateSpaceTransport.lean   # checked matrix, metric, product, and unit transport
    StateSpaceCertificate.lean # claim-bound acceptance and algebra interpretation
    Fixtures/
      CurveFrames.lean        # independently held fan and full curve requests
      CurveReplay.lean        # generated kernel proofs for twelve invariant edges
      SurfaceFrames.lean      # fixed requests and ordinary surface algebra
      SurfaceReplay.lean      # generated kernel proofs for all three state tables

  Surfaces/
    Cohomology.lean            # graded Frobenius algebra of plane blowups
    CurveClasses.lean          # fixed P2, F1, and two-point blowup coordinates
    TargetData.lean            # divisor pairing, Chern class, and elliptic parameters
    Queries.lean               # query domain, degree checks, and finite seed obligations
    Contraction.lean           # exact finite inverse metric, including exceptional signs
    GluingEvaluation.lean      # executable full-class surface graph equations
    AncestorPolynomial.lean    # symmetric component variables and polynomial soundness
    PrimaryReduction.lean     # signed string/divisor reduction to full point queries
    PolynomialReduction.lean  # dimension filtering and sound component substitution
    DegreeZero.lean            # primary genus-zero/one values at the zero curve class
    DegreeZeroPolynomial.lean  # sound degree-zero substitution in Getzler equations

  Tautological/
    DecoratedStableGraph.lean  # decorated stable graphs modulo isomorphism
    GraphBounds.lean           # spanning-tree, stability, and decoration bounds
    GraphEnumeration.lean      # executable bounded strata, proved sound and complete
    GraphIsomorphisms.lean     # executable isomorphism and automorphism enumeration
    LegPsi.lean                # external psi action, grading, and normalization proofs
    LegPsiRealization.lean     # conditional realization and integrated relation equations
    NonseparatingGluing.lean   # graph gluing, node powers, quotient, and degree proofs
    NonseparatingRealization.lean # conditional graph interpretation and certificate transfer
    Relabel.lean               # external incidence, powers, and automorphism transport
    RelabelRealization.lean    # conditional graph and state-insertion naturality
    SeparatingGluing.lean      # component graph gluing and bilinear raw pushforward
    SeparatingRealization.lean # conditional product interpretation and row transfer
    BasicStrata.lean           # one-vertex and fundamental strata
    StrataModule.lean          # free rational module and relation quotients
    StrataAlgebra.lean         # certified product contract, not an instance
    StrataRealization.lean     # degree-preserving cohomology realization
    Getzler.lean               # named Mbar(1,4) relation generator
    GetzlerGraphs.lean         # 33 marked graphs and seven normalized cycles
    GetzlerRealization.lean    # checked Getzler consequence and conditional integrals
    GluingExpression.lean     # finite compositions of raw graph gluings
    GluingEvaluation.lean     # derived full-class iterated GW contractions
    GetzlerGluing.lean         # explicit constructions of all 33 marked columns
    GetzlerGW.lean             # checked replay implies the primary GW equation
    GluingAncestors.lean      # arbitrary external powers in iterated contractions
    GetzlerAncestors.lean     # checked replay implies the ancestor equation
    GluingMarking.lean        # all finite marking placements, retaining multiplicities
    GluingForgetful.lean      # derived forgetful realization of gluing expressions
    GetzlerForgetful.lean     # ancestor equations with arbitrary extra markings
    LowGenus.lean              # genus-zero psi values and geometry interface
    WDVV.lean                  # three marked raw boundary columns and exact row frame
    WDVVRealization.lean       # conditional certificate-to-GW convolution theorem

  Geometry/
    VirtualGWPackage.lean      # algebraic output carrier, not a realization proof
```

Only modules with implemented content are created. Future concrete targets and geometric realizations will be added when they carry proofs rather than placeholder declarations.

The essential formalization chain is

```text
perfect duality and contractions
  -> Frobenius algebra and topological CohFT
  -> full all-genus CohFT
  -> beta-resolved all-genus primary GW theory
  -> Novikov coefficients and quantum-product WDVV
  -> descendants, ancestors, rational-tail comparison, and total free energies
  -> stable graphs, arbitrary-background WDVV, and explicit unstable extensions
  -> decorated strata syntax, known relation quotients, and realization adapters
  -> algebraic output carrier for future virtual stable-map geometry
```

## Completed foundations

The completed Frobenius API now follows the chain

```text
counit -> trace pairing -> perfect duality -> symmetric copairing
       -> comultiplication -> cocommutative coalgebra -> Frobenius relation
       -> handle element.
```

The core definitions and proofs are basis-free. `CommFrobeniusAlgebra` is an explicit object rather than a typeclass, since a fixed algebra can admit more than one Frobenius functional. Its canonical coalgebra can be installed as a local mathlib instance when needed.

The completed topological-theory layer follows the chain

```text
finite-labelled multiplication
  -> all-genus Frobenius correlators
  -> basis-free named-slot contraction
  -> separating and nonseparating sewing
  -> bundled two-dimensional TFT
  -> stable scalar-valued topological CohFT
  -> recovery of the counit and three-point product
  -> full stable-arity Frobenius classification.
```

The geometric oriented bordism category is not formalized: `TwoDimensionalTFT` is its algebraic correlator presentation. `TopologicalCohFT` remains the scalar-valued degree-zero theory, while `CohFT` is valued in an abstract `StableCurveCohomology`. The constant target connects the two interfaces and serves as their regression model. For a general CohFT, `ConnectedDegreeZero` produces its topological part, while `GenusZeroGeometry` supplies the low-genus facts used for Frobenius extraction and WDVV.

## Notes

- [Notes index](notes/README.md)
- [Mathematics-to-Lean map](notes/MathematicsToLean.md)
- [Implementation progress record](notes/milestones/ImplementationProgress.md)
- [The mathematics and goals of AxiomaticGW](notes/mathematics/ProjectMathematicsAndGoals.md)
- [The point target and stable-curve intersection theory](notes/mathematics/PointTargetAndStableCurves.md)
- [Mathematics notes for M1--M10](notes/mathematics/README.md)
- [Roadmap to axiomatic Gromov--Witten theory](notes/milestones/AxiomaticGWRoadmap.md)
- [Completed topological field theory milestones](notes/milestones/TopologicalTFTMilestones.md)
- [Mathematical terminology audit](notes/milestones/TerminologyAudit.md)

Build the project with:

```bash
lake build
```

## Contributing

Contributions to definitions, proofs, examples, documentation, and API design are welcome. Please read [CONTRIBUTING.md](CONTRIBUTING.md) and consult the [design-decision ledger](notes/milestones/CohFTDesignDecisions.md) before changing an unsettled architectural convention.

Before opening a pull request, run:

```bash
lake build
lake lint
lake test
git diff --check
```

Please report ordinary bugs and mathematical issues through GitHub Issues. Sensitive security reports should follow [SECURITY.md](SECURITY.md).

## License

AxiomaticGW is released under the [Apache License 2.0](LICENSE). Citation metadata is available in [CITATION.cff](CITATION.cff), and notable changes are recorded in [CHANGELOG.md](CHANGELOG.md).

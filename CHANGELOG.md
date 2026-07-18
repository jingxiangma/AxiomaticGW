# Changelog

All notable user-visible changes to AxiomaticGW will be recorded here.

The project is research-stage and follows the pinned Lean/mathlib version in `lean-toolchain` and `lakefile.toml` rather than a stable compatibility policy.

## Unreleased

### Added

- Finite-free commutative Frobenius algebras and their canonical coalgebra.
- Basis-free copairing and named-slot contraction APIs.
- Finite-labelled all-genus topological correlators.
- Separating and nonseparating sewing theorems.
- Bundled two-dimensional TFTs and scalar-valued topological CohFTs.
- Internally graded even-cohomology targets with primitive stable-curve pullbacks and coherence laws.
- Full cohomology-valued all-genus CohFTs and the optional `GradedCohFT`, `GenusZeroGeometry`, and `ConnectedDegreeZero` layers.
- Target-generic node contraction and tensor-valued separating contraction.
- The constant degree-zero target, forward/reverse topological CohFT conversion, and end-to-end regression tests.
- Degree-preserving stable-curve pullbacks and the immediate forget/glue coherence laws needed by the flat-unit and topological-part constructions.
- Genus-zero restriction, Frobenius extraction, metric invariance, WDVV, commutativity, unit laws, and associativity for full CohFTs.
- Coherent degree-zero scalarization and classification of every stable topological CohFT correlator by its extracted commutative Frobenius algebra.
- README-linked mathematics-to-Lean and implementation-progress records covering conceptual correspondence, milestone scope, verification evidence, and commit provenance.
- Stable-curve psi classes, integration, forgetful pushforward, kappa classes, and numerical ancestor correlators.
- Positive locally finite effective curve monoids and finite curve-class splitting sets.
- Graded, beta-resolved primary GW theories with virtual-degree, normalization, gluing, and optional divisor axioms, plus a beta-zero reference model.
- The beta-preserving Novikov completion with proven convolution ring laws, monomials, and an injective finite monoid-algebra inclusion.
- Fixed-beta three-point products with derived coefficientwise small WDVV, associativity, commutativity, and unit laws.
- Distinct stable-map descendant and stable-curve ancestor classes with a weak residual decomposition and an optional positive-degree rational-tail factorization package.
- Novikov-valued formal potentials, commuting formal partial derivatives with a Leibniz rule, Laurent total free energies, and separately usable stable string/dilaton and descendant divisor law interfaces.
- Descendant and ancestor potentials constructed from invariants, stable-sector and directional differential operators, and the potential-level descendant--ancestor residual identity.
- The invariant-defined commutative big quantum product and its proved zero-background specialization to the small quantum product.
- Finite stable graphs with vertex stability, arithmetic genus, complete edge orders, and optional order-independent graph pullbacks.
- An explicit arbitrary-background genus-zero WDVV package deriving coefficientwise associativity of the big quantum product, together with the stable primary potential.
- Rational-tail stabilization data, a two-point calibration with a separately justified symplectic identity, and explicit coefficientwise Fock/quantized comparison carriers.
- Explicit unstable descendant conventions, a full descendant potential, and global correlator-level string and dilaton equations.
- A point-target stable-curve block with psi intersection numbers, dimension vanishing, initial values, a WDVV check, and the all-genus DVV proposition as an explicit geometric hypothesis.
- Decorated stable graphs modulo label-preserving isomorphism, including edge-branch exchange, kappa and psi decorations, codimension, one-vertex strata, and the free rational strata module.
- Known-relation quotients, degree-preserving realization maps and quotient factorization, a certified product contract, the exact named Getzler relation on `Mbar(1,4)`, and executable low-genus genus-zero psi values.
- An abstract virtual-GW algebraic output carrier connecting future geometric constructions to the primary and descendant axiomatic layers; the carrier itself is not a realization theorem.
- Mathematical notes and a roadmap toward axiomatic Gromov--Witten theory.

### Changed

- Reworked the mathematical notes against the project-local arXiv TeX sources, replacing narrative descriptions of copairing, gluing, virtual classes, descendant--ancestor comparison, quantum products, and GW equations with explicit formulas and stated conventions.
- Made production simplifier calls explicit with `simp only` or `simpa only`, and documented the dependency-stability policy for future proofs.
- Tightened public mathematical comments so fixed-class quantum products, rational-tail stabilization data, and coefficientwise Fock carriers are described without nonstandard or overstated terminology.
- Renamed the public `TopologicalCorrelatorTheory` API to `TwoDimensionalTFT` and `threePointFunctional` to `threePointFunction` to match the standard mathematical terminology.
- Renamed `CurveClassGW` to `GromovWittenTheory` and standardized the public small and big quantum-product declarations, including `GenusZeroWDVV`.
- Replaced `GW/QuantumProduct.lean` and `GW/FormalQuantumProduct.lean` with the canonical `GW/SmallQuantumProduct.lean` and consolidated `GW/BigQuantumProduct.lean` modules.
- Moved the point-target API from `AxiomaticGW.Point.Descendants` to `AxiomaticGW.PointTarget.Descendants`.

### Fixed

- Corrected the forget/nonseparating and left forget/separating label transports in the stable-curve coherence axioms.
- Added the stable-curve top-degree bound, forgetful-pushforward relabelling and degree-zero laws, and derived kappa naturality and degree theorems.
- Corrected the stable-map descendant grading so cotangent powers contribute before testing whether the expected output degree is nonnegative.
- Corrected decorated-graph isomorphism so the two branches of every internal edge may be exchanged, including transport of half-edge psi decorations.
- Added relabelling and total-degree theorems for ancestors and descendants, and derived the residual subtraction, relabelling, and homogeneity API.
- Replaced documentation claims of geometric boundary support and virtual realization with the weaker residual and carrier properties actually represented by the public API.
- Synchronized the README, mathematics notes, roadmap, mathlib inventory, design ledger, and historical follow-up annotations with the stable-graph, arbitrary-background genus-zero WDVV, stabilization, calibration, and full-potential APIs delivered in `9a3d625`.

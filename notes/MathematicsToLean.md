# Mathematics-to-Lean map

This file is the canonical bridge between the mathematical exposition and the Lean implementation. It maps implemented mathematical sections to source modules and principal declarations, and it states explicitly when a mathematical topic is intentionally not yet formalized.

The [implementation progress record](milestones/ImplementationProgress.md) contains dated scope, commit provenance, and verification evidence. Generated API documentation remains the declaration-level reference; this map explains where the mathematics enters that API.

## Cross-layer structure dependencies

- The formula-level input--output relationships among commutative Frobenius algebras, two-dimensional TFTs, CohFTs, and curve-class-resolved axiomatic GW theories are summarized in [Core structure dependencies](mathematics/CoreStructureDependencies.md).
- Frobenius-to-TFT construction and recovery correspond principally to [`TFT/Correlator.lean`](../AxiomaticGW/TFT/Correlator.lean), [`TFT/Frobenius.lean`](../AxiomaticGW/TFT/Frobenius.lean), and [`TFT/Classification.lean`](../AxiomaticGW/TFT/Classification.lean).
- The constant topological-CohFT construction, degree-zero topological part, and genus-zero Frobenius extraction correspond principally to [`CohFT/Topological.lean`](../AxiomaticGW/CohFT/Topological.lean), [`CohFT/TopologicalPart.lean`](../AxiomaticGW/CohFT/TopologicalPart.lean), and [`CohFT/Frobenius.lean`](../AxiomaticGW/CohFT/Frobenius.lean).
- The beta-resolved refinement and conditional Novikov recombination correspond principally to [`GW/Basic.lean`](../AxiomaticGW/GW/Basic.lean) and [`Coefficients/Novikov.lean`](../AxiomaticGW/Coefficients/Novikov.lean). The latter supplies coefficient convolution; no general bundled conversion from `GromovWittenTheory` to a Novikov-valued `CohFT` is claimed.

## M1. Perfect pairings and Frobenius algebras

**Mathematical note:** [M1. Perfect pairings and Frobenius algebras](mathematics/M01PerfectPairingsAndFrobeniusAlgebras.md).

- [Algebraic setting](mathematics/M01PerfectPairingsAndFrobeniusAlgebras.md#1-algebraic-setting) and [commutative Frobenius algebras](mathematics/M01PerfectPairingsAndFrobeniusAlgebras.md#2-commutative-frobenius-algebras) correspond to [`Frobenius/Basic.lean`](../AxiomaticGW/Frobenius/Basic.lean), principally `tracePairing`, `CommFrobeniusAlgebra`, `CommFrobeniusAlgebra.pairing`, and `pairing_assoc`.
- [Copairing and contraction](mathematics/M01PerfectPairingsAndFrobeniusAlgebras.md#3-copairing-and-contraction) correspond to [`Linear/PerfectPairing.lean`](../AxiomaticGW/Linear/PerfectPairing.lean), [`Linear/Copairing.lean`](../AxiomaticGW/Linear/Copairing.lean), and [`Linear/Contraction.lean`](../AxiomaticGW/Linear/Contraction.lean), principally `SymmetricPerfectPairing`, `toDual`, `copairing`, `contractTwo`, `selfContract`, and `pairContract`.
- [Coalgebra structure](mathematics/M01PerfectPairingsAndFrobeniusAlgebras.md#4-coalgebra-structure) corresponds to [`Frobenius/Constructions.lean`](../AxiomaticGW/Frobenius/Constructions.lean) and [`Frobenius/Coalgebra.lean`](../AxiomaticGW/Frobenius/Coalgebra.lean), principally `casimir`, `handleElement`, `comul`, `coassoc`, `toCoalgebra`, and `toIsCocomm`.
- [Examples](mathematics/M01PerfectPairingsAndFrobeniusAlgebras.md#5-examples) correspond to [`Frobenius/Examples.lean`](../AxiomaticGW/Frobenius/Examples.lean), including `baseRing` and `productAlgebra`. The dual-number example remains mathematical only.

## M2. Two-dimensional topological field theory

**Mathematical note:** [M2. Two-dimensional topological field theory](mathematics/M02TwoDimensionalTFT.md).

- [Bordisms and field theories](mathematics/M02TwoDimensionalTFT.md#1-bordisms-and-field-theories) are represented algebraically by [`TFT/Basic.lean`](../AxiomaticGW/TFT/Basic.lean), [`TFT/Frobenius.lean`](../AxiomaticGW/TFT/Frobenius.lean), and [`TFT/Classification.lean`](../AxiomaticGW/TFT/Classification.lean), principally `TwoDimensionalTFT`, `CommFrobeniusAlgebra.toTwoDimensionalTFT`, and the product and round-trip theorems. The geometric oriented bordism category itself is deliberately not formalized.
- [Finite-labelled correlators](mathematics/M02TwoDimensionalTFT.md#2-finite-labelled-correlators) correspond to [`TFT/FiniteProduct.lean`](../AxiomaticGW/TFT/FiniteProduct.lean) and [`TFT/Correlator.lean`](../AxiomaticGW/TFT/Correlator.lean), principally mathlib's `MultilinearMap.mkPiAlgebra`, `CommFrobeniusAlgebra.correlator`, its normalization theorems, and `correlator_succ_eq_option_handle`.
- [Sewing identities](mathematics/M02TwoDimensionalTFT.md#3-sewing-identities) correspond to [`Linear/Contraction.lean`](../AxiomaticGW/Linear/Contraction.lean) and [`TFT/Sewing.lean`](../AxiomaticGW/TFT/Sewing.lean), principally `sewing_identity`, `selfContract_correlator`, and `pairContract_correlator`.
- [Topological CohFT viewpoint](mathematics/M02TwoDimensionalTFT.md#4-topological-cohft-viewpoint) corresponds to [`Combinatorics/StableArity.lean`](../AxiomaticGW/Combinatorics/StableArity.lean) and [`CohFT/Topological.lean`](../AxiomaticGW/CohFT/Topological.lean), principally `StableArity`, `TopologicalCohFT`, and the two `toTopologicalCohFT` constructions.
- Concrete correlator computations are collected in [`TFT/Examples.lean`](../AxiomaticGW/TFT/Examples.lean).

## M3. Stable curves and gluing

**Mathematical note:** [M3. Stable curves and gluing](mathematics/M03StableCurvesAndGluing.md).

- [Stable marked curves](mathematics/M03StableCurvesAndGluing.md#1-stable-marked-curves) are represented only through their numerical stable range in [`Combinatorics/StableArity.lean`](../AxiomaticGW/Combinatorics/StableArity.lean). The moduli stacks themselves are not constructed.
- [Primitive maps](mathematics/M03StableCurvesAndGluing.md#2-primitive-maps) and the [abstract cohomology system](mathematics/M03StableCurvesAndGluing.md#3-abstract-cohomology-system) correspond to [`CohFT/StableCurve.lean`](../AxiomaticGW/CohFT/StableCurve.lean), principally `EvenGradedAlgebra`, `StableCurveCohomology`, `GenusZeroGeometry`, `ConnectedDegreeZero`, and their degree and coherence fields.
- The constant degree-zero realization, including its canonical stable-graph pullback, is implemented in [`CohFT/Constant.lean`](../AxiomaticGW/CohFT/Constant.lean) and exercised through [`AxiomaticGWTest/Basic.lean`](../AxiomaticGWTest/Basic.lean).
- [Stable graphs](mathematics/M03StableCurvesAndGluing.md#4-stable-graphs) correspond to [`Combinatorics/StableGraph.lean`](../AxiomaticGW/Combinatorics/StableGraph.lean), principally `StableGraph`, `VertexLabel`, `totalGenus`, `ContractionOrder`, and the optional `StableGraphPullbacks`. Complete edge orders are proved permutation-equivalent, and an order-coherent pullback package yields a canonical order-independent graph pullback. Concrete geometric graph pullbacks remain instance data, and actual combinatorial edge contraction is not defined.

## M4. Full unital CohFT

**Mathematical note:** [M4. Full unital CohFT](mathematics/M04FullUnitalCohFT.md).

- [State space and classes](mathematics/M04FullUnitalCohFT.md#1-state-space-and-classes), [relabelling and gluing](mathematics/M04FullUnitalCohFT.md#2-relabelling-and-gluing), and [unit and normalization](mathematics/M04FullUnitalCohFT.md#3-unit-and-normalization) correspond to [`CohFT/Basic.lean`](../AxiomaticGW/CohFT/Basic.lean), principally `CohFT` and `GradedCohFT`.
- [Underlying Frobenius algebra](mathematics/M04FullUnitalCohFT.md#4-underlying-frobenius-algebra) corresponds to [`CohFT/GenusZero.lean`](../AxiomaticGW/CohFT/GenusZero.lean) and [`CohFT/Frobenius.lean`](../AxiomaticGW/CohFT/Frobenius.lean), principally `CohFT.toGenusZeroCohFT`, `GenusZeroCohFT.product`, `pairing_products_wdvv`, `product_assoc`, and `toCommFrobeniusAlgebra`.
- [Topological part and genus zero](mathematics/M04FullUnitalCohFT.md#5-topological-part-and-genus-zero) correspond to [`CohFT/TopologicalPart.lean`](../AxiomaticGW/CohFT/TopologicalPart.lean) and [`CohFT/Classification.lean`](../AxiomaticGW/CohFT/Classification.lean), principally `CohFT.topologicalPart` and `TopologicalCohFT.classification`. The latter currently inherits an `Algebra ℚ R` hypothesis from the full CohFT route.

## M5. Tautological classes and ancestors

**Mathematical note:** [M5. Tautological classes and ancestors](mathematics/M05TautologicalClassesAndAncestors.md).

- Stable-curve cotangent classes, top-degree integration, forgetful pushforward with relabelling naturality, degree shift, degree-zero vanishing and projection formula, rational-tail correction, and kappa classes correspond to [`CohFT/Tautological.lean`](../AxiomaticGW/CohFT/Tautological.lean), principally `PsiClasses`, `StableCurveIntegration`, `ForgetfulPushforward`, `PsiForgetFormula`, `PsiClasses.monomial`, and `PsiClasses.kappa`. General pushforward composition and base-change are not encoded.
- Numerical ancestor correlators and the constant-target model correspond to [`CohFT/Ancestors.lean`](../AxiomaticGW/CohFT/Ancestors.lean), principally `CohFT.ancestor`, `constantStableCurveCohomology.psiClasses`, `integration`, and `forgetfulPushforward`.
- Decorated stable graphs, their label-preserving isomorphisms, kappa/psi decorations, codimension, one-vertex strata, and isomorphism classes correspond to [`Tautological/DecoratedStableGraph.lean`](../AxiomaticGW/Tautological/DecoratedStableGraph.lean) and [`Tautological/BasicStrata.lean`](../AxiomaticGW/Tautological/BasicStrata.lean), principally `StableGraphCode`, `DecoratedStableGraph`, `TautologicalStratum`, `TautologicalStratum.oneVertex`, and `TautologicalStratum.fundamental`. Branch exchange at a node is part of graph isomorphism.
- The free rational strata module, codimension submodules, dimension relations, relation quotients, certified product contract, and degree-preserving cohomology realization correspond to [`Tautological/StrataModule.lean`](../AxiomaticGW/Tautological/StrataModule.lean), [`Tautological/StrataAlgebra.lean`](../AxiomaticGW/Tautological/StrataAlgebra.lean), and [`Tautological/StrataRealization.lean`](../AxiomaticGW/Tautological/StrataRealization.lean). `CertifiedStrataProduct` specifies the laws that a common-refinement and excess-intersection algorithm must prove; the algorithm itself is not implemented and no ring instance is installed.
- The seven-term Getzler relation on `Mbar(1,4)` is recorded in [`Tautological/Getzler.lean`](../AxiomaticGW/Tautological/Getzler.lean) as a normalization-explicit named generator. Its vanishing in `GetzlerStrataEncoding.KnownQuotient` is formal by construction, while `GetzlerRelationGeometry` keeps geometric validity as separate input. When a cycle-compatible realization is supplied, `knownRelations_le_realization_kernel` and `realizationFactor` prove the corresponding quotient factorization. [`Tautological/LowGenus.lean`](../AxiomaticGW/Tautological/LowGenus.lean) implements the standard genus-zero psi-value formula and an explicit certificate connecting it to a geometric integration model.
- Hodge/`lambda` classes, the all-genus common-refinement product enumeration, an explicit decorated-graph encoding of the seven normalized Getzler cycles, geometric proofs of tautological relations, and a concrete stable-curve cohomology ring remain unimplemented.

## M6. Curve-class-resolved GW axioms

**Mathematical note:** [M6. Curve-class-resolved GW axioms](mathematics/M06CurveClassResolvedGW.md).

- Positive locally finite effective classes and finite additive splittings correspond to [`Coefficients/EffectiveCurveClass.lean`](../AxiomaticGW/Coefficients/EffectiveCurveClass.lean), principally `EffectiveCurveMonoid`, `bounded`, `splittings`, and `hasAntidiagonal`.
- The graded state space, primary beta-resolved theory, virtual-degree law, and optional divisor axiom correspond to [`GW/Basic.lean`](../AxiomaticGW/GW/Basic.lean) and [`CohFT/Basic.lean`](../AxiomaticGW/CohFT/Basic.lean), principally `GradedStateSpace`, `GromovWittenTheory`, `GWOutputDegree`, and `GWDivisorAxiom`.
- The theory supported at beta zero is implemented in [`GW/Constant.lean`](../AxiomaticGW/GW/Constant.lean).

## M7. Novikov coefficients and quantum products

**Mathematical note:** [M7. Novikov coefficients and quantum products](mathematics/M07NovikovAndQuantumProducts.md).

- The beta-preserving completion, finite-antidiagonal convolution, monomials, and finite-support inclusion correspond to [`Coefficients/Novikov.lean`](../AxiomaticGW/Coefficients/Novikov.lean), principally `NovikovSeries`, `coeff_mul`, `monomial_mul_monomial`, and `ofMonoidAlgebra`.
- Fixed-beta three-point products and derived coefficientwise WDVV and associativity correspond to [`GW/SmallQuantumProduct.lean`](../AxiomaticGW/GW/SmallQuantumProduct.lean), principally `GromovWittenTheory.smallQuantumProductCoefficient`, `smallQuantumProduct`, `smallQuantumProductCoefficient_wdvv`, and `smallQuantumProductCoefficient_assoc`.
- The primary-background series, big quantum product, stable primary potential, and genus-zero WDVV hypothesis correspond to [`GW/BigQuantumProduct.lean`](../AxiomaticGW/GW/BigQuantumProduct.lean), principally `primaryThreePointSeriesCoefficient`, `bigQuantumProduct`, `GenusZeroWDVV`, `bigQuantumProduct_associative`, and `primaryPotential`. A full formal third-derivative identification is not yet asserted.

## M8. Descendants and ancestor comparison

**Mathematical note:** [M8. Descendants and descendant--ancestor comparison](mathematics/M08DescendantsAndAncestors.md).

- Beta-resolved ancestor classes and the distinct stabilized stable-map descendant family correspond to [`GW/Descendants/Basic.lean`](../AxiomaticGW/GW/Descendants/Basic.lean), principally `GromovWittenTheory.ancestorClass`, `ancestorClass_relabel`, `ancestorClass_total_degree`, `ancestorInvariant`, `StableMapDescendants`, and the two invariant relabelling theorems.
- The recorded residual and integrated identity correspond to [`GW/Descendants/Comparison.lean`](../AxiomaticGW/GW/Descendants/Comparison.lean), principally `DescendantAncestorComparison`, `boundaryCorrection_eq_sub`, `boundaryCorrection_relabel`, `boundaryCorrection_degree`, and `invariant_eq_ancestor_add_boundary`. These derived theorems make the weak residual coherent and homogeneous, but the interface still does not encode geometric boundary support or a stabilization theorem.
- The optional geometric strengthening corresponds to [`GW/Descendants/Stabilization.lean`](../AxiomaticGW/GW/Descendants/Stabilization.lean). `StabilizationBoundaryComparison` exhibits the residual as a finite sum over positive-degree rational-tail splittings, using explicit boundary pushforward and two-point tail-operator data. The same operators define `TwoPointCalibration`; `CalibrationBoundaryRelation` derives coefficientwise symplecticity, and `GiventalComparison` supplies the additional genus-one scalar factor and coefficientwise descendant--ancestor identity without treating them as consequences of the weak residual.

## M9. Potentials and equations

**Mathematical note:** [M9. All-genus potentials and equations](mathematics/M09PotentialsAndEquations.md).

- Descendant-variable indexing, Novikov-valued formal potentials, and partial derivatives with Leibniz and commutation laws correspond to [`Coefficients/DescendantVariables.lean`](../AxiomaticGW/Coefficients/DescendantVariables.lean), principally `DescendantVariable`, `FormalPotential`, `MvPowerSeries.pderiv`, `pderiv_mul`, and `iteratedPDeriv`.
- Genus potentials and Laurent-series total free energies correspond to [`Coefficients/GenusExpansion.lean`](../AxiomaticGW/Coefficients/GenusExpansion.lean), principally `GWPotentials`, `totalFreeEnergy`, and `totalFreeEnergy_coeff`.
- Stable-sector potentials constructed from descendant and ancestor invariants correspond to [`GW/Descendants/Potentials.lean`](../AxiomaticGW/GW/Descendants/Potentials.lean), principally `profileWeight`, `GromovWittenTheory.descendantPotential`, `ancestorPotential`, `stablePart`, `insertionDerivative`, and the residual identity `descendantPotential_eq_ancestor_add_boundary`. Profiles outside stable curve arities are set to zero by convention, not by a geometric vanishing theorem.
- Optional stable string and dilaton laws and the separately divisor-dependent law correspond to [`GW/Descendants/Equations.lean`](../AxiomaticGW/GW/Descendants/Equations.lean), principally `DescendantStringDilatonLaws`, `DescendantDivisorLaw`, and their compatibility package `DescendantEquationLaws`. The exponential total potential is deliberately not represented by this Laurent completion.
- Explicit unstable numerical data correspond to [`GW/Descendants/FullPotential.lean`](../AxiomaticGW/GW/Descendants/FullPotential.lean), principally `UnstableDescendantConventions`, `invariant`, `global_string`, `global_dilaton`, and `fullDescendantPotential`. Positive-degree unstable values are supplied data, never inferred from the stable-curve carrier.

## Point-target stable-curve block

**Mathematical note:** [The point target and stable-curve intersection theory](mathematics/PointTargetAndStableCurves.md).

- The point primary class, psi-class intersection numbers, point ancestors, dimension vanishing, initial values, and unit-class WDVV test correspond to [`PointTarget/Descendants.lean`](../AxiomaticGW/PointTarget/Descendants.lean), principally `PointTarget.primaryClass`, `intersectionNumber`, `ancestor`, `intersectionNumber_eq_zero_of_degree_ne`, `intersectionNumber_zero_three`, `intersectionNumber_one_one`, and `unitClass_wdvv`.
- The labelled all-genus DVV formula corresponds to `PointTarget.DVVRecursion`. It is an explicit higher tautological hypothesis on a geometric stable-curve model, not a theorem of the primitive `PsiClasses` interface.

## M10. Algebraic output carrier

**Mathematical note:** [M10. Geometric realization](mathematics/M10GeometricRealization.md).

- The algebraic output carrier for future virtual intersection theory corresponds to [`Geometry/VirtualGWPackage.lean`](../AxiomaticGW/Geometry/VirtualGWPackage.lean), principally `VirtualGWPackage` and its projections to the primary theory, descendants, and residual decomposition. The optional stabilization package is deliberately separate, and neither package proves that its fields arise from geometry.
- Actual moduli stacks, obstruction theories, and virtual fundamental classes are outside the implemented repository foundations.

## Maintenance rule

When a milestone changes the public mathematical API, update this map in the same change. Keep dated implementation and verification details in the [progress record](milestones/ImplementationProgress.md) rather than duplicating them here.
